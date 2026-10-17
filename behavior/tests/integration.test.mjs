import { test, before, after } from "node:test";
import assert from "node:assert/strict";
import { readFileSync, writeFileSync, mkdtempSync, rmSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { createServer } from "node:http";
import { Engine } from "../lib/engine.mjs";
import {
  extractPHP,
  extractProject,
  reconstructPHP,
} from "../extractors/php.mjs";
import { EvidenceStore } from "../lib/store.mjs";
import {
  SqliteTransfer,
  HttpAdapter,
  CommandAdapter,
  runScenario,
  mapObservation,
} from "../lib/adapters.mjs";
import {
  checkTrace,
  migrationContract,
  compareMigration,
  minimize,
} from "../lib/conformance.mjs";
import { explore, traverse, validatePath } from "../lib/explore.mjs";
import { canonical, digest } from "../lib/data.mjs";
import { compose } from "../lib/compose.mjs";
import { service } from "../lib/service.mjs";
import { analyse, exportFacts } from "../lib/analysis.mjs";
import {
  validateFacts,
  admit,
  reconstructBinary,
} from "../lib/reconstruct.mjs";
const source = readFileSync(
    new URL("../fixtures/transfers.php", import.meta.url),
    "utf8",
  ),
  contracts = JSON.parse(
    readFileSync(new URL("../fixtures/contracts.json", import.meta.url)),
  ),
  extraction = extractPHP(source);
let engine, intended, legacy;
const initial = [
    [
      ["alice", 100],
      ["bob", 0],
    ],
    [],
    [],
    [],
  ],
  input = { amount: 10, authorized: true, requestId: "r1" };
before(async () => {
  engine = new Engine();
  for (const name of ["intended", "legacy"]) {
    const p = reconstructPHP(extraction, contracts, name + "Transfer").program,
      c = await engine.certify(
        p,
        [],
        name === "intended"
          ? { retrySafe: true, preserves: ["alice", "bob"] }
          : {},
      );
    assert.equal(c.status, "accepted", c.reason);
    if (name === "intended") intended = c.certificate;
    else legacy = c.certificate;
  }
});
after(() => engine.close());
test("PHP is parsed into real AST and source-linked facts", () => {
  assert.equal(extraction.ast.kind, "program");
  assert.equal(extraction.functions.length, 3);
  validateFacts(extraction);
  assert.ok(extraction.facts.Calls.some((x) => x[1] === "debit"));
  assert.ok(
    extraction.facts.Node.every((x) => x[0].startsWith(extraction.artifact)),
  );
});
test("reconstruction produces named assumptions, not implementation proofs", () => {
  const r = reconstructPHP(extraction, contracts, "intendedTransfer");
  assert.equal(r.status, "reconstructed");
  assert.equal(admit(r).status, "incomplete");
  assert.equal(
    admit(
      r,
      r.assumptions.map((a) => a.claim),
    ).status,
    "conditional",
  );
});
test("unknown call blocks executable reconstruction", () => {
  const r = reconstructPHP(extraction, contracts, "unresolvedTransfer");
  assert.equal(r.status, "incomplete");
  assert.equal(r.program, null);
  assert.match(r.obligations[0].reason, /unmapped/);
});
test("unsupported return cannot silently truncate source", () => {
  const x = extractPHP("<?php function x() { return 1; debit(2); }");
  assert.equal(reconstructPHP(x, contracts, "x").program, null);
});
test("source byte identity changes when implementation changes", () =>
  assert.notEqual(extractPHP(source + "\n").artifact, extraction.artifact));
test("malformed PHP fails extraction", () =>
  assert.throws(() => extractPHP("<?php function {")));
test("canonical object key order is stable", () =>
  assert.equal(digest({ b: 2, a: 1 }), digest({ a: 1, b: 2 })));
test("evidence hashes and dependency identities are enforced", () => {
  const s = new EvidenceStore();
  try {
    const a = s.put("fact", { a: 1 });
    assert.equal(s.get(a).value.a, 1);
    assert.throws(() => s.put("evidence", {}, ["missing"]));
    s.db.prepare("UPDATE artifacts SET body=? WHERE id=?").run("{}", a);
    assert.throws(() => s.get(a), /hash mismatch/);
  } finally {
    s.close();
  }
});
test("journals require leases and detect tampering", () => {
  const s = new EvidenceStore();
  try {
    assert.throws(() => s.append("x", "a", {}));
    s.lease("x", "a", 100, 1000);
    assert.throws(() => s.lease("x", "b", 100, 1001));
    s.append("x", "a", { v: 1 }, 1001);
    assert.equal(s.verify().entries, 1);
    assert.throws(() => s.append("x", "a", {}, 1100));
    s.db.exec("UPDATE journal SET previous='tamper'");
    assert.throws(() => s.verify());
  } finally {
    s.close();
  }
});
test("actual SQLite receipts survive reopening", () => {
  const dir = mkdtempSync(join(tmpdir(), "behavior-db-")),
    p = join(dir, "db");
  try {
    let a = new SqliteTransfer(p);
    a.execute(input);
    a.close();
    a = new SqliteTransfer(p);
    a.execute(input);
    assert.deepEqual(a.snapshot().store, [
      ["alice", 90],
      ["bob", 10],
    ]);
    assert.equal(a.snapshot().effects.length, 1);
    a.close();
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
});
test("lost response plus retry resolves uncertainty for intended implementation", async () => {
  const a = new SqliteTransfer(),
    s = new EvidenceStore();
  try {
    const t = await runScenario(
      a,
      [{ input, options: { fault: "after-commit" } }, { input }],
      s,
    );
    const result = await checkTrace(engine, intended, initial, t);
    assert.equal(result.status, "compatible");
    assert.equal(result.worlds, 1);
  } finally {
    a.close();
    s.close();
  }
});
test("same scenario detects duplicate transfer in legacy implementation", async () => {
  const a = new SqliteTransfer(":memory:", { legacy: true }),
    s = new EvidenceStore();
  try {
    const t = await runScenario(
      a,
      [{ input, options: { fault: "after-commit" } }, { input }],
      s,
    );
    const result = await checkTrace(engine, intended, initial, t);
    assert.equal(result.status, "violation");
    assert.equal(result.counterexample.length, 2);
  } finally {
    a.close();
    s.close();
  }
});
test("precommit failure rolls back real database", () => {
  const a = new SqliteTransfer();
  try {
    a.execute(input, { fault: "before-commit" });
    assert.deepEqual(a.snapshot().store, initial[0]);
    assert.equal(a.snapshot().effects.length, 0);
  } finally {
    a.close();
  }
});
test("partial observations never establish complete conformance", async () => {
  const t = [
    {
      input: Object.entries(input).sort(),
      outcome: "completed",
      observation: { store: [["alice", 90]], effects: [], complete: false },
    },
  ];
  assert.equal(
    (await checkTrace(engine, intended, initial, t)).status,
    "inconclusive",
  );
});
test("malformed observation rejected", async () =>
  await assert.rejects(() =>
    checkTrace(engine, intended, initial, [
      {
        input: Object.entries(input).sort(),
        outcome: "completed",
        observation: { store: [], effects: [], complete: "yes" },
      },
    ]),
  ));
test("world bounds yield inconclusive", async () =>
  assert.equal(
    (
      await checkTrace(
        engine,
        intended,
        initial,
        [{ input: Object.entries(input).sort(), outcome: "unknown-commit" }],
        { maxWorlds: 1 },
      )
    ).status,
    "inconclusive",
  ));
test("projection is generated from actual semantic transitions and rechecked", async () => {
  const p = await explore(engine, intended, initial, [input], { depth: 2 });
  assert.equal(p.models[0].vertices.length, 2);
  const path = traverse(p, { seed: 41, length: 5 });
  assert.deepEqual(path, traverse(p, { seed: 41, length: 5 }));
  assert.equal(
    (await validatePath(engine, intended, p, path.path)).status,
    "validated",
  );
  p.models[0].edges[0].properties.expected = initial;
  await assert.rejects(() => validatePath(engine, intended, p, path.path));
});
test("exploration records bounds explicitly", async () => {
  const p = await explore(engine, intended, initial, [input], { maxStates: 1 });
  assert.equal(p.truncated, true);
  assert.equal(p.models[0].vertices.length, 1);
});
test("migration decisions bind exact models and exact finding", () => {
  const m = migrationContract(legacy, intended),
    l = { x: 1 },
    r = { x: 2 },
    finding = compareMigration(m, legacy, intended, l, r).finding;
  m.decisions.push({
    finding,
    disposition: "allow",
    approvedBy: "reviewer",
    rationale: "intentional change",
  });
  assert.equal(
    compareMigration(m, legacy, intended, l, r).status,
    "approved-change",
  );
  assert.equal(
    compareMigration(m, legacy, intended, l, { x: 3 }).status,
    "unapproved-change",
  );
  assert.throws(() => compareMigration(m, intended, intended, l, r));
  m.decisions.push(m.decisions[0]);
  assert.throws(() => compareMigration(m, legacy, intended, l, r));
});
test("minimizer retains failure-producing subsequence", async () =>
  assert.deepEqual(
    await minimize(
      [1, 2, 3, 4],
      async (xs) => xs.includes(2) && xs.includes(4),
    ),
    [2, 4],
  ));
test("named definitions expand with parameter binding and reject recursion", () => {
  assert.deepEqual(
    compose({
      program: ["invoke", "set", [["lit", 2]]],
      definitions: {
        set: { parameters: ["v"], program: ["put", "x", ["param", "v"]] },
      },
    }).program,
    ["put", "x", ["lit", 2]],
  );
  assert.throws(() =>
    compose({
      program: ["invoke", "x", []],
      definitions: { x: { parameters: [], program: ["invoke", "x", []] } },
    }),
  );
});
test("HTTP adapter performs real request and preserves raw response", async () => {
  const server = createServer(async (req, res) => {
    let b = "";
    for await (const c of req) b += c;
    assert.equal(JSON.parse(b).amount, 10);
    res.end(
      JSON.stringify({
        balances: { alice: 90, bob: 10 },
        effects: [["transfer", 10]],
      }),
    );
  });
  await new Promise((r) => server.listen(0, "127.0.0.1", r));
  try {
    const adapter = new HttpAdapter({
      url: `http://127.0.0.1:${server.address().port}`,
      observationMap: {
        version: 1,
        assumption: "snapshot-complete",
        statuses: { 200: "completed" },
        store: { alice: ["balances", "alice"], bob: ["balances", "bob"] },
        effects: ["effects"],
        complete: true,
      },
    });
    const r = await adapter.execute(input);
    assert.equal(r.outcome, "completed");
    assert.deepEqual(r.observation.store, [
      ["alice", 90],
      ["bob", 10],
    ]);
    assert.ok(r.raw.body);
    assert.equal(r.mapping.length, 64);
  } finally {
    await new Promise((r) => server.close(r));
  }
});
test("missing mapped fields remain unobserved", () =>
  assert.equal(
    mapObservation(
      { status: 200, body: "{}" },
      {
        version: 1,
        assumption: "test",
        store: { x: ["x"] },
        effects: ["effects"],
        complete: true,
        statuses: { 200: "completed" },
      },
    ).observation,
    null,
  ));
test("command adapter uses JSON stdin and records raw stdout", async () => {
  const a = new CommandAdapter(process.execPath, [
    "-e",
    "process.stdin.once('data',d=>{JSON.parse(d);console.log(JSON.stringify({outcome:'completed'}))})",
  ]);
  const r = await a.execute(input);
  assert.equal(r.outcome, "completed");
  assert.ok(r.raw.stdout);
});
test("persistent local API requires auth and serves real certificates", async () => {
  const s = await service({ token: "0123456789abcdef" });
  try {
    const url = `http://127.0.0.1:${s.port}/certify`;
    assert.equal(
      (await fetch(url, { method: "POST", body: "{}" })).status,
      403,
    );
    const r = await fetch(url, {
      method: "POST",
      headers: { authorization: "Bearer 0123456789abcdef" },
      body: JSON.stringify({ program: ["skip"] }),
    });
    assert.equal(r.status, 200);
    assert.equal((await r.json()).result.status, "accepted");
  } finally {
    await s.close();
  }
});
test("binary reconstruction requires exact artifact and explicit assumptions", () => {
  const x = {
    version: 1,
    producer: "ghidra",
    artifact: "a".repeat(64),
    facts: Object.fromEntries(
      [
        "Node",
        "Flow",
        "Calls",
        "DefUse",
        "Reads",
        "Writes",
        "Boundary",
        "Entry",
        "Unknown",
        "Contains",
      ].map((k) => [k, []]),
    ),
  };
  x.facts.Entry = [["f", "addr"]];
  assert.throws(() => reconstructBinary(x, { artifact: "b".repeat(64) }));
  const r = reconstructBinary(x, {
    artifact: x.artifact,
    entry: "addr",
    program: ["skip"],
    assumptions: ["external-call-model"],
  });
  assert.equal(r.status, "assumed");
});
test("Soufflé runs when installed; absence is explicitly unavailable", (t) => {
  const r = analyse(extraction);
  if (r.status === "unavailable") {
    if (process.env.BEHAVIOR_REQUIRE_EXTERNAL) throw Error(r.reason);
    t.skip(r.reason);
    return;
  }
  assert.equal(r.status, "complete");
  assert.ok(
    r.relations.MayCall.some(
      (x) => x[0] === "legacyTransfer" && x[1] === "debit",
    ),
  );
});

test("project extraction namespaces identical files and rejects ambiguous entries", () => {
  const dir = mkdtempSync(join(tmpdir(), "behavior-project-"));
  try {
    writeFileSync(join(dir, "a.php"), source);
    writeFileSync(join(dir, "b.php"), source);
    const project = extractProject(dir);
    assert.equal(project.manifest.length, 2);
    assert.equal(
      new Set(project.facts.Node.map((r) => r[0])).size,
      project.facts.Node.length,
    );
    assert.throws(
      () => reconstructPHP(project, {}, "legacyTransfer"),
      /ambiguous/,
    );
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
});
