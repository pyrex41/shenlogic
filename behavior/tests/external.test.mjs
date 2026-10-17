import { test } from "node:test";
import assert from "node:assert/strict";
import { mkdtempSync, readFileSync, rmSync, existsSync } from "node:fs";
import { tmpdir } from "node:os";
import { join, resolve } from "node:path";
import { spawnSync } from "node:child_process";
import { Engine } from "../lib/engine.mjs";
import { root } from "../lib/runtime.mjs";
import { explore, validatePath } from "../lib/explore.mjs";
import { graphwalker } from "../lib/graphwalker.mjs";
import { validateFacts } from "../lib/reconstruct.mjs";
import { SqlAdapter } from "../lib/sql.mjs";
test(
  "real GraphWalker path is revalidated by Shen",
  { timeout: 60000 },
  async (t) => {
    if (!process.env.GRAPHWALKER_JAR && !process.env.GRAPHWALKER) {
      if (process.env.BEHAVIOR_REQUIRE_EXTERNAL)
        throw Error("GraphWalker required");
      t.skip("GraphWalker not configured");
      return;
    }
    const e = new Engine();
    try {
      const c = (await e.certify(["once", "id", ["put", "x", ["input", "n"]]]))
        .certificate;
      const p = await explore(
        e,
        c,
        [[["x", 0]], [], [], []],
        [
          { id: "r1", n: 1 },
          { id: "r2", n: 2 },
        ],
        { depth: 3 },
      );
      const walk = graphwalker(p, {
        generator: "random(length(10))",
        seed: 42,
      });
      assert.equal(walk.status, "proposed");
      assert.ok(walk.path.length);
      assert.equal(
        (await validatePath(e, c, p, walk.path)).status,
        "validated",
      );
    } finally {
      e.close();
    }
  },
);
test(
  "real Ghidra exports compiled native fixture",
  { timeout: 180000 },
  (t) => {
    if (!process.env.GHIDRA_HOME) {
      if (process.env.BEHAVIOR_REQUIRE_EXTERNAL) throw Error("Ghidra required");
      t.skip("GHIDRA_HOME not configured");
      return;
    }
    const dir = mkdtempSync(join(tmpdir(), "behavior-ghidra-"));
    try {
      const binary = join(dir, "fixture"),
        out = join(dir, "facts.json");
      const cc = spawnSync(
        process.env.CC ?? "cc",
        ["-O0", "-g", "-o", binary, resolve(root, "fixtures/native.c")],
        { encoding: "utf8" },
      );
      assert.equal(cc.status, 0, cc.stderr);
      const r = spawnSync(
        resolve(process.env.GHIDRA_HOME, "support/analyzeHeadless"),
        [
          dir,
          "project",
          "-import",
          binary,
          "-scriptPath",
          resolve(root, "extractors"),
          "-postScript",
          "BehaviorFacts.java",
          out,
          "-deleteProject",
        ],
        { encoding: "utf8", timeout: 150000, maxBuffer: 10000000 },
      );
      assert.equal(r.status, 0, r.stdout + r.stderr);
      assert.ok(existsSync(out), r.stdout + r.stderr);
      const facts = validateFacts(JSON.parse(readFileSync(out)));
      assert.ok(facts.facts.Entry.some((r) => r[0] === "bounded_copy"));
      assert.ok(facts.pcode.length);
      const nodes = new Set(facts.facts.Node.map((r) => r[0]));
      for (const [a, b] of facts.facts.DefUse) {
        assert.ok(nodes.has(a));
        assert.ok(nodes.has(b));
      }
    } finally {
      rmSync(dir, { recursive: true, force: true });
    }
  },
);
test("existing ShenLogic translation is available in the persistent worker", async () => {
  const e = new Engine();
  try {
    const output = await e.runtime.call(
      "translate-source",
      resolve(root, "../examples/tsl-lists.shen"),
      "tsl",
    );
    assert.match(output, /defined-first/);
    assert.match(output, /append2/);
    assert.equal((await e.certify(["skip"])).status, "accepted");
  } finally {
    e.close();
  }
});
test("Postgres adapter preserves parameterization and commit uncertainty", async () => {
  const calls = [];
  let failCommit = false;
  const driver = {
    query: async (sql, args) => {
      calls.push([sql, args]);
      if (sql === "COMMIT" && failCommit) throw Error("connection lost");
      return { rows: sql === "snapshot" ? [{ k: "x", v: 1 }] : [] };
    },
    end: async () => {},
  };
  const config = {
    version: 1,
    kind: "postgres",
    commands: { set: [{ sql: "UPDATE t SET x=$1", parameters: ["value"] }] },
    observation: {
      assumption: "complete-snapshot",
      storeQuery: "snapshot",
      effectsQuery: "effects",
      keyColumn: "k",
      valueColumn: "v",
      topicColumn: "topic",
      effectColumn: "value",
      complete: true,
    },
  };
  const a = new SqlAdapter(driver, config);
  assert.equal(
    (await a.execute({ command: "set", value: 1 })).outcome,
    "completed",
  );
  assert.deepEqual(calls[1], ["UPDATE t SET x=$1", [1]]);
  failCommit = true;
  assert.equal(
    (await a.execute({ command: "set", value: 1 })).outcome,
    "unknown-commit",
  );
});
test("MySQL adapter normalizes driver rows and rolls back statement errors", async () => {
  const calls = [];
  const driver = {
    query: async (sql, args) => {
      calls.push(sql);
      if (sql === "broken") throw Error("SQL failure");
      return [[], []];
    },
    end: async () => {},
  };
  const a = new SqlAdapter(driver, {
    version: 1,
    kind: "mysql",
    commands: { set: [{ sql: "broken", parameters: [] }] },
  });
  assert.equal((await a.execute({ command: "set" })).outcome, "not-committed");
  assert.deepEqual(calls, ["BEGIN", "broken", "ROLLBACK"]);
});
