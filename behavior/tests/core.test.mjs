import { test, before, after } from "node:test";
import assert from "node:assert/strict";
import { Engine } from "../lib/engine.mjs";
import { sequence } from "../lib/data.mjs";
let e;
before(async () => {
  e = new Engine();
  await e.runtime.ready;
});
after(() => e.close());
const initial = [
  [
    ["alice", 100],
    ["bob", 0],
  ],
  [],
  [],
  [],
];
const body = sequence([
  ["require", ["input", "authorized"]],
  ["put", "alice", ["-", ["get", "alice"], ["input", "amount"]]],
  ["put", "bob", ["+", ["get", "bob"], ["input", "amount"]]],
  ["emit", "transfer", ["input", "amount"]],
]);
const transfer = ["once", "requestId", body],
  input = { amount: 10, authorized: true, requestId: "r1" };
async function cert(p = transfer, r = [], policy = {}) {
  const x = await e.certify(p, r, policy);
  assert.equal(x.status, "accepted", x.reason);
  return x.certificate;
}
test("actual System S rejects absent resource and duplication", async () => {
  assert.equal((await e.certify(["consume", "a"], [])).status, "rejected");
  await assert.rejects(() => e.certify(["skip"], ["a", "a"]));
  assert.equal((await e.certify(["produce", "a"], [])).status, "rejected");
  assert.equal(
    (await e.certify(["produce", "a"], ["mint:a"])).status,
    "accepted",
  );
});
test("sequence requires exact intermediate resource context", async () => {
  const c = await cert(["seq", ["consume", "a"], ["skip"]], ["a"]);
  c.proof[1] = ["a"];
  assert.equal((await e.verify(c)).status, "rejected");
});
test("resource cannot be consumed twice", async () =>
  assert.equal(
    (await e.certify(["seq", ["consume", "a"], ["consume", "a"]], ["a"]))
      .status,
    "rejected",
  ));
test("branches require the same resource remainder", async () =>
  assert.equal(
    (
      await e.certify(
        ["case", ["lit", true], ["consume", "a"], ["skip"]],
        ["a"],
      )
    ).status,
    "rejected",
  ));
test("repeat requires resource invariant", async () => {
  assert.equal(
    (await e.certify(["repeat", 2, ["consume", "a"]], ["a"])).status,
    "rejected",
  );
  const c = await cert(["repeat", 2, ["skip"]]);
  assert.equal((await e.run(c, initial, input))[0], "ok");
});
test("effect inclusion is a distinct behavioral type", async () => {
  assert.equal(
    (await e.certify(body, [], { allowedEffects: [["write", "alice"]] }))
      .status,
    "rejected",
  );
  await cert(transfer, [], {
    allowedEffects: [
      ["write", "alice"],
      ["write", "bob"],
      ["emit", "transfer"],
    ],
  });
});
test("retry safety requires the approved derivation method", async () => {
  assert.equal(
    (await e.certify(body, [], { retrySafe: true })).status,
    "rejected",
  );
  await cert(transfer, [], {
    retrySafe: true,
    proofMethod: "durable-deduplication",
  });
  assert.equal(
    (await e.certify(transfer, [], { proofMethod: "trust-me" })).status,
    "rejected",
  );
});
test("affine conservation accepts balanced transfer and rejects money creation", async () => {
  await cert(transfer, [], { preserves: ["alice", "bob"] });
  assert.equal(
    (
      await e.certify(["put", "bob", ["+", ["get", "bob"], ["lit", 1]]], [], {
        preserves: ["alice", "bob"],
      })
    ).status,
    "rejected",
  );
});
test("affine proof covers both branches", async () =>
  assert.equal(
    (
      await e.certify(
        ["case", ["input", "x"], ["skip"], ["put", "bob", ["lit", 1]]],
        [],
        { preserves: ["alice", "bob"] },
      )
    ).status,
    "rejected",
  ));
test("nonlinear invariant is rejected instead of assumed", async () =>
  assert.equal(
    (
      await e.certify(
        ["put", "bob", ["*", ["get", "bob"], ["get", "alice"]]],
        [],
        { preserves: ["alice", "bob"] },
      )
    ).status,
    "rejected",
  ));
test("proof is bound to program and rulepack", async () => {
  const c = await cert();
  const forged = structuredClone(c);
  forged.program = ["skip"];
  assert.equal((await e.verify(forged)).status, "rejected");
  c.rulepack = "wrong";
  assert.equal((await e.verify(c)).status, "rejected");
});
test("forged primitive proof cannot certify composite program", async () => {
  const c = await cert();
  c.proof = ["primitive"];
  assert.equal((await e.verify(c)).status, "rejected");
});
test("forged effects rejected", async () => {
  const c = await cert();
  c.effects = [];
  assert.equal((await e.verify(c)).status, "rejected");
});
test("durable deduplication leaves exact state unchanged on retry", async () => {
  const c = await cert();
  const one = await e.run(c, initial, input),
    two = await e.run(c, one[1], input);
  assert.equal(one[0], "ok");
  assert.deepEqual(one[1][0], [
    ["alice", 90],
    ["bob", 10],
  ]);
  assert.deepEqual(two[1], one[1]);
  assert.equal(one[1][2].length, 1);
});
test("request identity conflict fails without changing state", async () => {
  const c = await cert();
  const one = await e.run(c, initial, input),
    two = await e.run(c, one[1], { ...input, amount: 11 });
  assert.equal(two[0], "error");
  assert.deepEqual(two[1], one[1]);
});
test("atomic failure rolls back preceding writes and effects", async () => {
  const c = await cert([
    "atomic",
    sequence([
      ["put", "alice", ["lit", 0]],
      ["emit", "oops", ["lit", 1]],
      ["require", ["lit", false]],
    ]),
  ]);
  const r = await e.run(c, initial, {});
  assert.equal(r[0], "error");
  assert.deepEqual(r[1], initial);
});
test("checked integer overflow rolls back once", async () => {
  const c = await cert();
  const s = [
    [
      ["alice", 100],
      ["bob", 2147483647],
    ],
    [],
    [],
    [],
  ];
  const r = await e.run(c, s, input);
  assert.equal(r[0], "error");
  assert.deepEqual(r[1], s);
});
test("fuel exhaustion is inconclusive, not proof or rollback success", async () => {
  const c = await cert();
  const r = await e.run(c, initial, input, 2);
  assert.equal(r[0], "inconclusive");
  assert.deepEqual(r[1], initial);
});
test("unknown commit retains both possible worlds", async () => {
  const c = await cert();
  const r = await e.observe(
    c,
    initial,
    Object.entries(input).sort(),
    "unknown-commit",
  );
  assert.equal(r[0], "alternatives");
  assert.equal(r[1].length, 2);
});
test("unknown commit cannot assume atomicity of arbitrary program", async () => {
  const c = await cert(body);
  assert.equal(
    (
      await e.observe(
        c,
        initial,
        Object.entries(input).sort(),
        "unknown-commit",
      )
    )[0],
    "inconclusive",
  );
});
test("unknown commit plus exhausted fuel remains inconclusive", async () => {
  const c = await cert();
  assert.equal(
    (
      await e.observe(
        c,
        initial,
        Object.entries(input).sort(),
        "unknown-commit",
        1,
      )
    )[0],
    "inconclusive",
  );
});
test("malformed data, floats, oversized integers, and missing inputs rejected", async () => {
  await assert.rejects(() => cert(["put", "x", ["lit", 0.5]]));
  await assert.rejects(() => cert(["put", "x", ["lit", 2147483648]]));
  const c = await cert();
  assert.equal((await e.run(c, initial, {}))[0], "error");
});
test("quotes, newlines and Shen syntax remain inert wire strings", async () => {
  const value = '\" (set dangerous true)\nλ';
  const c = await cert(["put", "text", ["lit", value]]);
  assert.equal((await e.run(c, initial, {}))[1][0].at(-1)[1], value);
});
test("repeated verification remains usable in persistent runtime", async () => {
  const c = await cert();
  for (let i = 0; i < 40; i++)
    assert.equal((await e.verify(c)).status, "accepted");
});
