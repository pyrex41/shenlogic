import { readFileSync, mkdirSync, writeFileSync } from "node:fs";
import { resolve } from "node:path";
import { Engine } from "./engine.mjs";
import { root } from "./runtime.mjs";
import { extractPHP, reconstructPHP } from "../extractors/php.mjs";
import { analyse, exportFacts } from "./analysis.mjs";
import { EvidenceStore } from "./store.mjs";
import { SqliteTransfer, runScenario } from "./adapters.mjs";
import {
  checkTrace,
  migrationContract,
  compareMigration,
  minimize,
} from "./conformance.mjs";
import { explore, traverse, validatePath } from "./explore.mjs";
export async function demo(dir = resolve(root, "build/demo")) {
  mkdirSync(dir, { recursive: true });
  const e = new Engine(),
    store = new EvidenceStore(resolve(dir, "evidence.sqlite"));
  const save = (name, data) =>
    writeFileSync(
      resolve(dir, name + ".json"),
      JSON.stringify(data, null, 2) + "\n",
    );
  try {
    const extraction = extractPHP(
        readFileSync(resolve(root, "fixtures/transfers.php"), "utf8"),
        "transfers.php",
      ),
      contracts = JSON.parse(
        readFileSync(resolve(root, "fixtures/contracts.json")),
      ),
      models = {};
    save("extraction", extraction);
    exportFacts(extraction, resolve(dir, "facts"));
    const source = store.put("extraction", extraction);
    for (const [name, entry] of [
      ["legacy", "legacyTransfer"],
      ["intended", "intendedTransfer"],
    ]) {
      const r = reconstructPHP(extraction, contracts, entry);
      const c = await e.certify(
        r.program,
        [],
        name === "intended"
          ? {
              retrySafe: true,
              proofMethod: "durable-deduplication",
              preserves: ["alice", "bob"],
              allowedEffects: [
                ["write", "alice"],
                ["write", "bob"],
                ["emit", "transfer"],
              ],
            }
          : { preserves: ["alice", "bob"] },
      );
      if (c.status !== "accepted") throw Error(c.reason);
      models[name] = c.certificate;
      save(name, { reconstruction: r, ...c });
      store.put("reconstruction", r, [source]);
    }
    const initial = [
        [
          ["alice", 100],
          ["bob", 0],
        ],
        [],
        [],
        [],
      ],
      input = { requestId: "req-1", amount: 10, authorized: true },
      steps = [{ input, options: { fault: "after-commit" } }, { input }],
      traces = {};
    for (const legacy of [true, false]) {
      const adapter = new SqliteTransfer(":memory:", { legacy });
      try {
        traces[legacy ? "legacy" : "intended"] = await runScenario(
          adapter,
          steps,
          store,
          { lease: "demo-" + (legacy ? "legacy" : "intended") },
        );
      } finally {
        adapter.close();
      }
    }
    const intended = await checkTrace(
        e,
        models.intended,
        initial,
        traces.intended,
      ),
      violation = await checkTrace(e, models.intended, initial, traces.legacy);
    save("traces", traces);
    save("conformance", { intended, legacyAgainstIntended: violation });
    const finite = await explore(
      e,
      models.intended,
      initial,
      [input, { ...input, requestId: "req-2" }],
      { depth: 3, maxStates: 30 },
    );
    save("projection", finite);
    writeFileSync(
      resolve(dir, "graphwalker.json"),
      JSON.stringify({ models: finite.models }, null, 2),
    );
    const walk = traverse(finite, { seed: 41, length: 8 });
    const validation = await validatePath(
      e,
      models.intended,
      finite,
      walk.path,
    );
    save("scenario", { walk, ...validation });
    const migration = migrationContract(models.legacy, models.intended);
    const difference = compareMigration(
      migration,
      models.legacy,
      models.intended,
      traces.legacy.at(-1).observation,
      traces.intended.at(-1).observation,
    );
    save("migration", { contract: migration, result: difference });
    const minimal = await minimize(steps, async (candidate) => {
      const a = new SqliteTransfer(":memory:", { legacy: true });
      try {
        const t = await runScenario(a, candidate, store, { lease: "minimize" });
        return (
          (await checkTrace(e, models.intended, initial, t)).status ===
          "violation"
        );
      } finally {
        a.close();
      }
    });
    save("counterexample", {
      steps: minimal,
      initial,
      certificate: models.intended,
    });
    const analysis = analyse(extraction);
    save("analysis", analysis);
    const summary = {
      intended: intended.status,
      legacyAgainstIntended: violation.status,
      migration: difference.status,
      minimalCounterexampleSteps: minimal.length,
      behavioralPolicies: [
        "retry-safe",
        "affine-money-conservation",
        "effect-inclusion",
      ],
      graph: {
        vertices: finite.models[0].vertices.length,
        edges: finite.models[0].edges.length,
        truncated: finite.truncated,
      },
      souffle: analysis.status,
      journal: store.verify(),
      directory: dir,
    };
    save("summary", summary);
    return summary;
  } finally {
    e.close();
    store.close();
  }
}
