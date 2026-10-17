#!/usr/bin/env node
import { readFileSync, writeFileSync, statSync } from "node:fs";
import { resolve } from "node:path";
import { randomBytes } from "node:crypto";
import { SqlAdapter } from "../lib/sql.mjs";
import { Engine } from "../lib/engine.mjs";
import {
  extractPHP,
  extractProject,
  reconstructPHP,
} from "../extractors/php.mjs";
import {
  validateFacts,
  reconstructBinary,
  admit,
} from "../lib/reconstruct.mjs";
import { analyse, exportFacts } from "../lib/analysis.mjs";
import { explore, traverse, validatePath } from "../lib/explore.mjs";
import { checkTrace, compareMigration, minimize } from "../lib/conformance.mjs";
import { EvidenceStore } from "../lib/store.mjs";
import {
  SqliteTransfer,
  CommandAdapter,
  HttpAdapter,
  runScenario,
} from "../lib/adapters.mjs";
import { service } from "../lib/service.mjs";
import { graphwalker } from "../lib/graphwalker.mjs";
import { compose } from "../lib/compose.mjs";
import { demo } from "../lib/demo.mjs";
const [command, ...args] = process.argv.slice(2),
  json = (p) => JSON.parse(readFileSync(p, "utf8"));
let engine;
const getEngine = () => (engine ??= new Engine());
const certificate = (x) => x.certificate ?? x;
const output = (x) => process.stdout.write(JSON.stringify(x, null, 2) + "\n");
try {
  let result;
  switch (command) {
    case "logic":
      result = await getEngine().runtime.call(
        "translate-source",
        resolve(args[0]),
        args[1] ?? "tsl",
      );
      break;
    case "extract":
      result = statSync(args[0]).isDirectory()
        ? extractProject(args[0])
        : extractPHP(readFileSync(args[0], "utf8"), args[0]);
      break;
    case "import-ghidra":
      result = validateFacts(json(args[0]));
      break;
    case "facts": {
      const x = validateFacts(json(args[0]));
      exportFacts(x, args[1]);
      result = { status: "exported", directory: resolve(args[1]) };
      break;
    }
    case "analyse":
      result = analyse(validateFacts(json(args[0])));
      break;
    case "reconstruct":
      result = reconstructPHP(json(args[0]), json(args[1]), args[2]);
      break;
    case "reconstruct-binary":
      result = reconstructBinary(json(args[0]), json(args[1]));
      break;
    case "admit":
      result = admit(json(args[0]), args[1] ? json(args[1]) : []);
      break;
    case "certify": {
      const raw = json(args[0]),
        x = Array.isArray(raw) ? { program: raw } : compose(raw);
      result = await getEngine().certify(
        x.program,
        x.resources ?? [],
        x.policy ?? {},
      );
      break;
    }
    case "verify":
      result = await getEngine().verify(certificate(json(args[0])));
      break;
    case "simulate": {
      const x = json(args[1]);
      result = await getEngine().run(
        certificate(json(args[0])),
        x.state,
        x.input,
        x.fuel,
      );
      break;
    }
    case "explore": {
      const x = json(args[1]);
      result = await explore(
        getEngine(),
        certificate(json(args[0])),
        x.initial,
        x.inputs,
        x.options,
      );
      break;
    }
    case "walk":
      result = traverse(json(args[0]), args[1] ? json(args[1]) : {});
      break;
    case "validate-path":
      result = await validatePath(
        getEngine(),
        certificate(json(args[0])),
        json(args[1]),
        json(args[2]).path,
      );
      break;
    case "graphwalker":
      result = graphwalker(json(args[0]));
      break;
    case "check-trace": {
      const x = json(args[1]);
      result = await checkTrace(
        getEngine(),
        certificate(json(args[0])),
        x.initial,
        x.trace,
        x.options,
      );
      break;
    }
    case "compare": {
      const x = json(args[0]);
      result = compareMigration(
        x.contract,
        x.legacy,
        x.intended,
        x.left,
        x.right,
      );
      break;
    }
    case "run": {
      const x = json(args[0]),
        store = new EvidenceStore(args[1] ?? ":memory:");
      let adapter;
      try {
        if (["postgres", "mysql"].includes(x.adapter.kind))
          adapter = await SqlAdapter.connect(x.adapter);
        else if (x.adapter.kind === "sqlite-transfer")
          adapter = new SqliteTransfer(x.adapter.path ?? ":memory:", x.adapter);
        else if (x.adapter.kind === "command")
          adapter = new CommandAdapter(
            x.adapter.command,
            x.adapter.args,
            x.adapter,
          );
        else if (x.adapter.kind === "http")
          adapter = new HttpAdapter(x.adapter);
        else throw Error("unknown adapter");
        result = {
          trace: await runScenario(adapter, x.steps, store),
          journal: store.verify(),
        };
      } finally {
        await adapter?.close?.();
        store.close();
      }
      break;
    }
    case "replay": {
      const x = json(args[0]),
        store = new EvidenceStore(":memory:"),
        adapter = new SqliteTransfer(":memory:", {
          legacy: true,
          initial: Object.fromEntries(x.initial[0]),
        });
      try {
        const trace = await runScenario(adapter, x.steps, store);
        result = await checkTrace(getEngine(), x.certificate, x.initial, trace);
      } finally {
        adapter.close();
        store.close();
      }
      break;
    }
    case "journal": {
      const store = new EvidenceStore(args[0]);
      try {
        result = store.verify();
      } finally {
        store.close();
      }
      break;
    }
    case "artifact": {
      const store = new EvidenceStore(args[0]);
      try {
        result = store.get(args[1]);
      } finally {
        store.close();
      }
      break;
    }
    case "demo":
      result = await demo(args[0]);
      break;
    case "serve": {
      const token =
          process.env.BEHAVIOR_TOKEN ?? randomBytes(24).toString("hex"),
        s = await service({
          port: Number(args[0] ?? 0),
          database: args[1] ?? ":memory:",
          token,
        });
      output({ listening: `http://127.0.0.1:${s.port}`, token });
      process.once("SIGINT", () => s.close());
      process.once("SIGTERM", () => s.close());
      break;
    }
    default:
      result = {
        usage:
          "behavior extract PHP | facts EXTRACTION DIR | analyse EXTRACTION | reconstruct EXTRACTION CONTRACTS ENTRY | import-ghidra JSON | reconstruct-binary EXTRACTION MANIFEST | admit RECONSTRUCTION [APPROVED] | certify MODEL | verify CERTIFICATE | simulate CERTIFICATE REQUEST | explore CERTIFICATE REQUEST | walk PROJECTION [OPTIONS] | validate-path CERTIFICATE PROJECTION PATH | graphwalker PROJECTION | check-trace CERTIFICATE REQUEST | compare REQUEST | run SCENARIO [DB] | replay COUNTEREXAMPLE | journal DB | artifact DB ID | demo [DIR] | serve [PORT] [DB]",
      };
      if (command && command !== "--help") process.exitCode = 2;
  }
  if (result !== undefined) {
    output(result);
    if (
      [
        "rejected",
        "violation",
        "incomplete",
        "unavailable",
        "forbidden-change",
        "unapproved-change",
      ].includes(result?.status)
    )
      process.exitCode = 1;
  }
} catch (e) {
  output({ status: "error", error: e.message });
  process.exitCode = 2;
} finally {
  engine?.close();
}
