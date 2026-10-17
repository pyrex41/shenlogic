import {
  mkdirSync,
  writeFileSync,
  readFileSync,
  mkdtempSync,
  rmSync,
} from "node:fs";
import { tmpdir } from "node:os";
import { resolve } from "node:path";
import { spawnSync } from "node:child_process";
import { root } from "./runtime.mjs";
export function exportFacts(extraction, dir) {
  mkdirSync(dir, { recursive: true });
  for (const [name, rows] of Object.entries(extraction.facts)) {
    if (!/^[A-Za-z]+$/.test(name)) throw Error("invalid relation");
    for (const row of rows)
      for (const x of row)
        if (/[\t\r\n]/.test(String(x))) throw Error("unsafe TSV value");
    writeFileSync(
      resolve(dir, name + ".facts"),
      rows.map((r) => r.join("\t")).join("\n") + (rows.length ? "\n" : ""),
    );
  }
}
export function analyse(extraction) {
  const dir = mkdtempSync(resolve(tmpdir(), "shen-analysis-"));
  try {
    exportFacts(extraction, dir);
    const r = spawnSync(
      process.env.SOUFFLE ?? "souffle",
      ["-F", dir, "-D", dir, resolve(root, "analysis/code.dl")],
      { encoding: "utf8", timeout: 60000 },
    );
    if (r.error?.code === "ENOENT")
      return {
        status: "unavailable",
        engine: "souffle",
        reason: "souffle executable not installed",
      };
    if (r.error || r.status !== 0) throw Error(r.error?.message ?? r.stderr);
    const relations = {};
    for (const n of ["Reachable", "MayCall", "MayWrite", "Unresolved"])
      relations[n] = readFileSync(resolve(dir, n + ".csv"), "utf8")
        .trim()
        .split("\n")
        .filter(Boolean)
        .map((x) => x.split("\t"));
    return {
      status: "complete",
      engine: "souffle",
      interpretation: "may-analysis",
      relations,
    };
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
}
