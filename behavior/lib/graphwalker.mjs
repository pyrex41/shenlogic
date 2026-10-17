import { spawnSync } from "node:child_process";
import { mkdtempSync, writeFileSync, rmSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
// Optional external planner. Its proposed path is always rechecked by validatePath.
export function graphwalker(
  projection,
  {
    command = process.env.GRAPHWALKER ?? "graphwalker",
    generator = "random(length(100))",
    timeout = 30000,
    seed = 1,
    jar = process.env.GRAPHWALKER_JAR,
  } = {},
) {
  const dir = mkdtempSync(join(tmpdir(), "behavior-gw-"));
  try {
    const file = join(dir, "model.json");
    writeFileSync(file, JSON.stringify({ models: projection.models }));
    const r = spawnSync(
      jar ? "java" : command,
      [
        ...(jar ? ["-jar", jar] : []),
        "offline",
        "-m",
        file,
        generator,
        "--seed",
        String(seed),
      ],
      { encoding: "utf8", timeout, maxBuffer: 4000000 },
    );
    if (r.error?.code === "ENOENT")
      return {
        status: "unavailable",
        reason: "GraphWalker executable not installed",
      };
    if (r.error || r.status !== 0) throw Error(r.error?.message ?? r.stderr);
    const edges = new Set(projection.models[0].edges.map((e) => e.name)),
      vertices = new Set(projection.models[0].vertices.map((v) => v.name)),
      path = [];
    for (const line of r.stdout.trim().split("\n").filter(Boolean)) {
      const name = JSON.parse(line).currentElementName;
      if (edges.has(name))
        path.push(projection.models[0].edges.find((e) => e.name === name).id);
      else if (!vertices.has(name))
        throw Error("unknown planner element " + name);
    }
    return {
      status: "proposed",
      seed,
      path,
      raw: r.stdout,
      notice: "Recheck with validatePath before execution.",
    };
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
}
