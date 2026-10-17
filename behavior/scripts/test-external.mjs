import { spawnSync } from "node:child_process";
import { resolve } from "node:path";
import { root } from "../lib/runtime.mjs";
const t = resolve(root, ".tools");
const env = {
  ...process.env,
  BEHAVIOR_REQUIRE_EXTERNAL: "1",
  SOUFFLE: process.env.SOUFFLE ?? resolve(t, "souffle/usr/bin/souffle"),
  GRAPHWALKER_JAR: process.env.GRAPHWALKER_JAR ?? resolve(t, "graphwalker.jar"),
  GHIDRA_HOME: process.env.GHIDRA_HOME ?? resolve(t, "ghidra_12.1.4_PUBLIC"),
  JAVA_HOME: process.env.JAVA_HOME ?? resolve(t, "jdk"),
  LD_LIBRARY_PATH: [
    resolve(t, "ncurses/usr/lib/x86_64-linux-gnu"),
    process.env.LD_LIBRARY_PATH,
  ]
    .filter(Boolean)
    .join(":"),
};
const r = spawnSync(
  process.execPath,
  [
    "--test",
    "tests/core.test.mjs",
    "tests/integration.test.mjs",
    "tests/external.test.mjs",
  ],
  { cwd: root, env, stdio: "inherit" },
);
process.exit(r.status ?? 1);
