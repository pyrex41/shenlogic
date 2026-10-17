import { spawnSync } from "node:child_process";
import { existsSync, mkdirSync, readFileSync, writeFileSync } from "node:fs";
import { resolve } from "node:path";
import { createHash } from "node:crypto";
import { root } from "../lib/runtime.mjs";
const tools = resolve(root, ".tools"),
  lock = JSON.parse(readFileSync(resolve(root, "toolchain.json")));
mkdirSync(tools, { recursive: true });
function run(command, args, cwd = tools) {
  const r = spawnSync(command, args, { cwd, stdio: "inherit" });
  if (r.error || r.status !== 0)
    throw Error(`${command} failed: ${r.error?.message ?? r.status}`);
}
for (const [name, r] of Object.entries(lock.repositories)) {
  const dir = resolve(tools, name);
  if (!existsSync(dir)) {
    run("git", ["clone", r.url, dir]);
    run("git", ["checkout", "--detach", r.revision], dir);
  }
  const head = spawnSync("git", ["rev-parse", "HEAD"], {
    cwd: dir,
    encoding: "utf8",
  });
  if (head.stdout.trim() !== r.revision)
    throw Error(`Refusing to modify unexpected ${name} checkout`);
}
run("make", ["-j2"], resolve(tools, "LuaJIT"));
run("npm", ["ci", "--ignore-scripts"], root);
if (process.argv.includes("--external")) {
  if (process.platform !== "linux" || process.arch !== "x64")
    throw Error(
      "external bundle is Linux x64; configure external tools manually on other platforms",
    );
  for (const [name, a] of Object.entries(lock.externalLinuxX64)) {
    const path = resolve(tools, name);
    if (!existsSync(path))
      run("curl", ["-L", "--fail", "--max-time", "180", "-o", path, a.url]);
    if (
      createHash("sha256").update(readFileSync(path)).digest("hex") !== a.sha256
    )
      throw Error("checksum mismatch " + name);
  }
  run("dpkg-deb", ["-x", "souffle.deb", "souffle"]);
  run("dpkg-deb", ["-x", "ncurses.deb", "ncurses"]);
  if (!existsSync(resolve(tools, "ghidra_12.1.4_PUBLIC")))
    run("unzip", ["-q", "ghidra.zip"]);
  mkdirSync(resolve(tools, "jdk"), { recursive: true });
  run("tar", ["xzf", "jdk.tar.gz", "-C", "jdk", "--strip-components=1"]);
}
console.log(
  "Pinned tools ready. npm test, or npm run test:external after --external.",
);
