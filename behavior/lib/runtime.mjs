import { spawn } from "node:child_process";
import { createInterface } from "node:readline";
import { fileURLToPath } from "node:url";
import { resolve } from "node:path";
import { existsSync } from "node:fs";
export const root = fileURLToPath(new URL("../", import.meta.url));
function wire(v, depth = 0) {
  if (depth > 200) throw Error("data nesting exceeds 200");
  if (Array.isArray(v))
    return `(l ${v.map((x) => wire(x, depth + 1)).join(" ")})`;
  if (typeof v === "string") return `(s "${Buffer.from(v).toString("hex")}")`;
  if (typeof v === "boolean") return String(v);
  if (Number.isInteger(v) && Math.abs(v) <= 2147483647) return String(v);
  throw Error(
    "wire accepts arrays, strings, booleans and signed 32-bit integers",
  );
}
export class Runtime {
  constructor({ timeout = 30000 } = {}) {
    this.timeout = timeout;
    this.pending = [];
    this.stderr = "";
    this.closed = false;
    const bundled = resolve(root, ".tools/LuaJIT/src/luajit");
    const local = existsSync(bundled)
      ? bundled
      : resolve(root, "../../dependencies/LuaJIT/src/luajit");
    const lua = process.env.LUA ?? (existsSync(local) ? local : "luajit");
    this.process = spawn(lua, [resolve(root, "lib/worker.lua")], {
      cwd: root,
      env: {
        ...process.env,
        SHEN_LUA_ROOT:
          process.env.SHEN_LUA_ROOT ??
          (existsSync(resolve(root, ".tools/shen-lua"))
            ? resolve(root, ".tools/shen-lua")
            : resolve(root, "../../shen-lua")),
      },
      stdio: ["pipe", "pipe", "pipe"],
    });
    this.ready = new Promise((res, rej) => {
      this.readyResolve = res;
      this.readyReject = rej;
    });
    this.startTimer = setTimeout(
      () => this.fail(Error("Shen boot timed out")),
      timeout,
    );
    this.process.stderr.on("data", (x) => {
      this.stderr = (this.stderr + x).slice(-10000);
    });
    createInterface({ input: this.process.stdout }).on("line", (line) => {
      let m;
      try {
        m = JSON.parse(line);
      } catch {
        this.fail(Error(`Invalid worker output: ${line}`));
        return;
      }
      if (m.ready) {
        clearTimeout(this.startTimer);
        this.readyResolve();
        return;
      }
      const p = this.pending.shift();
      if (!p) {
        this.fail(Error("unsolicited worker response"));
        return;
      }
      clearTimeout(p.timer);
      m.ok ? p.resolve(m.value) : p.reject(Error(m.error));
    });
    this.process.on("error", (e) => this.fail(e));
    this.process.on("exit", (code, signal) =>
      this.fail(Error(`Shen exited ${code ?? signal}: ${this.stderr}`)),
    );
  }
  fail(e) {
    this.closed = true;
    clearTimeout(this.startTimer);
    this.readyReject(e);
    for (const p of this.pending) {
      clearTimeout(p.timer);
      p.reject(e);
    }
    this.pending = [];
    this.process.kill();
  }
  async call(...args) {
    await this.ready;
    if (this.closed) throw Error("runtime closed");
    const line = wire(args);
    if (line.length > 4000000) throw Error("request too large");
    return new Promise((resolve, reject) => {
      const timer = setTimeout(
        () => this.fail(Error("Shen request timed out; worker terminated")),
        this.timeout,
      );
      this.pending.push({ resolve, reject, timer });
      this.process.stdin.write(line + "\n");
    });
  }
  close() {
    this.closed = true;
    this.process.stdin.end();
  }
}
