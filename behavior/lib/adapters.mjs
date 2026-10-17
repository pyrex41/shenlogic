import { DatabaseSync } from "node:sqlite";
import { spawn } from "node:child_process";
import { canonical, pairs, digest } from "./data.mjs";
// Independent implementation fixture: actual SQL transactions and durable receipts.
// This is deliberately not a second interpreter for the behavioral language.
export class SqliteTransfer {
  constructor(
    path = ":memory:",
    { legacy = false, initial = { alice: 100, bob: 0 } } = {},
  ) {
    this.legacy = legacy;
    this.db = new DatabaseSync(path);
    this.db.exec(
      `PRAGMA journal_mode=WAL; CREATE TABLE IF NOT EXISTS accounts(name TEXT PRIMARY KEY,balance INTEGER NOT NULL); CREATE TABLE IF NOT EXISTS receipts(id TEXT PRIMARY KEY,payload TEXT NOT NULL); CREATE TABLE IF NOT EXISTS outbox(seq INTEGER PRIMARY KEY,amount INTEGER NOT NULL);`,
    );
    for (const [k, v] of Object.entries(initial))
      this.db.prepare("INSERT OR IGNORE INTO accounts VALUES(?,?)").run(k, v);
  }
  snapshot() {
    return {
      store: this.db
        .prepare("SELECT name,balance FROM accounts ORDER BY name")
        .all()
        .map((r) => [r.name, r.balance]),
      effects: this.db
        .prepare("SELECT amount FROM outbox ORDER BY seq")
        .all()
        .map((r) => ["transfer", r.amount]),
      complete: true,
    };
  }
  execute(input, { fault = "none" } = {}) {
    if (!["none", "before-commit", "after-commit"].includes(fault))
      throw Error("unknown fault");
    const { requestId, amount, authorized } = input;
    if (
      typeof requestId !== "string" ||
      !requestId.length ||
      !Number.isInteger(amount) ||
      amount < 0 ||
      amount > 2147483647 ||
      typeof authorized !== "boolean"
    )
      throw Error("invalid transfer request");
    const payload = canonical(pairs(input));
    this.db.exec("BEGIN IMMEDIATE");
    let committed = false;
    try {
      if (!this.legacy) {
        const old = this.db
          .prepare("SELECT payload FROM receipts WHERE id=?")
          .get(requestId);
        if (old) {
          if (old.payload !== payload) throw Error("request identity conflict");
          this.db.exec("COMMIT");
          committed = true;
          return {
            outcome: "completed",
            observation: this.snapshot(),
            raw: { deduplicated: true },
          };
        }
      }
      if (!authorized) throw Error("requirement failed");
      const balance = (n) =>
        this.db.prepare("SELECT balance FROM accounts WHERE name=?").get(n)
          .balance;
      if (balance("alice") < amount) throw Error("requirement failed");
      if (balance("bob") + amount > 2147483647) throw Error("integer overflow");
      this.db
        .prepare("UPDATE accounts SET balance=balance-? WHERE name=?")
        .run(amount, "alice");
      this.db
        .prepare("UPDATE accounts SET balance=balance+? WHERE name=?")
        .run(amount, "bob");
      this.db.prepare("INSERT INTO outbox(amount) VALUES(?)").run(amount);
      if (!this.legacy)
        this.db
          .prepare("INSERT INTO receipts VALUES(?,?)")
          .run(requestId, payload);
      if (fault === "before-commit") {
        this.db.exec("ROLLBACK");
        return {
          outcome: "not-committed",
          observation: this.snapshot(),
          raw: { fault },
        };
      }
      this.db.exec("COMMIT");
      committed = true;
      if (fault === "after-commit")
        return { outcome: "unknown-commit", raw: { fault } };
      return {
        outcome: "completed",
        observation: this.snapshot(),
        raw: { deduplicated: false },
      };
    } catch (e) {
      if (!committed) this.db.exec("ROLLBACK");
      return {
        outcome: "not-committed",
        observation: this.snapshot(),
        raw: { error: e.message },
      };
    }
  }
  close() {
    this.db.close();
  }
}
export class HttpAdapter {
  constructor({ url, timeout = 10000, map, observationMap }) {
    this.url = new URL(url);
    if (!["http:", "https:"].includes(this.url.protocol))
      throw Error("HTTP URL required");
    this.timeout = timeout;
    this.map = map;
    this.observationMap = observationMap;
  }
  async execute(input) {
    let raw;
    try {
      const r = await fetch(this.url, {
        method: "POST",
        headers: { "content-type": "application/json" },
        body: JSON.stringify(input),
        signal: AbortSignal.timeout(this.timeout),
      });
      raw = { status: r.status, body: await r.text() };
    } catch (e) {
      return { outcome: "unknown-commit", raw: { transportError: e.message } };
    }
    if (this.observationMap)
      return {
        ...mapObservation(raw, this.observationMap),
        raw,
        mapping: digest(this.observationMap),
      };
    if (typeof this.map !== "function")
      return { outcome: "unknown-commit", raw };
    return { ...this.map(raw), raw };
  }
}
export class CommandAdapter {
  constructor(
    command,
    args = [],
    { timeout = 10000, maxBytes = 1000000 } = {},
  ) {
    this.command = command;
    this.args = args;
    this.timeout = timeout;
    this.maxBytes = maxBytes;
  }
  execute(input) {
    return new Promise((resolve, reject) => {
      const child = spawn(this.command, this.args, {
        stdio: ["pipe", "pipe", "pipe"],
      });
      let stdout = "",
        stderr = "",
        finished = false;
      const finish = (f, v) => {
        if (finished) return;
        finished = true;
        clearTimeout(timer);
        f(v);
      };
      const timer = setTimeout(() => {
        child.kill("SIGKILL");
        finish(resolve, {
          outcome: "unknown-commit",
          raw: { timeout: true, stdout, stderr },
        });
      }, this.timeout);
      child.on("error", (e) => finish(reject, e));
      child.stdout.on("data", (d) => {
        stdout += d;
        if (Buffer.byteLength(stdout) > this.maxBytes) {
          child.kill("SIGKILL");
          finish(reject, Error("adapter output bound"));
        }
      });
      child.stderr.on("data", (d) => {
        stderr = (stderr + d).slice(-10000);
      });
      child.on("exit", (code) => {
        try {
          if (code !== 0)
            return finish(resolve, {
              outcome: "unknown-commit",
              raw: { exit: code, stdout, stderr },
            });
          const result = JSON.parse(stdout);
          if (
            !["completed", "not-committed", "unknown-commit"].includes(
              result.outcome,
            )
          )
            throw Error("invalid adapter outcome");
          finish(resolve, { ...result, raw: { stdout, stderr, exit: code } });
        } catch (e) {
          finish(reject, e);
        }
      });
      child.stdin.on("error", () => {});
      child.stdin.end(JSON.stringify(input) + "\n");
    });
  }
}
export async function runScenario(
  adapter,
  steps,
  store,
  { lease = "scenario", owner = "runner" } = {},
) {
  store.lease(lease, owner);
  const trace = [];
  for (const step of steps) {
    store.lease(lease, owner);
    store.append(lease, owner, { phase: "intent", step });
    let result;
    try {
      result = await adapter.execute(step.input, step.options ?? {});
    } catch (e) {
      result = { outcome: "unknown-commit", raw: { adapterError: e.message } };
    }
    const event = { input: pairs(step.input), ...result };
    const id = store.put("raw-observation", event);
    store.append(lease, owner, { phase: "observation", artifact: id });
    trace.push(event);
  }
  return trace;
}

export function mapObservation(raw, map) {
  if (
    map.version !== 1 ||
    !map.assumption ||
    !map.store ||
    !Array.isArray(map.effects) ||
    typeof map.complete !== "boolean"
  )
    throw Error("invalid observation map");
  const outcome = map.statuses?.[String(raw.status)] ?? "unknown-commit";
  if (!["completed", "not-committed", "unknown-commit"].includes(outcome))
    throw Error("invalid mapped outcome");
  let body;
  try {
    body = JSON.parse(raw.body);
  } catch {
    return { outcome, observation: null };
  }
  const get = (path) => {
    if (!Array.isArray(path)) throw Error("path must be an array");
    let value = body;
    for (const key of path) {
      if (
        value === null ||
        typeof value !== "object" ||
        !Object.hasOwn(value, key)
      )
        throw Error("missing observation field");
      value = value[key];
    }
    return value;
  };
  try {
    return {
      outcome,
      observation: {
        store: Object.entries(map.store)
          .sort()
          .map(([key, path]) => [key, get(path)]),
        effects: get(map.effects),
        complete: map.complete,
      },
    };
  } catch {
    return { outcome, observation: null };
  }
}
