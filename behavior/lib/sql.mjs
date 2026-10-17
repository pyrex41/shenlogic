import { bindings, assertData } from "./data.mjs";
// Templates and observation mappings are trusted configuration, never assembled
// from request strings. Connections are supplied explicitly by the caller.
export class SqlAdapter {
  constructor(driver, config) {
    if (!["postgres", "mysql"].includes(config.kind) || config.version !== 1)
      throw Error("invalid SQL adapter config");
    this.driver = driver;
    this.config = config;
  }
  static async connect(config) {
    let driver;
    if (config.kind === "postgres") {
      const { Client } = await import("pg");
      driver = new Client(config.connection);
      await driver.connect();
    } else if (config.kind === "mysql") {
      const mysql = await import("mysql2/promise");
      driver = await mysql.createConnection(config.connection);
    } else throw Error("unknown SQL backend");
    return new SqlAdapter(driver, config);
  }
  async query(sql, params = []) {
    const r = await this.driver.query(sql, params);
    return this.config.kind === "postgres" ? r.rows : r[0];
  }
  async snapshot() {
    const m = this.config.observation;
    if (!m?.assumption) throw Error("observation assumption required");
    const scalar = (x) => {
      if (
        typeof x === "string" &&
        /^-?(0|[1-9][0-9]*)$/.test(x) &&
        m.integerStrings
      )
        x = Number(x);
      assertData(x);
      if (Array.isArray(x)) throw Error("scalar SQL value required");
      return x;
    };
    const store = (await this.query(m.storeQuery))
      .map((r) => [String(r[m.keyColumn]), scalar(r[m.valueColumn])])
      .sort(([a], [b]) => (a < b ? -1 : a > b ? 1 : 0));
    bindings(store);
    const effects = (await this.query(m.effectsQuery)).map((r) => [
      String(r[m.topicColumn]),
      scalar(r[m.effectColumn]),
    ]);
    return { store, effects, complete: m.complete === true };
  }
  async execute(input) {
    const command = this.config.commands?.[input.command];
    if (!command) throw Error("unknown SQL command");
    let phase = "begin";
    const raw = [];
    try {
      await this.query("BEGIN");
      phase = "statements";
      for (const statement of command) {
        if (
          typeof statement.sql !== "string" ||
          !Array.isArray(statement.parameters)
        )
          throw Error("invalid SQL template");
        const parameters = statement.parameters.map((k) => {
          if (!Object.hasOwn(input, k))
            throw Error("missing SQL parameter " + k);
          assertData(input[k]);
          return input[k];
        });
        const rows = await this.query(statement.sql, parameters);
        raw.push({ statement: raw.length, rows });
      }
      phase = "commit";
      await this.query("COMMIT");
      phase = "observe";
      return { outcome: "completed", observation: await this.snapshot(), raw };
    } catch (e) {
      let outcome = "unknown-commit";
      if (phase === "statements") {
        try {
          await this.query("ROLLBACK");
          outcome = "not-committed";
        } catch {}
      }
      return { outcome, raw: { phase, error: e.message, statements: raw } };
    }
  }
  async close() {
    await this.driver.end();
  }
}
