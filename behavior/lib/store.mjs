import { DatabaseSync } from "node:sqlite";
import { canonical, digest } from "./data.mjs";
export class EvidenceStore {
  constructor(path = ":memory:") {
    this.db = new DatabaseSync(path);
    this.db.exec(`PRAGMA foreign_keys=ON; PRAGMA journal_mode=WAL;
 CREATE TABLE IF NOT EXISTS artifacts(id TEXT PRIMARY KEY, kind TEXT NOT NULL, body TEXT NOT NULL);
 CREATE TABLE IF NOT EXISTS links(parent TEXT REFERENCES artifacts(id),child TEXT REFERENCES artifacts(id),role TEXT NOT NULL,PRIMARY KEY(parent,child,role));
 CREATE TABLE IF NOT EXISTS leases(name TEXT PRIMARY KEY, owner TEXT NOT NULL, expires INTEGER NOT NULL);
 CREATE TABLE IF NOT EXISTS journal(seq INTEGER PRIMARY KEY,previous TEXT NOT NULL,id TEXT UNIQUE NOT NULL,body TEXT NOT NULL);`);
  }
  put(kind, value, dependencies = []) {
    const body = { kind, value, dependencies: [...dependencies].sort() },
      id = digest(body);
    this.db.exec("BEGIN IMMEDIATE");
    try {
      for (const d of dependencies) this.get(d);
      this.db
        .prepare("INSERT OR IGNORE INTO artifacts VALUES(?,?,?)")
        .run(id, kind, canonical(body));
      for (const d of dependencies)
        this.db
          .prepare("INSERT OR IGNORE INTO links VALUES(?,?,?)")
          .run(id, d, "depends-on");
      this.db.exec("COMMIT");
      return id;
    } catch (e) {
      this.db.exec("ROLLBACK");
      throw e;
    }
  }
  get(id) {
    const row = this.db
      .prepare("SELECT body FROM artifacts WHERE id=?")
      .get(id);
    if (!row) throw Error("missing artifact " + id);
    const value = JSON.parse(row.body);
    if (digest(value) !== id) throw Error("artifact hash mismatch");
    return value;
  }
  lease(name, owner, ttl = 60000, now = Date.now()) {
    if (!Number.isSafeInteger(ttl) || ttl <= 0)
      throw Error("invalid lease ttl");
    this.db.exec("BEGIN IMMEDIATE");
    try {
      const row = this.db
        .prepare("SELECT * FROM leases WHERE name=?")
        .get(name);
      if (row && row.expires > now && row.owner !== owner)
        throw Error("lease held");
      this.db
        .prepare("INSERT OR REPLACE INTO leases VALUES(?,?,?)")
        .run(name, owner, now + ttl);
      this.db.exec("COMMIT");
    } catch (e) {
      this.db.exec("ROLLBACK");
      throw e;
    }
  }
  append(name, owner, event, now = Date.now()) {
    this.db.exec("BEGIN IMMEDIATE");
    try {
      const lease = this.db
        .prepare("SELECT * FROM leases WHERE name=?")
        .get(name);
      if (!lease || lease.owner !== owner || lease.expires <= now)
        throw Error("lease missing or expired");
      const last = this.db
        .prepare("SELECT seq,id FROM journal ORDER BY seq DESC LIMIT 1")
        .get();
      const seq = (last?.seq ?? 0) + 1,
        previous = last?.id ?? "",
        body = { seq, previous, name, owner, event },
        id = digest(body);
      this.db
        .prepare("INSERT INTO journal VALUES(?,?,?,?)")
        .run(seq, previous, id, canonical(body));
      this.db.exec("COMMIT");
      return id;
    } catch (e) {
      this.db.exec("ROLLBACK");
      throw e;
    }
  }
  verify() {
    let previous = "",
      seq = 0;
    for (const row of this.db
      .prepare("SELECT * FROM journal ORDER BY seq")
      .all()) {
      const b = JSON.parse(row.body);
      if (
        row.seq !== ++seq ||
        row.previous !== previous ||
        b.seq !== seq ||
        b.previous !== previous ||
        digest(b) !== row.id
      )
        throw Error("journal integrity failure");
      previous = row.id;
    }
    return { entries: seq, head: previous };
  }
  close() {
    this.db.close();
  }
}
