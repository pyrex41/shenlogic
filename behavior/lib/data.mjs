import { createHash } from "node:crypto";
export function canonical(x) {
  if (x === null || typeof x === "boolean" || typeof x === "string")
    return JSON.stringify(x);
  if (typeof x === "number") {
    if (!Number.isSafeInteger(x)) throw Error("noninteger data");
    return String(x);
  }
  if (Array.isArray(x)) return "[" + x.map(canonical).join(",") + "]";
  if (x && Object.getPrototypeOf(x) === Object.prototype)
    return (
      "{" +
      Object.keys(x)
        .sort()
        .map((k) => JSON.stringify(k) + ":" + canonical(x[k]))
        .join(",") +
      "}"
    );
  throw Error("unsupported canonical value");
}
export const digest = (x) =>
  createHash("sha256").update(canonical(x)).digest("hex");
export const bytesDigest = (x) => createHash("sha256").update(x).digest("hex");
export const pairs = (o) =>
  Object.entries(o).sort(([a], [b]) => (a < b ? -1 : a > b ? 1 : 0));
export const object = (p) => Object.fromEntries(p);
export function assertData(x, depth = 0) {
  if (depth > 100) throw Error("nesting bound");
  if (Array.isArray(x)) {
    if (x.length > 10000) throw Error("list bound");
    for (const v of x) assertData(v, depth + 1);
    return;
  }
  if (typeof x === "string") {
    if (Buffer.byteLength(x) > 65536) throw Error("string bound");
    return;
  }
  if (typeof x === "boolean") return;
  if (Number.isInteger(x) && Math.abs(x) <= 2147483647) return;
  throw Error("invalid model datum");
}
export function program(p, depth = 0) {
  if (depth > 100 || !Array.isArray(p)) throw Error("invalid program");
  const [k, ...a] = p;
  const arities = {
    skip: 0,
    require: 1,
    put: 2,
    emit: 2,
    consume: 1,
    produce: 1,
    seq: 2,
    case: 3,
    repeat: 2,
    atomic: 1,
    once: 2,
  };
  if (!(k in arities) || a.length !== arities[k])
    throw Error("unsupported program " + k);
  assertData(p);
  if (k === "seq") {
    program(a[0], depth + 1);
    program(a[1], depth + 1);
  }
  if (k === "case") {
    expression(a[0]);
    program(a[1], depth + 1);
    program(a[2], depth + 1);
  }
  if (k === "repeat") {
    if (!Number.isInteger(a[0]) || a[0] < 0 || a[0] > 1000)
      throw Error("invalid repeat");
    program(a[1], depth + 1);
  }
  if (k === "atomic") program(a[0], depth + 1);
  if (k === "once") {
    name(a[0]);
    program(a[1], depth + 1);
  }
  if (["put", "emit"].includes(k)) {
    name(a[0]);
    expression(a[1]);
  }
  if (k === "require") expression(a[0]);
  if (["consume", "produce"].includes(k)) name(a[0]);
  return p;
}
export function name(n) {
  if (typeof n !== "string" || !n.length) throw Error("nonempty name required");
}
export function expression(e) {
  if (!Array.isArray(e)) throw Error("invalid expression");
  const [k, ...a] = e;
  if (k === "lit" && a.length === 1 && !Array.isArray(a[0])) {
    assertData(a[0]);
    return;
  }
  if (["get", "input"].includes(k) && a.length === 1) {
    name(a[0]);
    return;
  }
  if (k === "not" && a.length === 1) {
    expression(a[0]);
    return;
  }
  if (
    ["+", "-", "*", "=", "<", "<=", "and", "or"].includes(k) &&
    a.length === 2
  ) {
    a.forEach(expression);
    return;
  }
  throw Error("unsupported expression");
}
export function resources(r) {
  if (!Array.isArray(r) || new Set(r).size !== r.length)
    throw Error("invalid resource context");
  r.forEach(name);
}
export function bindings(b) {
  if (!Array.isArray(b)) throw Error("bindings required");
  const seen = new Set();
  for (const pair of b) {
    if (!Array.isArray(pair) || pair.length !== 2)
      throw Error("invalid binding");
    name(pair[0]);
    if (seen.has(pair[0])) throw Error("duplicate binding");
    seen.add(pair[0]);
    assertData(pair[1]);
    if (Array.isArray(pair[1])) throw Error("scalar binding required");
  }
}
export function state(s) {
  if (!Array.isArray(s) || s.length !== 4)
    throw Error("state must have four fields");
  bindings(s[0]);
  resources(s[1]);
  assertData(s[2]);
  assertData(s[3]);
  if (!Array.isArray(s[2]) || !Array.isArray(s[3]))
    throw Error("bad effects/receipts");
  for (const e of s[2])
    if (!Array.isArray(e) || e.length !== 2 || typeof e[0] !== "string")
      throw Error("bad effect");
  const ids = new Set();
  for (const d of s[3]) {
    if (
      !Array.isArray(d) ||
      d.length !== 2 ||
      !Array.isArray(d[0]) ||
      d[0].length !== 2 ||
      !Array.isArray(d[1]) ||
      d[1].length !== 2
    )
      throw Error("bad receipt");
    const id = canonical(d[0]);
    if (ids.has(id)) throw Error("duplicate receipt");
    ids.add(id);
    program(d[1][0]);
    bindings(d[1][1]);
  }
}
export const sequence = (ps) =>
  ps.length
    ? ps.reduceRight((q, p) => (q ? ["seq", p, q] : p), null)
    : ["skip"];
