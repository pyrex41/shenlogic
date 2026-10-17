import { readdirSync, readFileSync } from "node:fs";
import { join, relative, resolve } from "node:path";
import PHP from "php-parser";
import { bytesDigest, digest, sequence, program } from "../lib/data.mjs";
const parser = new PHP({
  parser: { extractDoc: true, suppressErrors: false },
  ast: { withPositions: true, withSource: true },
});
const children = (n) =>
  Object.entries(n ?? {})
    .filter(
      ([k]) =>
        !["loc", "comments", "leadingComments", "trailingComments"].includes(k),
    )
    .flatMap(([, v]) =>
      Array.isArray(v) ? v.filter((x) => x?.kind) : v?.kind ? [v] : [],
    );
const callName = (n) =>
  n?.kind === "name" ? n.name : n?.kind === "identifier" ? n.name : null;
export function extractPHP(source, filename = "input.php") {
  const ast = JSON.parse(JSON.stringify(parser.parseCode(source, filename))),
    hash = bytesDigest(source),
    facts = {
      Node: [],
      Flow: [],
      Calls: [],
      DefUse: [],
      Reads: [],
      Writes: [],
      Boundary: [],
      Entry: [],
      Unknown: [],
      Contains: [],
    },
    ids = new WeakMap(),
    functions = [];
  function walk(n, parent = null) {
    if (!n?.kind) return;
    const id = `${hash}:${bytesDigest(filename)}:${n.loc?.start.offset ?? 0}:${n.kind}:${facts.Node.length}`;
    ids.set(n, id);
    facts.Node.push([
      id,
      n.kind,
      filename,
      n.loc?.start.line ?? 0,
      n.loc?.end.line ?? 0,
    ]);
    if (parent) facts.Contains.push([parent, id]);
    if (n.kind === "function" || n.kind === "method") {
      const name = callName(n.name) ?? n.name;
      functions.push({ name, id, node: n, artifact: hash, filename });
      facts.Entry.push([String(name), id]);
    }
    for (const c of children(n)) walk(c, id);
  }
  walk(ast);
  function scan(n, owner) {
    if (n.kind === "function" || n.kind === "method") owner = ids.get(n);
    const id = ids.get(n);
    if (n.kind === "call") {
      const target = callName(n.what);
      if (target) facts.Calls.push([id, target]);
      else facts.Unknown.push([id, "unresolved-call-target"]);
    }
    if (n.kind === "variable") {
      if (typeof n.name === "string")
        facts.Reads.push([id, "variable:" + n.name]);
      else facts.Unknown.push([id, "dynamic-variable"]);
    }
    if (n.kind === "assign") {
      const variable = n.left?.kind === "variable" ? n.left.name : null;
      if (typeof variable === "string")
        facts.Writes.push([id, "variable:" + variable]);
      else facts.Unknown.push([id, "complex-write"]);
    }
    if (["eval", "include", "goto", "yield", "yieldfrom"].includes(n.kind))
      facts.Unknown.push([id, "dynamic-or-unsupported-control:" + n.kind]);
    for (const c of children(n)) scan(c, owner);
  }
  scan(ast, null);
  // Conservative statement CFG. Loops and exception flow stay explicitly incomplete.
  function block(b, next = null) {
    const list =
      b?.kind === "block"
        ? b.children
        : b?.kind === "program"
          ? b.children
          : [b];
    let continuation = next;
    for (let i = list.length - 1; i >= 0; i--) {
      const n = list[i];
      if (!n) continue;
      const id = ids.get(n);
      if (n.kind === "if") {
        const yes = block(n.body, continuation),
          no = n.alternate ? block(n.alternate, continuation) : continuation;
        if (yes) facts.Flow.push([id, yes, "true"]);
        if (no) facts.Flow.push([id, no, "false"]);
      } else if (
        ["while", "do", "for", "foreach", "try", "switch"].includes(n.kind)
      ) {
        facts.Unknown.push([id, "incomplete-control-flow:" + n.kind]);
        if (continuation) facts.Flow.push([id, continuation, "may-next"]);
      } else if (!["return", "throw"].includes(n.kind) && continuation)
        facts.Flow.push([id, continuation, "next"]);
      continuation = id;
    }
    return continuation;
  }
  for (const f of functions) {
    const start = block(f.node.body);
    if (start) facts.Flow.push([f.id, start, "entry"]);
  }
  // Def-use facts are explicitly MAY relationships within a function, not SSA.
  for (const f of functions) {
    const descendants = new Set();
    function collect(n) {
      descendants.add(ids.get(n));
      for (const c of children(n)) collect(c);
    }
    collect(f.node);
    for (const [w, key] of facts.Writes)
      if (descendants.has(w))
        for (const [r, k] of facts.Reads)
          if (k === key && descendants.has(r)) facts.DefUse.push([w, r, "may"]);
  }
  return {
    version: 1,
    producer: "php-parser-3.7.0",
    artifact: hash,
    filename,
    ast,
    facts,
    functions: functions.map(({ name, id, node, artifact, filename }) => ({
      name,
      id,
      node,
      artifact,
      filename,
    })),
    coverage: {
      syntax: true,
      cfg: "partial",
      calls: "partial",
      defUse: "may-overapproximation",
    },
  };
}
export function reconstructPHP(extraction, contracts, entry) {
  const matches = extraction.functions.filter(
    (f) => f.id === entry || f.name === entry,
  );
  if (matches.length !== 1)
    throw Error("entry missing or ambiguous; use exact node ID: " + entry);
  const f = matches[0];
  const obligations = [],
    assumptions = [],
    mapping = [];
  const nodes = extraction.facts.Node;
  const id = (n) =>
    nodes.find((row) =>
      row[0].startsWith(
        `${f.artifact ?? extraction.artifact}:${bytesDigest(f.filename ?? extraction.filename)}:${n.loc?.start.offset ?? 0}:${n.kind}:`,
      ),
    )?.[0] ?? f.id;
  function unknown(n, reason) {
    obligations.push({ site: id(n), reason });
    return ["skip"];
  }
  function expr(n) {
    if (n?.kind === "number") {
      const x = Number(n.value);
      if (Number.isInteger(x) && Math.abs(x) <= 2147483647) return ["lit", x];
    }
    if (n?.kind === "boolean" || n?.kind === "string") return ["lit", n.value];
    if (
      n?.kind === "variable" &&
      typeof n.name === "string" &&
      contracts.parameters?.[n.name]
    )
      return ["input", contracts.parameters[n.name]];
    if (n?.kind === "bin") {
      const op = {
        "+": "+",
        "-": "-",
        "*": "*",
        "===": "=",
        "<": "<",
        "<=": "<=",
        "&&": "and",
        "||": "or",
      }[n.type];
      if (op) return [op, expr(n.left), expr(n.right)];
    }
    throw Error("unsupported expression " + n?.kind);
  }
  function subst(p, args) {
    if (Array.isArray(p)) {
      if (p[0] === "arg" && p.length === 2) {
        if (!Number.isInteger(p[1]) || p[1] < 0 || p[1] >= args.length)
          throw Error("contract argument out of range");
        return expr(args[p[1]]);
      }
      return p.map((x) => subst(x, args));
    }
    return p;
  }
  function stmt(n) {
    if (!n) return ["skip"];
    if (n.kind === "block") return sequence(n.children.map(stmt));
    if (n.kind === "expressionstatement") return stmt(n.expression);
    if (n.kind === "if") {
      try {
        return ["case", expr(n.test), stmt(n.body), stmt(n.alternate)];
      } catch (e) {
        return unknown(n, e.message);
      }
    }
    if (n.kind === "call") {
      const name = callName(n.what),
        c = contracts.calls?.[name],
        scope = contracts.scopes?.[name];
      try {
        if (scope) {
          const body = n.arguments[scope.body];
          if (body?.kind !== "closure")
            return unknown(n, "scope body is not a closure");
          if (scope.kind === "once") {
            const key = expr(n.arguments[scope.argument]);
            if (key[0] !== "input" || key[1] !== scope.key)
              return unknown(n, "deduplication key mismatch");
          }
          assumptions.push({ site: id(n), claim: scope.assumption });
          const p =
            scope.kind === "once"
              ? ["once", scope.key, stmt(body.body)]
              : scope.kind === "atomic"
                ? ["atomic", stmt(body.body)]
                : null;
          if (!p) return unknown(n, "unsupported scope");
          mapping.push({ site: id(n), program: p, contract: name });
          return p;
        }
        if (!c) return unknown(n, "unmapped call " + (name ?? "<dynamic>"));
        if (n.arguments.length !== c.arity)
          return unknown(n, "call arity mismatch " + name);
        if (!c.assumption)
          throw Error("contract must name its trust assumption");
        const p = subst(c.program, n.arguments);
        program(p);
        assumptions.push({ site: id(n), claim: c.assumption });
        mapping.push({ site: id(n), program: p, contract: name });
        return p;
      } catch (e) {
        return unknown(n, e.message);
      }
    }
    return unknown(n, "unsupported statement " + n.kind);
  }
  const p = stmt(f.node.body);
  return {
    version: 1,
    entry,
    source: extraction.artifact,
    contracts: digest(contracts),
    status: obligations.length ? "incomplete" : "reconstructed",
    program: obligations.length ? null : p,
    candidate: p,
    mapping,
    assumptions,
    obligations,
  };
}

export function extractProject(directory) {
  const base = resolve(directory),
    files = [];
  function walk(dir) {
    for (const entry of readdirSync(dir, { withFileTypes: true }).sort((a, b) =>
      a.name.localeCompare(b.name),
    )) {
      if (
        entry.isSymbolicLink() ||
        [".git", "node_modules", "vendor"].includes(entry.name)
      )
        continue;
      const p = join(dir, entry.name);
      if (entry.isDirectory()) walk(p);
      else if (entry.isFile() && entry.name.endsWith(".php")) files.push(p);
    }
  }
  walk(base);
  if (!files.length) throw Error("no PHP files found");
  const units = files.map((file) =>
    extractPHP(readFileSync(file, "utf8"), relative(base, file)),
  );
  const manifest = units.map((u) => ({
    path: u.filename,
    artifact: u.artifact,
  }));
  const facts = Object.fromEntries(
    Object.keys(units[0].facts).map((k) => [
      k,
      units.flatMap((u) => u.facts[k]),
    ]),
  );
  return {
    version: 1,
    producer: "php-parser-3.7.0",
    artifact: digest(manifest),
    filename: base,
    manifest,
    facts,
    functions: units.flatMap((u) => u.functions),
    units,
    coverage: {
      syntax: true,
      cfg: "partial",
      calls: "partial",
      defUse: "may-overapproximation",
      excluded: ["symlinks", ".git", "node_modules", "vendor"],
    },
  };
}
