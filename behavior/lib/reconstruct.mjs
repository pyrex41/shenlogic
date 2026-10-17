import { digest, program } from "./data.mjs";
export function validateFacts(x) {
  if (
    x.version !== 1 ||
    !["ghidra", "php-parser-3.7.0"].includes(x.producer) ||
    !/^[a-f0-9]{64}$/.test(x.artifact)
  )
    throw Error("invalid extraction envelope");
  const schema = {
    Node: 5,
    Flow: 3,
    Calls: 2,
    DefUse: 3,
    Reads: 2,
    Writes: 2,
    Boundary: 3,
    Entry: 2,
    Unknown: 2,
    Contains: 2,
  };
  for (const [name, arity] of Object.entries(schema)) {
    if (!Array.isArray(x.facts?.[name]))
      throw Error("missing relation " + name);
    for (const row of x.facts[name])
      if (
        !Array.isArray(row) ||
        row.length !== arity ||
        row.some((v) => typeof v !== "string" && !Number.isSafeInteger(v))
      )
        throw Error("invalid " + name);
  }
  return x;
}
// Binary realization must be explicitly bound to an exact artifact and entry.
export function reconstructBinary(x, manifest) {
  validateFacts(x);
  if (x.producer !== "ghidra" || manifest.artifact !== x.artifact)
    throw Error("binary identity mismatch");
  const entry = x.facts.Entry.find(([n, id]) => id === manifest.entry);
  if (!entry) throw Error("binary entry absent");
  program(manifest.program);
  if (!Array.isArray(manifest.assumptions) || !manifest.assumptions.length)
    throw Error("binary abstraction assumptions required");
  return {
    version: 1,
    source: x.artifact,
    entry: entry[0],
    status: "assumed",
    program: manifest.program,
    assumptions: manifest.assumptions,
    obligations: x.facts.Unknown.map(([site, reason]) => ({ site, reason })),
    mapping: [{ site: manifest.entry, program: manifest.program }],
    manifest: digest(manifest),
  };
}
export function admit(reconstruction, approvedAssumptions = []) {
  const pending = (reconstruction.assumptions ?? []).filter(
    (a) => !approvedAssumptions.includes(typeof a === "string" ? a : a.claim),
  );
  return {
    status:
      !reconstruction.program ||
      reconstruction.obligations?.length ||
      pending.length
        ? "incomplete"
        : "conditional",
    source: reconstruction.source,
    open: reconstruction.obligations ?? [],
    assumptions: reconstruction.assumptions ?? [],
    unapproved: pending,
  };
}
