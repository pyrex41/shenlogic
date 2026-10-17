import { digest, bindings, assertData, canonical } from "./data.mjs";
export async function checkTrace(
  engine,
  certificate,
  initial,
  trace,
  { maxWorlds = 1000, fuel = 10000 } = {},
) {
  if (!Number.isInteger(maxWorlds) || maxWorlds < 1 || maxWorlds > 10000)
    throw Error("invalid world bound");
  let worlds = [initial],
    incomplete = false;
  const judgments = [];
  for (let i = 0; i < trace.length; i++) {
    const event = trace[i];
    bindings(event.input);
    const next = [];
    for (const w of worlds) {
      const r = await engine.observe(
        certificate,
        w,
        event.input,
        event.outcome,
        fuel,
      );
      if (r[0] === "alternatives") next.push(...r[1]);
      else if (r[0] === "ok" || r[0] === "error") next.push(r[1]);
      else return { status: "inconclusive", reason: r[2], index: i, judgments };
    }
    worlds = [...new Map(next.map((w) => [canonical(w), w])).values()];
    if (worlds.length > maxWorlds)
      return {
        status: "inconclusive",
        reason: "world bound exceeded",
        index: i,
        judgments,
      };
    if (event.observation) {
      const o = event.observation;
      bindings(o.store);
      assertData(o.effects);
      if (typeof o.complete !== "boolean" || !Array.isArray(o.effects))
        throw Error("invalid observation envelope");
      for (const ef of o.effects)
        if (!Array.isArray(ef) || ef.length !== 2 || typeof ef[0] !== "string")
          throw Error("invalid observed effect");
      const [status, matched] = await engine.runtime.call(
        "judge",
        worlds,
        o.store,
        o.effects,
        o.complete,
      );
      judgments.push({ index: i, status, worlds: matched.length });
      if (status === "violation")
        return {
          status,
          index: i,
          judgments,
          counterexample: trace.slice(0, i + 1),
        };
      worlds = matched;
      incomplete = !o.complete;
    } else {
      incomplete = true;
      judgments.push({
        index: i,
        status: "inconclusive",
        reason: "no observation",
      });
    }
  }
  return {
    status: incomplete ? "inconclusive" : "compatible",
    worlds: worlds.length,
    judgments,
    scope: "observed finite trace; not universal implementation conformance",
  };
}
export function migrationContract(legacy, intended, decisions = []) {
  return {
    version: 1,
    legacy: digest(legacy),
    intended: digest(intended),
    decisions,
  };
}
export function compareMigration(contract, legacy, intended, left, right) {
  if (
    contract.version !== 1 ||
    contract.legacy !== digest(legacy) ||
    contract.intended !== digest(intended)
  )
    throw Error("migration model identity mismatch");
  if (canonical(left) === canonical(right)) return { status: "preserved" };
  const finding = digest({
    legacy: contract.legacy,
    intended: contract.intended,
    left,
    right,
  });
  const matches = contract.decisions.filter((d) => d.finding === finding);
  if (matches.length > 1) throw Error("ambiguous migration decisions");
  if (!matches.length)
    return { status: "unapproved-change", finding, left, right };
  const d = matches[0];
  if (
    !d.approvedBy ||
    !d.rationale ||
    !["allow", "forbid"].includes(d.disposition)
  )
    throw Error("incomplete migration decision");
  return {
    status: d.disposition === "allow" ? "approved-change" : "forbidden-change",
    finding,
    decision: d,
  };
}
// Delta debugging preserves scenario order and only removes operations.
export async function minimize(items, fails) {
  if (!(await fails(items))) throw Error("initial scenario does not fail");
  let out = items.slice(),
    n = 2;
  while (out.length > 1) {
    let reduced = false;
    const size = Math.ceil(out.length / n);
    for (let i = 0; i < out.length; i += size) {
      const candidate = out.slice(0, i).concat(out.slice(i + size));
      if (candidate.length && (await fails(candidate))) {
        out = candidate;
        n = Math.max(2, n - 1);
        reduced = true;
        break;
      }
    }
    if (!reduced) {
      if (n >= out.length) break;
      n = Math.min(out.length, n * 2);
    }
  }
  return out;
}
