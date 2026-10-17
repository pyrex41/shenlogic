import { readFileSync } from "node:fs";
import { Runtime, root } from "./runtime.mjs";
import {
  program,
  resources,
  state,
  bindings,
  digest,
  canonical,
  assertData,
} from "./data.mjs";
export const RULEPACK = digest([
  "calculus-v1",
  readFileSync(root + "shen/calculus.shen", "utf8"),
  readFileSync(root + "shen/machine.shen", "utf8"),
  readFileSync(root + "lib/worker.lua", "utf8"),
]);
export class Engine {
  constructor(opts = {}) {
    this.runtime = new Runtime(opts);
  }
  async certify(p, input = [], policy = {}) {
    program(p);
    resources(input);
    const r = await this.runtime.call("infer", p, input);
    if (r[0] !== "ok") return { status: "rejected", reason: r[1] };
    const [, output, effects, proof] = r;
    const certificate = {
      version: 1,
      rulepack: RULEPACK,
      program: p,
      input,
      output,
      effects,
      proof,
      policy,
    };
    const result = await this.verify(certificate);
    return result.status === "accepted"
      ? { ...result, certificate, id: digest(certificate) }
      : result;
  }
  async verify(c) {
    try {
      if (c.version !== 1 || c.rulepack !== RULEPACK)
        throw Error("incompatible rulepack");
      program(c.program);
      resources(c.input);
      resources(c.output);
      assertData(c.effects);
      assertData(c.proof);
      if (!c.policy || typeof c.policy !== "object" || Array.isArray(c.policy))
        throw Error("invalid policy");
      for (const k of Object.keys(c.policy))
        if (
          !["retrySafe", "allowedEffects", "proofMethod", "preserves"].includes(
            k,
          )
        )
          throw Error("unknown policy " + k);
      if (
        !(await this.runtime.call(
          "check",
          c.program,
          c.input,
          c.output,
          c.effects,
          c.proof,
        ))
      )
        return {
          status: "rejected",
          reason: "derivation does not inhabit behavioral type",
        };
      if (
        c.policy.retrySafe !== undefined &&
        typeof c.policy.retrySafe !== "boolean"
      )
        throw Error("retrySafe must be boolean");
      if (c.policy.retrySafe || c.policy.proofMethod) {
        if (
          c.policy.proofMethod &&
          c.policy.proofMethod !== "durable-deduplication"
        )
          throw Error("unsupported proof method");
        if (
          !(await this.runtime.call(
            "retry-safe",
            c.program,
            c.input,
            c.effects,
            ["by-durable-deduplication", c.proof],
          ))
        )
          return {
            status: "rejected",
            reason: "required retry-safe derivation absent",
          };
      }
      if (c.policy.allowedEffects) {
        assertData(c.policy.allowedEffects);
        if (
          !(await this.runtime.call(
            "effects-within",
            c.program,
            c.input,
            c.output,
            c.policy.allowedEffects,
            ["by-effect-inclusion", c.effects, c.proof],
          ))
        )
          return { status: "rejected", reason: "effects exceed policy" };
      }
      if (c.policy.preserves) {
        resources(c.policy.preserves);
        if (
          !(await this.runtime.call(
            "preserves",
            c.program,
            c.input,
            c.output,
            c.effects,
            c.policy.preserves,
            ["by-affine-invariant", c.proof],
          ))
        )
          return {
            status: "rejected",
            reason: "affine invariant not established",
          };
      }
      return { status: "accepted", rulepack: RULEPACK };
    } catch (e) {
      return { status: "rejected", reason: e.message };
    }
  }
  async run(c, s, input = {}, fuel = 10000) {
    const v = await this.verify(c);
    if (v.status !== "accepted") throw Error(v.reason);
    state(s);
    const b = (Array.isArray(input) ? input : Object.entries(input))
      .slice()
      .sort(([a], [b]) => (a < b ? -1 : a > b ? 1 : 0));
    bindings(b);
    if (canonical(s[1]) !== canonical(c.input))
      throw Error("state resource context does not match certificate");
    if (!Number.isInteger(fuel) || fuel < 1 || fuel > 1000000)
      throw Error("invalid fuel");
    return this.runtime.call("run", c.program, s, b, fuel);
  }
  async observe(c, s, input, observation, fuel = 10000) {
    const v = await this.verify(c);
    if (v.status !== "accepted") throw Error(v.reason);
    state(s);
    input = input.slice().sort(([a], [b]) => (a < b ? -1 : a > b ? 1 : 0));
    bindings(input);
    if (canonical(s[1]) !== canonical(c.input))
      throw Error("resource context mismatch");
    if (!Number.isInteger(fuel) || fuel < 1 || fuel > 1000000)
      throw Error("invalid fuel");
    if (
      observation === "unknown-commit" &&
      !["atomic", "once"].includes(c.program[0])
    )
      return [
        "inconclusive",
        s,
        "unknown commit requires an atomic command boundary",
        fuel,
      ];
    if (!["completed", "not-committed", "unknown-commit"].includes(observation))
      throw Error("unsupported observation");
    return this.runtime.call("observe", c.program, s, input, observation, fuel);
  }
  async graph(c) {
    const v = await this.verify(c);
    if (v.status !== "accepted") throw Error(v.reason);
    return this.runtime.call("graph", c.program);
  }
  close() {
    this.runtime.close();
  }
}
