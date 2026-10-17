import { program, digest } from "./data.mjs";
// Named behavioral definitions are macros over inert data, never host code.
export function compose(model) {
  const definitions = model.definitions ?? {};
  let nodes = 0;
  function substitute(x, env) {
    if (Array.isArray(x)) {
      if (x[0] === "param" && x.length === 2) {
        if (!Object.hasOwn(env, x[1])) throw Error("unbound parameter " + x[1]);
        return env[x[1]];
      }
      return x.map((v) => substitute(v, env));
    }
    return x;
  }
  function expand(p, stack = []) {
    if (++nodes > 10000 || stack.length > 100) throw Error("expansion bound");
    if (!Array.isArray(p)) throw Error("program required");
    if (p[0] === "invoke") {
      const [, name, args] = p,
        d = definitions[name];
      if (
        p.length !== 3 ||
        !d ||
        !Array.isArray(args) ||
        !Array.isArray(d.parameters) ||
        args.length !== d.parameters.length
      )
        throw Error("invalid invocation " + name);
      if (stack.includes(name))
        throw Error("recursive invocation needs explicit bounded repeat");
      if (new Set(d.parameters).size !== d.parameters.length)
        throw Error("duplicate parameter");
      return expand(
        substitute(
          d.program,
          Object.fromEntries(d.parameters.map((k, i) => [k, args[i]])),
        ),
        [...stack, name],
      );
    }
    const q = structuredClone(p);
    if (q[0] === "seq") {
      q[1] = expand(q[1], stack);
      q[2] = expand(q[2], stack);
    }
    if (q[0] === "case") {
      q[2] = expand(q[2], stack);
      q[3] = expand(q[3], stack);
    }
    if (q[0] === "atomic") q[1] = expand(q[1], stack);
    if (["repeat", "once"].includes(q[0])) q[2] = expand(q[2], stack);
    return q;
  }
  const p = expand(model.program);
  program(p);
  return {
    program: p,
    source: digest(model),
    resources: model.resources ?? [],
    policy: model.policy ?? {},
  };
}
