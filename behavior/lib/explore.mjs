import { digest, canonical } from "./data.mjs";
export async function explore(
  engine,
  certificate,
  initial,
  inputs,
  { depth = 3, maxStates = 100, maxEdges = 1000, fuel = 10000 } = {},
) {
  if (
    !Number.isInteger(depth) ||
    depth < 0 ||
    depth > 30 ||
    !Number.isInteger(maxStates) ||
    maxStates < 1 ||
    maxStates > 10000 ||
    !Number.isInteger(maxEdges) ||
    maxEdges < 1 ||
    maxEdges > 100000
  )
    throw Error("invalid exploration bounds");
  const initialId = "v_" + digest(initial),
    states = new Map([[initialId, initial]]),
    queue = [[initialId, 0]],
    edges = [],
    outcomes = [];
  let truncated = false;
  for (let i = 0; i < queue.length; i++) {
    const [id, d] = queue[i];
    if (d >= depth) {
      truncated = true;
      continue;
    }
    for (const input of inputs) {
      if (edges.length >= maxEdges) {
        truncated = true;
        break;
      }
      const result = await engine.run(certificate, states.get(id), input, fuel);
      outcomes.push({ from: id, input, result });
      if (result[0] !== "ok") continue;
      const state = result[1],
        target = "v_" + digest(state);
      if (!states.has(target)) {
        if (states.size >= maxStates) {
          truncated = true;
          continue;
        }
        states.set(target, state);
        queue.push([target, d + 1]);
      }
      const eid = "e_" + digest([id, input, target]);
      edges.push({
        id: eid,
        name: eid,
        sourceVertexId: id,
        targetVertexId: target,
        properties: {
          input,
          expected: state,
          certificate: digest(certificate),
        },
      });
    }
  }
  const graph = {
    name: "behavior",
    id: "model_" + digest(certificate),
    startElementId: initialId,
    generator: "random(length(100))",
    vertices: [...states].map(([id, state]) => ({
      id,
      name: id,
      properties: { state },
    })),
    edges,
  };
  return {
    version: 1,
    certificate: digest(certificate),
    initial: initialId,
    bounds: { depth, maxStates, maxEdges, fuel },
    truncated,
    scope: "bounded concrete command transitions",
    models: [graph],
    outcomes,
  };
}
export function traverse(projection, { seed = 1, length = 20 } = {}) {
  if (
    !Number.isInteger(seed) ||
    !Number.isInteger(length) ||
    length < 0 ||
    length > 10000
  )
    throw Error("invalid traversal options");
  const model = projection.models[0],
    path = [];
  let state = projection.initial,
    x = seed >>> 0;
  for (let i = 0; i < length; i++) {
    const edges = model.edges
      .filter((e) => e.sourceVertexId === state)
      .sort((a, b) => a.id.localeCompare(b.id));
    if (!edges.length) break;
    x = (Math.imul(1664525, x) + 1013904223) >>> 0;
    const e = edges[x % edges.length];
    path.push(e.id);
    state = e.targetVertexId;
  }
  return { version: 1, projection: digest(projection), seed, path };
}
export async function validatePath(engine, certificate, projection, path) {
  if (projection.certificate !== digest(certificate))
    throw Error("projection certificate mismatch");
  let vertex = projection.initial,
    state = projection.models[0].vertices.find((v) => v.id === vertex)
      ?.properties.state;
  if (!state || vertex !== "v_" + digest(state))
    throw Error("missing or corrupt initial state");
  const steps = [];
  for (const id of path) {
    const e = projection.models[0].edges.find((e) => e.id === id);
    if (!e || e.sourceVertexId !== vertex)
      throw Error("disconnected or unknown edge");
    const r = await engine.run(certificate, state, e.properties.input);
    if (r[0] !== "ok" || canonical(r[1]) !== canonical(e.properties.expected))
      throw Error("infeasible projection edge");
    const target = projection.models[0].vertices.find(
      (v) => v.id === e.targetVertexId,
    );
    if (
      e.targetVertexId !== "v_" + digest(r[1]) ||
      canonical(target?.properties.state ?? null) !== canonical(r[1]) ||
      e.properties.certificate !== digest(certificate) ||
      e.id !== "e_" + digest([vertex, e.properties.input, e.targetVertexId])
    )
      throw Error("corrupt projection edge identity");
    state = r[1];
    vertex = e.targetVertexId;
    steps.push({ input: e.properties.input, expected: state, edge: id });
  }
  return { status: "validated", steps };
}
