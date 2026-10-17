import { createServer } from "node:http";
import { timingSafeEqual } from "node:crypto";
import { Engine } from "./engine.mjs";
import { EvidenceStore } from "./store.mjs";
import { explore } from "./explore.mjs";
import { checkTrace } from "./conformance.mjs";
export async function service({
  port = 0,
  token,
  database = ":memory:",
  engine = new Engine(),
} = {}) {
  if (typeof token !== "string" || token.length < 16)
    throw Error("API token must contain at least 16 characters");
  const store = new EvidenceStore(database);
  await engine.runtime.ready;
  const server = createServer(async (req, res) => {
    res.setHeader("content-type", "application/json");
    const reply = (status, body) => {
      res.statusCode = status;
      res.end(JSON.stringify(body));
    };
    const given = Buffer.from(req.headers.authorization ?? ""),
      expected = Buffer.from("Bearer " + token);
    if (
      req.headers.origin ||
      given.length !== expected.length ||
      !timingSafeEqual(given, expected)
    )
      return reply(403, { error: "unauthorized" });
    try {
      if (req.method === "GET" && /^\/artifact\/[a-f0-9]{64}$/.test(req.url))
        return reply(200, store.get(req.url.split("/")[2]));
      if (req.method !== "POST") return reply(405, { error: "POST required" });
      let body = "",
        bytes = 0;
      for await (const chunk of req) {
        bytes += chunk.length;
        if (bytes > 1000000) {
          reply(413, { error: "request bound" });
          return;
        }
        body += chunk;
      }
      const x = JSON.parse(body);
      let result;
      switch (req.url) {
        case "/certify":
          result = await engine.certify(
            x.program,
            x.resources ?? [],
            x.policy ?? {},
          );
          break;
        case "/verify":
          result = await engine.verify(x.certificate);
          break;
        case "/run":
          result = await engine.run(x.certificate, x.state, x.input, x.fuel);
          break;
        case "/explore":
          result = await explore(
            engine,
            x.certificate,
            x.initial,
            x.inputs,
            x.options,
          );
          break;
        case "/check-trace":
          result = await checkTrace(
            engine,
            x.certificate,
            x.initial,
            x.trace,
            x.options,
          );
          break;
        default:
          return reply(404, { error: "unknown endpoint" });
      }
      const id = store.put("api-result", { request: x, result });
      reply(200, { artifact: id, result });
    } catch (e) {
      reply(400, { error: e.message });
    }
  });
  await new Promise((resolve, reject) => {
    server.once("error", reject);
    server.listen(port, "127.0.0.1", resolve);
  });
  return {
    server,
    port: server.address().port,
    close: async () => {
      await new Promise((r) => server.close(r));
      engine.close();
      store.close();
    },
  };
}
