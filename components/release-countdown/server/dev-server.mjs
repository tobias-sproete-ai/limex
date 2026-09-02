import { createReadStream } from "node:fs";
import { createServer } from "node:http";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";

const root = dirname(dirname(fileURLToPath(import.meta.url)));
const port = Number(process.env.PORT || 4177);

const files = new Map([
  ["/", [join(root, "demo/index.html"), "text/html; charset=utf-8"]],
  ["/src/countdown-widget.mjs", [join(root, "src/countdown-widget.mjs"), "text/javascript; charset=utf-8"]],
  ["/src/countdown-core.mjs", [join(root, "src/countdown-core.mjs"), "text/javascript; charset=utf-8"]]
]);

const server = createServer((request, response) => {
  response.setHeader("Cache-Control", "no-store");
  response.setHeader("X-Content-Type-Options", "nosniff");

  if (request.url === "/api/time" && (request.method === "HEAD" || request.method === "GET")) {
    response.setHeader("X-Limex-Server-Time", new Date().toISOString());
    response.setHeader("Content-Type", "application/json; charset=utf-8");
    response.statusCode = 200;
    response.end(request.method === "HEAD" ? undefined : JSON.stringify({ status: "TIME_ONLY" }));
    return;
  }

  const selected = files.get(request.url);
  if (!selected || request.method !== "GET") {
    response.statusCode = 404;
    response.end("Not found");
    return;
  }

  response.setHeader("Content-Type", selected[1]);
  createReadStream(selected[0]).pipe(response);
});

server.listen(port, "127.0.0.1", () => {
  process.stdout.write(`LIMEX_COUNTDOWN_DEMO http://127.0.0.1:${port}\n`);
});
