import { createHash } from "node:crypto";
import { readFile } from "node:fs/promises";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";

const root = dirname(dirname(fileURLToPath(import.meta.url)));
const manifest = JSON.parse(await readFile(join(root, "ARTIFACT_MANIFEST.json"), "utf8"));
const entries = Object.entries(manifest.files).sort(([a], [b]) =>
  a < b ? -1 : a > b ? 1 : 0
);

for (const [relativePath, expectedHash] of entries) {
  const bytes = await readFile(join(root, relativePath));
  const actualHash = createHash("sha256").update(bytes).digest("hex");
  if (actualHash !== expectedHash) {
    throw new Error(`HASH_MISMATCH ${relativePath}: ${actualHash} != ${expectedHash}`);
  }
}

const treePreimage = entries.map(([path, hash]) => `${hash}  ${path}\n`).join("");
const treeHash = createHash("sha256").update(treePreimage).digest("hex");
if (treeHash !== manifest.tree_sha256) {
  throw new Error(`TREE_HASH_MISMATCH ${treeHash} != ${manifest.tree_sha256}`);
}

process.stdout.write(JSON.stringify({
  status: "PASS_MANIFEST_READBACK",
  files: entries.length,
  tree_sha256: treeHash
}) + "\n");
