#!/usr/bin/env node

import { createHash } from "node:crypto";
import { readFile, readdir, stat } from "node:fs/promises";
import { dirname, join, relative, resolve } from "node:path";
import { fileURLToPath } from "node:url";

const root = resolve(dirname(fileURLToPath(import.meta.url)), "..");
const fail = (reason) => {
  process.stdout.write(`${JSON.stringify({ status: "FAIL", reason })}\n`);
  process.exit(1);
};
const sha256 = (bytes) => createHash("sha256").update(bytes).digest("hex");

const expected = new Map();
for (const line of (await readFile(join(root, "SHA256SUMS"), "utf8")).trim().split("\n")) {
  const match = line.match(/^([0-9a-f]{64})  (.+)$/);
  if (!match) fail("MALFORMED_SHA256SUMS");
  expected.set(match[2], match[1]);
}

for (const [path, digest] of expected) {
  const bytes = await readFile(join(root, path));
  if (sha256(bytes) !== digest) fail(`HASH_MISMATCH:${path}`);
}

const machine = JSON.parse(await readFile(join(root, "GOLDSTANDARD_GOLDBACH_TOTAL_TOKEN_CENSUS_V1.json"), "utf8"));
const m = machine.adjudicated_local_measurement;
if (m.goldbach_only_lower_bound_tokens + m.mixed_nonseparable_tokens !== m.goldbach_related_upper_bound_tokens) {
  fail("LOWER_PLUS_MIXED_RECONCILIATION_FAILED");
}
if (m.goldbach_related_upper_bound_tokens + m.non_goldbach_sidequest_tokens !== m.full_local_chronology_tokens) {
  fail("UPPER_PLUS_SIDEQUEST_RECONCILIATION_FAILED");
}
if (machine.verdict.global_exact_total !== "NOT_IDENTIFIABLE") fail("GLOBAL_STATUS_DRIFT");
if (machine.verdict.energy_inference !== "NOT_PERFORMED") fail("ENERGY_STATUS_DRIFT");

const files = [];
async function walk(dir) {
  for (const entry of await readdir(dir, { withFileTypes: true })) {
    const path = join(dir, entry.name);
    if (entry.isSymbolicLink()) fail(`SYMLINK_FORBIDDEN:${relative(root, path)}`);
    if (entry.isDirectory()) await walk(path);
    else if (entry.isFile()) files.push(relative(root, path));
    else fail(`SPECIAL_FILE_FORBIDDEN:${relative(root, path)}`);
  }
}
await walk(root);

for (const path of files) {
  const info = await stat(join(root, path));
  if (info.size > 1_000_000) fail(`UNEXPECTED_LARGE_FILE:${path}`);
  if (/\.jsonl$/i.test(path)) fail(`RAW_LEDGER_FORBIDDEN:${path}`);
  if (path === "scripts/verify_public_release.mjs") continue;
  const text = await readFile(join(root, path), "utf8");
  if (/\/Users\//.test(text) || /[A-Za-z]:\\Users\\/.test(text)) fail(`ABSOLUTE_USER_PATH_FORBIDDEN:${path}`);
  if (/BEGIN (RSA |OPENSSH |EC |DSA )?PRIVATE KEY/.test(text)) fail(`PRIVATE_KEY_FORBIDDEN:${path}`);
}

const required = [
  "README.md",
  "GOLDSTANDARD_GOLDBACH_TOTAL_TOKEN_CENSUS_V1.md",
  "GOLDSTANDARD_GOLDBACH_TOTAL_TOKEN_CENSUS_V1.json",
  "AUDIT_SUMMARY.md",
  "STATUS.md",
  "NOTICE.md",
  "RELEASE_NOTES.md",
  "PUBLICATION_MANIFEST.json",
  "scripts/verify_public_release.mjs"
];
for (const path of required) if (!expected.has(path)) fail(`UNBOUND_REQUIRED_FILE:${path}`);

process.stdout.write(`${JSON.stringify({
  status: "PASS",
  package_id: "goldbach-token-census-v1.0.0",
  bound_files: expected.size,
  global_exact_total: "NOT_IDENTIFIABLE",
  proof_status: "NO_PROOF"
})}\n`);
