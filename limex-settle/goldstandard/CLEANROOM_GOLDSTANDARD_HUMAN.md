# LIMEX Settle cleanroom release Goldstandard

## Bound result

This artifact set is the security-hardening successor candidate `LIMEX_SETTLE_CLEANROOM_V1_1_RC1`. It preserves the deterministic settlement and release-seal implementation while removing organization-specific identifiers, personal identifiers, local host paths, repository coordinates, credentials, private operational evidence, and inventories of excluded private sources.

The successor rejects lexical and physical artifact-role aliasing, remeasures every live release input before accepting an existing envelope, bounds SQLite pages, rows and event-result materialization, verifies restrictive local storage permissions, binds release-state operations to a retained directory descriptor, rejects namespace displacement, compares HEAD/index/raw worktree state without invoking repository-selected content filters, and requires the frozen verifier to receive an expected package root from a separate trusted channel.

## Evidence classes

- Implementation: present in `src/`.
- Finite regression corpus: present in `tests/`.
- Cleanroom provenance: `CLEANROOM_PROVENANCE.json`.
- Security review: summarized in `evidence/SECURITY_SCAN_STATUS.json` after completion.
- Technical validation: `evidence/CLEANROOM_VALIDATION_REPORT.json`.
- Whole-package byte identity: `PACKAGE_MANIFEST.json` and `SHA256SUMS.txt`.

## Status boundary

A cleanroom validation pass establishes only that all final package files pass the generic metadata and secret-pattern scan, that source parses, all 107 included finite tests pass under the stated local no-network sandbox, the security summary matches the reviewed file inventory and bound report bytes, provenance rows match their outputs, and package identity is reproducible against a separately supplied expected root.

It does not establish public-release authority, patentability, freedom to operate, legal or regulatory compliance, production readiness, external-provider operation, hard real-time behavior, universal security, or an adversarially atomic multi-file snapshot on a concurrently writable filesystem. Public release additionally requires a separately attested immutable snapshot or read-only source and a signed independent security attestation bound to the same root. `PUBLIC_RELEASE_GATE.json` remains authoritative and fail-closed.

## Mutation rule

This candidate becomes append-only when `PACKAGE_MANIFEST.json` is built. Any later byte change requires a successor identity, a fresh cleanroom scan, a fresh security scan, rebuilt manifests, and renewed release-gate evidence. No in-place correction is admissible after freeze.
