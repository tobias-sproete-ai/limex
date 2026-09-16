# LIMEX Settle cleanroom v1.1.0-rc.1

This successor closes lexical and physical artifact-role aliasing, revalidates all live inputs on idempotent replay, enforces bounded ledger growth and restrictive local storage permissions, rejects macOS extended ALLOW ACLs, binds tracked Git bytes with aggregate SHA-256 and bounded work, and requires a caller-supplied trusted package root for frozen verification. It does not claim an adversarially atomic filesystem snapshot; that remains a separately bound release prerequisite.

- Removed organization-specific identifiers, personal identifiers, local host paths, repository coordinates, credentials, private operational evidence, and excluded-source inventory metadata.
- Replaced deployment-specific filing-status labels and reference identifiers with neutral public contract values.
- Preserved the settlement-core logic and its finite test corpus.
- Added a self-contained cleanroom validator and a non-mutating frozen-package verifier.
- Kept the public-release gate closed.

This candidate is prepared for later review and publication. It has not been publicly released.
