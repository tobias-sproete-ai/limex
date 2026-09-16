# LIMEX Settle — public cleanroom release candidate

`RELEASE = LIMEX_SETTLE_CLEANROOM_V1_1_RC1`

`PUBLICATION_STATUS = BLOCKED__NO_PUBLIC_RELEASE_DISPATCH`

This package contains a self-contained reference implementation of a deterministic, fail-closed settlement and release-seal core. It separates technical event evidence from billing or payment execution, rejects ambiguous or replayed state transitions, binds release inputs by content digest, and keeps language-model output outside the authority boundary.

The package deliberately contains no organization-specific identity, personal identity, host path, repository coordinate, credential, private operational record, or excluded-source inventory. Its cleanroom provenance records only public package paths, predecessor content digests, and the transformation class.

## Local verification

```sh
python3 -B scripts/validate_cleanroom_release.py
python3 -B scripts/build_manifest.py
python3 -B scripts/verify_frozen_package.py --expected-root-sha256 <TRUSTED_PACKAGE_ROOT_SHA256>
```

The first command performs the bounded cleanroom, source, security-evidence and 107-test gates under a local no-network sandbox. The second creates the self-excluding manifest and checksum list. The third re-verifies the frozen identity against a package-root digest obtained through a separate trusted channel; copying the value from the package itself is not authentication.

The local storage boundary is deliberately strict: the state and ledger directories must be owner-only, existing state files are rechecked, macOS extended ALLOW ACLs are rejected, and unsupported ACL platforms fail closed. Release-state operations stay bound to one retained directory descriptor and stop if the configured namespace is displaced. Tracked Git bytes additionally receive an aggregate SHA-256 identity and application-level file, byte, output and time budgets; HEAD must resolve directly to a commit, and HEAD, index and raw worktree bytes are compared without invoking repository-selected content filters or replacement objects. Every Git child disables lazy object fetching, interactive prompts, credential helpers and transports. This candidate currently makes no cross-platform storage-assurance or hard OS-level process-resource claim.

## Release boundary

This is a technically validated candidate, not a deployed payment rail, wallet, blockchain, bank integration, production service, safety certification, patentability opinion, or public-release authorization. Public dispatch remains blocked until every condition in `PUBLIC_RELEASE_GATE.json` is independently satisfied for these exact bytes.
