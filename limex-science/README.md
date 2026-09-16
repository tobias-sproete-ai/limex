# LIMEX Science public cleanroom RC4

Read the [LIMEX Science preface](PREFACE.md), the [research-payload binding](RESEARCH_PAYLOAD_BINDING.json), and the [owner-approval boundary](release/OWNER_RELEASE_APPROVAL.md).

This candidate separates two different things:

1. **Public research artefacts.** Once independently cleared and released, downloaded files cannot be technically limited to verified scientists. Their lawful use is governed by the selected licence and applicable law.
2. **Scarce sponsored compute.** This remains a controlled service capability. Admission is individual, project-, purpose-, key-, time-, scope- and budget-bound and is rechecked on every use.

The included Python core is a deterministic structural admission projector. It deliberately cannot verify a real person, trust an identity provider, issue a token, dispatch compute, or activate an account. Its strongest result is `HOLD_EXTERNAL_VERIFICATION_REQUIRED`; every result has `external_effect = DENY` and `access_grant = null`.

Actual accreditation requires a separately operated service that verifies signed evidence against configured trust anchors, current revocation state and holder-of-key proof, followed by two independent scientific reviews. Neither ORCID nor institutional login alone is sufficient.

Current release state: `RC4__PENDING_POST_FREEZE_AUDIT_AND_DIGEST_BOUND_CONFIRMATION__NO_SPONSORED_COMPUTE`.

Before freezing a newly assembled successor, run:

```sh
python3 -m unittest discover -s tests -v
python3 scripts/validate_cleanroom_release.py
python3 scripts/build_manifest.py
```

After downloading or checking out the frozen RC4, run only the post-freeze checks:

```sh
python3 -m unittest discover -s tests -v
python3 scripts/verify_frozen_package.py
shasum -a 256 -c SHA256SUMS.txt
```

The validator and manifest builder intentionally reject an already frozen package. That rejection protects the once-only freeze and is not a release failure.

The research payload is not duplicated inside this access-control package. It is bound to the immutable `goldbach-v1.8.767` repository tag by `RESEARCH_PAYLOAD_BINDING.json`; `proof_status = NO_PROOF` remains unchanged.
