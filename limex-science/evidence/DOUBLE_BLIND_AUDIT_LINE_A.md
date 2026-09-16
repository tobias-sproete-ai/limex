# Double-blind audit line A: admission-contract and state-machine review

Reviewed protected input root: `5bfe5702b3747fa5198125e503c93c7fe49c3701a7fc550a04efddcb95b2d99e`

Verdict: `PASS_SOURCE_CONFORMANCE__LIVE_ACCREDITATION_FAIL_CLOSED`.

The read-only reviewer independently executed 49 unit tests, 35 binding mutations, 1,140 type/shape mutations and 56 lifecycle combinations. No path produced `ACTIVE`, a capability, compute dispatch, public release, an uncaught exception with effect, or an output other than `DENY_FAIL_CLOSED` / `HOLD_EXTERNAL_VERIFICATION_REQUIRED` with `external_effect = DENY` and `access_grant = null`.

The review confirmed joint binding of one `NATURAL_PERSON` subject, application, project, purpose, scopes, budget, time window, credential key and policy. Evidence and reviews must remain valid through the requested grant. Evidence, reviews, revocation and terms remain marked `SIGNATURE_AND_TRUST_CHAIN_VERIFICATION_REQUIRED`; self-asserted `VERIFIED` values are rejected. ORCID remains optional provenance and cannot substitute for either admission route.

Initial pre-freeze findings were not suppressed. They were reproduced and closed before this verdict:

- tested-source mutation was prevented through before/after protected-tree identity;
- the exact A0-A14 service-gate list became mandatory;
- only canonical raw JSON bytes reach the public evaluator;
- signed terms, maximum revocation age/TTL and evidence/review coverage through grant expiry became mandatory;
- nesting and container-node limits prevent recursive input failure;
- validation report, logs and tested-tree root became freeze-bound;
- report schemas and nonclaims became exact rather than partial;
- manifest creation became once-only with `O_EXCL`;
- duplicate JSON keys became invalid at every machine-effective parser.

The reviewer changed no package file and contacted no external service. Its PASS does not cover real identity proofing, trust-chain verification, account activation, capability issuance, compute operation, legal approval or publication authority.
