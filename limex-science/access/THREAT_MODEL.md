# Sponsored-compute accreditation threat model

Status: `DESIGN_REVIEWED__RUNTIME_NOT_IMPLEMENTED__ALL_LIVE_ACCESS_FAIL_CLOSED`

## Protected assets

Sponsor credentials and budget; identity and holder-of-key evidence; capabilities and revocation state; research applications, prompts, uploads and outputs; reviewer/appeal data; audit logs; and the scientific nonclaims of the public capsule.

## Trust boundaries

1. applicant to intake;
2. intake to identity/federation/ORCID verifiers;
3. client to holder-of-key verifier;
4. reviewers to admission decision;
5. admission service to capability issuer;
6. capability issuer to gateway and compute provider;
7. runtime to tools, network and data stores;
8. metering/audit to operators and reviewers;
9. emergency authority to issuance and execution;
10. public artefact distribution to uncontrolled downstream use.

This package implements only bounded structural validation and lifecycle projection within boundary 4. It implements none of the other runtime boundaries.

## Priority attack stories

- forged `eligible=true`, copied assertions or unknown issuers create false authority;
- stolen or shared credentials consume another person's budget;
- compromised IdP/ORCID account is confused with scientific eligibility;
- sponsor key leaks through client code, headers, traces, logs or support exports;
- token replay or audience/project confusion crosses capability boundaries;
- a revocation race permits refresh or execution after a hold;
- prompt laundering and encoded attachments evade a simple domain filter;
- model/tool egress exfiltrates internal, cross-tenant or confidential data;
- an admitted project changes purpose, data, tools or outputs without review;
- Sybil accounts or project splitting multiply quotas;
- reviewer or operator collusion bypasses conflict controls;
- audit logs become a secondary personal-data or research-surveillance store;
- false positives exclude early-career or independent researchers;
- an emergency hold is either abused selectively or fails to propagate.

## Mandatory runtime gates before any pilot

- verified issuer metadata/trust anchors, signed-assertion verification, audience/time/nonce/replay/key-rotation checks;
- separate fresh holder-of-key challenge and sender-constrained capability;
- append-only admission receipt over exact policy, evidence digests, reviewers, project, scope, budget, key and expiry;
- server-side secret store, log/header redaction and provider cost ceiling;
- tenant isolation, tool/data/egress allowlists and exfiltration tests;
- atomic budget reservation across aliases, projects and concurrent requests;
- online revocation and tested emergency hold across issuer, gateway, caches and in-flight work;
- privacy purpose/lawful-basis matrix, retention limits, access control, correction/deletion and provider/back-up propagation;
- independent appeal and a manual independent-researcher route;
- a small, quota-bound, independently audited pilot.

## Residual risks and nonclaims

No identity system proves benign intent. Holder-of-key does not prove exclusive human control. A signed assertion is true only within its issuer's assurance and compromise model. Revocation cannot recover already observed data or outputs. Pseudonymisation is not anonymisation. Review can be biased or collusive. Abuse testing cannot prove absence of dual use. Hashes prove byte identity, not truth, authority or legality.
