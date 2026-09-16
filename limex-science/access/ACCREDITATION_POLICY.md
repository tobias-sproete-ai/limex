# Individual accreditation policy for sponsored compute

## Boundary first

Accreditation controls a scarce operated service, not the later use of public files. No automatic rule can prove a person's intent or make misuse impossible. The enforceable objective is narrower: no compute capability is issued unless current, cryptographically verified evidence and two independent scientific approvals bind the same subject, project, purpose, key, scopes, time window and budget.

## Admission routes

### Institutional route

Required inputs are: externally verified high-assurance federated identity, current research affiliation or role, holder-of-key evidence, accepted terms, fresh revocation state and two independent scientific approvals. ORCID may add provenance but cannot replace any required item.

### Independent-researcher route

Absence of an institutional account is not an automatic denial. Required inputs are: externally verified identity proofing at the configured assurance level, a reproducible research artefact for the requested scope, holder-of-key evidence, accepted terms, fresh revocation state and two independent scientific approvals. Publication count is not a universal eligibility condition.

## Four-eyes and conflict rules

- Exactly two scientific reviewers are required for the bounded pilot.
- Reviewer identifiers must differ from one another and from the applicant.
- Both reviews must bind the identical scope digest and declare no known conflict.
- Identity verification and scientific review are separate decisions; neither implies the other.
- A denial receives a reason code and a human appeal path. An appeal never activates access automatically.

## Capability contract

An external issuer, not this package, must issue a short-lived sender-constrained capability. It must bind audience, endpoint, subject, project, purpose, scopes, budget, expiry, policy version, credential key and revocation epoch. Every request must prove key possession and be rechecked against expiry, revocation, remaining quota, method/endpoint and request binding. Raw sponsor API keys are forbidden.

## Immediate holds

Credential sharing, suspected compromise, stale assurance, affiliation departure, reviewer conflict, project drift, scope laundering, quota splitting, prohibited egress or inconsistent evidence places only the affected subject/project capability on hold. A confirmed policy- or trust-anchor compromise places the affected trust domain on hold. Reactivation requires new evidence and a fresh decision; it is not a retry of the old grant.

## Data minimisation

The operating service should use a stable pseudonymous subject identifier in routine logs. Identity documents and detailed affiliation attributes stay in the dedicated verifier domain; the decision core receives only necessary signed claims and digests. Retention, access, correction and deletion rules require separate legal approval.

## Pilot saturation criterion

Do not build a universal SSO/ORCID/token marketplace before an actual compute partner and bounded pilot exist. The first pilot is small, manually reviewed, quota-bound and revocable. Automate only a measured bottleneck. This is the explicit control against `DROHENDES UNNÖTIGES KOMPLEXITÄTSWACHSTUM`.
