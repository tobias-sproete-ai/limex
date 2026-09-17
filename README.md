At 23:59 CEST on 15 September 2026, we froze more than a software release.

LIMEX carries an intellectual lineage inside its control architecture: Kant’s boundary between appearance and justified knowledge; Popper’s asymmetry between a bounded success and a decisive counterexample; Montesquieu’s separation of rule, proposal, audit and execution; Epictetus’ discipline of controlling only one’s own transitions; Dijkstra’s demand for intellectual humility; Taleb’s via negativa; and Kleene’s three-valued logic for TRUE, FALSE and UNKNOWN.

These thinkers do not act as runtime authorities, and their philosophy is not “proved” by code. Their ideas were translated into deterministic gates: proposals are not truths, unknown is not permission, a model cannot audit itself, and missing evidence must remain missing.

The release identity was hash-bound and published. Any future change must become a new version with a new digest. No invisible rewrite. No narrative override.

We did not throw away the ability to build successors. We threw away the ability to pretend that a successor was the original.

Kant is not quoted in the kernel.

His boundary is.

https://github.com/tobias-sproete-ai/limex

## Scientific mapping

**Artifact status:** `PHILOSOPHICAL_RATIONALE__NON_NORMATIVE__NO_PROOF_OR_AUTHORITY_EFFECT`

The table below is a traceability map between historical ideas and named LIMEX control contracts. It identifies design influence; it does not make the cited thinkers authors of the technical mechanisms, turn philosophy into executable authority, or establish that the implementation, runtime environment, or open world has been completely proved.

| Intellectual lineage | Historical idea used as design rationale | LIMEX contract or boundary | Technical translation | Evidence status | Does not establish |
|---|---|---|---|---|---|
| Immanuel Kant | Cognition has limits; a representation is not identical to justified knowledge. | `V3-D-LIMEX-BOUNDARY-001`; `V3-F-TYPED-K3-ADMISSION-001` | A model output remains a candidate. A claim is admitted only inside declared predicates with bound inputs, verifiers and effect paths; `UNKNOWN` does not satisfy an admission predicate. | The contracts are normative within their declared control scope; the Kant mapping is explanatory metadata. | Global truth, global safety, or a claim that the trusted computing base is a Kantian *a priori* structure. |
| Karl Popper | Bounded confirmation and falsification are evidentially asymmetric. | `V3-F-AUDIT-TOTALITY-003`; bounded evidence classes for passes and counterexamples | Mandatory negative mutations must validate as `BLOCKED`. A bounded successful run supports only the executed scope, while a reproducible counterexample can defeat the exact bound candidate under its stated assumptions. | Normative negative-test obligation plus bounded empirical evidence. | Universal verification from passing tests, or refutation of every possible successor from one counterexample. |
| Montesquieu | Concentrated authority should be divided among independently constrained roles. | `V3-F-DISJOINT-COMMIT-001` | A material commit requires deterministic verification, independent veto-capable audit, attributable human authorization and external runtime enforcement. | Normative conjunction in the formula register; actual independence requires deployment evidence. | Institutional independence merely because four labels or processes exist. |
| Epictetus | Discipline begins with what is within one’s control. | `V3-F-UNKNOWN-PROBE-ELIGIBILITY-001`; detectable fail-closed boundary | LIMEX governs its own admissible transitions. Unknown evidence blocks forward production; even an evidence probe needs separate authorization, boundedness, reversibility and relevance. | Normative routing for declared and detectable states. | Control over a stochastic model’s internal state, an external community, or unknown states outside the declared detection boundary. |
| Edsger W. Dijkstra | Intellectual confidence cannot substitute for disciplined control of complexity. | `V3-F-PREFLIGHT-FAIL-STOP-001`; `V3-F-FOOTPRINT-NONINFERENCE-001` | A failed binding preflight permits no validator invocation. A small source tree does not imply speed, portability, security or a small runtime trusted base. | Normative non-inference and fail-stop contracts. | Universal correctness, absence of implementation defects, or performance and security properties not independently measured. |
| Nassim Nicholas Taleb / *via negativa* | Robustness can be improved by removing fragile permissions and unsupported paths before adding autonomy. | `V3-F-DIAGNOSIS-ACTION-COHERENCE-001`; `V3-F-REPAIR-CLOSURE-001` | A repair is admissible only if it removes the root cause, preserves or replaces the binding through independent acceptance, and passes revalidation; otherwise the action is bottom. | Normative repair closure; the *via negativa* association is a design heuristic. | A theorem of antifragility, a proof of system safety, or an identity between Taleb’s work, Stoicism and LIMEX. |
| Stephen Cole Kleene | Strong three-valued logic distinguishes `TRUE`, `FALSE` and `UNKNOWN`. | `V3-F-TYPED-K3-ADMISSION-001`; `V3-F-ESFD-K3-001` | Typed predicate polarity prevents overloaded admission semantics. `UNKNOWN` is not coerced to either truth value and cannot authorize forward production; it routes planning back to the declared end state. | Formal logical lineage implemented as a versioned control contract. | Logical completeness, global truth, or proof that all real-world uncertainty has been represented. |
| Cryptographic identity boundary | Identity evidence must remain distinct from truth, authorship and execution evidence. | `V3-F-TREE-HASH-BOUNDARY-001` | Equality of tree hashes establishes byte identity only under the declared hashing schema. A changed successor necessarily receives a different digest. | Normative identity boundary plus published Git object identity. | Signer authenticity, atomic transport, runtime equivalence, correctness, or literal impossibility of deleting or retargeting a mutable remote reference. |

## Interpretation boundary

Philosophical rationale is permitted only as metadata. The proposed non-interference target is:

```text
for all x, r1, r2:
    Project(x, r1) = Project(x, r2)
```

Here, `r1` and `r2` range over well-formed, non-normative rationale records. The expression is the candidate validation target `FMT-RATIONALE-NONINTERFERENCE-001`; it is not asserted here as a proved core invariant. Any rationale record claiming proof, legal, runtime or decision authority must be rejected as `PHILOSOPHICAL_RATIONALE_AUTHORITY_ESCALATION_DENIED`.

## Historical reference points

- Immanuel Kant, *Critique of Pure Reason* (1781; second edition 1787).
- Karl Popper, *Logik der Forschung* (1934), later published in English as *The Logic of Scientific Discovery* (1959).
- Montesquieu, *The Spirit of the Laws* (1748).
- Epictetus, *Enchiridion*, section 1.
- Edsger W. Dijkstra, “The Humble Programmer” (1972).
- Nassim Nicholas Taleb, *Antifragile* (2012), used here only for the modern *via negativa* design heuristic.
- Stephen Cole Kleene, *Introduction to Metamathematics* (1952).

## Verification note

The identifiers in this table refer to the versioned LIMEX formula register. This single-file publication is a scientific citation and traceability map. It does not itself publish the implementation, validator suite, deployment evidence or full formula register, and it carries no independent proof or runtime authority.

`proof_status = MAPPING_ONLY__NO_PROOF_OR_RUNTIME_AUTHORITY`
