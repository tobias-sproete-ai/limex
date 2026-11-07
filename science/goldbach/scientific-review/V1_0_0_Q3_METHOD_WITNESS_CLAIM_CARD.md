# Q3 method-witness claim card v1.0.0

## The question this card answers

What exactly can a reviewer test in the `goldbach-v1.8.795` capsule without
having to infer a global Goldbach result?

## Exact public status

```text
V1_8_793_REDUCED_GATE          = KERNEL_PROVED_CONDITIONAL
V1_8_794_FULL_PSI_TRANSFER     = KERNEL_PROVED
V1_8_795_METHOD_WITNESS        = KERNEL_PROVED
Q3_SIGN_SENSITIVE_GATE         = OPEN
GLOBAL_MINOR_ARC_CLOSURE       = OPEN
GLOBAL_GOLDBACH_STATUS         = NO_PROOF
```

The status is supplied by the published [formal status record](../STATUS.md).
The word `KERNEL_PROVED` applies only to the signatures Lean has compiled in
the exact capsule. It does not promote a local formal result into a proof of
the binary Goldbach conjecture.

## Bounded claim under review

The method witness formalizes the following narrow conclusion:

> If the literal absolute envelope proportional to `x / log(x)` is inserted
> into the present `log(M)^21` project normalization, the resulting absolute
> majorant contains a term proportional to `log(M)^20`, which diverges for a
> positive constant. Therefore that absolute-majorant composition cannot close
> this local q=3 gate by itself.

In the published exposition, the relevant expression is:

\[
2C\frac{\log(M)^{21}}{\log(M)}
= 2C\log(M)^{20} \longrightarrow \infty
\qquad (C>0).
\]

## What the formal capsule lets a reviewer establish

1. The exact source tree listed in `SOURCE_CLOSURE.json` is the intended
   custom source closure for the tagged capsule.
2. The public audit entry point imports the q=3 reduction, the exact
   full-psi transfer, and the method-specific obstruction.
3. The published build is intended to produce no `sorryAx` and no
   project-specific axiom in the reported audit signatures.
4. The encoded method witness has the narrow scope stated above.

## What remains outside the claim

- An unconditional sign-sensitive bound for the remaining q=3 residual.
- A source estimate whose decay survives the actual project normalization, if
  an absolute route is retained.
- Uniform treatment of the remaining non-diagonal and minor-arc channels.
- Any proof or falsification of the binary Goldbach conjecture.

## First adversarial checks

A useful first review can focus on one of these questions:

1. **Statement fidelity:** Does the Lean theorem signature encode the exact
   scope described above, rather than a stronger informal statement?
2. **Normalization fidelity:** Is the `log(M)^21` normalization represented as
   described in the formal source?
3. **Assumption boundary:** Are the analytic inputs explicitly represented as
   assumptions or external references rather than silently promoted to a
   project axiom?
4. **Scope discipline:** Does any public wording imply that the obstruction is
   a global no-go theorem or a counterexample to Goldbach? It must not.

## Useful artifacts

- [Public capsule README](../README.md)
- [Formal status](../STATUS.md)
- [Audit entry point](../lean/Audit.lean)
- [Source closure](../SOURCE_CLOSURE.json)
- [Published source hashes](../SHA256SUMS)
- [Reproduction and challenge guide](V1_0_0_REPRODUCTION_AND_CHALLENGE_GUIDE.md)

## Review result boundary

A reviewer who confirms this claim card has confirmed the scope of one
formalized method witness. That result remains narrower than a complete
analytic argument and much narrower than a proof of the binary Goldbach
conjecture.
