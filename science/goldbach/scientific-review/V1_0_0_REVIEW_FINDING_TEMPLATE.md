# Scientific review finding template v1.0.0

Use one template per bounded finding. Do not use a successful build as a proxy
for a global mathematical conclusion.

```markdown
## Review target

- Capsule tag:
- Exact commit:
- Reviewed artifact(s):
- Theorem symbol(s), if applicable:

## Finding type

- [ ] Reproduction mismatch
- [ ] Source/hash mismatch
- [ ] Formal-scope mismatch
- [ ] Assumption-boundary issue
- [ ] Mathematical objection
- [ ] Documentation mismatch
- [ ] Open obligation confirmed

## Exact observation

Describe what you observed. Quote only the necessary source fragment, command
output, theorem signature, derivation, or counterexample.

## Reproduction steps

1.
2.
3.

## Expected versus observed

- Expected:
- Observed:

## Scope of the finding

State precisely whether the finding concerns a local build, a theorem
signature, an external premise, documentation, or a mathematical derivation.
Do not infer a global Goldbach conclusion unless the finding itself establishes
one.

## Suggested resolution or question

What exact clarification, correction, or independent check would resolve the
finding?
```

## Minimum standard for an actionable report

An actionable report identifies the exact tag, commit, artifact, and observed
result. It should let another reader reproduce the issue without private LIMEX
context or access to a model.
