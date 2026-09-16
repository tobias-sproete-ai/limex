# Research payload boundary

No research payload is duplicated inside this access-control package.

`RESEARCH_PAYLOAD_BINDING.json` binds the research payload externally to the immutable repository tag `goldbach-v1.8.767`, including its tag object, commit, tree, file count, pinned Lean/Mathlib toolchain, build report, source-closure receipt, checksum inventory and declared axiom profile. The binding preserves the global mathematical status without promotion:

```text
RESEARCH_PAYLOAD = BOUND_EXTERNAL_REPOSITORY_TAG__GOLDBACH_V1_8_767
GOLDBACH_PROOF_STATUS = NO_PROOF
PUBLICATION_AUTHORITY = NOT_GRANTED
```

This binding is provenance only. It does not convert a kernel-checked conditional theorem or reduction into a proof of the Goldbach conjecture, and it does not authorize publication, accreditation or compute.
