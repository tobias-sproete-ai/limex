# RC4 audit lineage

The historical double-blind reports in this directory reviewed the protected input root `5bfe5702b3747fa5198125e503c93c7fe49c3701a7fc550a04efddcb95b2d99e`. They are retained as historical design-review evidence only and are not represented as an exact-byte security approval of RC4.

The independent post-freeze review of RC2 identified one material contradiction: `research/README.md` stated that the research payload was not bound while the release gate, binding record, READMEs and Goldstandards correctly bound `goldbach-v1.8.767`. RC2 remains an immutable negative witness and is not eligible for publication.

RC3 corrected the payload contradiction. Its independent post-freeze review then identified a separate scope overreach: Science documentation technically asserted a no-founder-backdoor property for the separate LIMEX LLM release although the Science package did not contain or audit the LLM bytes. RC3 remains an immutable negative witness and is not eligible for publication.

RC4 limits its technical no-founder-key, no-override and no-reopening assertion to the exact Science RC4 bytes. The Preface records the separate owner declaration concerning LIMEX LLM but expressly marks it as outside the Science audit and subject to the LLM release's own digest-bound evidence. RC4 requires a new post-freeze independent audit over its package root, ZIP digest, commit and proposed tag. That audit is stored outside the self-hashed package to avoid recursive identity. The external release envelope must bind the resulting audit receipt before publication.
