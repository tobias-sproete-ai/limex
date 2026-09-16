# Release instructions

1. Obtain the expected package-root SHA-256 through a trusted channel independent of the package.
2. Verify `PACKAGE_MANIFEST.json` and `SHA256SUMS.txt` with `python3 -B scripts/verify_frozen_package.py --expected-root-sha256 <TRUSTED_PACKAGE_ROOT_SHA256>`.
3. Bind an immutable-snapshot or read-only-source attestation for the exact measured bytes.
4. Bind a signed independent security attestation to the same expected package root.
5. Bind an official filing receipt, application identifier, and priority timestamp outside this package.
6. Obtain an authorized legal release decision for the exact package root.
7. Select and add the intended licence; rebuild and revalidate the package.
8. Run a fresh privacy and security validation over the rebuilt bytes.
9. Bind the exact repository target.
10. Obtain the required physical executive authorization and technical release confirmation.
11. Publish only the newly bound successor package.

Do not edit this frozen candidate in place. Any change creates a new candidate identity and requires the full validation sequence again.
