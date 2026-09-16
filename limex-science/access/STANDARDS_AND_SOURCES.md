# Standards and source boundary

The following sources inform the interface design; none attests this implementation or grants access:

- NIST SP 800-63-4 and companion volumes: identity proofing, authentication and federation are distinct assurance functions; privacy, redress and continuous evaluation remain separate requirements. <https://pages.nist.gov/800-63-4/sp800-63.html>
- eduGAIN and REFEDS: federation metadata and assurance profiles let a relying party interpret home-organisation assertions. They do not decide scientific eligibility. <https://edugain.org/edugain-strategy-2025-2030/> and <https://refeds.org/assurance>
- ORCID OAuth: binds a login flow to an authenticated ORCID iD. The provenance and source of record assertions still matter; ORCID is not a competence or intent certificate. <https://info.orcid.org/documentation/api-tutorials/api-tutorial-get-and-authenticated-orcid-id/> and <https://info.orcid.org/orcid-trust/>
- W3C WebAuthn / IETF RFC 9449: holder-of-key and sender-constrained mechanisms reduce replay and stolen-bearer-token risk. Proof of key possession is not itself identity proofing or authorization. <https://www.w3.org/TR/webauthn-3/> and <https://www.rfc-editor.org/rfc/rfc9449.html>
- GDPR Article 5: purpose limitation and data minimisation guide the personal-data boundary; deployment requires a separate lawful-basis, retention and data-subject-rights analysis. <https://eur-lex.europa.eu/legal-content/EN/TXT/?uri=CELEX:32016R0679>

Normative deployment profiles and approved trust anchors are intentionally absent from this candidate. Inventing them before a real partner exists would create false assurance.
