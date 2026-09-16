from __future__ import annotations

import copy
import sys
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "src"))

import science_admission_core as core


NOW = 2_000_000_000
H = "a" * 64
K = "b" * 64
P = "c" * 64


def evidence(kind: str, number: int, assurance: str) -> dict:
    return {
        "schema": "limex-science-external-evidence-receipt-v1",
        "kind": kind,
        "issuer_id": f"ISSUER:{number:02d}",
        "receipt_id": f"RECEIPT:{number:02d}",
        "application_id": "APPLICATION:ALPHA",
        "subject_id": "SUBJECT:ALPHA",
        "project_id": "PROJECT:GOLDBACH",
        "credential_key_sha256": K,
        "issued_at": NOW - 60,
        "expires_at": NOW + 7200,
        "assurance_profile": assurance,
        "verification_status": "SIGNATURE_AND_TRUST_CHAIN_VERIFICATION_REQUIRED",
        "payload_sha256": H,
        "signature_sha256": P,
    }


def packet(route: str = "INSTITUTIONAL") -> dict:
    receipts = [
        evidence("FEDERATED_IDENTITY", 1, "FEDERATED_IDENTITY_HIGH"),
        evidence("RESEARCH_AFFILIATION", 2, "RESEARCH_AFFILIATION_CURRENT"),
        evidence("HOLDER_OF_KEY", 3, "HOLDER_OF_KEY_FRESH_CHALLENGE"),
    ]
    if route == "INDEPENDENT_RESEARCHER":
        receipts = [
            evidence("INDEPENDENT_IDENTITY_PROOFING", 1, "IDENTITY_PROOFING_HIGH"),
            evidence("REPRODUCIBLE_RESEARCH_ARTIFACT", 2, "REPRODUCIBLE_SCOPE_REVIEWED"),
            evidence("HOLDER_OF_KEY", 3, "HOLDER_OF_KEY_FRESH_CHALLENGE"),
        ]
    value = {
        "schema": "limex-science-admission-packet-v1",
        "application_id": "APPLICATION:ALPHA",
        "route": route,
        "subject_id": "SUBJECT:ALPHA",
        "subject_kind": "NATURAL_PERSON",
        "project_id": "PROJECT:GOLDBACH",
        "purpose_code": "FORMAL_SCIENCE_RESEARCH",
        "requested_scopes": ["BOUNDED_MODEL_INFERENCE", "FORMAL_ARTIFACT_BUILD"],
        "requested_budget_units": 1000,
        "requested_not_before": NOW - 10,
        "requested_expires_at": NOW + 3600,
        "credential_key_sha256": K,
        "policy_sha256": H,
        "evidence_receipts": receipts,
        "scientific_reviews": [],
        "revocation_snapshot": {
            "schema": "limex-science-revocation-snapshot-v1",
            "issuer_id": "REVOCATION:AUTHORITY",
            "application_id": "APPLICATION:ALPHA",
            "subject_id": "SUBJECT:ALPHA",
            "project_id": "PROJECT:GOLDBACH",
            "credential_key_sha256": K,
            "epoch": 17,
            "checked_at": NOW - 5,
            "expires_at": NOW + 60,
            "subject_status": "ACTIVE",
            "credential_status": "ACTIVE",
            "project_status": "ACTIVE",
            "snapshot_sha256": H,
            "signature_sha256": P,
            "verification_status": "SIGNATURE_AND_TRUST_CHAIN_VERIFICATION_REQUIRED",
        },
        "terms_acceptance": {
            "schema": "limex-science-terms-acceptance-v1",
            "issuer_id": "TERMS:AUTHORITY",
            "receipt_id": "TERMS:RECEIPT:01",
            "application_id": "APPLICATION:ALPHA",
            "subject_id": "SUBJECT:ALPHA",
            "project_id": "PROJECT:GOLDBACH",
            "terms_version": "TERMS.V1",
            "purpose_code": "FORMAL_SCIENCE_RESEARCH",
            "policy_sha256": H,
            "credential_key_sha256": K,
            "accepted_at": NOW - 100,
            "acceptance_sha256": H,
            "signature_sha256": P,
            "verification_status": "SIGNATURE_AND_TRUST_CHAIN_VERIFICATION_REQUIRED",
        },
    }
    scope = core._scope_digest(value)
    value["scientific_reviews"] = [
        {
            "schema": "limex-science-scientific-review-v1",
            "reviewer_id": f"REVIEWER:{number}",
            "reviewer_organization_id": f"ORGANIZATION:{number}",
            "application_id": "APPLICATION:ALPHA",
            "subject_id": "SUBJECT:ALPHA",
            "project_id": "PROJECT:GOLDBACH",
            "decision": "APPROVE_DECLARED_RESEARCH_SCOPE",
            "conflict_status": "NO_KNOWN_CONFLICT_DECLARED",
            "scope_sha256": scope,
            "issued_at": NOW - 20,
            "expires_at": NOW + 7200,
            "signature_sha256": P,
            "verification_status": "SIGNATURE_AND_TRUST_CHAIN_VERIFICATION_REQUIRED",
        }
        for number in (1, 2)
    ]
    return value


class AdmissionTests(unittest.TestCase):
    def decision(self, value: dict) -> dict:
        try:
            raw = core.canonical_bytes(value)
        except core.AdmissionError:
            raw = b"{" + (b" " * (core.MAX_PACKET_BYTES + 1))
        return core.evaluate_canonical_application(raw, now=NOW)

    def assert_denied(self, value: dict, reason: str) -> None:
        result = self.decision(value)
        self.assertEqual(result["decision"], "DENY_FAIL_CLOSED")
        self.assertEqual(result["reason"], reason)
        self.assertEqual(result["external_effect"], "DENY")
        self.assertIsNone(result["access_grant"])

    def test_institutional_route_only_reaches_external_hold(self):
        result = self.decision(packet())
        self.assertEqual(result["decision"], "HOLD_EXTERNAL_VERIFICATION_REQUIRED")
        self.assertEqual(result["external_effect"], "DENY")
        self.assertIsNone(result["access_grant"])

    def test_independent_route_is_not_excluded(self):
        result = self.decision(packet("INDEPENDENT_RESEARCHER"))
        self.assertEqual(result["decision"], "HOLD_EXTERNAL_VERIFICATION_REQUIRED")

    def test_extra_field_is_rejected(self):
        value = packet()
        value["eligible"] = True
        self.assert_denied(value, "PACKET_CLOSED_SCHEMA")

    def test_group_subject_is_rejected(self):
        value = packet()
        value["subject_kind"] = "GROUP_ACCOUNT"
        self.assert_denied(value, "SUBJECT_KIND_INVALID")

    def test_unhashable_route_shape_is_denied_not_crashed(self):
        value = packet()
        value["route"] = []
        self.assert_denied(value, "ROUTE_INVALID")

    def test_unhashable_scope_shape_is_denied_not_crashed(self):
        value = packet()
        value["requested_scopes"] = [{}]
        self.assert_denied(value, "SCOPES_INVALID")

    def test_orcid_alone_cannot_replace_route_evidence(self):
        value = packet()
        value["evidence_receipts"] = [
            evidence("ORCID_PROVENANCE", 1, "AUTHENTICATED_ORCID_ONLY"),
            evidence("HOLDER_OF_KEY", 2, "HOLDER_OF_KEY_FRESH_CHALLENGE"),
            evidence("RESEARCH_AFFILIATION", 3, "RESEARCH_AFFILIATION_CURRENT"),
        ]
        self.assert_denied(value, "ROUTE_EVIDENCE_MISSING")

    def test_missing_holder_of_key_is_rejected(self):
        value = packet()
        value["evidence_receipts"][2] = evidence("ORCID_PROVENANCE", 3, "AUTHENTICATED_ORCID_ONLY")
        self.assert_denied(value, "HOLDER_OF_KEY_EVIDENCE_MISSING")

    def test_wrong_assurance_is_rejected(self):
        value = packet()
        value["evidence_receipts"][0]["assurance_profile"] = "LOW"
        self.assert_denied(value, "EVIDENCE_0_ASSURANCE")

    def test_self_asserted_verified_flag_is_rejected(self):
        value = packet()
        value["evidence_receipts"][0]["verification_status"] = "VERIFIED"
        self.assert_denied(value, "EVIDENCE_0_UNSAFE_VERIFICATION_STATUS")

    def test_duplicate_receipt_replay_is_rejected(self):
        value = packet()
        value["evidence_receipts"][1]["receipt_id"] = value["evidence_receipts"][0]["receipt_id"]
        self.assert_denied(value, "EVIDENCE_REPLAY_OR_DUPLICATE")

    def test_duplicate_evidence_kind_is_rejected(self):
        value = packet()
        value["evidence_receipts"][1] = evidence("FEDERATED_IDENTITY", 2, "FEDERATED_IDENTITY_HIGH")
        self.assert_denied(value, "EVIDENCE_KIND_AMBIGUITY")

    def test_stale_evidence_is_rejected(self):
        value = packet()
        value["evidence_receipts"][0]["expires_at"] = NOW
        self.assert_denied(value, "EVIDENCE_0_STALE_OR_INVALID_WINDOW")

    def test_subject_mismatch_is_rejected(self):
        value = packet()
        value["evidence_receipts"][0]["subject_id"] = "SUBJECT:OTHER"
        self.assert_denied(value, "EVIDENCE_0_SUBJECT_OR_PROJECT_MISMATCH")

    def test_key_mismatch_is_rejected(self):
        value = packet()
        value["evidence_receipts"][0]["credential_key_sha256"] = H
        self.assert_denied(value, "EVIDENCE_0_KEY_MISMATCH")

    def test_only_one_review_is_rejected(self):
        value = packet()
        value["scientific_reviews"] = value["scientific_reviews"][:1]
        self.assert_denied(value, "EXACTLY_TWO_SCIENTIFIC_REVIEWS_REQUIRED")

    def test_same_reviewer_twice_is_rejected(self):
        value = packet()
        value["scientific_reviews"][1]["reviewer_id"] = value["scientific_reviews"][0]["reviewer_id"]
        self.assert_denied(value, "REVIEWERS_NOT_DISTINCT")

    def test_review_conflict_is_rejected(self):
        value = packet()
        value["scientific_reviews"][0]["conflict_status"] = "UNKNOWN"
        self.assert_denied(value, "REVIEW_0_CONFLICT")

    def test_review_signature_verification_cannot_be_self_asserted(self):
        value = packet()
        value["scientific_reviews"][0]["verification_status"] = "VERIFIED"
        self.assert_denied(value, "REVIEW_0_UNSAFE_VERIFICATION_STATUS")

    def test_scope_change_after_review_is_rejected(self):
        value = packet()
        value["requested_budget_units"] += 1
        self.assert_denied(value, "REVIEW_0_SCOPE_MISMATCH")

    def test_disallowed_scope_is_rejected(self):
        value = packet()
        value["requested_scopes"] = ["GENERAL_NETWORK_ACCESS"]
        self.assert_denied(value, "SCOPE_NOT_ALLOWED")

    def test_excessive_budget_is_rejected(self):
        value = packet()
        value["requested_budget_units"] = core.MAX_BUDGET_UNITS + 1
        self.assert_denied(value, "BUDGET_INVALID")

    def test_long_lived_grant_is_rejected(self):
        value = packet()
        value["requested_expires_at"] = value["requested_not_before"] + core.MAX_GRANT_SECONDS + 1
        self.assert_denied(value, "GRANT_WINDOW_TOO_LONG")

    def test_stale_revocation_snapshot_is_rejected(self):
        value = packet()
        value["revocation_snapshot"]["expires_at"] = NOW
        self.assert_denied(value, "REVOCATION_SNAPSHOT_STALE")

    def test_revocation_key_mismatch_is_rejected(self):
        value = packet()
        value["revocation_snapshot"]["credential_key_sha256"] = H
        self.assert_denied(value, "REVOCATION_KEY_MISMATCH")

    def test_revoked_subject_is_rejected(self):
        value = packet()
        value["revocation_snapshot"]["subject_status"] = "REVOKED"
        self.assert_denied(value, "REVOKED_OR_SUSPENDED")

    def test_revocation_signature_verification_cannot_be_self_asserted(self):
        value = packet()
        value["revocation_snapshot"]["verification_status"] = "VERIFIED"
        self.assert_denied(value, "REVOCATION_UNSAFE_VERIFICATION_STATUS")

    def test_wrong_purpose_is_rejected(self):
        value = packet()
        value["purpose_code"] = "GENERAL_PURPOSE_COMPUTE"
        self.assert_denied(value, "PURPOSE_NOT_ALLOWED")

    def test_packet_size_is_bounded(self):
        result = core.evaluate_canonical_application(b"{" + b" " * (core.MAX_PACKET_BYTES + 1), now=NOW)
        self.assertEqual(result["decision"], "DENY_FAIL_CLOSED")

    def test_duplicate_json_key_is_rejected(self):
        result = core.evaluate_canonical_application(b'{"schema":"A","schema":"B"}', now=NOW)
        self.assertEqual(result["decision"], "DENY_FAIL_CLOSED")
        self.assertEqual(result["reason"], "DUPLICATE_JSON_KEY")

    def test_noncanonical_json_bytes_are_rejected(self):
        result = core.evaluate_canonical_application(b'{"b": 1, "a": 2}', now=NOW)
        self.assertEqual(result["decision"], "DENY_FAIL_CLOSED")
        self.assertEqual(result["reason"], "PACKET_BYTES_NOT_CANONICAL")

    def test_holder_key_evidence_too_old_is_rejected(self):
        value = packet()
        value["evidence_receipts"][2]["issued_at"] = NOW - core.EVIDENCE_MAX_AGE_SECONDS["HOLDER_OF_KEY"] - 1
        self.assert_denied(value, "EVIDENCE_2_TOO_OLD")

    def test_evidence_must_cover_requested_grant(self):
        value = packet()
        value["evidence_receipts"][0]["expires_at"] = NOW + 100
        self.assert_denied(value, "EVIDENCE_0_EXPIRES_BEFORE_REQUESTED_GRANT")

    def test_review_must_cover_requested_grant(self):
        value = packet()
        value["scientific_reviews"][0]["expires_at"] = NOW + 100
        self.assert_denied(value, "REVIEW_0_EXPIRES_BEFORE_REQUESTED_GRANT")

    def test_revocation_snapshot_max_age_is_enforced(self):
        value = packet()
        value["revocation_snapshot"]["checked_at"] = NOW - core.MAX_REVOCATION_AGE_SECONDS - 1
        value["revocation_snapshot"]["expires_at"] = NOW + 1
        self.assert_denied(value, "REVOCATION_SNAPSHOT_TOO_OLD")

    def test_revocation_snapshot_ttl_is_bounded(self):
        value = packet()
        value["revocation_snapshot"]["expires_at"] = value["revocation_snapshot"]["checked_at"] + core.MAX_REVOCATION_TTL_SECONDS + 1
        self.assert_denied(value, "REVOCATION_SNAPSHOT_TTL_TOO_LONG")

    def test_terms_signature_verification_cannot_be_self_asserted(self):
        value = packet()
        value["terms_acceptance"]["verification_status"] = "VERIFIED"
        self.assert_denied(value, "TERMS_UNSAFE_VERIFICATION_STATUS")

    def test_terms_key_is_bound(self):
        value = packet()
        value["terms_acceptance"]["credential_key_sha256"] = H
        self.assert_denied(value, "TERMS_KEY_MISMATCH")

    def test_deep_nesting_is_denied_without_exception(self):
        depth = core.MAX_PACKET_DEPTH + 2
        raw = (b"[" * depth) + b"0" + (b"]" * depth)
        result = core.evaluate_canonical_application(raw, now=NOW)
        self.assertEqual(result["decision"], "DENY_FAIL_CLOSED")
        self.assertEqual(result["reason"], "PACKET_NESTING_OR_NODE_LIMIT")


class LifecycleTests(unittest.TestCase):
    def test_external_verification_does_not_activate(self):
        state, action = core.project_restriction_state("PENDING_EXTERNAL_VERIFICATION", "EXTERNAL_VERIFICATION_PASSED")
        self.assertEqual((state, action), ("PENDING_CAPABILITY_ISSUANCE", "NO_OP"))

    def test_capability_event_cannot_activate(self):
        self.assertEqual(core.project_restriction_state("PENDING_CAPABILITY_ISSUANCE", "CAPABILITY_ISSUED_BY_EXTERNAL_SERVICE"), ("INVALID_TRANSITION_HALT", "BLOCK_ACCESS"))

    def test_revocation_blocks(self):
        self.assertEqual(core.project_restriction_state("ACTIVE", "REVOKE"), ("REVOKED", "BLOCK_ACCESS"))

    def test_invalid_transition_halts(self):
        self.assertEqual(core.project_restriction_state("SUSPENDED", "AUTO_RETRY"), ("INVALID_TRANSITION_HALT", "BLOCK_ACCESS"))

    def test_revoked_is_terminal_and_idempotent(self):
        self.assertEqual(core.project_restriction_state("REVOKED", "CAPABILITY_ISSUED_BY_EXTERNAL_SERVICE"), ("REVOKED", "NO_OP"))

    def test_non_string_transition_input_blocks(self):
        self.assertEqual(core.project_restriction_state([], "REVOKE"), ("INVALID_TRANSITION_HALT", "BLOCK_ACCESS"))


if __name__ == "__main__":
    unittest.main()
