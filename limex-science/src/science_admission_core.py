"""Pure fail-closed structural admission projection for LIMEX Science.

This module performs no identity proofing, signature verification, capability
issuance, network access, compute dispatch, or account activation.  A positive
result means only that a closed application packet is structurally eligible
for verification by a separately trusted capability issuer.
"""
from __future__ import annotations

import hashlib
import json
import re
from typing import Any


HEX64 = re.compile(r"[0-9a-f]{64}")
IDENTIFIER = re.compile(r"[A-Z0-9][A-Z0-9._:-]{2,127}")
MAX_PACKET_BYTES = 262_144
MAX_PACKET_DEPTH = 32
MAX_CONTAINER_NODES = 10_000
MAX_CLOCK_SKEW_SECONDS = 300
MAX_GRANT_SECONDS = 86_400
MAX_BUDGET_UNITS = 1_000_000
MAX_REVIEW_AGE_SECONDS = 2_592_000
MAX_REVOCATION_AGE_SECONDS = 60
MAX_REVOCATION_TTL_SECONDS = 300
CURRENT_TERMS_VERSION = "TERMS.V1"

PACKET_KEYS = {
    "schema",
    "application_id",
    "route",
    "subject_id",
    "subject_kind",
    "project_id",
    "purpose_code",
    "requested_scopes",
    "requested_budget_units",
    "requested_not_before",
    "requested_expires_at",
    "credential_key_sha256",
    "policy_sha256",
    "evidence_receipts",
    "scientific_reviews",
    "revocation_snapshot",
    "terms_acceptance",
}
EVIDENCE_KEYS = {
    "schema",
    "kind",
    "issuer_id",
    "receipt_id",
    "application_id",
    "subject_id",
    "project_id",
    "credential_key_sha256",
    "issued_at",
    "expires_at",
    "assurance_profile",
    "verification_status",
    "payload_sha256",
    "signature_sha256",
}
REVIEW_KEYS = {
    "schema",
    "reviewer_id",
    "reviewer_organization_id",
    "application_id",
    "subject_id",
    "project_id",
    "decision",
    "conflict_status",
    "scope_sha256",
    "issued_at",
    "expires_at",
    "signature_sha256",
    "verification_status",
}
REVOCATION_KEYS = {
    "schema",
    "issuer_id",
    "application_id",
    "subject_id",
    "project_id",
    "credential_key_sha256",
    "epoch",
    "checked_at",
    "expires_at",
    "subject_status",
    "credential_status",
    "project_status",
    "snapshot_sha256",
    "signature_sha256",
    "verification_status",
}
TERMS_KEYS = {
    "schema",
    "issuer_id",
    "receipt_id",
    "application_id",
    "subject_id",
    "project_id",
    "terms_version",
    "purpose_code",
    "policy_sha256",
    "credential_key_sha256",
    "accepted_at",
    "acceptance_sha256",
    "signature_sha256",
    "verification_status",
}

ALLOWED_SCOPES = {
    "FORMAL_ARTIFACT_BUILD",
    "FORMAL_ARTIFACT_AUDIT",
    "BOUNDED_MODEL_INFERENCE",
}
ALLOWED_PURPOSE = "FORMAL_SCIENCE_RESEARCH"
ROUTES = {"INSTITUTIONAL", "INDEPENDENT_RESEARCHER"}
EVIDENCE_ASSURANCE = {
    "FEDERATED_IDENTITY": "FEDERATED_IDENTITY_HIGH",
    "RESEARCH_AFFILIATION": "RESEARCH_AFFILIATION_CURRENT",
    "HOLDER_OF_KEY": "HOLDER_OF_KEY_FRESH_CHALLENGE",
    "INDEPENDENT_IDENTITY_PROOFING": "IDENTITY_PROOFING_HIGH",
    "REPRODUCIBLE_RESEARCH_ARTIFACT": "REPRODUCIBLE_SCOPE_REVIEWED",
    "ORCID_PROVENANCE": "AUTHENTICATED_ORCID_ONLY",
}
EVIDENCE_MAX_AGE_SECONDS = {
    "FEDERATED_IDENTITY": 900,
    "RESEARCH_AFFILIATION": 86_400,
    "HOLDER_OF_KEY": 300,
    "INDEPENDENT_IDENTITY_PROOFING": 31_536_000,
    "REPRODUCIBLE_RESEARCH_ARTIFACT": 2_592_000,
    "ORCID_PROVENANCE": 86_400,
}

__all__ = [
    "AdmissionError",
    "canonical_bytes",
    "decode_canonical_packet",
    "evaluate_canonical_application",
    "project_restriction_state",
]


class AdmissionError(ValueError):
    """Closed-schema or invariant violation."""


def _closed(value: Any, keys: set[str], label: str) -> dict[str, Any]:
    if type(value) is not dict or set(value) != keys:
        raise AdmissionError(f"{label}_CLOSED_SCHEMA")
    return value


def _identifier(value: Any, label: str) -> str:
    if type(value) is not str or not IDENTIFIER.fullmatch(value):
        raise AdmissionError(f"{label}_INVALID")
    return value


def _digest(value: Any, label: str) -> str:
    if type(value) is not str or not HEX64.fullmatch(value):
        raise AdmissionError(f"{label}_INVALID")
    return value


def _integer(value: Any, label: str, lower: int = 0, upper: int = 2**63 - 1) -> int:
    if type(value) is not int or value < lower or value > upper:
        raise AdmissionError(f"{label}_INVALID")
    return value


def _check_nesting(value: Any) -> None:
    stack: list[tuple[Any, int]] = [(value, 0)]
    seen: set[int] = set()
    nodes = 0
    while stack:
        item, depth = stack.pop()
        nodes += 1
        if nodes > MAX_CONTAINER_NODES or depth > MAX_PACKET_DEPTH:
            raise AdmissionError("PACKET_NESTING_OR_NODE_LIMIT")
        if type(item) is dict:
            identity = id(item)
            if identity in seen:
                raise AdmissionError("PACKET_CONTAINER_ALIAS_OR_CYCLE")
            seen.add(identity)
            stack.extend((child, depth + 1) for child in item.values())
        elif type(item) is list:
            identity = id(item)
            if identity in seen:
                raise AdmissionError("PACKET_CONTAINER_ALIAS_OR_CYCLE")
            seen.add(identity)
            stack.extend((child, depth + 1) for child in item)


def canonical_bytes(value: Any) -> bytes:
    """Return bounded canonical JSON bytes, rejecting non-JSON values."""
    try:
        _check_nesting(value)
        body = json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True, allow_nan=False).encode("ascii")
    except AdmissionError:
        raise
    except (TypeError, ValueError, UnicodeEncodeError, RecursionError) as exc:
        raise AdmissionError("PACKET_NOT_CANONICAL_JSON") from exc
    if len(body) > MAX_PACKET_BYTES:
        raise AdmissionError("PACKET_BYTE_LIMIT")
    return body


def decode_canonical_packet(raw: bytes) -> dict[str, Any]:
    """Decode exact canonical bytes while rejecting duplicate JSON keys."""
    if type(raw) is not bytes or len(raw) > MAX_PACKET_BYTES:
        raise AdmissionError("PACKET_BYTE_LIMIT_OR_TYPE")

    def reject_duplicates(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        result: dict[str, Any] = {}
        for key, value in pairs:
            if key in result:
                raise AdmissionError("DUPLICATE_JSON_KEY")
            result[key] = value
        return result

    try:
        value = json.loads(raw.decode("ascii"), object_pairs_hook=reject_duplicates)
    except AdmissionError:
        raise
    except (UnicodeDecodeError, json.JSONDecodeError, RecursionError) as exc:
        raise AdmissionError("PACKET_JSON_DECODE") from exc
    _check_nesting(value)
    if type(value) is not dict or canonical_bytes(value) != raw:
        raise AdmissionError("PACKET_BYTES_NOT_CANONICAL")
    return value


def _active_window(item: dict[str, Any], now: int, label: str) -> None:
    issued = _integer(item["issued_at"], f"{label}_ISSUED_AT")
    expires = _integer(item["expires_at"], f"{label}_EXPIRES_AT")
    if issued > now + MAX_CLOCK_SKEW_SECONDS or expires <= now or expires <= issued:
        raise AdmissionError(f"{label}_STALE_OR_INVALID_WINDOW")


def _scope_digest(packet: dict[str, Any]) -> str:
    bound = {
        "application_id": packet["application_id"],
        "route": packet["route"],
        "subject_id": packet["subject_id"],
        "subject_kind": packet["subject_kind"],
        "project_id": packet["project_id"],
        "purpose_code": packet["purpose_code"],
        "requested_scopes": packet["requested_scopes"],
        "requested_budget_units": packet["requested_budget_units"],
        "requested_not_before": packet["requested_not_before"],
        "requested_expires_at": packet["requested_expires_at"],
        "credential_key_sha256": packet["credential_key_sha256"],
        "policy_sha256": packet["policy_sha256"],
    }
    return hashlib.sha256(canonical_bytes(bound)).hexdigest()


def _validate_evidence(receipt: Any, packet: dict[str, Any], now: int, index: int) -> dict[str, Any]:
    item = _closed(receipt, EVIDENCE_KEYS, f"EVIDENCE_{index}")
    if item["schema"] != "limex-science-external-evidence-receipt-v1":
        raise AdmissionError(f"EVIDENCE_{index}_SCHEMA")
    for field in ("kind", "issuer_id", "receipt_id", "application_id", "subject_id", "project_id", "assurance_profile"):
        _identifier(item[field], f"EVIDENCE_{index}_{field.upper()}")
    _digest(item["credential_key_sha256"], f"EVIDENCE_{index}_KEY")
    _digest(item["payload_sha256"], f"EVIDENCE_{index}_PAYLOAD")
    _digest(item["signature_sha256"], f"EVIDENCE_{index}_SIGNATURE")
    _active_window(item, now, f"EVIDENCE_{index}")
    if item["kind"] not in EVIDENCE_ASSURANCE:
        raise AdmissionError(f"EVIDENCE_{index}_KIND")
    if item["assurance_profile"] != EVIDENCE_ASSURANCE[item["kind"]]:
        raise AdmissionError(f"EVIDENCE_{index}_ASSURANCE")
    if now - item["issued_at"] > EVIDENCE_MAX_AGE_SECONDS[item["kind"]]:
        raise AdmissionError(f"EVIDENCE_{index}_TOO_OLD")
    if item["expires_at"] < packet["requested_expires_at"]:
        raise AdmissionError(f"EVIDENCE_{index}_EXPIRES_BEFORE_REQUESTED_GRANT")
    if item["verification_status"] != "SIGNATURE_AND_TRUST_CHAIN_VERIFICATION_REQUIRED":
        raise AdmissionError(f"EVIDENCE_{index}_UNSAFE_VERIFICATION_STATUS")
    if item["application_id"] != packet["application_id"]:
        raise AdmissionError(f"EVIDENCE_{index}_APPLICATION_MISMATCH")
    if item["subject_id"] != packet["subject_id"] or item["project_id"] != packet["project_id"]:
        raise AdmissionError(f"EVIDENCE_{index}_SUBJECT_OR_PROJECT_MISMATCH")
    if item["credential_key_sha256"] != packet["credential_key_sha256"]:
        raise AdmissionError(f"EVIDENCE_{index}_KEY_MISMATCH")
    return item


def _validate_review(review: Any, packet: dict[str, Any], now: int, index: int, scope_sha256: str) -> dict[str, Any]:
    item = _closed(review, REVIEW_KEYS, f"REVIEW_{index}")
    if item["schema"] != "limex-science-scientific-review-v1":
        raise AdmissionError(f"REVIEW_{index}_SCHEMA")
    for field in ("reviewer_id", "reviewer_organization_id", "application_id", "subject_id", "project_id"):
        _identifier(item[field], f"REVIEW_{index}_{field.upper()}")
    _digest(item["scope_sha256"], f"REVIEW_{index}_SCOPE")
    _digest(item["signature_sha256"], f"REVIEW_{index}_SIGNATURE")
    if item["verification_status"] != "SIGNATURE_AND_TRUST_CHAIN_VERIFICATION_REQUIRED":
        raise AdmissionError(f"REVIEW_{index}_UNSAFE_VERIFICATION_STATUS")
    _active_window(item, now, f"REVIEW_{index}")
    if now - item["issued_at"] > MAX_REVIEW_AGE_SECONDS:
        raise AdmissionError(f"REVIEW_{index}_TOO_OLD")
    if item["expires_at"] < packet["requested_expires_at"]:
        raise AdmissionError(f"REVIEW_{index}_EXPIRES_BEFORE_REQUESTED_GRANT")
    if item["decision"] != "APPROVE_DECLARED_RESEARCH_SCOPE":
        raise AdmissionError(f"REVIEW_{index}_NOT_APPROVED")
    if item["conflict_status"] != "NO_KNOWN_CONFLICT_DECLARED":
        raise AdmissionError(f"REVIEW_{index}_CONFLICT")
    if item["application_id"] != packet["application_id"]:
        raise AdmissionError(f"REVIEW_{index}_APPLICATION_MISMATCH")
    if item["subject_id"] != packet["subject_id"] or item["project_id"] != packet["project_id"]:
        raise AdmissionError(f"REVIEW_{index}_SUBJECT_OR_PROJECT_MISMATCH")
    if item["scope_sha256"] != scope_sha256:
        raise AdmissionError(f"REVIEW_{index}_SCOPE_MISMATCH")
    if item["reviewer_id"] == packet["subject_id"]:
        raise AdmissionError(f"REVIEW_{index}_SELF_REVIEW")
    return item


def _evaluate_application_object(packet: Any, *, now: int) -> dict[str, Any]:
    """Return a deterministic non-authorizing admission projection.

    The function returns DENY on every malformed or incomplete packet.  The
    strongest result is HOLD_EXTERNAL_VERIFICATION_REQUIRED.  No output of
    this function is an access grant.
    """
    try:
        now = _integer(now, "NOW")
        packet_sha256 = hashlib.sha256(canonical_bytes(packet)).hexdigest()
        p = _closed(packet, PACKET_KEYS, "PACKET")
        if p["schema"] != "limex-science-admission-packet-v1":
            raise AdmissionError("PACKET_SCHEMA")
        for field in ("application_id", "subject_id", "project_id", "purpose_code"):
            _identifier(p[field], field.upper())
        if p["subject_kind"] != "NATURAL_PERSON":
            raise AdmissionError("SUBJECT_KIND_INVALID")
        if type(p["route"]) is not str or p["route"] not in ROUTES:
            raise AdmissionError("ROUTE_INVALID")
        if p["purpose_code"] != ALLOWED_PURPOSE:
            raise AdmissionError("PURPOSE_NOT_ALLOWED")
        if type(p["requested_scopes"]) is not list or not p["requested_scopes"]:
            raise AdmissionError("SCOPES_INVALID")
        if len(p["requested_scopes"]) > len(ALLOWED_SCOPES):
            raise AdmissionError("SCOPES_TOO_MANY")
        if any(type(scope) is not str for scope in p["requested_scopes"]):
            raise AdmissionError("SCOPES_INVALID")
        if p["requested_scopes"] != sorted(set(p["requested_scopes"])):
            raise AdmissionError("SCOPES_NOT_CANONICAL")
        if not set(p["requested_scopes"]).issubset(ALLOWED_SCOPES):
            raise AdmissionError("SCOPE_NOT_ALLOWED")
        _integer(p["requested_budget_units"], "BUDGET", 1, MAX_BUDGET_UNITS)
        not_before = _integer(p["requested_not_before"], "NOT_BEFORE")
        expires = _integer(p["requested_expires_at"], "EXPIRES_AT")
        if not_before > now + MAX_CLOCK_SKEW_SECONDS or expires <= now or expires <= not_before:
            raise AdmissionError("GRANT_WINDOW_INVALID")
        if expires - not_before > MAX_GRANT_SECONDS:
            raise AdmissionError("GRANT_WINDOW_TOO_LONG")
        _digest(p["credential_key_sha256"], "CREDENTIAL_KEY")
        _digest(p["policy_sha256"], "POLICY")

        if type(p["evidence_receipts"]) is not list or not (3 <= len(p["evidence_receipts"]) <= 6):
            raise AdmissionError("EVIDENCE_COUNT")
        evidence = [_validate_evidence(item, p, now, i) for i, item in enumerate(p["evidence_receipts"])]
        receipt_ids = [item["receipt_id"] for item in evidence]
        if len(set(receipt_ids)) != len(receipt_ids):
            raise AdmissionError("EVIDENCE_REPLAY_OR_DUPLICATE")
        evidence_kinds = [item["kind"] for item in evidence]
        if len(set(evidence_kinds)) != len(evidence_kinds):
            raise AdmissionError("EVIDENCE_KIND_AMBIGUITY")
        kinds = set(evidence_kinds)
        if "HOLDER_OF_KEY" not in kinds:
            raise AdmissionError("HOLDER_OF_KEY_EVIDENCE_MISSING")
        if p["route"] == "INSTITUTIONAL":
            required = {"FEDERATED_IDENTITY", "RESEARCH_AFFILIATION", "HOLDER_OF_KEY"}
        else:
            required = {"INDEPENDENT_IDENTITY_PROOFING", "REPRODUCIBLE_RESEARCH_ARTIFACT", "HOLDER_OF_KEY"}
        if not required.issubset(kinds):
            raise AdmissionError("ROUTE_EVIDENCE_MISSING")

        if type(p["scientific_reviews"]) is not list or len(p["scientific_reviews"]) != 2:
            raise AdmissionError("EXACTLY_TWO_SCIENTIFIC_REVIEWS_REQUIRED")
        scope_sha256 = _scope_digest(p)
        reviews = [_validate_review(item, p, now, i, scope_sha256) for i, item in enumerate(p["scientific_reviews"])]
        reviewer_ids = {item["reviewer_id"] for item in reviews}
        if len(reviewer_ids) != 2:
            raise AdmissionError("REVIEWERS_NOT_DISTINCT")

        rev = _closed(p["revocation_snapshot"], REVOCATION_KEYS, "REVOCATION")
        if rev["schema"] != "limex-science-revocation-snapshot-v1":
            raise AdmissionError("REVOCATION_SCHEMA")
        for field in ("issuer_id", "application_id", "subject_id", "project_id"):
            _identifier(rev[field], f"REVOCATION_{field.upper()}")
        _digest(rev["credential_key_sha256"], "REVOCATION_KEY")
        _integer(rev["epoch"], "REVOCATION_EPOCH", 1)
        checked = _integer(rev["checked_at"], "REVOCATION_CHECKED_AT")
        rev_expires = _integer(rev["expires_at"], "REVOCATION_EXPIRES_AT")
        _digest(rev["snapshot_sha256"], "REVOCATION_SNAPSHOT")
        _digest(rev["signature_sha256"], "REVOCATION_SIGNATURE")
        if rev["verification_status"] != "SIGNATURE_AND_TRUST_CHAIN_VERIFICATION_REQUIRED":
            raise AdmissionError("REVOCATION_UNSAFE_VERIFICATION_STATUS")
        if checked > now + MAX_CLOCK_SKEW_SECONDS or rev_expires <= now or rev_expires <= checked:
            raise AdmissionError("REVOCATION_SNAPSHOT_STALE")
        if now - checked > MAX_REVOCATION_AGE_SECONDS:
            raise AdmissionError("REVOCATION_SNAPSHOT_TOO_OLD")
        if rev_expires - checked > MAX_REVOCATION_TTL_SECONDS:
            raise AdmissionError("REVOCATION_SNAPSHOT_TTL_TOO_LONG")
        if any(rev[field] != "ACTIVE" for field in ("subject_status", "credential_status", "project_status")):
            raise AdmissionError("REVOKED_OR_SUSPENDED")
        if rev["application_id"] != p["application_id"] or rev["subject_id"] != p["subject_id"] or rev["project_id"] != p["project_id"]:
            raise AdmissionError("REVOCATION_BINDING_MISMATCH")
        if rev["credential_key_sha256"] != p["credential_key_sha256"]:
            raise AdmissionError("REVOCATION_KEY_MISMATCH")

        terms = _closed(p["terms_acceptance"], TERMS_KEYS, "TERMS")
        if terms["schema"] != "limex-science-terms-acceptance-v1":
            raise AdmissionError("TERMS_SCHEMA")
        for field in ("issuer_id", "receipt_id", "application_id", "subject_id", "project_id", "terms_version", "purpose_code"):
            _identifier(terms[field], f"TERMS_{field.upper()}")
        _integer(terms["accepted_at"], "TERMS_ACCEPTED_AT")
        _digest(terms["acceptance_sha256"], "TERMS_ACCEPTANCE")
        _digest(terms["signature_sha256"], "TERMS_SIGNATURE")
        _digest(terms["policy_sha256"], "TERMS_POLICY")
        _digest(terms["credential_key_sha256"], "TERMS_KEY")
        if terms["application_id"] != p["application_id"] or terms["subject_id"] != p["subject_id"] or terms["project_id"] != p["project_id"]:
            raise AdmissionError("TERMS_SUBJECT_OR_PROJECT_MISMATCH")
        if terms["policy_sha256"] != p["policy_sha256"]:
            raise AdmissionError("TERMS_POLICY_MISMATCH")
        if terms["credential_key_sha256"] != p["credential_key_sha256"]:
            raise AdmissionError("TERMS_KEY_MISMATCH")
        if terms["terms_version"] != CURRENT_TERMS_VERSION:
            raise AdmissionError("TERMS_VERSION_MISMATCH")
        if terms["verification_status"] != "SIGNATURE_AND_TRUST_CHAIN_VERIFICATION_REQUIRED":
            raise AdmissionError("TERMS_UNSAFE_VERIFICATION_STATUS")
        if terms["purpose_code"] != p["purpose_code"] or terms["accepted_at"] > now + MAX_CLOCK_SKEW_SECONDS:
            raise AdmissionError("TERMS_PURPOSE_OR_TIME_MISMATCH")
    except AdmissionError as exc:
        return {
            "schema": "limex-science-admission-decision-v1",
            "decision": "DENY_FAIL_CLOSED",
            "reason": str(exc),
            "packet_sha256": locals().get("packet_sha256"),
            "external_effect": "DENY",
            "access_grant": None,
        }

    return {
        "schema": "limex-science-admission-decision-v1",
        "decision": "HOLD_EXTERNAL_VERIFICATION_REQUIRED",
        "reason": "STRUCTURAL_CONSISTENCY_ONLY__VERIFY_ALL_SIGNATURES_TRUST_CHAINS_AND_REVOCATION_ONLINE",
        "packet_sha256": packet_sha256,
        "scope_sha256": scope_sha256,
        "external_effect": "DENY",
        "access_grant": None,
    }


def evaluate_canonical_application(raw: bytes, *, now: int) -> dict[str, Any]:
    """Only public evaluation entry: exact canonical bytes to DENY or HOLD."""
    try:
        packet = decode_canonical_packet(raw)
    except AdmissionError as exc:
        digest = hashlib.sha256(raw).hexdigest() if type(raw) is bytes and len(raw) <= MAX_PACKET_BYTES else None
        return {
            "schema": "limex-science-admission-decision-v1",
            "decision": "DENY_FAIL_CLOSED",
            "reason": str(exc),
            "packet_sha256": digest,
            "external_effect": "DENY",
            "access_grant": None,
        }
    return _evaluate_application_object(packet, now=now)


def project_restriction_state(current_state: str, event: str) -> tuple[str, str]:
    """Pure restriction projection; it can close access but never open it."""
    if type(current_state) is not str or type(event) is not str:
        return "INVALID_TRANSITION_HALT", "BLOCK_ACCESS"
    transitions = {
        ("PENDING_EXTERNAL_VERIFICATION", "EXTERNAL_VERIFICATION_PASSED"): ("PENDING_CAPABILITY_ISSUANCE", "NO_OP"),
        ("ACTIVE", "EXPIRED"): ("EXPIRED", "BLOCK_ACCESS"),
        ("ACTIVE", "SUSPEND"): ("SUSPENDED", "BLOCK_ACCESS"),
        ("ACTIVE", "REVOKE"): ("REVOKED", "BLOCK_ACCESS"),
        ("SUSPENDED", "REVOKE"): ("REVOKED", "BLOCK_ACCESS"),
    }
    if current_state in {"EXPIRED", "REVOKED"}:
        return current_state, "NO_OP"
    return transitions.get((current_state, event), ("INVALID_TRANSITION_HALT", "BLOCK_ACCESS"))
