"""Adversarial local tests for the LIMEX Settle release seal.

The fixtures use a disposable Git repository and synthetic evidence only.  No
network, wallet, payment rail, filing authority, or external side effect is
invoked.
"""
from __future__ import annotations

import hashlib
import importlib.util
import os
import shutil
import stat
import subprocess
import sys
import tempfile
import unittest
from unittest import mock
from pathlib import Path

import release_seal
from release_seal import (
    CONTRACT_SCHEMA,
    ENVELOPE_SCHEMA,
    RUN_SCHEMA,
    _run,
    file_sha256,
    payload_sha256,
    read_absolute_descriptor_bound,
    relative_posix_file,
    run,
    tree_identity,
    validate_head_worktree_bytes,
)
from settle_core import Invalid, canonical, decode, sha


HERE = Path(__file__).resolve().parent
GIT = Path(shutil.which("git") or "/usr/bin/git").resolve()


def load_script_module(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise AssertionError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


BUILD_MANIFEST = load_script_module("limex_settle_build_manifest", HERE.parent / "scripts" / "build_manifest.py")
VALIDATE_RELEASE = load_script_module(
    "limex_settle_validate_cleanroom_release",
    HERE.parent / "scripts" / "validate_cleanroom_release.py",
)
VERIFY_FROZEN = load_script_module(
    "limex_settle_verify_frozen_package",
    HERE.parent / "scripts" / "verify_frozen_package.py",
)


def git(repo: Path, *args: str) -> str:
    env = dict(os.environ)
    env.update({"LC_ALL": "C", "GIT_CONFIG_NOSYSTEM": "1"})
    result = subprocess.run(
        [str(GIT), "-C", str(repo), *args],
        capture_output=True,
        text=True,
        check=False,
        env=env,
        timeout=10,
    )
    if result.returncode != 0:
        raise AssertionError(result.stderr)
    return result.stdout.rstrip("\n")


class Fixture:
    def __init__(self):
        self.temp = tempfile.TemporaryDirectory(prefix="limex-settle-release-seal-")
        self.root = Path(self.temp.name).resolve()
        self.artifact_root = self.root / "artifacts"
        self.state_root = self.root / "state"
        self.limex_root = self.root / "limex"
        self.git_root = self.root / "repo"
        for path in (self.artifact_root, self.state_root, self.limex_root, self.git_root):
            path.mkdir()
        self.state_root.chmod(0o700)

        (self.limex_root / "SKILL.md").write_text("release: LIMEX R5.5.17\n", encoding="utf-8")
        (self.limex_root / "policy.txt").write_text("fail_closed=true\n", encoding="utf-8")
        self.runtime = tree_identity(self.limex_root)

        git(self.git_root, "init", "-q")
        git(self.git_root, "config", "user.name", "LIMEX Test")
        git(self.git_root, "config", "user.email", "limex-test.invalid@example.invalid")
        (self.git_root / "README.md").write_text("fixture\n", encoding="utf-8")
        git(self.git_root, "add", "README.md")
        git(self.git_root, "commit", "-q", "-m", "fixture")

        documents = {
            "cto.json": {
                "authorization_status": "LOCAL_SYNTHETIC_AUTHORITY_REFERENCE_ONLY",
                "evidence_ceiling": "LOCAL_SYNTHETIC_AUTHORITY_REFERENCE",
                "schema": "CTO_AUTHORIZATION_REFERENCE_V1",
            },
            "lean.json": {
                "axiom_profile": "STANDARD_ONLY",
                "exit_code": 0,
                "proof_status": "NO_PROOF",
                "schema": "LEAN_EVIDENCE_V1",
            },
            "pct.json": {
                "filing_status": "DRAFT_REVIEW_REQUIRED__NOT_FILING_READY",
                "schema": "PCT_REFERENCE_V1",
            },
            "tokens.json": {
                "causal_savings_status": "UNSUPPORTED",
                "schema": "TOKEN_METRICS_V1",
            },
        }
        for name, document in documents.items():
            (self.artifact_root / name).write_bytes(canonical(document))

        role_specs = (
            (
                "CTO_RELEASE_SEAL_AUTHORIZATION",
                "CTO_LOCAL_FIXTURE",
                "cto.json",
                "LOCAL_SYNTHETIC_AUTHORITY_REFERENCE",
                [{"pointer": "/authorization_status", "expected_scalar": "LOCAL_SYNTHETIC_AUTHORITY_REFERENCE_ONLY"}],
            ),
            (
                "LEAN_KERNEL_ATTESTATION",
                "LEAN_LOCAL_FIXTURE",
                "lean.json",
                "LOCAL_SYNTHETIC_KERNEL_METADATA",
                [{"pointer": "/exit_code", "expected_scalar": "0"}, {"pointer": "/proof_status", "expected_scalar": "NO_PROOF"}],
            ),
            (
                "PCT_REFERENCE",
                "PCT_LOCAL_FIXTURE",
                "pct.json",
                "LOCAL_SYNTHETIC_FILING_STATUS",
                [{"pointer": "/filing_status", "expected_scalar": "DRAFT_REVIEW_REQUIRED__NOT_FILING_READY"}],
            ),
            (
                "TOKEN_METRICS",
                "TOKEN_LOCAL_FIXTURE",
                "tokens.json",
                "LOCAL_SYNTHETIC_METRIC_STATUS",
                [{"pointer": "/causal_savings_status", "expected_scalar": "UNSUPPORTED"}],
            ),
        )
        artifacts = []
        for role, artifact_id, relative, evidence_class, assertions in role_specs:
            body = (self.artifact_root / relative).read_bytes()
            artifacts.append({
                "role": role,
                "artifact_id": artifact_id,
                "path": relative,
                "bytes": len(body),
                "sha256": sha(body),
                "evidence_class": evidence_class,
                "json_assertions": assertions,
            })

        self.contract = {
            "schema": CONTRACT_SCHEMA,
            "priority_id": "LIMEX-SETTLE-REFERENCE-0001",
            "settle_at_utc": "2026-09-15T10:00:00.000Z",
            "settle_at_local": "2026-09-15T12:00:00.000+02:00",
            "settle_timezone": "Europe/Berlin",
            "host_clock_evidence_class": "HOST_CLOCK_OBSERVATION_ONLY",
            "execution_scope": "LOCAL_SYNTHETIC_TEST",
            "runtime_binding": {
                "release": "LIMEX R5.5.17",
                **self.runtime,
                "python_version": sys.version.split()[0],
                "python_executable_sha256": file_sha256(Path(sys.executable).resolve()),
                "git_executable_sha256": file_sha256(GIT),
            },
            "git_binding": {
                "head_commit_sha1": git(self.git_root, "rev-parse", "HEAD"),
                "head_tree_sha1": git(self.git_root, "rev-parse", "HEAD^{tree}"),
                **validate_head_worktree_bytes(GIT, self.git_root),
                "clean_worktree": "REQUIRED",
            },
            "llm_interface_binding": {
                "mode": "DECOUPLED_VERSIONED_ATTESTATION_INTERFACE_REQUIRED",
                "schema_version": "LIMEX_LLM_EXECUTION_ATTESTATION_V1",
                "producer_runtime_sha256": self.runtime["tree_sha256"],
                "financial_feedback_to_llm": "DENY",
            },
            "artifacts": artifacts,
        }
        self.contract_path = self.root / "contract.json"
        self.config_path = self.root / "run.json"
        self.write()

    def write(self):
        self.contract_path.write_bytes(canonical(self.contract))
        self.config = {
            "schema": RUN_SCHEMA,
            "artifact_root": str(self.artifact_root),
            "contract_path": str(self.contract_path),
            "git_executable": str(GIT),
            "git_repo_root": str(self.git_root),
            "limex_root": str(self.limex_root),
            "state_root": str(self.state_root),
        }
        self.config_path.write_bytes(canonical(self.config))

    def upgrade_to_asserted_scope(self):
        self.contract["execution_scope"] = "AUTHORIZATION_ASSERTED_RELEASE_SEAL"
        replacements = {
            "CTO_RELEASE_SEAL_AUTHORIZATION": (
                "cto.json",
                "authorization_status",
                "EXPLICIT_CTO_RELEASE_SEAL_AUTHORIZATION",
                "CTO_ASSERTION_REFERENCE__AUTHENTICITY_NOT_VERIFIED",
            ),
            "PCT_REFERENCE": (
                "pct.json",
                "filing_status",
                "FILED_CONFIRMED_BY_AUTHORIZED_SOURCE",
                "AUTHORIZED_SOURCE_ASSERTION_REFERENCE__AUTHENTICITY_NOT_VERIFIED",
            ),
        }
        for role, (name, key, value, evidence_class) in replacements.items():
            path = self.artifact_root / name
            document = decode(path.read_bytes())
            document[key] = value
            body = canonical(document)
            path.write_bytes(body)
            artifact = self.artifact(role)
            artifact["bytes"] = len(body)
            artifact["sha256"] = sha(body)
            artifact["evidence_class"] = evidence_class
            artifact["json_assertions"] = [{"pointer": f"/{key}", "expected_scalar": value}]
        self.fx_role_class("LEAN_KERNEL_ATTESTATION", "LOCAL_KERNEL_REPORT_REFERENCE")
        self.fx_role_class("TOKEN_METRICS", "LOCAL_METRICS_REPORT_REFERENCE")

    def fx_role_class(self, role, evidence_class):
        self.artifact(role)["evidence_class"] = evidence_class

    def close(self):
        self.temp.cleanup()

    def artifact(self, role):
        return next(item for item in self.contract["artifacts"] if item["role"] == role)

    def settled(self, **kwargs):
        return _run(str(self.config_path), observed_at_utc="2026-09-15T10:00:00.000Z", **kwargs)


class ReleaseSealTests(unittest.TestCase):
    def setUp(self):
        self.fx = Fixture()

    def tearDown(self):
        self.fx.close()

    def test_success_and_idempotent_replay_do_not_mutate(self):
        first = self.fx.settled()
        self.assertEqual((first["STATE"], first["EXIT_CODE"], first["INPUT_COUNT"]), ("SETTLED", 0, 4))
        self.assertEqual((first["OPERATION_DOMAIN"], first["EXECUTION_SCOPE"]), ("RELEASE_SEAL", "LOCAL_SYNTHETIC_TEST"))
        files_before = {p.name: (sha(p.read_bytes()), p.stat().st_mtime_ns) for p in self.fx.state_root.iterdir()}
        second = self.fx.settled()
        files_after = {p.name: (sha(p.read_bytes()), p.stat().st_mtime_ns) for p in self.fx.state_root.iterdir()}
        self.assertEqual(second["STATE"], "ALREADY_SETTLED")
        self.assertEqual(second["PAYLOAD_SHA256"], first["PAYLOAD_SHA256"])
        self.assertEqual(files_after, files_before)

    def test_existing_envelope_remeasures_live_runtime_before_success(self):
        first = self.fx.settled()
        self.assertEqual(first["STATE"], "SETTLED")
        (self.fx.limex_root / "policy.txt").write_text("fail_closed=false\n", encoding="utf-8")
        replay = self.fx.settled()
        self.assertEqual(replay["STATE"], "CORRUPTED_HALT")
        self.assertEqual(replay["REASON"], "LIMEX_RUNTIME_IDENTITY_MISMATCH")

    def test_envelope_contains_no_external_effect_authority(self):
        result = self.fx.settled()
        final = self.fx.state_root / f"{result['PRIORITY_ID']}.release-sealed.json"
        envelope = decode(final.read_bytes())
        self.assertEqual(envelope["schema"], ENVELOPE_SCHEMA)
        self.assertEqual(envelope["payload"]["external_effect"], "DENY")
        self.assertEqual(envelope["payload"]["llm_interface_binding"]["financial_feedback_to_llm"], "DENY")

    def test_not_due_creates_no_state(self):
        result = _run(str(self.fx.config_path), observed_at_utc="2026-09-15T09:59:59.999Z")
        self.assertEqual((result["STATE"], result["EXIT_CODE"]), ("NOT_DUE", 2))
        self.assertEqual(list(self.fx.state_root.iterdir()), [])

    def test_existing_reservation_cannot_bypass_due_time(self):
        result = self.fx.settled(fault="AFTER_LOCK")
        self.assertEqual(result["STATE"], "CORRUPTED_HALT")
        replay = _run(str(self.fx.config_path), observed_at_utc="2026-09-15T09:59:59.999Z")
        self.assertEqual(
            (replay["STATE"], replay["REASON"]),
            ("CORRUPTED_HALT", "EXISTING_STATE_BEFORE_SETTLE_TIME"),
        )

    def test_state_root_must_be_private(self):
        self.fx.state_root.chmod(0o755)
        self.assertEqual(self.fx.settled()["REASON"], "LEDGER_STORAGE_PERMISSIONS_TOO_BROAD")

    @unittest.skipUnless(sys.platform == "darwin", "Darwin ACL adapter test")
    def test_state_root_rejects_extended_allow_acl_through_descriptor(self):
        subprocess.run(
            ["/bin/chmod", "+a", "everyone allow read", str(self.fx.state_root)],
            check=True,
            capture_output=True,
        )
        try:
            self.assertEqual(
                self.fx.settled()["REASON"],
                "LEDGER_STORAGE_ALLOW_ACL_REJECTED",
            )
        finally:
            subprocess.run(
                ["/bin/chmod", "-N", str(self.fx.state_root)],
                check=True,
                capture_output=True,
            )

    def test_state_operations_remain_bound_to_opened_directory_after_path_replacement(self):
        original_open = release_seal.open_private_state_root
        displaced = self.fx.root / "state-opened-object"

        def open_then_replace(path):
            descriptor, identity = original_open(path)
            path.rename(displaced)
            path.mkdir(mode=0o700)
            return descriptor, identity

        with mock.patch("release_seal.open_private_state_root", side_effect=open_then_replace):
            result = self.fx.settled()
        self.assertEqual(
            (result["STATE"], result["REASON"]),
            ("CORRUPTED_HALT", "STATE_ROOT_NAMESPACE_DISPLACED"),
        )
        self.assertEqual(list(self.fx.state_root.iterdir()), [])
        self.assertEqual(list(displaced.iterdir()), [])

    def test_existing_state_file_permissions_are_rechecked(self):
        first = self.fx.settled()
        self.assertEqual(first["STATE"], "SETTLED")
        final = self.fx.state_root / f"{first['PRIORITY_ID']}.release-sealed.json"
        final.chmod(0o644)
        self.assertEqual(self.fx.settled()["REASON"], "LEDGER_STORAGE_PERMISSIONS_TOO_BROAD")

    def test_git_tracked_content_sha256_is_bound(self):
        self.fx.contract["git_binding"]["tracked_content_sha256"] = "0" * 64
        self.fx.write()
        self.assertEqual(self.fx.settled()["REASON"], "GIT_TREE_STATE_MISMATCH")

    def test_git_tracked_file_count_budget_is_enforced(self):
        with mock.patch("release_seal.MAX_GIT_TRACKED_FILES", 0):
            with self.assertRaisesRegex(Invalid, "GIT_TRACKED_FILE_COUNT_BOUND_EXCEEDED"):
                validate_head_worktree_bytes(GIT, self.fx.git_root)

    def test_git_tracked_byte_budget_is_enforced(self):
        with mock.patch("release_seal.MAX_GIT_TRACKED_BYTES", 0):
            with self.assertRaisesRegex(Invalid, "GIT_TRACKED_BYTE_BOUND_EXCEEDED"):
                validate_head_worktree_bytes(GIT, self.fx.git_root)

    def test_git_tracked_hash_deadline_is_enforced(self):
        head_listing = subprocess.run(
            [str(GIT), "-C", str(self.fx.git_root), "ls-tree", "-r", "-z", "HEAD"],
            check=True,
            capture_output=True,
        ).stdout
        index_listing = subprocess.run(
            [str(GIT), "-C", str(self.fx.git_root), "ls-files", "--stage", "-z"],
            check=True,
            capture_output=True,
        ).stdout
        with mock.patch("release_seal.MAX_GIT_TRACKED_HASH_SECONDS", 0.0):
            with mock.patch(
                "release_seal.run_git_bytes",
                side_effect=[head_listing, index_listing],
            ):
                with mock.patch(
                    "release_seal.inventory_worktree_files",
                    return_value={"README.md"},
                ):
                    with mock.patch("release_seal.time.monotonic", side_effect=[0.0, 1.0]):
                        with self.assertRaisesRegex(Invalid, "GIT_TRACKED_HASH_DEADLINE_EXCEEDED"):
                            validate_head_worktree_bytes(GIT, self.fx.git_root)

    def test_git_untracked_worktree_file_is_rejected_without_git_status(self):
        (self.fx.git_root / "untracked.txt").write_text("untracked\n", encoding="utf-8")
        self.assertEqual(
            self.fx.settled()["REASON"],
            "GIT_WORKTREE_INVENTORY_MISMATCH",
        )

    def test_git_index_must_equal_head_even_when_worktree_bytes_match_head(self):
        readme = self.fx.git_root / "README.md"
        original = readme.read_bytes()
        readme.write_bytes(b"staged-only\n")
        git(self.fx.git_root, "add", "README.md")
        readme.write_bytes(original)
        self.assertEqual(self.fx.settled()["REASON"], "GIT_INDEX_HEAD_MISMATCH")

    def test_repo_clean_filter_helper_is_not_executed(self):
        marker = self.fx.root / "clean-filter-ran"
        helper = self.fx.root / "clean-filter.sh"
        helper.write_text(
            f"#!/bin/sh\n: > '{marker}'\n/bin/cat\n",
            encoding="utf-8",
        )
        helper.chmod(0o700)
        git(self.fx.git_root, "config", "filter.evil.clean", str(helper))
        info_attributes = self.fx.git_root / ".git" / "info" / "attributes"
        info_attributes.write_text("README.md filter=evil\n", encoding="utf-8")
        readme = self.fx.git_root / "README.md"
        readme.write_bytes(readme.read_bytes())
        result = self.fx.settled()
        self.assertEqual(result["STATE"], "SETTLED")
        self.assertFalse(marker.exists())

    def test_repo_process_filter_helper_is_not_executed(self):
        marker = self.fx.root / "process-filter-ran"
        helper = self.fx.root / "process-filter.sh"
        helper.write_text(
            f"#!/bin/sh\n: > '{marker}'\nexit 1\n",
            encoding="utf-8",
        )
        helper.chmod(0o700)
        git(self.fx.git_root, "config", "filter.evil.process", str(helper))
        info_attributes = self.fx.git_root / ".git" / "info" / "attributes"
        info_attributes.write_text("README.md filter=evil\n", encoding="utf-8")
        readme = self.fx.git_root / "README.md"
        readme.write_bytes(readme.read_bytes())
        result = self.fx.settled()
        self.assertEqual(result["STATE"], "SETTLED")
        self.assertFalse(marker.exists())

    def test_artifact_tamper_is_hard_halt(self):
        (self.fx.artifact_root / "lean.json").write_bytes(b"tampered")
        result = self.fx.settled()
        self.assertEqual((result["STATE"], result["REASON"]), ("CORRUPTED_HALT", "ARTIFACT_IDENTITY_MISMATCH"))

    def test_json_assertion_mismatch_is_hard_halt(self):
        path = self.fx.artifact_root / "lean.json"
        document = decode(path.read_bytes())
        document["exit_code"] = 1
        body = canonical(document)
        path.write_bytes(body)
        artifact = self.fx.artifact("LEAN_KERNEL_ATTESTATION")
        artifact["bytes"] = len(body)
        artifact["sha256"] = sha(body)
        self.fx.write()
        result = self.fx.settled()
        self.assertEqual(result["REASON"], "ARTIFACT_ASSERTION_MISMATCH")

    def test_artifact_leaf_symlink_is_rejected(self):
        target = self.fx.artifact_root / "actual.json"
        target.write_bytes((self.fx.artifact_root / "lean.json").read_bytes())
        (self.fx.artifact_root / "lean.json").unlink()
        (self.fx.artifact_root / "lean.json").symlink_to(target)
        self.assertIn(self.fx.settled()["REASON"], {"SYMLINK_OR_NON_DIRECTORY_REJECTED", "ARTIFACT_IDENTITY_MISMATCH"})

    def test_limex_tree_tamper_is_rejected(self):
        (self.fx.limex_root / "policy.txt").write_text("fail_closed=false\n", encoding="utf-8")
        self.assertEqual(self.fx.settled()["REASON"], "LIMEX_RUNTIME_IDENTITY_MISMATCH")

    def test_git_dirty_tree_is_rejected(self):
        (self.fx.git_root / "README.md").write_text("dirty\n", encoding="utf-8")
        self.assertEqual(self.fx.settled()["REASON"], "GIT_TRACKED_WORKTREE_BYTE_MISMATCH")

    def test_git_tracked_executable_bit_drift_is_rejected(self):
        readme = self.fx.git_root / "README.md"
        readme.chmod(readme.stat().st_mode | stat.S_IXUSR)
        self.assertEqual(
            self.fx.settled()["REASON"],
            "GIT_TRACKED_WORKTREE_MODE_MISMATCH",
        )

    def test_git_assume_unchanged_cannot_hide_tracked_byte_drift(self):
        git(self.fx.git_root, "update-index", "--assume-unchanged", "README.md")
        (self.fx.git_root / "README.md").write_text("concealed\n", encoding="utf-8")
        self.assertEqual(self.fx.settled()["REASON"], "GIT_INDEX_CONCEALMENT_FLAG_REJECTED")

    def test_git_skip_worktree_cannot_hide_tracked_byte_drift(self):
        git(self.fx.git_root, "update-index", "--skip-worktree", "README.md")
        (self.fx.git_root / "README.md").write_text("concealed\n", encoding="utf-8")
        self.assertEqual(self.fx.settled()["REASON"], "GIT_INDEX_CONCEALMENT_FLAG_REJECTED")

    def test_runtime_binary_mismatch_is_rejected(self):
        self.fx.contract["runtime_binding"]["python_executable_sha256"] = "0" * 64
        self.fx.write()
        self.assertEqual(self.fx.settled()["REASON"], "PYTHON_EXECUTABLE_MISMATCH")

    def test_unpinned_git_executable_is_rejected(self):
        self.fx.config["git_executable"] = "/bin/echo"
        self.fx.config_path.write_bytes(canonical(self.fx.config))
        self.assertEqual(self.fx.settled()["REASON"], "PINNED_SYSTEM_GIT_REQUIRED")

    def test_llm_feedback_or_tight_coupling_is_rejected(self):
        self.fx.contract["llm_interface_binding"]["financial_feedback_to_llm"] = "ALLOW"
        self.fx.write()
        self.assertEqual(self.fx.settled()["REASON"], "LLM_INTERFACE_BINDING_INVALID")

    def test_llm_runtime_identity_is_bound_but_independent(self):
        self.fx.contract["llm_interface_binding"]["producer_runtime_sha256"] = "1" * 64
        self.fx.write()
        result = self.fx.settled()
        self.assertEqual(result["STATE"], "SETTLED")
        final = self.fx.state_root / f"{result['PRIORITY_ID']}.release-sealed.json"
        envelope = decode(final.read_bytes())
        self.assertEqual(
            envelope["payload"]["llm_interface_binding"]["producer_runtime_sha256"],
            "1" * 64,
        )
        self.assertNotEqual(
            envelope["payload"]["llm_interface_binding"]["producer_runtime_sha256"],
            envelope["payload"]["runtime"]["tree_sha256"],
        )

    def test_local_synthetic_scope_cannot_claim_real_cto_authorization(self):
        cto = self.fx.artifact("CTO_RELEASE_SEAL_AUTHORIZATION")
        cto["json_assertions"] = [
            {"pointer": "/authorization_status", "expected_scalar": "EXPLICIT_CTO_RELEASE_SEAL_AUTHORIZATION"}
        ]
        self.fx.write()
        self.assertEqual(self.fx.settled()["REASON"], "REQUIRED_ROLE_ASSERTION_MISSING")

    def test_asserted_scope_requires_authorized_filing_status(self):
        self.fx.contract["execution_scope"] = "AUTHORIZATION_ASSERTED_RELEASE_SEAL"
        self.fx.write()
        self.assertEqual(self.fx.settled()["REASON"], "REQUIRED_ROLE_ASSERTION_MISSING")

    def test_asserted_scope_rejects_synthetic_evidence_classes(self):
        self.fx.upgrade_to_asserted_scope()
        self.fx.artifact("CTO_RELEASE_SEAL_AUTHORIZATION")["evidence_class"] = "LOCAL_SYNTHETIC_AUTHORITY_REFERENCE"
        self.fx.write()
        self.assertEqual(
            self.fx.settled()["REASON"],
            "ROLE_EVIDENCE_CLASS_MISMATCH",
        )

    def test_asserted_scope_positive_path_is_explicitly_unauthenticated(self):
        self.fx.upgrade_to_asserted_scope()
        self.fx.write()
        result = self.fx.settled()
        self.assertEqual((result["STATE"], result["EXECUTION_SCOPE"]), (
            "SETTLED",
            "AUTHORIZATION_ASSERTED_RELEASE_SEAL",
        ))

    def test_local_utc_or_zone_mismatch_is_rejected(self):
        self.fx.contract["settle_at_local"] = "2026-09-15T12:00:00.000+01:00"
        self.fx.write()
        self.assertEqual(self.fx.settled()["REASON"], "SETTLE_LOCAL_OFFSET_ZONE_MISMATCH")

    def test_artifact_order_is_canonical_and_fail_closed(self):
        self.fx.contract["artifacts"].reverse()
        self.fx.write()
        self.assertEqual(self.fx.settled()["REASON"], "ARTIFACT_BINDINGS_CANONICAL_ORDER_REQUIRED")

    def test_assertion_order_is_canonical_and_fail_closed(self):
        self.fx.artifact("LEAN_KERNEL_ATTESTATION")["json_assertions"].reverse()
        self.fx.write()
        self.assertEqual(self.fx.settled()["REASON"], "ASSERTIONS_CANONICAL_ORDER_REQUIRED")

    def test_path_traversal_is_rejected_before_artifact_read(self):
        self.fx.contract["artifacts"][0]["path"] = "../lean.json"
        self.fx.write()
        self.assertEqual(self.fx.settled()["REASON"], "PATH_TRAVERSAL_REJECTED")

    def test_lexical_artifact_path_aliases_are_rejected(self):
        for alias in ("./lean.json", "nested//lean.json", "nested/lean.json/"):
            with self.subTest(alias=alias), self.assertRaisesRegex(
                Exception, "CANONICAL_RELATIVE_POSIX_PATH_REQUIRED"
            ):
                relative_posix_file(alias)

    def test_artifact_role_lexical_alias_is_rejected(self):
        shared_body = canonical({
            "authorization_status": "LOCAL_SYNTHETIC_AUTHORITY_REFERENCE_ONLY",
            "exit_code": 0,
        })
        (self.fx.artifact_root / "shared.json").write_bytes(shared_body)
        for role, path in (
            ("CTO_RELEASE_SEAL_AUTHORIZATION", "shared.json"),
            ("LEAN_KERNEL_ATTESTATION", "./shared.json"),
        ):
            artifact = self.fx.artifact(role)
            artifact.update(path=path, bytes=len(shared_body), sha256=sha(shared_body))
        self.fx.write()
        self.assertEqual(
            self.fx.settled()["REASON"],
            "CANONICAL_RELATIVE_POSIX_PATH_REQUIRED",
        )

    def test_hardlinked_artifact_roles_are_rejected(self):
        source = self.fx.artifact_root / "cto.json"
        alias = self.fx.artifact_root / "cto-hardlink.json"
        os.link(source, alias)
        artifact = self.fx.artifact("LEAN_KERNEL_ATTESTATION")
        body = source.read_bytes()
        artifact.update(
            path=alias.name,
            bytes=len(body),
            sha256=sha(body),
            json_assertions=[{
                "pointer": "/authorization_status",
                "expected_scalar": "LOCAL_SYNTHETIC_AUTHORITY_REFERENCE_ONLY",
            }, {
                "pointer": "/exit_code",
                "expected_scalar": "0",
            }, {
                "pointer": "/proof_status",
                "expected_scalar": "NO_PROOF",
            }],
        )
        self.fx.write()
        self.assertEqual(
            self.fx.settled()["REASON"],
            "DUPLICATE_PHYSICAL_ARTIFACT_BINDING",
        )

    def test_canonical_relative_artifact_path_remains_accepted(self):
        self.assertEqual(relative_posix_file("nested/lean.json"), ("nested", "lean.json"))

    def test_existing_lock_blocks_second_first_writer(self):
        (self.fx.state_root / ".LIMEX-SETTLE-REFERENCE-0001.lock").write_text("occupied", encoding="utf-8")
        result = self.fx.settled()
        self.assertEqual(result["STATE"], "CORRUPTED_HALT")

    def test_corrupt_preexisting_final_is_never_accepted(self):
        final = self.fx.state_root / "LIMEX-SETTLE-REFERENCE-0001.release-sealed.json"
        final.write_bytes(canonical({"schema": ENVELOPE_SCHEMA, "payload": {}, "payload_sha256": "0" * 64}))
        self.assertEqual(self.fx.settled()["STATE"], "CORRUPTED_HALT")

    def test_recomputed_unkeyed_envelope_tamper_is_rejected_against_contract(self):
        result = self.fx.settled()
        final = self.fx.state_root / f"{result['PRIORITY_ID']}.release-sealed.json"
        final.chmod(0o600)
        envelope = decode(final.read_bytes())
        envelope["payload"]["git"]["head_commit_sha1"] = "0" * 40
        envelope["payload_sha256"] = payload_sha256(envelope["payload"])
        final.write_bytes(canonical(envelope))
        self.assertEqual(self.fx.settled()["STATE"], "CORRUPTED_HALT")

    def test_recomputed_settled_time_tamper_is_rejected_against_reservation(self):
        result = self.fx.settled()
        final = self.fx.state_root / f"{result['PRIORITY_ID']}.release-sealed.json"
        final.chmod(0o600)
        envelope = decode(final.read_bytes())
        envelope["payload"]["settled_at_utc"] = "2026-09-15T10:00:01.000Z"
        envelope["payload_sha256"] = payload_sha256(envelope["payload"])
        final.write_bytes(canonical(envelope))
        self.assertEqual(self.fx.settled()["STATE"], "CORRUPTED_HALT")

    def test_repo_fsmonitor_helper_is_disabled_and_not_executed(self):
        marker = self.fx.root / "fsmonitor-ran"
        helper = self.fx.root / "fsmonitor.sh"
        helper.write_text(f"#!/bin/sh\n: > '{marker}'\nexit 0\n", encoding="utf-8")
        helper.chmod(0o700)
        git(self.fx.git_root, "config", "core.fsmonitor", str(helper))
        result = self.fx.settled()
        self.assertEqual(result["STATE"], "SETTLED")
        self.assertFalse(marker.exists())

    def test_special_artifact_file_is_rejected_without_blocking(self):
        fifo = self.fx.artifact_root / "special.fifo"
        os.mkfifo(fifo)
        artifact = self.fx.artifact("LEAN_KERNEL_ATTESTATION")
        artifact.update(path="special.fifo", bytes=1, sha256="0" * 64)
        self.fx.write()
        result = self.fx.settled()
        self.assertEqual((result["STATE"], result["REASON"]), ("CORRUPTED_HALT", "ARTIFACT_REGULAR_FILE_REQUIRED"))

    def test_config_parent_symlink_is_rejected(self):
        alias = self.fx.root / "alias"
        alias.symlink_to(self.fx.root, target_is_directory=True)
        result = _run(str(alias / "run.json"), observed_at_utc="2026-09-15T10:00:00.000Z")
        self.assertEqual((result["STATE"], result["REASON"]), ("CORRUPTED_HALT", "SYMLINK_OR_NON_DIRECTORY_REJECTED"))

    def test_fault_after_lock_stays_fail_closed(self):
        result = self.fx.settled(fault="AFTER_LOCK")
        self.assertEqual((result["STATE"], result["REASON"]), ("CORRUPTED_HALT", "INJECTED_AFTER_LOCK"))
        self.assertFalse((self.fx.state_root / "LIMEX-SETTLE-REFERENCE-0001.release-sealed.json").exists())
        recovered = self.fx.settled()
        self.assertEqual(recovered["STATE"], "SETTLED")

    def test_every_git_child_denies_lazy_fetch_prompt_credentials_and_transports(self):
        real_popen = release_seal.subprocess.Popen
        observed = []

        def capture_contract(*args, **kwargs):
            command = args[0] if args else kwargs["args"]
            if command and Path(command[0]).resolve() == GIT:
                observed.append((list(command), dict(kwargs.get("env", {}))))
            return real_popen(*args, **kwargs)

        with mock.patch.object(release_seal.subprocess, "Popen", side_effect=capture_contract):
            result = self.fx.settled()

        self.assertEqual(result["STATE"], "SETTLED")
        self.assertGreater(len(observed), 0)
        required_options = {
            "protocol.allow=never",
            "protocol.file.allow=never",
            "protocol.ext.allow=never",
            "protocol.ssh.allow=never",
            "protocol.git.allow=never",
            "protocol.http.allow=never",
            "protocol.https.allow=never",
            "credential.helper=",
        }
        for command, environment in observed:
            self.assertIn("--no-replace-objects", command)
            configured = {command[index + 1] for index, value in enumerate(command[:-1]) if value == "-c"}
            self.assertTrue(required_options.issubset(configured))
            self.assertEqual(environment["GIT_NO_LAZY_FETCH"], "1")
            self.assertEqual(environment["GIT_NO_REPLACE_OBJECTS"], "1")
            self.assertEqual(environment["GIT_TERMINAL_PROMPT"], "0")
            self.assertEqual(environment["GCM_INTERACTIVE"], "Never")

    def test_git_replace_ref_cannot_overlay_bound_head_tree(self):
        original = git(self.fx.git_root, "rev-parse", "HEAD")
        tracked = self.fx.git_root / "README.md"
        tracked.write_text("replacement tree\n", encoding="utf-8")
        git(self.fx.git_root, "add", "README.md")
        git(self.fx.git_root, "commit", "-q", "-m", "replacement")
        replacement = git(self.fx.git_root, "rev-parse", "HEAD")
        git(self.fx.git_root, "reset", "--hard", "-q", original)
        git(self.fx.git_root, "replace", original, replacement)

        self.assertNotEqual(git(self.fx.git_root, "rev-parse", "HEAD^{tree}"), self.fx.contract["git_binding"]["head_tree_sha1"])
        result = self.fx.settled()
        self.assertEqual(result["STATE"], "SETTLED")

    def test_git_head_must_not_point_directly_to_tree_object(self):
        tree = git(self.fx.git_root, "rev-parse", "HEAD^{tree}")
        (self.fx.git_root / ".git" / "HEAD").write_text(tree + "\n", encoding="ascii")
        self.fx.contract["git_binding"]["head_commit_sha1"] = tree
        self.fx.write()

        result = self.fx.settled()
        self.assertEqual((result["STATE"], result["REASON"]), ("CORRUPTED_HALT", "GIT_HEAD_COMMIT_REQUIRED"))

    def test_git_head_must_not_point_to_annotated_tag_object(self):
        commit = git(self.fx.git_root, "rev-parse", "HEAD")
        git(self.fx.git_root, "tag", "-a", "bound-tag", "-m", "bound tag", commit)
        tag = git(self.fx.git_root, "rev-parse", "refs/tags/bound-tag")
        (self.fx.git_root / ".git" / "HEAD").write_text(tag + "\n", encoding="ascii")
        self.fx.contract["git_binding"]["head_commit_sha1"] = tag
        self.fx.write()

        result = self.fx.settled()
        self.assertEqual((result["STATE"], result["REASON"]), ("CORRUPTED_HALT", "GIT_HEAD_COMMIT_REQUIRED"))

    def test_fault_after_stage_stays_fail_closed(self):
        result = self.fx.settled(fault="AFTER_STAGE_FSYNC")
        self.assertEqual((result["STATE"], result["REASON"]), ("CORRUPTED_HALT", "INJECTED_AFTER_STAGE_FSYNC"))
        self.assertFalse((self.fx.state_root / "LIMEX-SETTLE-REFERENCE-0001.release-sealed.json").exists())
        recovered = self.fx.settled()
        self.assertEqual(recovered["STATE"], "SETTLED")

    def test_fault_after_publish_recovers_by_readback_only(self):
        failed = self.fx.settled(fault="AFTER_PUBLISH")
        self.assertEqual((failed["STATE"], failed["REASON"]), ("CORRUPTED_HALT", "INJECTED_AFTER_PUBLISH"))
        replay = self.fx.settled()
        self.assertEqual((replay["STATE"], replay["REASON"], replay["EXIT_CODE"]), ("ALREADY_SETTLED", "VALID_EXISTING_ENVELOPE", 0))

    def test_noncanonical_or_duplicate_key_run_config_is_rejected(self):
        self.fx.config_path.write_bytes(b'{"schema":"LIMEX_SETTLE_RUN_CONFIG_V1","schema":"LIMEX_SETTLE_RUN_CONFIG_V1"}')
        self.assertEqual(self.fx.settled()["STATE"], "CORRUPTED_HALT")

    def test_extra_config_field_is_rejected(self):
        self.fx.config["unexpected"] = "value"
        self.fx.config_path.write_bytes(canonical(self.fx.config))
        self.assertEqual(self.fx.settled()["REASON"], "RUN_CONFIG_CLOSED_SCHEMA_REQUIRED")

    def test_real_parallel_cli_first_writers_publish_at_most_once(self):
        self.fx.contract["settle_at_utc"] = "2020-01-01T00:00:00.000Z"
        self.fx.contract["settle_at_local"] = "2020-01-01T01:00:00.000+01:00"
        self.fx.write()
        source = HERE.parent / "src"
        command = [sys.executable, "-B", str(source / "release_seal.py"), str(self.fx.config_path)]
        env = dict(os.environ)
        env.update({"PYTHONPATH": str(source), "PYTHONDONTWRITEBYTECODE": "1"})
        processes = [subprocess.Popen(command, cwd=self.fx.root, env=env, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True) for _ in range(2)]
        outputs = [process.communicate(timeout=20) for process in processes]
        states = []
        for process, (stdout, stderr) in zip(processes, outputs):
            self.assertEqual(stderr, "")
            values = dict(line.split("=", 1) for line in stdout.splitlines())
            states.append(values["STATE"])
            self.assertIn(process.returncode, {0, 1})
        self.assertEqual(states.count("SETTLED"), 1)
        self.assertTrue(set(states).issubset({"SETTLED", "ALREADY_SETTLED", "CORRUPTED_HALT"}))
        self.assertEqual(run(str(self.fx.config_path))["STATE"], "ALREADY_SETTLED")


class PackageTreeIdentityTests(unittest.TestCase):
    def test_absolute_json_input_is_bounded_before_decode(self):
        with tempfile.TemporaryDirectory(prefix="limex-settle-bounded-input-") as tree_name:
            oversized = Path(tree_name) / "oversized.json"
            with oversized.open("wb") as handle:
                handle.truncate(4_194_305)
            with self.assertRaisesRegex(Exception, "ABSOLUTE_FILE_BYTE_BOUND_EXCEEDED"):
                read_absolute_descriptor_bound(str(oversized.resolve()), "READ_FAILED")

    def test_manifest_builder_rejects_oversized_regular_file(self):
        with tempfile.TemporaryDirectory(prefix="limex-settle-manifest-bound-") as tree_name:
            root = Path(tree_name)
            (root / "large.bin").write_bytes(b"12")
            with mock.patch.object(BUILD_MANIFEST, "MAX_FILE_BYTES", 1):
                with self.assertRaisesRegex(SystemExit, "FAIL_CLOSED_FILE_BYTE_BOUND:large.bin"):
                    BUILD_MANIFEST.collect_entries(root)

    def test_frozen_verifier_rejects_unbound_manifest_metadata(self):
        with tempfile.TemporaryDirectory(prefix="limex-settle-manifest-metadata-") as tree_name:
            root = Path(tree_name)
            manifest = root / "PACKAGE_MANIFEST.json"
            checksums = root / "SHA256SUMS.txt"
            (root / "payload.txt").write_text("bound\n", encoding="utf-8")
            with (
                mock.patch.object(BUILD_MANIFEST, "ROOT", root),
                mock.patch.object(BUILD_MANIFEST, "MANIFEST", manifest),
                mock.patch.object(BUILD_MANIFEST, "CHECKSUMS", checksums),
                mock.patch.object(BUILD_MANIFEST, "EXCLUDED", {manifest.name, checksums.name}),
            ):
                BUILD_MANIFEST.main()
            document = __import__("json").loads(manifest.read_text(encoding="utf-8"))
            document["release"] = "RELABELLED"
            manifest.write_text(__import__("json").dumps(document), encoding="utf-8")
            with (
                mock.patch.object(VERIFY_FROZEN, "ROOT", root),
                mock.patch.object(VERIFY_FROZEN, "MANIFEST", manifest),
                mock.patch.object(VERIFY_FROZEN, "CHECKSUMS", checksums),
                mock.patch.object(VERIFY_FROZEN, "EXCLUDED", {manifest.name, checksums.name}),
            ):
                with self.assertRaisesRegex(SystemExit, "FAIL_CLOSED_MANIFEST_RELEASE"):
                    VERIFY_FROZEN.main("0" * 64)

    def test_frozen_verifier_requires_external_expected_root(self):
        with self.assertRaisesRegex(SystemExit, "FAIL_CLOSED_CALLER_EXPECTED_ROOT_REQUIRED"):
            VERIFY_FROZEN.main()

    def test_security_status_digest_is_verified_against_report_bytes(self):
        with tempfile.TemporaryDirectory(prefix="limex-settle-security-binding-") as tree_name:
            root = Path(tree_name)
            evidence = root / "evidence"
            evidence.mkdir()
            report = evidence / "SECURITY_SCAN_REPORT.json"
            report.write_text('{"schema":"LIMEX_SETTLE_CLEANROOM_SECURITY_REPORT_V1"}\n', encoding="utf-8")
            status = evidence / "SECURITY_SCAN_STATUS.json"
            status.write_text(
                '{"report_path":"evidence/SECURITY_SCAN_REPORT.json","report_sha256":"' + "0" * 64 + '","scope":"FULL_CLEANROOM_CANDIDATE","status":"PASS_WITH_LIMITS"}\n',
                encoding="utf-8",
            )
            with (
                mock.patch.object(VALIDATE_RELEASE, "ROOT", root),
                mock.patch.object(VALIDATE_RELEASE, "EVIDENCE", evidence),
            ):
                with self.assertRaisesRegex(RuntimeError, "SECURITY_REPORT_DIGEST_MISMATCH"):
                    VALIDATE_RELEASE.security_gate([report, status])

    def test_manifest_rejects_directory_symlink_escape(self):
        with tempfile.TemporaryDirectory(prefix="limex-settle-manifest-tree-") as tree_name:
            root = Path(tree_name)
            (root / "bound.txt").write_text("bound\n", encoding="utf-8")
            (root / "UNBOUND_DIRECTORY_SYMLINK").symlink_to(Path("/tmp"), target_is_directory=True)
            with self.assertRaisesRegex(SystemExit, r"FAIL_CLOSED_SYMLINK_ENTRY:UNBOUND_DIRECTORY_SYMLINK"):
                BUILD_MANIFEST.collect_entries(root)

    def test_validator_rejects_directory_symlink_escape(self):
        with tempfile.TemporaryDirectory(prefix="limex-settle-validator-tree-") as tree_name:
            root = Path(tree_name)
            (root / "bound.txt").write_text("bound\n", encoding="utf-8")
            (root / "UNBOUND_DIRECTORY_SYMLINK").symlink_to(Path("/tmp"), target_is_directory=True)
            with self.assertRaisesRegex(RuntimeError, r"SYMLINK_FORBIDDEN:UNBOUND_DIRECTORY_SYMLINK"):
                VALIDATE_RELEASE.inventory(root)

    def test_validator_overwrites_stale_pass_when_tree_is_rejected(self):
        with tempfile.TemporaryDirectory(prefix="limex-settle-validator-cli-") as clone_name:
            clone = Path(clone_name) / "package"
            shutil.copytree(HERE.parent, clone)
            report_path = clone / "evidence" / "CLEANROOM_VALIDATION_REPORT.json"
            report_path.parent.mkdir(exist_ok=True)
            report_path.write_text('{"status":"PASS_LOCAL_RELEASE_CANDIDATE_WITH_LIMITS"}\n', encoding="utf-8")
            (clone / "UNBOUND_DIRECTORY_SYMLINK").symlink_to(Path("/tmp"), target_is_directory=True)
            environment = {
                "PATH": "/usr/bin:/bin",
                "LC_ALL": "C",
                "PYTHONDONTWRITEBYTECODE": "1",
            }
            result = subprocess.run(
                [sys.executable, "-B", str(clone / "scripts" / "validate_cleanroom_release.py")],
                cwd=clone,
                env=environment,
                stdin=subprocess.DEVNULL,
                capture_output=True,
                text=True,
                check=False,
                timeout=20,
            )
            self.assertEqual(result.returncode, 1)
            report = __import__("json").loads(report_path.read_text(encoding="utf-8"))
            self.assertEqual(report["status"], "FAIL_CLOSED")
            self.assertIn("SYMLINK_FORBIDDEN:UNBOUND_DIRECTORY_SYMLINK", report["detail"])

    def test_manifest_invalidates_stale_outputs_before_tree_rejection(self):
        with tempfile.TemporaryDirectory(prefix="limex-settle-manifest-cli-") as tree_name:
            root = Path(tree_name)
            manifest = root / "PACKAGE_MANIFEST.json"
            checksums = root / "SHA256SUMS.txt"
            manifest.write_text('{"status":"PASS"}\n', encoding="utf-8")
            checksums.write_text("stale\n", encoding="utf-8")
            (root / "UNBOUND_DIRECTORY_SYMLINK").symlink_to(Path("/tmp"), target_is_directory=True)
            with (
                mock.patch.object(BUILD_MANIFEST, "ROOT", root),
                mock.patch.object(BUILD_MANIFEST, "MANIFEST", manifest),
                mock.patch.object(BUILD_MANIFEST, "CHECKSUMS", checksums),
                mock.patch.object(BUILD_MANIFEST, "EXCLUDED", {manifest.name, checksums.name}),
            ):
                with self.assertRaisesRegex(SystemExit, r"FAIL_CLOSED_SYMLINK_ENTRY:UNBOUND_DIRECTORY_SYMLINK"):
                    BUILD_MANIFEST.main()
            self.assertIn("INVALIDATED_PENDING_REBUILD__NO_PASS_CLAIM", manifest.read_text(encoding="utf-8"))
            self.assertEqual(checksums.read_bytes(), b"")

    def test_manifest_is_last_commit_marker_on_final_publish_fault(self):
        with tempfile.TemporaryDirectory(prefix="limex-settle-manifest-commit-") as tree_name:
            root = Path(tree_name)
            manifest = root / "PACKAGE_MANIFEST.json"
            checksums = root / "SHA256SUMS.txt"
            payload = root / "payload.txt"
            payload.write_text("bound\n", encoding="utf-8")
            manifest.write_text('{"status":"STALE_PASS"}\n', encoding="utf-8")
            checksums.write_text("stale\n", encoding="utf-8")
            real_atomic_replace = BUILD_MANIFEST.atomic_replace
            call_count = 0

            def fail_before_manifest_commit(path, body):
                nonlocal call_count
                call_count += 1
                if call_count == 4:
                    raise OSError("INJECTED_BEFORE_FINAL_MANIFEST_COMMIT")
                return real_atomic_replace(path, body)

            with (
                mock.patch.object(BUILD_MANIFEST, "ROOT", root),
                mock.patch.object(BUILD_MANIFEST, "MANIFEST", manifest),
                mock.patch.object(BUILD_MANIFEST, "CHECKSUMS", checksums),
                mock.patch.object(BUILD_MANIFEST, "EXCLUDED", {manifest.name, checksums.name}),
                mock.patch.object(BUILD_MANIFEST, "atomic_replace", side_effect=fail_before_manifest_commit),
            ):
                with self.assertRaisesRegex(OSError, "INJECTED_BEFORE_FINAL_MANIFEST_COMMIT"):
                    BUILD_MANIFEST.main()
            self.assertEqual(call_count, 4)
            self.assertIn("INVALIDATED_PENDING_REBUILD__NO_PASS_CLAIM", manifest.read_text(encoding="utf-8"))
            self.assertNotEqual(checksums.read_text(encoding="utf-8"), "")


if __name__ == "__main__":
    result = unittest.TextTestRunner(verbosity=2).run(unittest.defaultTestLoader.loadTestsFromModule(sys.modules[__name__]))
    raise SystemExit(0 if result.wasSuccessful() else 1)
