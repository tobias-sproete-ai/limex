from __future__ import annotations

import sys
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))

import build_manifest
import validate_cleanroom_release
import verify_frozen_package


DUPLICATE = '{"scope":"UNSAFE","scope":"SAFE"}'


class ReleaseControlTests(unittest.TestCase):
    def test_validator_rejects_duplicate_json_keys(self):
        with self.assertRaises(RuntimeError):
            validate_cleanroom_release.strict_json_loads(DUPLICATE, "fixture")

    def test_builder_rejects_duplicate_json_keys(self):
        with self.assertRaises(SystemExit):
            build_manifest.strict_json_loads(DUPLICATE, "fixture")

    def test_frozen_verifier_rejects_duplicate_json_keys(self):
        with self.assertRaises(SystemExit):
            verify_frozen_package.strict_json_loads(DUPLICATE, "fixture")

    def test_exclusive_freeze_create_never_replaces(self):
        with tempfile.TemporaryDirectory(prefix="limex-science-freeze-") as temporary:
            target = Path(temporary) / "marker"
            build_manifest.exclusive_create(target, b"first")
            with self.assertRaises(SystemExit):
                build_manifest.exclusive_create(target, b"second")
            self.assertEqual(target.read_bytes(), b"first")


if __name__ == "__main__":
    unittest.main()
