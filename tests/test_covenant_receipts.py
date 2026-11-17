"""Regression tests: missing execution or source drift cannot yield PASS."""
from __future__ import annotations

from copy import deepcopy
import hashlib
import importlib.util
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("verify_covenant", ROOT / "scripts/verify_covenant.py")
VERIFY = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(VERIFY)


def source_state():
    return {
        "commit": "a" * 40, "tree": "b" * 40, "tracked_status": "",
        "inputs": {"proof.lean": {
            "sha256": "c" * 64, "head_blob": "d" * 40,
            "working_blob": "d" * 40, "matches_head": True,
        }},
    }


class CovenantReceiptTests(unittest.TestCase):
    def test_complete_unchanged_success(self):
        state = source_state()
        self.assertEqual(VERIFY.assess(state, deepcopy(state), [{"exit_code": 0}], 1)[0], "PASS")

    def test_absent_exit_code_is_unknown(self):
        state = source_state()
        self.assertEqual(VERIFY.assess(state, state, [{"exit_code": None}], 1)[0], "UNKNOWN")

    def test_nonzero_native_exit_fails(self):
        state = source_state()
        self.assertEqual(VERIFY.assess(state, state, [{"exit_code": 7}], 1)[0], "FAIL")

    def test_incomplete_sequence_is_unknown(self):
        state = source_state()
        self.assertEqual(VERIFY.assess(state, state, [], 1)[0], "UNKNOWN")

    def test_missing_final_snapshot_is_unknown(self):
        self.assertEqual(VERIFY.assess(source_state(), None, [{"exit_code": 0}], 1)[0], "UNKNOWN")

    def test_commit_change_fails_even_with_zero_exit(self):
        before = source_state()
        after = deepcopy(before)
        after["commit"] = "e" * 40
        self.assertEqual(VERIFY.assess(before, after, [{"exit_code": 0}], 1)[0], "FAIL")

    def test_input_bytes_change_fails_even_with_zero_exit(self):
        before = source_state()
        after = deepcopy(before)
        after["inputs"]["proof.lean"]["sha256"] = "f" * 64
        self.assertEqual(VERIFY.assess(before, after, [{"exit_code": 0}], 1)[0], "FAIL")

    def test_dirty_tracked_source_fails(self):
        state = source_state()
        state["tracked_status"] = " M proof.lean"
        self.assertEqual(VERIFY.assess(state, state, [{"exit_code": 0}], 1)[0], "FAIL")

    def test_required_input_must_match_committed_blob(self):
        state = source_state()
        state["inputs"]["proof.lean"]["matches_head"] = False
        self.assertEqual(VERIFY.assess(state, state, [{"exit_code": 0}], 1)[0], "FAIL")

    def test_runner_preserves_native_failure_and_log_hash(self):
        with tempfile.TemporaryDirectory() as directory:
            log = Path(directory) / "probe.log"
            result = VERIFY.run_command(
                [sys.executable, "-c", "import sys; print('native-probe'); sys.exit(7)"],
                Path(directory), log,
            )
            self.assertEqual(result["exit_code"], 7)
            self.assertEqual(result["log_sha256"], hashlib.sha256(log.read_bytes()).hexdigest())
            self.assertIn("native-probe", log.read_text())

    def test_timeout_does_not_become_zero(self):
        with tempfile.TemporaryDirectory() as directory:
            log = Path(directory) / "timeout.log"
            with patch.object(VERIFY.subprocess, "run", side_effect=subprocess.TimeoutExpired(["probe"], 900)):
                result = VERIFY.run_command(["probe"], Path(directory), log)
            self.assertIsNone(result["exit_code"])
            self.assertIn("TimeoutExpired", result["error"])


if __name__ == "__main__":
    unittest.main()
