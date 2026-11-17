"""Exhaustive offline refusal matrix; standard library only."""
import itertools
import sys
import unittest
from dataclasses import replace
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from release_admission import Snapshot, admit, effective_score


def all_good() -> Snapshot:
    sha = "a" * 40  # synthetic: parity demonstration, never real source proof
    return Snapshot(
        source_sha=sha, checked_sha=sha, published_sha=sha, runtime_sha=sha,
        required_ci_green=True, signature_verified=True, evidence_fresh=True,
        runtime_healthy=True, owner_approved=True, maintenance_open=True,
    )


class AdmissionTests(unittest.TestCase):
    def test_all_necessary_gates(self):
        fields = (
            "required_ci_green", "signature_verified", "evidence_fresh",
            "runtime_healthy", "owner_approved", "maintenance_open",
        )
        for values in itertools.product((False, True), repeat=len(fields)):
            s = replace(all_good(), **dict(zip(fields, values)))
            decision = admit(s)
            self.assertEqual(decision.eligible, all(values), (values, decision))
            self.assertEqual(effective_score(s, 1.0), 1.0 if all(values) else 0.0)
            if all(values):
                self.assertEqual(decision.status, "ELIGIBLE_NOT_DEPLOYED")
            else:
                self.assertEqual(decision.status, "HOLD")

    def test_each_sha_mismatch_holds(self):
        for field in ("checked_sha", "published_sha", "runtime_sha"):
            with self.subTest(field=field):
                s = replace(all_good(), **{field: "b" * 40})
                self.assertFalse(admit(s).eligible)
                self.assertEqual(effective_score(s, 1.0), 0.0)

    def test_old_results_do_not_admit_new_main(self):
        s = replace(all_good(), source_sha="b" * 40)
        self.assertIn("CHECKED_HEAD_MISMATCH", admit(s).holds)
        self.assertIn("PUBLISHER_MISMATCH", admit(s).holds)
        self.assertIn("RUNTIME_SOURCE_MISMATCH", admit(s).holds)

    def test_unavailable_is_not_false_success(self):
        for field in ("checked_sha", "published_sha", "runtime_sha"):
            with self.subTest(field=field):
                s = replace(all_good(), **{field: None})
                self.assertFalse(admit(s).eligible)
        for source in ("", "abc", "A" * 40, "g" * 40):
            with self.subTest(source=source):
                self.assertIn("SOURCE_UNVERIFIED", admit(replace(all_good(), source_sha=source)).holds)

    def test_truthy_non_boolean_is_rejected(self):
        for value in (1, "true", None):
            with self.subTest(value=value):
                s = replace(all_good(), signature_verified=value)
                self.assertIn("SIGNED_RECEIPT_MISSING", admit(s).holds)

    def test_signature_and_expiry_cannot_be_compensated(self):
        for flags in (
            {"signature_verified": False},
            {"evidence_fresh": False},
            {"runtime_healthy": False},
            {"owner_approved": False},
            {"maintenance_open": False},
        ):
            s = replace(all_good(), **flags)
            self.assertEqual(effective_score(s, 1.0), 0.0)

    def test_score_input_validation(self):
        for value in (float("nan"), float("inf"), -0.1, 1.1, True, "0.9"):
            with self.subTest(value=value):
                with self.assertRaises(ValueError):
                    effective_score(all_good(), value)

    def test_decision_not_a_deployment_claim(self):
        d = admit(all_good())
        self.assertEqual(d.status, "ELIGIBLE_NOT_DEPLOYED")
        self.assertFalse(d.holds)


if __name__ == "__main__":
    unittest.main()
