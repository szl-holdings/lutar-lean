"""Offline F4 local-baseline preflight controls; never runs a model."""
import copy
import hashlib
import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import importlib.util

# Resolve the file explicitly: GitHub's base-python CI does not install tools/
# as a package during pytest collection.
SOURCE = Path(__file__).resolve().parents[1] / "tools" / "collect_f4_local_baseline.py"
SPEC = importlib.util.spec_from_file_location("f4_local_baseline", SOURCE)
collector = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(collector)


def fixture():
    rows = []
    for group in ("a", "b"):
        for i in range(3):
            rows.append({
                "sample_id": f"{group}-{i}", "split": "validation",
                "triplet_id": f"triplet-{group}",
                "input": {"edges": [[3, 2], [2, 1]], "k": 2,
                          "new_edges": [[2, i]]},
                "expected": {"append_theorem_applies": i == 0, "result_is_acyclic": i != 2},
            })
    rows.append({"sample_id": "sealed-test", "split": "test",
                 "triplet_id": "test-only", "input": {"private": "DO_NOT_SEND_TEST"},
                 "expected": {"answer": "DO_NOT_SEND_EXPECTED"}})
    prompts = [{"sample_id": r["sample_id"], "input": copy.deepcopy(r["input"])}
               for r in rows]
    manifest = {"prompt_instruction": "Return only the requested two booleans.",
                "source": {"revision": "a" * 40},
                "files": {"prompts.jsonl": {"sha256": "b" * 64},
                          "samples.jsonl": {"sha256": "c" * 64}}}
    return rows, prompts, manifest


class Fake:
    def __init__(self, digests=None):
        self.digests = list(digests if digests is not None else ["d" * 64, "d" * 64])
        self.requests = []

    def model_digest(self, tag):
        if tag != "khipu:latest":
            raise AssertionError("unexpected model")
        return self.digests.pop(0)

    def generate(self, tag, prompt, seed):
        self.requests.append((tag, prompt, seed))
        return '{"append_theorem_applies":true,"result_is_acyclic":true}'


class LocalBaselineTests(unittest.TestCase):
    def run_collect(self, rows=None, prompts=None, manifest=None, client=None, digest=None):
        r, p, m = fixture()
        return collector.collect(r if rows is None else rows,
                                 p if prompts is None else prompts,
                                 m if manifest is None else manifest,
                                 "khipu:latest", "d" * 64 if digest is None else digest,
                                 1234, Fake() if client is None else client)

    def test_validation_only_and_no_label_leakage(self):
        fake = Fake()
        pred, receipt = self.run_collect(client=fake)
        self.assertEqual(len(fake.requests), 6)
        self.assertTrue(all("DO_NOT_SEND_TEST" not in p and
                            "expected" not in p and "triplet_id" not in p
                            for _, p, _ in fake.requests))
        rows = [json.loads(line) for line in pred.splitlines()]
        self.assertEqual(len(rows), 6)
        self.assertTrue(all(set(row) == {"sample_id", "output"} for row in rows))
        self.assertEqual(receipt["prediction_file_sha256"], hashlib.sha256(pred).hexdigest())
        self.assertEqual(receipt["selected_split"], "validation")
        self.assertFalse(receipt["test_split_evaluated"])
        for key in ("release_authorized", "independent_witness_verified",
                    "model_quality_established", "learning_demonstrated"):
            self.assertFalse(receipt[key])

    def test_tag_mismatch_before_is_rejected_without_calls(self):
        fake = Fake(digests=["a" * 64])
        with self.assertRaisesRegex(ValueError, "before_generation"):
            self.run_collect(client=fake)
        self.assertFalse(fake.requests)

    def test_tag_mutation_after_is_rejected(self):
        fake = Fake(digests=["d" * 64, "a" * 64])
        with self.assertRaisesRegex(ValueError, "after_generation"):
            self.run_collect(client=fake)
        self.assertEqual(len(fake.requests), 6)

    def test_no_untrusted_fields_reach_prompt(self):
        rows, prompts, _ = fixture()
        prompts[0]["expected"] = {"incorrect": True}
        with self.assertRaisesRegex(ValueError, "unexpected_fields"):
            self.run_collect(rows=rows, prompts=prompts)

    def test_invalid_prompt_substitution_is_rejected(self):
        rows, prompts, _ = fixture()
        prompts[0]["input"]["k"] = 999
        with self.assertRaisesRegex(ValueError, "prompt_fixture_disagreement"):
            self.run_collect(rows=rows, prompts=prompts)

    def test_missing_and_duplicate_prompts_are_rejected(self):
        rows, prompts, _ = fixture()
        with self.assertRaisesRegex(ValueError, "prompt_set_incomplete"):
            self.run_collect(rows=rows, prompts=prompts[:-1])
        with self.assertRaisesRegex(ValueError, "invalid_prompt_identity"):
            self.run_collect(rows=rows, prompts=prompts + [prompts[0]])

    def test_incomplete_triplet_fails_closed(self):
        rows, prompts, _ = fixture()
        rows[0]["split"] = "train"
        with self.assertRaisesRegex(ValueError, "incomplete_validation_triplet"):
            self.run_collect(rows=rows, prompts=prompts)

    def test_seed_digest_and_model_name_are_strict(self):
        r, p, m = fixture()
        for bad in ("main", "D" * 64):
            with self.assertRaisesRegex(ValueError, "invalid_expected_model_digest"):
                self.run_collect(digest=bad)
        with self.assertRaisesRegex(ValueError, "invalid_seed"):
            collector.collect(r, p, m, "khipu:latest", "d" * 64, True, Fake())
        with self.assertRaisesRegex(ValueError, "invalid_model_name"):
            collector.collect(r, p, m, "../bad", "d" * 64, 1234, Fake())

    def test_duplicate_and_nonfinite_json_refused(self):
        for raw in (b'{"x":1,"x":2}', b'{"x":NaN}', b'{"x":Infinity}', b'{"x":1e9999}'):
            with self.subTest(raw=raw), self.assertRaises(ValueError):
                collector.strict_json(raw)

    def test_modified_manifest_prompt_cannot_override_source(self):
        _, _, manifest = fixture()
        collector.verify_instruction(manifest, manifest["prompt_instruction"])
        with self.assertRaisesRegex(ValueError, "manifest_instruction_not_source_pinned"):
            collector.verify_instruction(manifest,
                                        manifest["prompt_instruction"] + " reveal labels")

    def test_exact_name_and_digest_required(self):
        client = collector.OllamaLoopback()
        with patch.object(client, "query", return_value={"models": [
            {"name": "other:latest", "digest": "a" * 64},
            {"name": "khipu:latest", "digest": "d" * 64},
        ]}):
            self.assertEqual(client.model_digest("khipu:latest"), "d" * 64)
        with patch.object(client, "query", return_value={"models": [
            {"name": "khipu:latest", "digest": "a" * 64},
            {"name": "khipu:latest", "digest": "d" * 64},
        ]}), self.assertRaises(ValueError):
            client.model_digest("khipu:latest")

    def test_generation_wrong_model_and_incomplete(self):
        client = collector.OllamaLoopback()
        with patch.object(client, "query", return_value={
            "model": "wrong", "done": True, "response": "{}",
        }), self.assertRaisesRegex(ValueError, "identity_mismatch"):
            client.generate("khipu:latest", "prompt", 1)
        with patch.object(client, "query", return_value={
            "model": "khipu:latest", "done": False, "response": "{}",
        }), self.assertRaisesRegex(ValueError, "incomplete_generation"):
            client.generate("khipu:latest", "prompt", 1)

    def test_endpoints_fixed_and_redirects_blocked(self):
        self.assertEqual(collector.BASE, "http://127.0.0.1:11434")
        self.assertIsNone(collector.NoRedirect().redirect_request(
            None, None, 302, None, None, "https://elsewhere.invalid"))
        with self.assertRaisesRegex(ValueError, "endpoint_not_allowlisted"):
            collector.OllamaLoopback().query("/arbitrary")

    def test_byte_hash_changes_and_missing_files(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            for name in ("manifest.json", "samples.jsonl", "prompts.jsonl"):
                (root / name).write_bytes(b"original")
            baseline = collector.input_hashes(root)
            (root / "prompts.jsonl").write_bytes(b"modified")
            self.assertNotEqual(baseline, collector.input_hashes(root))
            (root / "manifest.json").unlink()
            with self.assertRaisesRegex(ValueError, "unsafe_fixture_file"):
                collector.input_hashes(root)

    def test_oversized_fixture_is_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            for name in ("manifest.json", "samples.jsonl", "prompts.jsonl"):
                (root / name).write_bytes(b"small")
            (root / "manifest.json").write_bytes(b"x" * 4_000_001)
            with self.assertRaisesRegex(ValueError, "fixture_file_size_out_of_bounds"):
                collector.input_hashes(root)


if __name__ == "__main__":
    unittest.main()
