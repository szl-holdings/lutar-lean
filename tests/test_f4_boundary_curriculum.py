#!/usr/bin/env python3
"""CPU contract tests; oracle-derived outputs below are not model evidence."""

from __future__ import annotations

import copy
import itertools
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest import mock

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

from tools import build_f4_boundary_curriculum as build  # noqa: E402
from tools import evaluate_f4_boundary as score  # noqa: E402
from tools.locked_formula_runtime import LockedDomainError  # noqa: E402

FIXTURE = REPO_ROOT / "tests/fixtures/f4_boundary_v1"


class HypothesisBoundaryTests(unittest.TestCase):
    def test_matched_triplet_does_not_teach_the_incorrect_converse(self):
        base = [[3, 2], [2, 1]]
        cases = [(0, (True, True)), (4, (False, True)), (3, (False, False))]
        for target, expected in cases:
            with self.subTest(target=target):
                result = build.label_input({"edges": base, "k": 2, "new_edges": [[2, target]]})
                self.assertEqual(tuple(result[key] for key in build.LABEL_KEYS), expected)

    def test_k_can_be_old_and_nonmaximal(self):
        result = build.label_input({
            "edges": [[5, 2], [3, 0]], "k": 3, "new_edges": [[3, 1]],
        })
        self.assertEqual(result, dict(zip(build.LABEL_KEYS, (True, True))))

    def test_both_exact_hypotheses_are_required(self):
        for value in [
            {"edges": [[0, 1]], "k": 3, "new_edges": [[3, 1]]},
            {"edges": [[2, 1]], "k": 3, "new_edges": [[2, 0]]},
        ]:
            self.assertEqual(
                build.label_input(value), dict(zip(build.LABEL_KEYS, (False, True)))
            )

    def test_empty_append_is_vacuously_valid_and_self_loop_is_cyclic(self):
        self.assertEqual(
            build.label_input({"edges": [], "k": 0, "new_edges": []}),
            dict(zip(build.LABEL_KEYS, (True, True))),
        )
        self.assertEqual(
            build.label_input({"edges": [], "k": 0, "new_edges": [[0, 0]]}),
            dict(zip(build.LABEL_KEYS, (False, False))),
        )

    def test_invalid_domains_raise_instead_of_producing_labels(self):
        class IntSubclass(int):
            pass

        for bad in [True, False, -1, 1.0, "1", None, IntSubclass(2)]:
            with self.subTest(value=bad):
                with self.assertRaises(LockedDomainError):
                    build.label_input({"edges": [], "k": bad, "new_edges": []})
                with self.assertRaises(LockedDomainError):
                    build.label_input({"edges": [[2, bad]], "k": 3, "new_edges": []})
                with self.assertRaises(LockedDomainError):
                    build.topological_acyclic([[2, bad]])
        for edges in [None, "21", 1, [[1]], [[2, 1, 0]], [{"src": 2, "dst": 1}]]:
            with self.subTest(edges=edges):
                with self.assertRaises(LockedDomainError):
                    build.label_input({"edges": edges, "k": 2, "new_edges": []})
        with self.assertRaises(LockedDomainError):
            build.label_input({"edges": [], "k": 0, "new_edges": [], "extra": 1})

    def test_independent_kahn_matches_runtime_on_all_three_node_graphs(self):
        possible = list(itertools.product(range(3), repeat=2))
        for mask in range(1 << len(possible)):
            edges = [edge for i, edge in enumerate(possible) if mask & (1 << i)]
            self.assertEqual(
                build.topological_acyclic(edges),
                not build.khipu_has_cycle_without_invariant(edges),
            )
        self.assertTrue(build.topological_acyclic([[2, 1], [2, 1]]))
        self.assertFalse(build.topological_acyclic([[2, 1], [2, 1], [1, 2]]))

    def test_oracle_or_hypothesis_disagreement_stops_generation(self):
        value = {"edges": [[2, 1]], "k": 2, "new_edges": [[2, 0]]}
        for function, answer in [
            ("khipu_has_cycle_without_invariant", True),
            ("khipu_backward_invariant", False),
            ("khipu_append_hypothesis", False),
            ("khipu_append_preserves_acyclic", False),
        ]:
            with self.subTest(function=function):
                with mock.patch.object(build, function, return_value=answer):
                    with self.assertRaises(build.OracleMismatch):
                        build.label_input(value)


class FixtureContractTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.bundle = build.build_bundle(seed=20261116, families=12, relabelings=2)
        cls.rows = score.read_jsonl(cls.bundle["samples.jsonl"])

    def test_frozen_fixture_is_exactly_reproducible(self):
        again = build.build_bundle(seed=20261116, families=12, relabelings=2)
        self.assertEqual(self.bundle, again)
        for name, data in self.bundle.items():
            self.assertEqual((FIXTURE / name).read_bytes(), data, name)
        self.assertEqual(score.load_fixture(FIXTURE), self.rows)

    def test_seed_changes_data_without_changing_family_split_policy(self):
        other = build.build_samples(seed=20261117, families=12, relabelings=2)
        self.assertNotEqual(other, self.rows)
        for row in self.rows + other:
            self.assertEqual(row["split"], build.split_for_family(row["family_id"]))

    def test_rank_preserving_relabeling_and_edge_permutation_preserve_family(self):
        base = [[5, 2], [2, 1], [4, 0]]
        renamed = [[80, 10], [50, 30], [90, 50]]
        # Sorted nodes 0,1,2,4,5 map to 10,30,50,80,90.
        self.assertEqual(build.family_id(base), build.family_id(renamed))
        self.assertEqual(
            build.split_for_family(build.family_id(base)),
            build.split_for_family(build.family_id(renamed)),
        )

    def test_all_mutations_and_relabelings_stay_with_their_base_family(self):
        membership = {}
        triplets = {}
        for row in self.rows:
            membership.setdefault(row["family_id"], set()).add(row["split"])
            triplets.setdefault(row["triplet_id"], []).append(row)
        self.assertEqual(len(membership), 12)
        self.assertTrue(all(len(splits) == 1 for splits in membership.values()))
        self.assertEqual(len(triplets), 24)
        for rows in triplets.values():
            self.assertEqual({row["boundary_case"] for row in rows}, set(build.CASES))
        # Every append is nonempty and joins nodes already present in the base.
        # This removes the shortcut "new node => harmless".
        for row in self.rows:
            value = row["input"]
            nodes = {node for edge in value["edges"] for node in edge}
            self.assertIn(value["k"], nodes)
            self.assertLess(value["k"], max(nodes))
            self.assertEqual(len(value["new_edges"]), 1)
            self.assertIn(value["new_edges"][0][1], nodes)

    def test_split_leak_and_forged_family_are_rejected(self):
        rows = copy.deepcopy(self.rows)
        rows[0]["split"] = next(split for split in build.SPLITS if split != rows[0]["split"])
        with self.assertRaisesRegex(ValueError, "split"):
            build.validate_samples(rows)
        rows = copy.deepcopy(self.rows)
        rows[0]["family_id"] = "forged-family"
        with self.assertRaisesRegex(ValueError, "family"):
            build.validate_samples(rows)

    def test_wrong_labels_incomplete_triplets_and_duplicates_are_rejected(self):
        rows = copy.deepcopy(self.rows)
        rows[1]["expected"]["result_is_acyclic"] = not rows[1]["expected"]["result_is_acyclic"]
        with self.assertRaisesRegex(ValueError, "label"):
            build.validate_samples(rows)
        with self.assertRaisesRegex(ValueError, "triplets"):
            build.validate_samples(self.rows[:-1])
        with self.assertRaisesRegex(ValueError, "duplicate"):
            build.validate_samples(self.rows + [self.rows[0]])

    def test_prompt_export_contains_no_labels_or_case_metadata(self):
        prompts = score.read_jsonl(self.bundle["prompts.jsonl"])
        for prompt, row in zip(prompts, self.rows):
            self.assertEqual(set(prompt), {"sample_id", "input"})
            self.assertEqual(prompt["input"], row["input"])

    def test_manifest_reports_denominators_source_and_unmeasured_headroom(self):
        manifest = score.strict_json(self.bundle["manifest.json"].decode())
        self.assertEqual(manifest["source"]["revision"], build.SOURCE_REVISION)
        self.assertFalse(manifest["source"]["kernel_rechecked_by_this_tool"])
        self.assertEqual(manifest["counts"]["samples"], 72)
        self.assertEqual(manifest["counts"]["by_split"], {"train": 48, "validation": 18, "test": 6})
        self.assertEqual(manifest["counts"]["by_case"], dict.fromkeys(build.CASES, 24))
        self.assertEqual(manifest["provenance"]["kind"], build.SYNTHETIC)
        self.assertFalse(manifest["provenance"]["model_run"])
        self.assertFalse(manifest["provenance"]["serving_evidence"])
        self.assertFalse(manifest["provenance"]["learning_demonstrated"])
        self.assertFalse(manifest["headroom_gate"]["training_ready"])
        self.assertEqual(manifest["headroom_gate"]["status"], "BASELINE_HEADROOM_NOT_MEASURED")

    def test_bundle_tamper_and_changed_source_pin_are_rejected(self):
        with tempfile.TemporaryDirectory() as temp:
            directory = Path(temp)
            for name, data in self.bundle.items():
                (directory / name).write_bytes(data)
            (directory / "samples.jsonl").write_bytes(self.bundle["samples.jsonl"] + b"\n")
            with self.assertRaisesRegex(ValueError, "digest"):
                score.load_fixture(directory)
        with mock.patch.dict(build.SOURCE_HASHES, {
            "tools/locked_formula_runtime.py": "0" * 64,
        }):
            with self.assertRaisesRegex(ValueError, "source content"):
                build.source_snapshot()

    def test_zero_or_invalid_generation_parameters_are_rejected(self):
        for values in [
            {"seed": 1, "families": 0, "relabelings": 2},
            {"seed": 1, "families": 1, "relabelings": 0},
            {"seed": True, "families": 1, "relabelings": 2},
            {"seed": 1, "families": -1, "relabelings": 2},
        ]:
            with self.subTest(values=values):
                with self.assertRaises(ValueError):
                    build.build_samples(**values)


class PredictionContractTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.rows = score.load_fixture(FIXTURE)
        cls.test_rows = [row for row in cls.rows if row["split"] == "test"]

    def predictions(self):
        # Oracle outputs are only test scaffolding, never saved as model results.
        return [{"sample_id": row["sample_id"], "output": json.dumps(row["expected"])}
                for row in self.test_rows]

    def test_correct_oracle_outputs_check_scoring_but_cannot_claim_learning(self):
        result = score.evaluate(self.rows, self.predictions(), split="test")
        self.assertEqual(result["joint_accuracy"], {"numerator": 6, "denominator": 6, "value": 1.0})
        self.assertEqual(result["triplet_accuracy"], {"numerator": 2, "denominator": 2, "value": 1.0})
        self.assertEqual(result["false_theorem_application_rate"]["denominator"], 4)
        self.assertEqual(result["false_acyclic_rate"]["denominator"], 2)
        self.assertEqual(result["parse_failure_rate"]["value"], 0)
        self.assertEqual(result["status"], "SCORED_NO_ACCEPTANCE_DECISION")
        self.assertEqual(result["learning_conclusion"], "NOT_ESTABLISHED_BY_SINGLE_EVALUATION")

    def test_incorrect_converse_fails_every_triplet(self):
        predictions = self.predictions()
        for row, prediction in zip(self.test_rows, predictions):
            if not row["expected"]["append_theorem_applies"]:
                prediction["output"] = json.dumps(dict(zip(build.LABEL_KEYS, (False, False))))
        result = score.evaluate(self.rows, predictions, split="test")
        self.assertEqual(result["joint_accuracy"]["numerator"], 4)
        self.assertEqual(result["triplet_accuracy"]["numerator"], 0)

    def test_row_order_only_predictor_cannot_solve_any_frozen_split(self):
        cycle = list(build.CASES.values())
        for split in build.SPLITS:
            rows = [row for row in self.rows if row["split"] == split]
            predictions = [
                {"sample_id": row["sample_id"],
                 "output": json.dumps(dict(zip(build.LABEL_KEYS, cycle[index % 3])))}
                for index, row in enumerate(rows)
            ]
            result = score.evaluate(self.rows, predictions, split=split)
            self.assertLess(result["joint_accuracy"]["value"], 1.0)
            self.assertLess(result["triplet_accuracy"]["value"], 1.0)

    def test_false_acyclic_and_false_theorem_application_rates(self):
        predictions = self.predictions()
        for prediction in predictions:
            prediction["output"] = json.dumps(dict(zip(build.LABEL_KEYS, (True, True))))
        result = score.evaluate(self.rows, predictions, split="test")
        self.assertEqual(result["false_acyclic_rate"]["value"], 1.0)
        self.assertEqual(result["false_theorem_application_rate"]["value"], 1.0)
        self.assertEqual(result["joint_accuracy"]["numerator"], 2)

    def test_missing_and_malformed_outputs_keep_full_denominators(self):
        predictions = self.predictions()[1:]
        predictions[0]["output"] = "not JSON"
        result = score.evaluate(self.rows, predictions, split="test")
        self.assertEqual(result["missing_predictions"], 1)
        self.assertEqual(result["parse_failure_rate"], {"numerator": 2, "denominator": 6, "value": 1 / 3})
        self.assertEqual(result["joint_accuracy"]["denominator"], 6)
        result = score.evaluate(self.rows, [], split="test")
        self.assertEqual(result["joint_accuracy"]["value"], 0)
        self.assertEqual(result["triplet_accuracy"]["value"], 0)
        self.assertEqual(result["parse_failure_rate"]["value"], 1)

    def test_parser_rejects_coercion_duplicate_keys_constants_and_prose(self):
        invalid = [
            '{"append_theorem_applies":1,"result_is_acyclic":true}',
            '{"append_theorem_applies":"false","result_is_acyclic":true}',
            '{"append_theorem_applies":null,"result_is_acyclic":true}',
            '{"append_theorem_applies":false,"append_theorem_applies":true,"result_is_acyclic":true}',
            '{"append_theorem_applies":NaN,"result_is_acyclic":true}',
            '{"append_theorem_applies":true,"result_is_acyclic":true,"extra":0}',
            'Answer: {"append_theorem_applies":true,"result_is_acyclic":true}',
            '[]', '{}', None, {"append_theorem_applies": True, "result_is_acyclic": True},
        ]
        for output in invalid:
            with self.subTest(output=output):
                self.assertIsNone(score.parse_output(output))

    def test_duplicate_unknown_and_wrong_split_prediction_ids_are_rejected(self):
        predictions = self.predictions()
        with self.assertRaisesRegex(ValueError, "duplicate"):
            score.evaluate(self.rows, predictions + [predictions[0]], split="test")
        for identifier in [
            "unknown",
            next(row["sample_id"] for row in self.rows if row["split"] == "train"),
        ]:
            with self.assertRaisesRegex(ValueError, "wrong-split"):
                score.evaluate(self.rows, [{"sample_id": identifier, "output": "{}"}], split="test")

    def test_empty_split_and_blank_jsonl_line_cannot_silently_pass(self):
        one_family = build.build_samples(seed=1, families=1, relabelings=1)
        other_split = next(split for split in build.SPLITS if split != one_family[0]["split"])
        with self.assertRaisesRegex(ValueError, "no samples"):
            score.evaluate(one_family, [], split=other_split)
        with self.assertRaises(ValueError):
            score.read_jsonl(b'{}\n\n')


if __name__ == "__main__":
    unittest.main()
