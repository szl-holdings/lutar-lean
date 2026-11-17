#!/usr/bin/env python3
"""Score saved F4 predictions on CPU; makes no model-learning or promotion claim."""

from __future__ import annotations

import argparse
from collections import Counter, defaultdict
import hashlib
import json
from pathlib import Path

from tools import build_f4_boundary_curriculum as curriculum

EVALUATOR_REVISION = "f4-boundary-evaluator-v1"


def _unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def _reject_constant(value):
    raise ValueError(f"non-JSON numeric constant: {value}")


def strict_json(text: str):
    return json.loads(text, object_pairs_hook=_unique_object, parse_constant=_reject_constant)


def read_jsonl(data: bytes) -> list:
    # Empty/blank lines are errors; silently dropped lines would alter coverage.
    return [strict_json(line) for line in data.decode("utf-8").splitlines()]


def load_fixture(directory: Path) -> list[dict]:
    manifest = strict_json((directory / "manifest.json").read_text(encoding="utf-8"))
    if manifest.get("schema") != curriculum.SCHEMA:
        raise ValueError("fixture schema mismatch")
    if manifest.get("source") != curriculum.source_snapshot():
        raise ValueError("fixture source pin mismatch")
    generator = manifest.get("generator", {})
    actual_generator = hashlib.sha256(
        Path(curriculum.__file__).read_text(encoding="utf-8").encode()
    ).hexdigest()
    if (generator.get("revision") != curriculum.GENERATOR_REVISION
            or generator.get("sha256_lf_utf8") != actual_generator):
        raise ValueError("fixture generator revision mismatch")
    provenance = manifest.get("provenance", {})
    if (provenance.get("kind") != curriculum.SYNTHETIC
            or any(provenance.get(key) is not False
                   for key in ("serving_evidence", "model_run", "learning_demonstrated"))):
        raise ValueError("fixture provenance must remain synthetic")
    if set(manifest.get("files", {})) != {"samples.jsonl", "prompts.jsonl"}:
        raise ValueError("fixture file inventory mismatch")
    files = {}
    for name, metadata in manifest["files"].items():
        data = (directory / name).read_bytes()
        if (hashlib.sha256(data).hexdigest() != metadata.get("sha256")
                or len(data) != metadata.get("bytes")):
            raise ValueError(f"fixture digest mismatch: {name}")
        files[name] = read_jsonl(data)
    rows = files["samples.jsonl"]
    curriculum.validate_samples(rows)
    expected_prompts = [{"sample_id": row["sample_id"], "input": row["input"]} for row in rows]
    if curriculum.canonical(files["prompts.jsonl"]) != curriculum.canonical(expected_prompts):
        raise ValueError("prompt file must contain only sample_id and input")
    families = {row["family_id"]: row["split"] for row in rows}
    expected_counts = {
        "families": len(families),
        "triplets": len({row["triplet_id"] for row in rows}),
        "samples": len(rows),
        "by_split": {split: sum(row["split"] == split for row in rows)
                     for split in curriculum.SPLITS},
        "by_case": dict(Counter(row["boundary_case"] for row in rows)),
    }
    if curriculum.canonical(manifest.get("counts")) != curriculum.canonical(expected_counts):
        raise ValueError("fixture count mismatch")
    if manifest.get("families") != families:
        raise ValueError("fixture family inventory mismatch")
    return rows


def parse_output(output: object) -> dict | None:
    """Only exact JSON booleans count; no coercion, code fences or prose."""
    if type(output) is not str:
        return None
    try:
        value = strict_json(output)
    except (ValueError, RecursionError):
        return None
    if (type(value) is not dict or set(value) != set(curriculum.LABEL_KEYS)
            or any(type(value[key]) is not bool for key in curriculum.LABEL_KEYS)):
        return None
    return value


def _metric(numerator: int, denominator: int) -> dict:
    return {
        "numerator": numerator, "denominator": denominator,
        "value": numerator / denominator if denominator else None,
    }


def evaluate(samples: list[dict], predictions: list[dict], *, split: str) -> dict:
    curriculum.validate_samples(samples)
    if split not in curriculum.SPLITS:
        raise ValueError("unknown split")
    rows = [row for row in samples if row["split"] == split]
    if not rows:
        raise ValueError("selected split has no samples")
    allowed = {row["sample_id"] for row in rows}
    parsed = {}
    for row in predictions:
        if type(row) is not dict or set(row) != {"sample_id", "output"}:
            raise ValueError("prediction rows require exactly sample_id and output")
        identifier = row["sample_id"]
        if type(identifier) is not str or identifier not in allowed:
            raise ValueError("unknown or wrong-split prediction id")
        if identifier in parsed:
            raise ValueError("duplicate prediction id")
        parsed[identifier] = parse_output(row["output"])
    correct = {}
    triplets: dict[str, list[bool]] = defaultdict(list)
    parse_failures = false_applies = false_acyclic = 0
    premise_invalid = cyclic = 0
    for row in rows:
        output = parsed.get(row["sample_id"])
        expected = row["expected"]
        is_correct = output == expected
        correct[row["sample_id"]] = is_correct
        triplets[row["triplet_id"]].append(is_correct)
        parse_failures += output is None
        premise_invalid += not expected["append_theorem_applies"]
        cyclic += not expected["result_is_acyclic"]
        if output is not None:
            false_applies += (
                not expected["append_theorem_applies"] and output["append_theorem_applies"]
            )
            false_acyclic += not expected["result_is_acyclic"] and output["result_is_acyclic"]
    return {
        "schema": "szl.f4-boundary.evaluation/v1",
        "evaluator_revision": EVALUATOR_REVISION,
        "status": "SCORED_NO_ACCEPTANCE_DECISION",
        "learning_conclusion": "NOT_ESTABLISHED_BY_SINGLE_EVALUATION",
        "headroom_gate": "NOT_ASSESSED_FROM_ROLE_UNSPECIFIED_PREDICTIONS",
        "dataset_provenance": curriculum.SYNTHETIC,
        "split": split,
        "samples": len(rows),
        "families": len({row["family_id"] for row in rows}),
        "missing_predictions": len(allowed - parsed.keys()),
        "joint_accuracy": _metric(sum(correct.values()), len(rows)),
        "triplet_accuracy": _metric(sum(all(group) for group in triplets.values()), len(triplets)),
        "false_theorem_application_rate": _metric(false_applies, premise_invalid),
        "false_acyclic_rate": _metric(false_acyclic, cyclic),
        "parse_failure_rate": _metric(parse_failures, len(rows)),
        "per_item": [
            {"sample_id": row["sample_id"], "correct": correct[row["sample_id"]],
             "parse_failure": parsed.get(row["sample_id"]) is None}
            for row in rows
        ],
        "note": (
            "Missing and malformed outputs count as incorrect and as parse failures. "
            "False-claim rates count parsed false claims over all applicable examples; "
            "read them together with coverage and joint accuracy. No model is run here."
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dataset", type=Path, required=True)
    parser.add_argument("--predictions", type=Path, required=True)
    parser.add_argument("--split", choices=curriculum.SPLITS, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    samples = load_fixture(args.dataset)
    prediction_bytes = args.predictions.read_bytes()
    report = evaluate(samples, read_jsonl(prediction_bytes), split=args.split)
    report["input_sha256"] = {
        "manifest": hashlib.sha256((args.dataset / "manifest.json").read_bytes()).hexdigest(),
        "samples": hashlib.sha256((args.dataset / "samples.jsonl").read_bytes()).hexdigest(),
        "predictions": hashlib.sha256(prediction_bytes).hexdigest(),
    }
    with args.output.open("xb") as stream:
        stream.write(json.dumps(report, indent=2, sort_keys=True).encode() + b"\n")
    print(f"Saved {args.split} prediction scores to {args.output}; no acceptance decision.")


if __name__ == "__main__":
    main()
