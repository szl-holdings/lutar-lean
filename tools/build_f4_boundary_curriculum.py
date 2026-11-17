#!/usr/bin/env python3
"""Build synthetic F4 boundary fixtures on CPU; no model or serving evidence."""

from __future__ import annotations

import argparse
from collections import Counter, defaultdict, deque
import hashlib
import json
from pathlib import Path
import random

from tools.locked_formula_runtime import (
    LockedDomainError,
    khipu_append_hypothesis,
    khipu_append_preserves_acyclic,
    khipu_backward_invariant,
    khipu_has_cycle_without_invariant,
)

REPO_ROOT = Path(__file__).resolve().parents[1]
SOURCE_REVISION = "5e8a92917d2d4bfeb371a2372f87a4c7660d996d"
SOURCE_HASHES = {
    "Lutar/Puriq/Formulas/ProvedFormulas.lean":
        "a9a79ec21074a5e4f8a542a0270050b36ba697654aef8da9cfa1a846ca95413d",
    "tools/locked_formula_runtime.py":
        "d7d11386f2c4de5814f7583561052fcc81ebbbcf2d9f6372938083c4913ff41c",
}
THEOREM = "Puriq.Formula.Proved.f4_khipu_dag_acyclic_preserved"
GENERATOR_REVISION = "f4-boundary-v1"
SCHEMA = "szl.f4-boundary.fixture/v1"
SYNTHETIC = "SYNTHETIC_EXPERIMENT_FIXTURE"
CASES = {
    "valid_append": (True, True),
    "harmless_hypothesis_violation": (False, True),
    "cycle": (False, False),
}
LABEL_KEYS = ("append_theorem_applies", "result_is_acyclic")
SPLITS = ("train", "validation", "test")
PROMPT_INSTRUCTION = (
    "Return only a JSON object with exactly two boolean fields: "
    "append_theorem_applies and result_is_acyclic. For this exact F4 append "
    "theorem, every base edge (src,dst) must satisfy dst<src, and every new "
    "edge must have source k and target<k. k need not be fresh or maximal. "
    "The second field asks whether the union of base and new edges actually "
    "has no directed cycle, independently of whether these hypotheses hold."
)


class OracleMismatch(RuntimeError):
    """Independent oracle and runtime mirror disagree; do not emit a label."""


def canonical(value: object) -> bytes:
    return json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=True,
        allow_nan=False,
    ).encode("utf-8")


def digest(value: object) -> str:
    return hashlib.sha256(canonical(value)).hexdigest()


def _nat(value: object, name: str) -> int:
    if type(value) is not int or value < 0:
        raise LockedDomainError(f"{name} must be an exact nonnegative int")
    return value


def _edges(value: object) -> list[tuple[int, int]]:
    # The fixture interface admits finite JSON-style sequences, not arbitrary
    # iterators or objects with overloaded ordering/equality.
    if type(value) not in (list, tuple):
        raise LockedDomainError("edges must be a finite list or tuple")
    result = []
    for edge in value:
        if type(edge) not in (list, tuple) or len(edge) != 2:
            raise LockedDomainError("each edge must have exactly two Nat endpoints")
        result.append((_nat(edge[0], "src"), _nat(edge[1], "dst")))
    return result


def topological_acyclic(edges: object) -> bool:
    """Kahn indegree elimination, independent of the runtime's DFS."""
    edges = _edges(edges)
    successors: dict[int, list[int]] = defaultdict(list)
    indegree: dict[int, int] = {}
    for src, dst in edges:
        successors[src].append(dst)
        indegree.setdefault(src, 0)
        indegree[dst] = indegree.get(dst, 0) + 1
    ready = deque(sorted(node for node, degree in indegree.items() if degree == 0))
    removed = 0
    while ready:
        node = ready.popleft()
        removed += 1
        for dst in successors[node]:
            indegree[dst] -= 1
            if indegree[dst] == 0:
                ready.append(dst)
    return removed == len(indegree)


def label_input(value: object) -> dict[str, bool]:
    """Return applicability and actual acyclicity; reject invalid domains."""
    if type(value) is not dict or set(value) != {"edges", "k", "new_edges"}:
        raise LockedDomainError("input must contain exactly edges, k and new_edges")
    base, new = _edges(value["edges"]), _edges(value["new_edges"])
    k = _nat(value["k"], "k")
    invariant = all(dst < src for src, dst in base)
    append_hypothesis = all(src == k and dst < k for src, dst in new)
    applies = invariant and append_hypothesis
    acyclic = topological_acyclic(base + new)
    if khipu_backward_invariant(base) != invariant:
        raise OracleMismatch("base hypothesis disagrees with runtime mirror")
    if khipu_append_hypothesis(k, new) != append_hypothesis:
        raise OracleMismatch("append hypothesis disagrees with runtime mirror")
    if khipu_has_cycle_without_invariant(base + new) != (not acyclic):
        raise OracleMismatch("Kahn and runtime DFS disagree")
    if applies:
        if not acyclic or not khipu_append_preserves_acyclic(base, k, new):
            raise OracleMismatch("F4 premise holds but an acyclicity check failed")
    else:
        try:
            khipu_append_preserves_acyclic(base, k, new)
        except LockedDomainError as exc:
            raise OracleMismatch("runtime rejected the independently checked domain") from exc
        except ValueError:
            pass
        else:
            raise OracleMismatch("runtime accepted a failed F4 premise")
    return dict(zip(LABEL_KEYS, (applies, acyclic)))


def family_id(edges: object) -> str:
    """Order-normalized base graph; independent of seed, appends and labels."""
    edges = _edges(edges)
    nodes = sorted({node for edge in edges for node in edge})
    rank = {node: i for i, node in enumerate(nodes)}
    shape = sorted((rank[src], rank[dst]) for src, dst in edges)
    return "f4-family-" + digest(shape)


def split_for_family(identifier: str) -> str:
    # Stable 60/20/20 assignment by family hash, never by individual example.
    bucket = int(hashlib.sha256(identifier.encode("ascii")).hexdigest(), 16) % 10
    return "train" if bucket < 6 else "validation" if bucket < 8 else "test"


def _candidate(rng: random.Random):
    size = rng.randint(6, 18)
    density = rng.uniform(0.12, 0.40)
    base = [(src, dst) for src in range(size) for dst in range(src)
            if rng.random() < density]
    nodes = sorted({node for edge in base for node in edge})
    # Remove unused numeric positions before identifying the base family.
    rank = {node: i for i, node in enumerate(nodes)}
    base = sorted((rank[src], rank[dst]) for src, dst in base)
    nodes = list(range(len(nodes)))
    rng.shuffle(nodes)
    for k in nodes:
        lower = [node for node in nodes if node < k and (k, node) not in base]
        higher = [node for node in nodes if node > k]
        cyclic = [node for node in higher
                  if not topological_acyclic(base + [(k, node)])]
        harmless = [node for node in higher if node not in cyclic]
        if lower and cyclic and harmless:
            # Every endpoint already occurs in the base graph. Node novelty
            # therefore cannot distinguish harmless from cyclic appends.
            return base, k, [rng.choice(lower), rng.choice(harmless), rng.choice(cyclic)]
    return None


def build_samples(*, seed: int, families: int, relabelings: int) -> list[dict]:
    _nat(seed, "seed")
    for name, value in (("families", families), ("relabelings", relabelings)):
        _nat(value, name)
        if value == 0:
            raise ValueError(f"{name} must be positive")
    rng = random.Random(seed)
    seen: set[str] = set()
    samples = []
    attempts = 0
    while len(seen) < families:
        attempts += 1
        if attempts > families * 1000:
            raise ValueError("could not generate enough distinct base families")
        candidate = _candidate(rng)
        if candidate is None:
            continue
        base, k, targets = candidate
        identifier = family_id(base)
        if identifier in seen:
            continue
        seen.add(identifier)
        nodes = sorted({node for edge in base for node in edge})
        for variant in range(relabelings):
            mapping = {node: node for node in nodes}
            if variant:
                cursor = variant * 10000 + rng.randint(100, 1000)
                for node in nodes:
                    cursor += rng.randint(1, 19)
                    mapping[node] = cursor
            renamed = [[mapping[src], mapping[dst]] for src, dst in base]
            renamed_targets = [mapping[node] for node in targets]
            triplet = "f4-triplet-" + digest({
                "edges": renamed, "k": mapping[k], "targets": renamed_targets,
            })
            for case, target in zip(CASES, renamed_targets):
                value = {
                    "edges": renamed, "k": mapping[k],
                    "new_edges": [[mapping[k], target]],
                }
                expected = label_input(value)
                if tuple(expected[key] for key in LABEL_KEYS) != CASES[case]:
                    raise OracleMismatch("candidate does not match its boundary class")
                samples.append({
                    "sample_id": "f4-sample-" + digest(value),
                    "family_id": identifier,
                    "triplet_id": triplet,
                    "relabeling": variant,
                    "split": split_for_family(identifier),
                    "boundary_case": case,
                    "input": value,
                    "expected": expected,
                    "provenance": SYNTHETIC,
                })
    # The label classes must not be recoverable from row_index % 3. Shuffle
    # serialization order independently of the graph/label generation stream.
    random.Random(f"f4-order-v1:{seed}").shuffle(samples)
    validate_samples(samples)
    return samples


def validate_samples(samples: object) -> None:
    """Recompute labels, identities and group boundaries before scoring."""
    if type(samples) is not list or not samples:
        raise ValueError("samples must be a nonempty list")
    required = {
        "sample_id", "family_id", "triplet_id", "relabeling", "split",
        "boundary_case", "input", "expected", "provenance",
    }
    seen = set()
    groups: dict[str, list[dict]] = defaultdict(list)
    for row in samples:
        if type(row) is not dict or set(row) != required:
            raise ValueError("sample schema mismatch")
        value = row["input"]
        labels = label_input(value)
        if row["sample_id"] != "f4-sample-" + digest(value):
            raise ValueError("sample identity mismatch")
        if row["sample_id"] in seen:
            raise ValueError("duplicate sample")
        seen.add(row["sample_id"])
        identifier = family_id(value["edges"])
        if row["family_id"] != identifier:
            raise ValueError("base-family identity mismatch")
        if row["split"] != split_for_family(identifier):
            raise ValueError("family split mismatch or leak")
        if row["provenance"] != SYNTHETIC:
            raise ValueError("fixture is not marked synthetic")
        _nat(row["relabeling"], "relabeling")
        expected = row["expected"]
        if (type(expected) is not dict or set(expected) != set(LABEL_KEYS)
                or any(type(expected[key]) is not bool for key in LABEL_KEYS)
                or expected != labels):
            raise ValueError("stored label mismatch")
        case = row["boundary_case"]
        if case not in CASES or tuple(expected[key] for key in LABEL_KEYS) != CASES[case]:
            raise ValueError("boundary case mismatch")
        groups[row["triplet_id"]].append(row)
    for identifier, rows in groups.items():
        by_case = {row["boundary_case"]: row for row in rows}
        if len(rows) != 3 or set(by_case) != set(CASES):
            raise ValueError("triplets must contain all three boundary cases exactly once")
        first = rows[0]
        for row in rows:
            if any(row[key] != first[key] for key in ("family_id", "split", "relabeling")):
                raise ValueError("triplet grouping mismatch")
            if (row["input"]["edges"] != first["input"]["edges"]
                    or row["input"]["k"] != first["input"]["k"]
                    or len(row["input"]["new_edges"]) != 1
                    or row["input"]["new_edges"][0][0] != row["input"]["k"]):
                raise ValueError("triplet input mismatch")
        targets = [by_case[case]["input"]["new_edges"][0][1] for case in CASES]
        expected_id = "f4-triplet-" + digest({
            "edges": first["input"]["edges"], "k": first["input"]["k"],
            "targets": targets,
        })
        if identifier != expected_id:
            raise ValueError("triplet identity mismatch")


def source_snapshot() -> dict:
    for name, expected in SOURCE_HASHES.items():
        actual = hashlib.sha256((REPO_ROOT / name).read_text(encoding="utf-8").encode()).hexdigest()
        if actual != expected:
            raise ValueError(f"pinned source content changed: {name}")
    return {
        "repository": "szl-holdings/lutar-lean",
        "revision": SOURCE_REVISION,
        "theorem": THEOREM,
        "file_sha256_lf_utf8": SOURCE_HASHES,
        "kernel_rechecked_by_this_tool": False,
    }


def build_bundle(*, seed: int, families: int, relabelings: int) -> dict[str, bytes]:
    source = source_snapshot()
    rows = build_samples(seed=seed, families=families, relabelings=relabelings)
    files = {
        "samples.jsonl": b"".join(canonical(row) + b"\n" for row in rows),
        "prompts.jsonl": b"".join(canonical({
            "sample_id": row["sample_id"], "input": row["input"],
        }) + b"\n" for row in rows),
    }
    family_splits = {row["family_id"]: row["split"] for row in rows}
    manifest = {
        "schema": SCHEMA,
        "provenance": {
            "kind": SYNTHETIC,
            "serving_evidence": False,
            "model_run": False,
            "learning_demonstrated": False,
            "description": "Synthetic graph labels; neither a model evaluation nor runtime receipts.",
        },
        "headroom_gate": {
            "status": "BASELINE_HEADROOM_NOT_MEASURED",
            "training_ready": False,
            "required_evidence": "Frozen base-model predictions with measurable errors, followed by a predefined matched-budget comparison.",
        },
        "source": source,
        "generator": {
            "path": "tools/build_f4_boundary_curriculum.py",
            "revision": GENERATOR_REVISION,
            "sha256_lf_utf8": hashlib.sha256(Path(__file__).read_text(encoding="utf-8").encode()).hexdigest(),
        },
        "parameters": {"seed": seed, "families": families, "relabelings": relabelings},
        "split_policy": "sha256(order-normalized base-family id) modulo 10: train<6, validation<8, else test",
        "families": dict(sorted(family_splits.items())),
        "counts": {
            "families": len(family_splits),
            "triplets": len({row["triplet_id"] for row in rows}),
            "samples": len(rows),
            "by_split": {split: sum(row["split"] == split for row in rows) for split in SPLITS},
            "by_case": dict(Counter(row["boundary_case"] for row in rows)),
        },
        "oracle": {
            "acyclicity": "Independent Kahn indegree elimination crosschecked with runtime DFS",
            "hypotheses": "Direct Nat predicates crosschecked with both runtime mirrors",
            "checked_samples": len(rows),
            "disagreements": 0,
        },
        "prompt_instruction": PROMPT_INSTRUCTION,
        "files": {name: {"sha256": hashlib.sha256(data).hexdigest(), "bytes": len(data)}
                  for name, data in files.items()},
    }
    files["manifest.json"] = json.dumps(manifest, indent=2, sort_keys=True).encode() + b"\n"
    return files


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--seed", type=int, default=20261116)
    parser.add_argument("--families", type=int, default=12)
    parser.add_argument("--relabelings", type=int, default=2,
                        help="includes the identity labeling")
    args = parser.parse_args()
    bundle = build_bundle(seed=args.seed, families=args.families, relabelings=args.relabelings)
    args.output_dir.mkdir(parents=True, exist_ok=False)
    for name, data in bundle.items():
        (args.output_dir / name).write_bytes(data)
    print(f"Wrote synthetic fixture to {args.output_dir}; no model was run.")


if __name__ == "__main__":
    main()
