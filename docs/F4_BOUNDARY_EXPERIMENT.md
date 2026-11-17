# F4 hypothesis-boundary experiment contract

**Status: CPU-only synthetic fixture and saved-prediction evaluator. Baseline
headroom is unmeasured; no model has been run or trained by these tools.**

This experiment separates two questions: whether the exact F4 append theorem
applies to an input, and whether the resulting graph is actually acyclic. A
sufficient hypothesis can fail while its conclusion remains true. The matched
examples deliberately test that distinction.

## Mathematical source and scope

The source pin is lutar-lean commit
`5e8a92917d2d4bfeb371a2372f87a4c7660d996d`.
The theorem is
`Puriq.Formula.Proved.f4_khipu_dag_acyclic_preserved` in
[ProvedFormulas.lean](../Lutar/Puriq/Formulas/ProvedFormulas.lean):

```lean
(es : KhipuEdges) (inv : KhipuBackwardInvariant es)
(k : Nat) (newEdges : KhipuEdges)
(hk : ∀ e ∈ newEdges, e.1 = k ∧ e.2 < k) :
∀ a, ¬ KhipuReach (es ++ newEdges) a a
```

The base invariant requires every edge to satisfy `dst < src`.
Every appended edge must have source `k` and target below `k`.
**`k` need not be fresh or maximal.** These are the exact hypotheses
of this append theorem, not a characterization of all acyclic graphs.

The generator checks the LF-normalized SHA-256 of this theorem source and
[locked_formula_runtime.py](../tools/locked_formula_runtime.py) against the pin.
A source change fails generation until deliberately reviewed and repinned.
This is a content check; it does not replay the Lean kernel. The compiled
theorem does not establish deployed-store behavior, concurrent-writer safety,
Byzantine agreement, or learned-model reliability. The existing
[claim map](../claims/locked-formulas.v1.json) remains authoritative.

For base edges `[(3,2),(2,1)]` and `k=2`:

| New edge | Append theorem applies | Result acyclic |
| --- | --- | --- |
| `(2,0)` | true | true |
| `(2,4)` | false | true |
| `(2,3)` | false | false |

The middle row prevents learning the incorrect converse. In generated
triplets, all append endpoints already occur in the base graph, removing
“the target is a new node” as a classification shortcut.

## Generator and split contract

Run from the repository root with Python 3.11 or 3.12; only the standard
library is required:

```bash
python -m tools.build_f4_boundary_curriculum --output-dir ../f4-fixture --seed 20261116 --families 12 --relabelings 2
```

The output directory must not already exist. The tool creates:

- `samples.jsonl`: inputs, expected booleans, boundary cases, family/triplet
  identifiers, split, relabeling index, and explicit synthetic provenance.
- `prompts.jsonl`: only opaque sample identifiers and input objects. The
  common instruction is in `manifest.json`.
- `manifest.json`: source pin and file hashes, generator revision and content
  hash, seed and parameters, exact counts, family assignments, oracle checks,
  data-file hashes, synthetic provenance, and the unmeasured-headroom gate.

The builder uses Kahn indegree elimination to determine actual acyclicity.
It independently evaluates the two F4 predicates, then crosschecks all three
results against the existing runtime DFS and hypothesis helpers. A disagreement
stops generation. Invalid domains raise errors; booleans, negative integers,
floats and malformed edges never become ordinary false labels.

A family is the base graph with its used node labels replaced by increasing
ranks. Its identifier is independent of the append mutation, relabeling, seed
and sample order. All three boundary cases and all order-preserving
relabelings of that base share one split. Assignment is SHA-256 of the family
identifier modulo ten: 0–5 train, 6–7 validation, 8–9 test. These proportions
are a hash policy, not guaranteed sample counts for a small fixture. Final
sample and prompt order is deterministically shuffled with a separate seed
stream; a repeating valid/harmless/cyclic row-index predictor cannot solve
any frozen split. Triplet identifiers preserve the grouping for scoring.

This is **not arbitrary graph-isomorphism deduplication**. It groups the
order-preserving relabelings that retain this theorem's numeric-order
hypotheses. Version 1 samples small backward graphs from candidate node counts
6–18; it does not establish transfer to larger or qualitatively different
graphs. The generator removes unused node positions.

The checked-in `tests/fixtures/f4_boundary_v1` is an engineering fixture:
12 base families, 24 triplets and 72 samples, with 24 examples of each class.
Its split counts are 48 train, 18 validation and 6 test. The test split has
only one base family, with two relabelings. It is too small for a scientific
learning conclusion. It is frozen to check software reproducibility, not to
supply reported model results.

Synthetic label provenance is separate from serving provenance. These files
have no real serving receipts and must not be represented as verified
own-metal responses. No model weights, private correspondence, or runtime
receipt exports are included.

## Saved-prediction evaluator

Select the intended split using the metadata in `samples.jsonl`, then send
only the matching `input` and common instruction to a model collector.
Do not send `expected`, `boundary_case`, family metadata, or labeled rows
to the model. The prompt export contains every split; it is not a ready-made
training file. A collector must enforce the split selection.

Each prediction line has exactly `sample_id` and `output`. The latter is
the raw model output as a string, for example:

```json
{"sample_id":"<id from the selected split>","output":"{\"append_theorem_applies\":false,\"result_is_acyclic\":true}"}
```

Score a saved file without invoking any model:

```bash
python -m tools.evaluate_f4_boundary --dataset ../f4-fixture --predictions ../predictions.jsonl --split test --output ../f4-scores.json
```

The evaluator validates source/generator pins, file hashes, labels, complete
triplets and split assignments. Unknown, duplicate or wrong-split prediction
IDs are errors. Empty splits are errors. Missing predictions and malformed
outputs are incorrect and remain in the full denominators. Parsing accepts
only the exact two boolean fields: no numeric/string coercion, duplicate JSON
keys, NaN, code fences, extra keys or surrounding prose.

| Metric | Numerator | Denominator |
| --- | --- | --- |
| Joint accuracy | Both booleans correct | All selected samples |
| Triplet accuracy | All three samples jointly correct | All selected triplets |
| False theorem-application rate | Parsed claim that theorem applies when premises fail | All premise-invalid samples |
| False acyclic rate | Parsed acyclic claim on a cyclic graph | All cyclic samples |
| Parse failure rate | Missing or malformed outputs | All selected samples |

False-claim rates alone can look low when a model produces no usable answers.
Always read them with joint accuracy, parse failures and the explicit missing
prediction count. Reports retain every item's correctness and parse status.
They report `SCORED_NO_ACCEPTANCE_DECISION` and make no promotion or learning
claim. The role of a prediction file is not inferred from its filename.

## Headroom gate before a learning study

The fixture manifest records `BASELINE_HEADROOM_NOT_MEASURED` and
`training_ready: false`. Passing oracle tests does not change that state.
The scorer alone cannot establish headroom because it does not establish
whether predictions came from a declared base model.

Before proposing a training run, freeze a sufficiently large evaluation set,
declare its base model revision, prompt/decoding configuration and data
exclusions, and collect genuine baseline predictions. If the base model
already solves the frozen task, this task has no demonstrated improvement
headroom: stop or preregister a harder held-out task before training. Errors
on the small checked-in fixture are not a sufficient study design.

A later study can compare the fixed base, positive-only F4 training and
matched boundary training at equal budgets. Keep mutation families together,
predefine the improvement criterion and repeated seeds, and prevent evaluation
examples from entering any training or self-improvement loop. Larger-graph
and new-structure transfer need separately frozen holdouts. This PR does not
implement training, confidence intervals, automatic admission, or that study.

## Local checks

```bash
python -m pytest -q tests/test_f4_boundary_curriculum.py tests/test_locked_formula_refinement.py tests/test_locked_formula_runtime_domain.py
python -m ruff check tools/build_f4_boundary_curriculum.py tools/evaluate_f4_boundary.py tests/test_f4_boundary_curriculum.py --select E9,F
```

Tests include the incorrect converse, an old/nonmaximal source, both failed
premises, invalid domains, self-loops, duplicate edges, exhaustive three-node
Kahn/DFS agreement, intentional oracle disagreement, frozen reproducibility,
split leaks, artifact tampering, strict parsing and complete scoring
denominators. Oracle-perfect predictions occur only inside tests to validate
the scoring arithmetic; they are not saved or presented as model outputs.
