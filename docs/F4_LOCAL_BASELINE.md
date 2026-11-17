# F4 local validation-only baseline collector

**Status: code-only research workflow; no model inference or training has been run by this PR.**
This extends the synthetic F4 theorem-boundary fixture after the merged
[experiment contract](F4_BOUNDARY_EXPERIMENT.md).

## Purpose and scope

The experiment asks separately whether the exact F4 append theorem applies
and whether a graph is actually acyclic. A failed sufficient condition can
still leave a graph acyclic. The original checked-in fixture has 72 samples:
48 train, **18 validation**, 6 test. Its test split has only one base family;
that is not a scientific generalization benchmark.

This collector always chooses **validation**, never test. Model responses on
validation are development feedback and must not later be counted as fresh
holdout results. No labels, expected answers, family IDs, split or test rows
are included in model requests. The original F4 fixture evaluator checks
exact source/generator/data pins before collection.

## Execution boundary

`tools/collect_f4_local_baseline.py` uses only stdlib and the fixed
`http://127.0.0.1:11434` Ollama API. It permits only `GET /api/tags` and
`POST /api/generate`; arbitrary URLs, inherited proxies, redirects, external
model providers, credential discovery, remote execution, training and model
promotion are unavailable.

The operator must choose a model tag and supply its exact lowercase,
64-character Ollama digest **separately**. The collector verifies tag/digest
both before and after sequential generation. Ollama tag listings are local
self-reports, not independently authenticated weight identities; an
in-flight malicious model swap cannot be ruled out by this check alone.

Each request has no retry, a 45-second HTTP timeout, `temperature=0`,
`seed=1234` (default), `num_predict=128` and JSON-format request. Determinism
is requested, **not proven**. Every raw answer is retained; malformed output
is not coerced into a successful answer. At most 96 validation rows are
allowed; incomplete three-case triplets fail closed.

Exact manifest, samples and prompts file byte digests are checked before
and after inference. The collector creates the previously absent output
directory only once all requests and identity checks complete. It never
overwrites an existing result. Unexpected filesystem failure could still
leave an incomplete directory; **only a successful exit and a complete
provenance JSON constitute a recorded local pilot**.

## Usage

Run from the root of `lutar-lean` with a locally running Ollama daemon.
Read the intended model digest from the loopback `/api/tags` response first.
Use an actual digest rather than the placeholder:

```bash
python -m tools.collect_f4_local_baseline \
  --dataset tests/fixtures/f4_boundary_v1 \
  --model khipu:latest \
  --model-digest <exact-local-64-char-hex-digest> \
  --output-dir ../f4-khipu-validation-pilot
```

The output directory contains `predictions.jsonl` with exactly
`sample_id` and raw `output`, compatible with the existing scorer, and
`provenance.json` with pinned file/model hashes, prompt-selection hash,
timestamps, parameters, row count and explicit authority limitations.

Score the predictions separately, without generating any model response:

```bash
python -m tools.evaluate_f4_boundary \
  --dataset tests/fixtures/f4_boundary_v1 \
  --predictions ../f4-khipu-validation-pilot/predictions.jsonl \
  --split validation \
  --output ../f4-khipu-validation-scores.json
```

The collector reports `MEASURED_UNQUALIFIED_LOCAL_PILOT` **only when run
successfully**; it does not decide an acceptance gate. The receipt retains
`model_quality_established=false`, `learning_demonstrated=false`,
`independent_witness_verified=false`, `release_authorized=false` and
`test_split_evaluated=false`.

Run offline regression checks with:

```bash
python -m unittest discover -s tests -p test_collect_f4_local_baseline.py
```

The tests use a fake local Ollama client; neither local nor cloud inference is
run by CI. A genuine learning study still requires a larger sealed final set
with adequate family diversity, actual baseline prediction receipts,
independent task labels, preregistered confidence/utility criteria, matched
budgets, repeated seeds and explicitly authorized model work.
