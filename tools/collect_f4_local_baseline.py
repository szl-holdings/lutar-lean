#!/usr/bin/env python3
"""Local-only F4 validation baseline. No test rows, training or promotion."""
from __future__ import annotations

import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
import math
from pathlib import Path
import re
import sys
import urllib.request

BASE = "http://127.0.0.1:11434"
MAX_ROWS = 96
MAX_RESPONSE = 65536
NAME = re.compile(r"[A-Za-z0-9][A-Za-z0-9_.:/-]{0,159}\Z")
HASH = re.compile(r"[a-f0-9]{64}\Z")


def require(ok, reason):
    if not ok:
        raise ValueError(reason)


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"), allow_nan=False,
                      ensure_ascii=True).encode("utf-8")


def digest(value):
    return hashlib.sha256(value).hexdigest()


def strict_json(raw):
    def pairs(items):
        result = {}
        for key, value in items:
            require(key not in result, "duplicate_json_key")
            result[key] = value
        return result

    def reject_constant(_):
        raise ValueError("nonfinite_json_constant")

    def finite_float(value):
        parsed = float(value)
        require(math.isfinite(parsed), "nonfinite_json_number")
        return parsed

    return json.loads(raw, object_pairs_hook=pairs, parse_constant=reject_constant,
                      parse_float=finite_float)


def input_hashes(directory):
    """Exact input file hashes before and after inference; no new trust root."""
    result = {}
    for filename in ("manifest.json", "samples.jsonl", "prompts.jsonl"):
        path = directory / filename
        require(not path.is_symlink() and path.is_file(), "unsafe_fixture_file")
        size = path.stat().st_size
        require(0 < size <= 4_000_000, "fixture_file_size_out_of_bounds")
        data = path.read_bytes()
        require(len(data) == size, "fixture_file_modified_during_read")
        result[filename] = digest(data)
    return result


class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, req, fp, code, msg, headers, newurl):
        return None


class OllamaLoopback:
    """Fixed loopback, no proxies or redirects, single attempt per request."""
    def __init__(self):
        self.opener = urllib.request.build_opener(urllib.request.ProxyHandler({}),
                                                  urllib.request.HTTPHandler(),
                                                  NoRedirect())

    def query(self, path, body=None):
        require(path in ("/api/tags", "/api/generate"), "endpoint_not_allowlisted")
        payload = None if body is None else canonical(body)
        req = urllib.request.Request(BASE + path, data=payload,
              headers={"Accept": "application/json", "Content-Type": "application/json"},
              method="GET" if body is None else "POST")
        with self.opener.open(req, timeout=45) as response:
            require(response.status == 200, "ollama_status_not_200")
            require("application/json" in response.headers.get("Content-Type", ""),
                    "unexpected_content_type")
            raw = response.read(MAX_RESPONSE + 1)
        require(0 < len(raw) <= MAX_RESPONSE, "ollama_response_size_invalid")
        result = strict_json(raw)
        require(type(result) is dict, "ollama_response_not_object")
        return result

    def model_digest(self, tag):
        result = self.query("/api/tags")
        models = result.get("models")
        require(type(models) is list and len(models) <= 200, "tag_inventory_unavailable")
        matches = [x for x in models if type(x) is dict and x.get("name") == tag]
        require(len(matches) == 1, "model_tag_missing_or_ambiguous")
        value = matches[0].get("digest")
        require(type(value) is str and HASH.fullmatch(value) is not None,
                "model_digest_unavailable")
        return value

    def generate(self, tag, prompt, seed):
        result = self.query("/api/generate", {
            "model": tag, "prompt": prompt, "stream": False, "format": "json",
            "options": {"temperature": 0, "seed": seed, "num_predict": 128},
            "keep_alive": "30s",
        })
        require(result.get("model") == tag, "model_response_identity_mismatch")
        require(result.get("done") is True, "incomplete_generation")
        output = result.get("response")
        require(type(output) is str and len(output.encode("utf-8")) <= 16384,
                "invalid_generation_response")
        return output


def select_validation(rows, prompt_rows):
    """Only sample IDs and prompt inputs go to the model; labels never do."""
    require(type(rows) is list and type(prompt_rows) is list, "rows_required")
    by_id = {}
    for row in rows:
        require(type(row) is dict and
                {"sample_id", "split", "triplet_id", "input"} <= set(row),
                "invalid_fixture_sample")
        ident = row["sample_id"]
        require(type(ident) is str and ident not in by_id, "duplicate_fixture_identity")
        by_id[ident] = row
    prompts = {}
    for row in prompt_rows:
        require(type(row) is dict and set(row) == {"sample_id", "input"},
                "prompt_contains_unexpected_fields")
        ident = row["sample_id"]
        require(type(ident) is str and ident not in prompts and ident in by_id,
                "invalid_prompt_identity")
        require(canonical(row["input"]) == canonical(by_id[ident]["input"]),
                "prompt_fixture_disagreement")
        prompts[ident] = row
    require(set(prompts) == set(by_id), "prompt_set_incomplete")
    chosen = [row for row in rows if row["split"] == "validation"]
    require(3 <= len(chosen) <= MAX_ROWS, "validation_count_out_of_bounds")
    require(all(n == 3 for n in Counter(r["triplet_id"] for r in chosen).values()),
            "incomplete_validation_triplet")
    return [{"sample_id": i, "input": prompts[i]["input"]}
            for i in sorted(r["sample_id"] for r in chosen)]


def collect(rows, prompt_rows, manifest, model, expected_digest, seed, client):
    require(type(model) is str and NAME.fullmatch(model) is not None, "invalid_model_name")
    require(type(expected_digest) is str and HASH.fullmatch(expected_digest) is not None,
            "invalid_expected_model_digest")
    require(type(seed) is int and 0 <= seed < 2**31, "invalid_seed")
    require(type(manifest) is dict and type(manifest.get("prompt_instruction")) is str
            and 0 < len(manifest["prompt_instruction"]) < 2048, "invalid_instruction")
    selected = select_validation(rows, prompt_rows)
    require(client.model_digest(model) == expected_digest,
            "model_tag_digest_mismatch_before_generation")
    start = datetime.now(timezone.utc).isoformat(timespec="seconds")
    predictions = []
    for item in selected:
        prompt = manifest["prompt_instruction"] + "\nInput JSON: " + (
            canonical(item["input"]).decode("ascii")
        )
        output = client.generate(model, prompt, seed)
        predictions.append({"sample_id": item["sample_id"], "output": output})
    require(client.model_digest(model) == expected_digest,
            "model_tag_digest_mismatch_after_generation")
    raw = b"".join(canonical(row) + b"\n" for row in predictions)
    receipt = {
        "schema": "szl.f4-local-baseline/v1",
        "state": "MEASURED_UNQUALIFIED_LOCAL_PILOT",
        "dataset_provenance": "SYNTHETIC_EXPERIMENT_FIXTURE",
        "base_model_tag": model, "ollama_model_digest": expected_digest,
        "model_digest_authentication": "LOCAL_TAGS_SELF_REPORTED_ONLY",
        "generator_source": manifest.get("source"),
        "manifest_canonical_sha256": digest(canonical(manifest)),
        "dataset_files_sha256": {k: v["sha256"] for k, v in manifest["files"].items()},
        "prompt_selection_sha256": digest(canonical(selected)),
        "prediction_file_sha256": digest(raw),
        "prompt_instruction_sha256": digest(manifest["prompt_instruction"].encode()),
        "selected_split": "validation", "selected_samples": len(predictions),
        "seed": seed, "temperature": 0, "num_predict": 128, "request_retries": 0,
        "started_at": start, "completed_at": datetime.now(timezone.utc).isoformat(timespec="seconds"),
        "model_quality_established": False, "learning_demonstrated": False,
        "independent_witness_verified": False, "release_authorized": False,
        "test_split_evaluated": False,
        "execution_scope": "LOCAL_LOOPBACK_INFERENCE_ONLY",
    }
    return raw, receipt


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dataset", type=Path, required=True)
    parser.add_argument("--model", required=True)
    parser.add_argument("--model-digest", required=True)
    parser.add_argument("--seed", type=int, default=1234)
    parser.add_argument("--output-dir", type=Path, required=True)
    args = parser.parse_args(argv)
    try:
        require(not args.output_dir.exists(), "output_directory_exists")
        files_before = input_hashes(args.dataset)
        # Existing F4 fixture reader rechecks theorem-source pin, generator and oracle.
        from tools.evaluate_f4_boundary import load_fixture
        rows = load_fixture(args.dataset)
        manifest = strict_json((args.dataset / "manifest.json").read_bytes())
        prompt_rows = [strict_json(line) for line in
                       (args.dataset / "prompts.jsonl").read_bytes().splitlines()]
        raw, receipt = collect(rows, prompt_rows, manifest, args.model,
                               args.model_digest, args.seed, OllamaLoopback())
        require(input_hashes(args.dataset) == files_before,
                "fixture_changed_during_inference")
        receipt["fixture_files_sha256"] = files_before
        args.output_dir.mkdir(parents=False, exist_ok=False)
        with (args.output_dir / "predictions.jsonl").open("xb") as stream:
            stream.write(raw)
        with (args.output_dir / "provenance.json").open("xb") as stream:
            stream.write(canonical(receipt) + b"\n")
        print("LOCAL_BASELINE_RECORDED_UNQUALIFIED: validation only; no promotion")
    except (ValueError, OSError, UnicodeError, RuntimeError) as exc:
        print("LOCAL_BASELINE_UNAVAILABLE:" + type(exc).__name__, file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
