#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Adversarial coverage for ``count_sorries.py`` — the sorry-gate honesty guard.

``count_sorries.py`` is the script the ``sorry-gate`` CI workflow runs
(``python3 count_sorries.py . 67``) to enforce the no-increase ``sorry``
baseline that keeps the locked-proof posture honest. Before this module it had
ZERO automated tests, so a regression in its comment-stripping, word-boundary
matching, ``.lean``-only scoping, or ``proposals/`` exclusion could silently let
a real ``sorry`` slip past the gate (bypassing the honesty guard) or over-count
a commented-out one.

These tests pin the guard's contract against adversarial inputs. They are
runnable both under pytest (``pytest tests/test_count_sorries.py``) and directly
(``python3 tests/test_count_sorries.py``).
"""

from __future__ import annotations

import importlib.util
import os
import sys
import tempfile

_TEST_DIR = os.path.dirname(os.path.abspath(__file__))
REPO_ROOT = os.path.dirname(_TEST_DIR)
_SCRIPT = os.path.join(REPO_ROOT, "count_sorries.py")


def _load():
    spec = importlib.util.spec_from_file_location("count_sorries", _SCRIPT)
    assert spec and spec.loader, f"cannot load guard from {_SCRIPT}"
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


cs = _load()


def _tree(files):
    """Materialise ``{relpath: content}`` into a fresh temp dir; return its root."""
    root = tempfile.mkdtemp(prefix="sorrygate_")
    for rel, txt in files.items():
        p = os.path.join(root, rel)
        os.makedirs(os.path.dirname(p), exist_ok=True)
        with open(p, "w", encoding="utf-8") as fh:
            fh.write(txt)
    return root


# ---- word-boundary matching -------------------------------------------------

def test_bare_sorry_is_counted():
    root = _tree({"A.lean": "theorem t : True := sorry\n"})
    assert cs.total_sorries(root) == 1


def test_sorryAx_is_not_counted():
    # `sorryAx` is a legitimate Lean term, not an open goal; the `\bsorry\b`
    # word boundary must exclude it, or the gate would over-count.
    root = _tree({"A.lean": "def x := sorryAx Bool false\n"})
    assert cs.total_sorries(root) == 0


def test_sorry_substring_words_not_counted():
    root = _tree({"A.lean": "def notsorry := 1\ndef sorrymatch := 2\n"})
    assert cs.total_sorries(root) == 0


def test_sorry_with_adjacent_punctuation_is_counted():
    root = _tree({"A.lean": "example := (sorry); by sorry\n"})
    assert cs.total_sorries(root) == 2


# ---- comment stripping ------------------------------------------------------

def test_line_comment_sorry_not_counted():
    root = _tree({"A.lean": "-- this sorry is only a line comment\n"})
    assert cs.total_sorries(root) == 0


def test_trailing_comment_keeps_real_sorry():
    root = _tree({"A.lean": "foo := sorry -- explain the sorry here\n"})
    assert cs.total_sorries(root) == 1


def test_block_comment_sorry_not_counted():
    root = _tree({"A.lean": "/- a sorry inside a block comment -/\n"})
    assert cs.total_sorries(root) == 0


def test_multiline_block_comment_sorry_not_counted():
    root = _tree({"A.lean": "/-\n  sorry\n  sorry\n-/\nreal := sorry\n"})
    assert cs.total_sorries(root) == 1


# ---- file-type + directory scoping -----------------------------------------

def test_non_lean_files_ignored():
    root = _tree({"notes.txt": "sorry sorry sorry\n", "s.py": "x = 'sorry'\n"})
    assert cs.total_sorries(root) == 0


def test_git_directory_skipped():
    root = _tree({".git/objects/x.lean": "sorry\n", "A.lean": "sorry\n"})
    assert cs.total_sorries(root) == 1


# ---- proposals/ exclusion (UNVERIFIED scratch mirror) ----------------------

def test_proposals_excluded_from_gated_total():
    root = _tree(
        {
            "Lutar/A.lean": "a := sorry\n",
            "proposals/M.lean": "m := sorry\nn := sorry\n",
        }
    )
    # Gated scan drops the proposals/ mirror so its sorries are not double-counted.
    assert cs.total_sorries(root) == 1
    # Transparency: include_excluded still reports every sorry (nothing hidden).
    allf = cs.scan(root, include_excluded=True)
    assert sum(allf.values()) == 3


def test_proposals_prefix_boundary_not_over_matched():
    # A top-level dir merely *starting* with 'proposals' (e.g. proposals_extra)
    # is NOT the excluded 'proposals' dir and must stay in the gated total.
    root = _tree({"proposals_extra/A.lean": "a := sorry\n"})
    assert cs.total_sorries(root) == 1


# ---- baseline gate ----------------------------------------------------------

def test_main_passes_when_equal_to_baseline():
    root = _tree({"A.lean": "sorry\nsorry\n"})
    assert cs.main(["count_sorries.py", root, "2"]) == 0


def test_main_fails_when_over_baseline():
    root = _tree({"A.lean": "sorry\nsorry\nsorry\n"})
    assert cs.main(["count_sorries.py", root, "2"]) == 1


def test_main_without_baseline_never_fails():
    root = _tree({"A.lean": "sorry\nsorry\n"})
    assert cs.main(["count_sorries.py", root]) == 0


if __name__ == "__main__":
    failures = 0
    for name, fn in sorted(globals().items()):
        if name.startswith("test_") and callable(fn):
            try:
                fn()
                print(f"PASS {name}")
            except AssertionError as exc:
                failures += 1
                print(f"FAIL {name}: {exc}")
    sys.exit(1 if failures else 0)
