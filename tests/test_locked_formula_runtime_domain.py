#!/usr/bin/env python3
"""Domain checks for the locked-formula runtime bridge.

Each Lean statement on the compiled locked-8 surface quantifies over a specific
type (``Nat``, ``List (Nat × Nat)``, ``List Nat``). The runtime bridge admits
only that domain and raises ``LockedDomainError`` (a ``ValueError`` subclass)
outside it, instead of returning a value that reads like a verdict.

These are software checks of the Python runtime. They do not extend or replace
the Lean statements. ``tests/test_locked_formula_refinement.py`` stays the
regression floor for the original vectors.
"""

from __future__ import annotations

import enum
import math
import os
import random
import sys
import time
import unittest
from collections import namedtuple
from decimal import Decimal

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, REPO_ROOT)

from tools.locked_formula_runtime import (  # noqa: E402
    LockedDomainError,
    chaski_enqueue_all,
    chaski_fifo_drain,
    chaski_retry_without_dedup,
    khipu_append_hypothesis,
    khipu_append_preserves_acyclic,
    khipu_backward_acyclic,
    khipu_backward_invariant,
    khipu_has_cycle_without_invariant,
    replay_eq,
    rs10_6_parity,
    rs10_6_remaining,
    seq_log_range,
)


class _CustomEq:
    def __eq__(self, other: object) -> bool:
        return False

    __hash__ = object.__hash__


class _RaisingEq:
    def __eq__(self, other: object) -> bool:
        raise RuntimeError("__eq__ must not be reached")

    __hash__ = object.__hash__


class _ArrayLikeEq:
    def __eq__(self, other: object) -> object:
        return [True, True]

    __hash__ = object.__hash__


class _AlwaysLess:
    def __lt__(self, other: object) -> bool:
        return True

    __hash__ = object.__hash__


class _SneakyInt(int):
    def __lt__(self, other: object) -> bool:
        return True

    __hash__ = int.__hash__


class _SneakyStr(str):
    pass


class _Colour(enum.IntEnum):
    RED = 1


_Edge = namedtuple("_Edge", "src dst")


class _CountingIterable:
    """An edge iterable that records how many times it is iterated."""

    def __init__(self, edges: list[tuple[int, int]]) -> None:
        self._edges = edges
        self.iterations = 0

    def __iter__(self):
        self.iterations += 1
        return iter(self._edges)


def _reference_has_cycle(edges: list[tuple[object, object]]) -> bool:
    """The pre-hardening recursive cycle search, kept as a small-graph oracle."""
    graph: dict[object, list[object]] = {}
    nodes: set[object] = set()
    for src, dst in edges:
        graph.setdefault(src, []).append(dst)
        nodes.add(src)
        nodes.add(dst)

    def dfs(node: object, stack: set[object]) -> bool:
        if node in stack:
            return True
        stack.add(node)
        for nxt in graph.get(node, []):
            if dfs(nxt, stack):
                return True
        stack.remove(node)
        return False

    return any(dfs(n, set()) for n in nodes)


def _layered_backward_dag(width: int, depth: int) -> list[tuple[int, int]]:
    """Every node in layer ``l + 1`` points to every node in layer ``l``."""
    edges = []
    for layer in range(depth):
        for i in range(width):
            src = (layer + 1) * width + i
            for j in range(width):
                edges.append((src, layer * width + j))
    return edges


class LockedDomainErrorTests(unittest.TestCase):
    def test_domain_error_is_a_value_error(self):
        self.assertTrue(issubclass(LockedDomainError, ValueError))
        with self.assertRaises(ValueError):
            replay_eq(float("nan"))


class ReplayEqDomainTests(unittest.TestCase):
    """F1: ``f x = f x`` is admitted only on the JSON-canonical domain."""

    def test_admitted_json_canonical_values_are_reflexive(self):
        shared = [1, "a"]
        admitted = [
            None,
            True,
            False,
            0,
            -5,
            2**100,
            "",
            "trace",
            1.5,
            -0.0,
            [],
            {},
            [1, "a", None, [2.5, {"k": [True, None]}]],
            {"outer": {"inner": [1, 2, 3]}},
            [shared, shared],
            {"a": shared, "b": shared},
        ]
        for value in admitted:
            with self.subTest(value=value):
                self.assertIs(replay_eq(value), True)

    def test_deep_nesting_needs_no_recursion(self):
        value: list[object] = []
        for _ in range(20_000):
            value = [value]
        self.assertIs(replay_eq(value), True)

    def test_shared_substructure_is_walked_once(self):
        # 2**60 paths, 61 distinct lists: only a memoized walk finishes.
        value: list[object] = []
        for _ in range(60):
            value = [value, value]
        start = time.perf_counter()
        self.assertIs(replay_eq(value), True)
        self.assertLess(time.perf_counter() - start, 2.0)

    def test_out_of_domain_values_fail_closed(self):
        rejected = {
            "nan": float("nan"),
            "inf": math.inf,
            "-inf": -math.inf,
            "nested nan": [float("nan")],
            "nan dict value": {"x": float("nan")},
            "tuple": (1, 2),
            "tuple in list": [(1, 2)],
            "set": {1, 2},
            "frozenset": frozenset({1}),
            "bytes": b"x",
            "bytearray": bytearray(b"x"),
            "complex": 1j,
            "decimal": Decimal("1.5"),
            "int key": {1: "a"},
            "tuple key": {(1, 2): "a"},
            "str subclass key": {_SneakyStr("k"): 1},
            "int subclass": _SneakyInt(3),
            "str subclass": _SneakyStr("trace"),
            "int enum": _Colour.RED,
            "custom eq": _CustomEq(),
            "raising eq": _RaisingEq(),
            "array-like eq": _ArrayLikeEq(),
            "custom eq nested": {"k": [_CustomEq()]},
            "function": len,
        }
        for label, value in rejected.items():
            with self.subTest(case=label):
                with self.assertRaises(LockedDomainError):
                    replay_eq(value)

    def test_container_cycles_fail_closed(self):
        self_list: list[object] = []
        self_list.append(self_list)

        self_dict: dict[str, object] = {}
        self_dict["me"] = self_dict

        a: list[object] = []
        b: list[object] = [a]
        a.append(b)

        mixed: dict[str, object] = {"items": []}
        mixed["items"].append({"back": mixed})

        for label, value in {
            "self list": self_list,
            "self dict": self_dict,
            "mutual lists": a,
            "dict-list-dict": mixed,
        }.items():
            with self.subTest(case=label):
                with self.assertRaises(LockedDomainError):
                    replay_eq(value)


class KhipuNatEdgeDomainTests(unittest.TestCase):
    """F4: edges must be ``Nat × Nat``; the edge iterable is read once."""

    def test_list_edges_are_accepted(self):
        self.assertTrue(khipu_backward_invariant([[1, 0]]))
        self.assertTrue(khipu_backward_acyclic([[1, 0], (2, 1)]))
        self.assertTrue(khipu_backward_acyclic([]))

    def test_nat_but_forward_edge_is_an_invariant_failure_not_a_domain_error(self):
        self.assertFalse(khipu_backward_invariant([(0, 1)]))
        with self.assertRaises(ValueError) as ctx:
            khipu_backward_acyclic([(0, 1)])
        self.assertNotIsInstance(ctx.exception, LockedDomainError)

    def test_non_nat_edges_fail_closed(self):
        rejected = {
            "negative": [(-1, -2)],
            "bool": [(True, False)],
            "float": [(1.5, 0.5)],
            "float dst": [(2, 1.0)],
            "str": [("b", "a")],
            "int subclass": [(_SneakyInt(1), 0)],
            "always-less": [(_AlwaysLess(), _AlwaysLess())],
            "one-element edge": [(1,)],
            "three-element edge": [(1, 0, 5)],
            "str edge": ["10"],
            "dict edge": [{1: 0}],
            "namedtuple edge": [_Edge(1, 0)],
        }
        for label, edges in rejected.items():
            with self.subTest(case=label):
                with self.assertRaises(LockedDomainError):
                    khipu_backward_invariant(edges)
                with self.assertRaises(LockedDomainError):
                    khipu_backward_acyclic(edges)

    def test_non_iterable_edges_fail_closed(self):
        with self.assertRaises(LockedDomainError):
            khipu_backward_acyclic(5)

    def test_one_shot_iterator_is_accepted(self):
        self.assertTrue(khipu_backward_acyclic(iter([(1, 0), (2, 1)])))
        self.assertTrue(khipu_backward_invariant(iter([(1, 0), (2, 1)])))

    def test_custom_lt_cycle_via_iterator_is_not_reported_acyclic(self):
        # Regression: the invariant check used to consume a one-shot iterator,
        # so the cycle search saw an empty graph and returned "acyclic".
        a, b = _AlwaysLess(), _AlwaysLess()
        cyclic = [(a, b), (b, a)]
        with self.assertRaises(LockedDomainError):
            khipu_backward_acyclic(iter(cyclic))
        with self.assertRaises(LockedDomainError):
            khipu_backward_acyclic(cyclic)

    def test_edge_iterable_is_iterated_exactly_once(self):
        edges = _CountingIterable([(1, 0), (2, 1), (3, 0)])
        self.assertTrue(khipu_backward_acyclic(edges))
        self.assertEqual(edges.iterations, 1)


class KhipuAppendHypothesisTests(unittest.TestCase):
    """F4 append: mirror Lean ``hk : ∀ e ∈ newEdges, e.1 = k ∧ e.2 < k``."""

    def test_non_fresh_non_max_k_is_accepted_as_in_lean(self):
        es = [(5, 2), (3, 0)]
        # k = 3 already occurs in es and is below the max node 5.
        self.assertTrue(khipu_append_hypothesis(3, [(3, 1)]))
        self.assertTrue(khipu_append_preserves_acyclic(es, 3, [(3, 1)]))

    def test_fresh_max_k_is_accepted(self):
        self.assertTrue(khipu_append_preserves_acyclic([(1, 0), (2, 1)], 3, [(3, 0), (3, 2)]))

    def test_empty_new_edges_satisfy_hk_vacuously(self):
        self.assertTrue(khipu_append_hypothesis(0, []))
        self.assertTrue(khipu_append_preserves_acyclic([(1, 0)], 0, []))

    def test_hk_rejects_wrong_source_or_non_backward_target(self):
        self.assertFalse(khipu_append_hypothesis(3, [(4, 1)]))
        self.assertFalse(khipu_append_hypothesis(3, [(3, 3)]))
        self.assertFalse(khipu_append_hypothesis(3, [(3, 5)]))
        self.assertFalse(khipu_append_hypothesis(3, [(3, 1), (2, 1)]))

    def test_append_requires_both_lean_hypotheses(self):
        with self.assertRaises(ValueError) as hk_ctx:
            khipu_append_preserves_acyclic([(1, 0)], 3, [(4, 1)])
        self.assertNotIsInstance(hk_ctx.exception, LockedDomainError)
        with self.assertRaises(ValueError) as inv_ctx:
            khipu_append_preserves_acyclic([(0, 1)], 3, [(3, 1)])
        self.assertNotIsInstance(inv_ctx.exception, LockedDomainError)

    def test_append_domain_is_nat(self):
        for k in (True, -1, 2.0, "3", _SneakyInt(3)):
            with self.subTest(k=k):
                with self.assertRaises(LockedDomainError):
                    khipu_append_hypothesis(k, [])
                with self.assertRaises(LockedDomainError):
                    khipu_append_preserves_acyclic([], k, [])
        with self.assertRaises(LockedDomainError):
            khipu_append_hypothesis(3, [(3, -1)])
        with self.assertRaises(LockedDomainError):
            khipu_append_preserves_acyclic([(1, 0.0)], 3, [(3, 1)])

    def test_append_reads_one_shot_iterators(self):
        self.assertTrue(khipu_append_preserves_acyclic(iter([(1, 0)]), 2, iter([(2, 1), (2, 0)])))


class KhipuCycleSearchTests(unittest.TestCase):
    """The cycle search is iterative and memoized; semantics are unchanged."""

    def test_long_backward_chain_needs_no_recursion(self):
        chain = [(i + 1, i) for i in range(5000)]
        self.assertTrue(khipu_backward_acyclic(chain))

    def test_long_forward_chain_has_no_cycle(self):
        chain = [(i, i + 1) for i in range(100_000)]
        self.assertFalse(khipu_has_cycle_without_invariant(chain))

    def test_long_cycle_is_detected(self):
        loop = [(i, i + 1) for i in range(5000)] + [(5000, 0)]
        self.assertTrue(khipu_has_cycle_without_invariant(loop))

    def test_self_loop_is_a_cycle(self):
        self.assertTrue(khipu_has_cycle_without_invariant([(3, 3)]))
        with self.assertRaises(ValueError):
            khipu_backward_acyclic([(3, 3)])

    def test_layered_dag_is_linear_not_exponential(self):
        edges = _layered_backward_dag(width=3, depth=200)
        start = time.perf_counter()
        self.assertTrue(khipu_backward_acyclic(edges))
        self.assertLess(time.perf_counter() - start, 2.0)

    def test_generic_hashable_nodes_are_kept(self):
        self.assertTrue(khipu_has_cycle_without_invariant([("a", "b"), ("b", "a")]))
        self.assertFalse(khipu_has_cycle_without_invariant([("a", "b"), ("b", "c")]))

    def test_agrees_with_reference_on_random_small_graphs(self):
        rng = random.Random(20261006)
        for _ in range(3000):
            n_nodes = rng.randint(1, 7)
            n_edges = rng.randint(0, 12)
            edges = [(rng.randrange(n_nodes), rng.randrange(n_nodes)) for _ in range(n_edges)]
            with self.subTest(edges=edges):
                self.assertEqual(
                    khipu_has_cycle_without_invariant(edges),
                    _reference_has_cycle(edges),
                )


class NatHelperDomainTests(unittest.TestCase):
    """F7, F18, F22 helpers admit only ``Nat`` inputs."""

    def test_existing_vectors_are_unchanged(self):
        self.assertEqual(rs10_6_parity(), 4)
        self.assertEqual(rs10_6_remaining(0), 10)
        self.assertEqual(rs10_6_remaining(4), 6)
        self.assertEqual(seq_log_range(0), [])
        self.assertEqual(seq_log_range(4), [0, 1, 2, 3])
        self.assertEqual(chaski_fifo_drain([10, 20, 30]), [10, 20, 30])
        self.assertEqual(chaski_retry_without_dedup([10, 20], 10), [10, 20, 10])
        self.assertEqual(chaski_enqueue_all([1], [2, 3]), [1, 2, 3])

    def test_f18_hypothesis_failure_is_not_a_domain_error(self):
        with self.assertRaises(ValueError) as ctx:
            rs10_6_remaining(5)
        self.assertNotIsInstance(ctx.exception, LockedDomainError)

    def test_negative_inputs_keep_their_messages(self):
        with self.assertRaisesRegex(LockedDomainError, r"^erasures must be >= 0$"):
            rs10_6_remaining(-1)
        with self.assertRaisesRegex(LockedDomainError, r"^n must be >= 0$"):
            seq_log_range(-1)

    def test_non_nat_scalars_fail_closed(self):
        for value in (2.5, True, False, "3", None, _SneakyInt(2)):
            with self.subTest(value=value):
                with self.assertRaises(LockedDomainError):
                    rs10_6_remaining(value)
                with self.assertRaises(LockedDomainError):
                    seq_log_range(value)

    def test_chaski_elements_must_be_nat(self):
        for msgs in ([-1], ["x"], [None], [True], [1.0], [_SneakyInt(1)]):
            with self.subTest(msgs=msgs):
                with self.assertRaises(LockedDomainError):
                    chaski_fifo_drain(msgs)
        with self.assertRaises(LockedDomainError):
            chaski_enqueue_all([-1], [2])
        with self.assertRaises(LockedDomainError):
            chaski_retry_without_dedup([10, 20], True)
        with self.assertRaises(LockedDomainError):
            chaski_fifo_drain(7)

    def test_chaski_reads_one_shot_iterators(self):
        self.assertEqual(chaski_fifo_drain(iter([1, 2])), [1, 2])
        self.assertEqual(chaski_enqueue_all(iter([1]), iter([2])), [1, 2])


if __name__ == "__main__":
    raise SystemExit(unittest.main())
