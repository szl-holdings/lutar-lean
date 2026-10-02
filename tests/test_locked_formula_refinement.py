#!/usr/bin/env python3
"""Runtime refinement checks for the compiled locked-8 surface.

These tests encode the original overclaim: F1 is reflexive equality, F18 is
parity arithmetic, F4 needs the backward-edge invariant, and F7 does not prove
exactly-once under retries.
"""

from __future__ import annotations

import os
import sys
import unittest

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, REPO_ROOT)

from tools.locked_formula_runtime import (  # noqa: E402
    chaski_fifo_drain,
    chaski_retry_without_dedup,
    khipu_backward_acyclic,
    khipu_has_cycle_without_invariant,
    replay_eq,
    rs10_6_parity,
    rs10_6_remaining,
    seq_log_range,
)


class LockedFormulaRefinementTests(unittest.TestCase):
    def test_f1_is_reflexive_equality(self):
        self.assertTrue(replay_eq(7))
        self.assertTrue(replay_eq("trace"))

    def test_f4_backward_edges_are_acyclic(self):
        self.assertTrue(khipu_backward_acyclic([(1, 0), (2, 1), (3, 0)]))

    def test_f4_forward_edge_can_cycle(self):
        cyclic = [(0, 1), (1, 0)]
        self.assertTrue(khipu_has_cycle_without_invariant(cyclic))
        with self.assertRaises(ValueError):
            khipu_backward_acyclic(cyclic)

    def test_f7_drain_equals_send_order(self):
        self.assertEqual(chaski_fifo_drain([10, 20, 30]), [10, 20, 30])

    def test_f7_retry_without_dedup_is_not_exactly_once(self):
        self.assertEqual(chaski_retry_without_dedup([10, 20], 10), [10, 20, 10])

    def test_f18_is_parity_count_not_a_codec(self):
        self.assertEqual(rs10_6_parity(), 4)
        self.assertEqual(rs10_6_remaining(4), 6)
        with self.assertRaises(ValueError):
            rs10_6_remaining(5)

    def test_f22_range_is_strictly_increasing(self):
        log = seq_log_range(4)
        self.assertEqual(log, [0, 1, 2, 3])
        self.assertLess(log[1], log[3])


if __name__ == "__main__":
    raise SystemExit(unittest.main())
