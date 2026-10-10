# SPDX-License-Identifier: Apache-2.0
"""Exact rational counterexample to written self-repair conjecture SR-1.

The check applies the synchronous neighbor average written in
conjectures/SELF_REPAIR_CONVERGENCE.md. It does not call a repair endpoint
and it does not certify a Lean proof.
"""

from __future__ import annotations

from fractions import Fraction
from pathlib import Path


SPEC = Path(__file__).resolve().parents[1] / "conjectures" / "SELF_REPAIR_CONVERGENCE.md"


def live_edge_step(
    health_a: Fraction,
    health_b: Fraction,
    rate: Fraction,
) -> tuple[Fraction, Fraction]:
    """One synchronous step on the survivor edge a—b.

    Each node is the other's only live neighbor, so the written average is
    the other node's health. Values used here stay inside [0, 1], so the
    written clip does not change them.
    """
    next_a = health_a + rate * (health_b - health_a)
    next_b = health_b + rate * (health_a - health_b)
    return next_a, next_b


def test_half_rate_stops_at_nineteen_twentieths() -> None:
    health = (Fraction(1), Fraction(9, 10))
    rate = Fraction(1, 2)
    once = live_edge_step(*health, rate)
    assert once == (Fraction(19, 20), Fraction(19, 20))
    assert live_edge_step(*once, rate) == once
    assert once != (Fraction(1), Fraction(1))


def test_unit_rate_swaps_forever() -> None:
    health = (Fraction(1), Fraction(9, 10))
    rate = Fraction(1)
    swapped = live_edge_step(*health, rate)
    assert swapped == (Fraction(9, 10), Fraction(1))
    assert live_edge_step(*swapped, rate) == health


def test_spec_keeps_the_refutation_and_the_locked_count() -> None:
    text = SPEC.read_text(encoding="utf-8")
    assert "false as stated" in text
    assert "19/20" in text
    assert "9/10" in text
    assert "locked-proven stays exactly 8" in text
    assert "Conjecture 1" in text
    assert "UNKNOWN" in text
