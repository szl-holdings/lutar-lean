# SPDX-License-Identifier: Apache-2.0
"""Executable predicate for the SZL mixing-map conjecture (CF sample).

Map M : Z+ -> Z+
    M(n) = n // 2          if n is even
    M(n) = (3n + 1) // 2   if n is odd and n % 4 == 1
    M(n) = (n + 1) // 2     if n is odd and n % 4 == 3

Conjecture: for every n >= 1 there is a k with M^k(n) = 1.

This is a NON-standard variant: it mixes an accelerating rule (n % 4 == 1) with a
contracting rule (n % 4 == 3) on the odd residues, so it is NOT the classical
Collatz map. Whether every orbit reaches 1 is, to the authors' knowledge, open.

Soundness contract required by conjecture_grader.py:
    holds(n) returns False ONLY when it has CERTAIN evidence n violates the
    conjecture — concretely, when the orbit of n enters a cycle that does not
    contain 1 (detected exactly via a visited set). On an inconclusive bounded
    run (step/value cap hit without resolution) it returns True, i.e. it asserts
    NO counterexample. The grader therefore can never fabricate a witness from
    this predicate; a REFUTED verdict here is a real, reproducible cycle.
"""
from __future__ import annotations

FINITE = False  # the domain (all positive integers) is infinite / streaming.

# Bounded-run caps. Hitting a cap means "inconclusive for this n" -> assert
# nothing (return True), never a false counterexample.
STEP_CAP = 100_000
VALUE_CAP = 10 ** 18


def M(n: int) -> int:
    if n % 2 == 0:
        return n // 2
    if n % 4 == 1:
        return (3 * n + 1) // 2
    return (n + 1) // 2  # n % 4 == 3


def holds(n: int) -> bool:
    """True if the orbit of n reaches 1, or the run is inconclusive within caps.
    False ONLY if a non-1 cycle is detected (a certain counterexample)."""
    x = int(n)
    if x < 1:
        # Out-of-domain inputs are not the conjecture's concern; assert nothing.
        return True
    seen = set()
    steps = 0
    while True:
        if x == 1:
            return True
        if x in seen:
            return False  # entered a cycle that does not contain 1 -> REAL refutation
        seen.add(x)
        x = M(x)
        steps += 1
        if steps > STEP_CAP or x > VALUE_CAP:
            return True  # inconclusive: assert no counterexample (honest)


def domain():
    """Stream the positive integers in order (infinite generator)."""
    n = 1
    while True:
        yield n
        n += 1


def sample(rng):
    """Draw a random positive integer for the sampler solver (probes larger n)."""
    return rng.randint(1, 10 ** 7)
