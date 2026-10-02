#!/usr/bin/env python3
"""Runtime models for the compiled locked-8 surface.

These functions refine the Lean statements into executable checks. They do not
make the Lean theorems into production proofs. FIFO-with-retries, RS codecs,
and Byzantine agreement remain outside this module.
"""

from __future__ import annotations

from typing import Iterable, Sequence


def replay_eq(value: object) -> bool:
    """F1 compiled statement: a pure value equals itself."""
    return value == value


def khipu_backward_invariant(edges: Sequence[tuple[int, int]]) -> bool:
    return all(dst < src for src, dst in edges)


def khipu_has_cycle_without_invariant(edges: Sequence[tuple[int, int]]) -> bool:
    """Reachability cycle search with no dst < src assumption."""
    graph: dict[int, list[int]] = {}
    nodes: set[int] = set()
    for src, dst in edges:
        graph.setdefault(src, []).append(dst)
        nodes.add(src)
        nodes.add(dst)

    def dfs(node: int, stack: set[int]) -> bool:
        if node in stack:
            return True
        stack.add(node)
        for nxt in graph.get(node, []):
            if dfs(nxt, stack):
                return True
        stack.remove(node)
        return False

    return any(dfs(n, set()) for n in nodes)


def khipu_backward_acyclic(edges: Sequence[tuple[int, int]]) -> bool:
    if not khipu_backward_invariant(edges):
        raise ValueError("backward-edge invariant failed")
    return not khipu_has_cycle_without_invariant(edges)


def chaski_enqueue_all(queue: list[int], msgs: Iterable[int]) -> list[int]:
    return list(queue) + list(msgs)


def chaski_fifo_drain(msgs: Sequence[int]) -> list[int]:
    return chaski_enqueue_all([], msgs)


def chaski_retry_without_dedup(msgs: Sequence[int], retried: int) -> list[int]:
    """Counterexample for exactly-once: a retry re-enqueues an already-sent id."""
    return chaski_fifo_drain(list(msgs) + [retried])


def rs10_6_parity() -> int:
    return 10 - 6


def rs10_6_remaining(erasures: int) -> int:
    if erasures < 0:
        raise ValueError("erasures must be >= 0")
    if erasures > 4:
        raise ValueError("locked F18 hypothesis e ≤ 4 failed")
    return 10 - erasures


def seq_log_range(n: int) -> list[int]:
    if n < 0:
        raise ValueError("n must be >= 0")
    return list(range(n))
