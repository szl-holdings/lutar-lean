#!/usr/bin/env python3
"""Runtime models for the compiled locked-8 surface.

These functions refine the Lean statements into executable checks on each
statement's own domain. They do not make the Lean theorems into production
proofs. FIFO-with-retries, RS codecs, and Byzantine agreement remain outside
this module.

Domain discipline: the Lean statements quantify over ``Nat``,
``List (Nat × Nat)`` and ``List Nat``. An input outside the admitted runtime
domain raises :class:`LockedDomainError` (a ``ValueError`` subclass) instead
of returning a value that would read like a verdict. Iterable inputs are read
exactly once.
"""

from __future__ import annotations

import math
from typing import Iterable, Iterator, Sequence


class LockedDomainError(ValueError):
    """Input lies outside the domain of the Lean statement being refined."""


def _require_nat(x: object, what: str) -> int:
    """Admit a Lean ``Nat``: an exact ``int`` that is ``>= 0``.

    ``bool`` and other ``int`` subclasses (which may override ``__eq__`` or
    ``__lt__``) are rejected.
    """
    if type(x) is not int:
        raise LockedDomainError(
            f"{what} must be a Nat (exact int; bool and int subclasses are excluded), got {type(x).__name__}"
        )
    if x < 0:
        raise LockedDomainError(f"{what} must be >= 0")
    return x


def _materialize(xs: object, what: str) -> tuple[object, ...]:
    """Read an iterable exactly once into a tuple."""
    try:
        it = iter(xs)
    except TypeError:
        raise LockedDomainError(f"{what} must be a finite iterable, got {type(xs).__name__}") from None
    return tuple(it)


def _nat_list(xs: object, what: str) -> list[int]:
    """A Lean ``List Nat``: every element must be a Nat."""
    return [_require_nat(x, f"{what} element") for x in _materialize(xs, what)]


def _nat_edges(edges: object) -> tuple[tuple[int, int], ...]:
    """A Lean ``KhipuEdges = List (Nat × Nat)``, read exactly once.

    Each edge must be an exact ``tuple`` or ``list`` of length 2 whose
    components are Nats.
    """
    normalized = []
    for edge in _materialize(edges, "edges"):
        if (type(edge) is not tuple and type(edge) is not list) or len(edge) != 2:
            raise LockedDomainError(
                f"each edge must be an exact tuple or list (src, dst) of length 2, got {type(edge).__name__}"
            )
        normalized.append((_require_nat(edge[0], "edge src"), _require_nat(edge[1], "edge dst")))
    return tuple(normalized)


def _require_json_canonical(value: object) -> None:
    """Admit exactly None, bool, int, str, finite float, list and str-keyed dict.

    Types are checked exactly (no subclasses). The walk is iterative, so deep
    nesting needs no recursion; a container already checked is not walked
    again, and a true container cycle raises :class:`LockedDomainError`.
    """
    on_path: set[int] = set()
    done: set[int] = set()
    stack: list[tuple[int, Iterator[object]]] = []

    def visit(obj: object) -> None:
        kind = type(obj)
        if obj is None or kind is bool or kind is int or kind is str:
            return
        if kind is float:
            if not math.isfinite(obj):
                raise LockedDomainError("replay_eq admits only finite floats (NaN and infinities are excluded)")
            return
        if kind is list or kind is dict:
            oid = id(obj)
            if oid in on_path:
                raise LockedDomainError("replay_eq value contains a container cycle")
            if oid in done:
                return
            if kind is dict:
                for key in obj:
                    if type(key) is not str:
                        raise LockedDomainError(
                            f"replay_eq admits only dicts with exact str keys, got {type(key).__name__} key"
                        )
                children: Iterator[object] = iter(obj.values())
            else:
                children = iter(obj)
            on_path.add(oid)
            stack.append((oid, children))
            return
        raise LockedDomainError(f"replay_eq value outside the admitted JSON-canonical domain: {kind.__name__}")

    visit(value)
    while stack:
        oid, children = stack[-1]
        depth = len(stack)
        for child in children:
            visit(child)
            if len(stack) != depth:
                break
        else:
            stack.pop()
            on_path.discard(oid)
            done.add(oid)


def replay_eq(value: object) -> bool:
    """F1 compiled statement ``f x = f x``, on the admitted JSON-canonical domain.

    The admitted domain is None, bool, int, str, finite float, list and dict
    with str keys, all by exact type (tuples, sets, bytes, NaN, infinities and
    user classes are excluded); container cycles are rejected. On that domain
    ``value == value`` is always True. Out-of-domain values raise
    :class:`LockedDomainError` before any ``__eq__`` is called.

    This is a reflexive-equality check only. It is not a replay-hash or
    persistence guarantee.
    """
    _require_json_canonical(value)
    return value == value


def _backward_invariant_holds(edges: tuple[tuple[int, int], ...]) -> bool:
    return all(dst < src for src, dst in edges)


def _append_hypothesis_holds(k: int, new_edges: tuple[tuple[int, int], ...]) -> bool:
    return all(src == k and dst < k for src, dst in new_edges)


def khipu_backward_invariant(edges: Sequence[tuple[int, int]]) -> bool:
    """Lean ``KhipuBackwardInvariant``: every edge satisfies ``dst < src``.

    Edges must be ``Nat × Nat``; anything else raises
    :class:`LockedDomainError` rather than returning False, so a domain error
    is not reported as an invariant failure.
    """
    return _backward_invariant_holds(_nat_edges(edges))


def khipu_has_cycle_without_invariant(edges: Sequence[tuple[int, int]]) -> bool:
    """Reachability cycle search with no dst < src assumption.

    This is the counterexample oracle, so nodes may be any hashable values.
    It is an iterative three-colour depth-first search (grey = on the current
    path, black = completed and memoized): linear in nodes plus edges, with no
    recursion. Self-loops count as cycles.
    """
    graph: dict[object, list[object]] = {}
    for src, dst in edges:
        graph.setdefault(src, []).append(dst)

    grey, black = 1, 2
    colour: dict[object, int] = {}
    for root in graph:
        if root in colour:
            continue
        colour[root] = grey
        stack: list[tuple[object, Iterator[object]]] = [(root, iter(graph[root]))]
        while stack:
            node, successors = stack[-1]
            for nxt in successors:
                state = colour.get(nxt)
                if state == grey:
                    return True
                if state is None:
                    colour[nxt] = grey
                    stack.append((nxt, iter(graph.get(nxt, ()))))
                    break
            else:
                colour[node] = black
                stack.pop()
    return False


def khipu_backward_acyclic(edges: Sequence[tuple[int, int]]) -> bool:
    """F4 runtime check: under the backward-edge invariant there is no cycle.

    The edge iterable is read exactly once and must be ``Nat × Nat``
    (otherwise :class:`LockedDomainError`). An invariant violation raises
    ``ValueError("backward-edge invariant failed")``. The cycle search runs on
    the same normalized edges that passed the invariant.
    """
    normalized = _nat_edges(edges)
    if not _backward_invariant_holds(normalized):
        raise ValueError("backward-edge invariant failed")
    return not khipu_has_cycle_without_invariant(normalized)


def khipu_append_hypothesis(k: int, new_edges: Sequence[tuple[int, int]]) -> bool:
    """Runtime mirror of the Lean F4 append hypothesis ``hk``.

    Lean: ``hk : ∀ e ∈ newEdges, e.1 = k ∧ e.2 < k``. Exactly that is checked:
    every new edge has source ``k`` and a target strictly below ``k``. Lean does
    NOT require ``k`` to be fresh (absent from the existing edges) or the
    maximum node, and neither does this check. ``k`` and the edges must be
    Nats (otherwise :class:`LockedDomainError`).
    """
    nat_k = _require_nat(k, "k")
    return _append_hypothesis_holds(nat_k, _nat_edges(new_edges))


def khipu_append_preserves_acyclic(
    es: Sequence[tuple[int, int]],
    k: int,
    new_edges: Sequence[tuple[int, int]],
) -> bool:
    """Runtime check of the F4 append statement ``f4_khipu_dag_acyclic_preserved``.

    Requires both Lean hypotheses: the backward-edge invariant on ``es``
    (``ValueError("backward-edge invariant failed")`` otherwise) and ``hk`` on
    ``new_edges`` (``ValueError("append hypothesis hk failed")`` otherwise).
    Then runs the cycle search on ``es ++ new_edges`` and returns True when no
    cycle is found. Lean does NOT require ``k`` to be fresh or the maximum
    node, and neither does this check. Each iterable is read exactly once.
    """
    base = _nat_edges(es)
    nat_k = _require_nat(k, "k")
    appended = _nat_edges(new_edges)
    if not _backward_invariant_holds(base):
        raise ValueError("backward-edge invariant failed")
    if not _append_hypothesis_holds(nat_k, appended):
        raise ValueError("append hypothesis hk failed")
    return not khipu_has_cycle_without_invariant(base + appended)


def chaski_enqueue_all(queue: list[int], msgs: Iterable[int]) -> list[int]:
    """Lean ``chaskiEnqueueAll q xs = q ++ xs`` on ``List Nat``."""
    return _nat_list(queue, "queue") + _nat_list(msgs, "msgs")


def chaski_fifo_drain(msgs: Sequence[int]) -> list[int]:
    return chaski_enqueue_all([], msgs)


def chaski_retry_without_dedup(msgs: Sequence[int], retried: int) -> list[int]:
    """Counterexample for exactly-once: a retry re-enqueues an already-sent id."""
    return chaski_fifo_drain(list(msgs) + [retried])


def rs10_6_parity() -> int:
    return 10 - 6


def rs10_6_remaining(erasures: int) -> int:
    _require_nat(erasures, "erasures")
    if erasures > 4:
        raise ValueError("locked F18 hypothesis e ≤ 4 failed")
    return 10 - erasures


def seq_log_range(n: int) -> list[int]:
    _require_nat(n, "n")
    return list(range(n))
