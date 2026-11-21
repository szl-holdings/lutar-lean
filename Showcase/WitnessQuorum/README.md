# Witness and quorum proofs (experimental)

This core-Lean pack checks two properties of linear receipt histories and a
finite quorum counting theorem. It is outside `Lutar/` and does not change the
locked theorem set or its counts.

| File | Result and limits |
| --- | --- |
| `ReceiptHistory.lean` | For histories of possibly different lengths, equal heads recomputed at the same checkpoint bind the receipts before it, using one injective link and seed. Equal signature **values** over `(length, head)` bind the full histories, transporting indices by the recovered length equality. This does not prevent signing two different values. |
| `HonestOverlap.lean` | Count Boolean flags over `Fin n`. The sum of two quorum sizes is at most the population plus the fault count plus the honest overlap count. If each size is at least `q`, faults are at most `f`, and `2*q > n+f`, the proof returns a shared nonfaulty index. For `n=3*f+1` and `q=2*f+1`, this instantiates Wave 10's `Intersecting` predicate. It is not a proof of protocol safety, liveness, or deployed behavior. |
| `BoundaryChecks.lean` | Concrete controls cover unbound links, unequal checkpoint lengths, and a pair of size-two quorums on three nodes whose only shared member is faulty. A separate control shows that injectivity gives different signature values for differing one-receipt histories. Guarded, fully qualified `#print axioms` commands pin the transitive footprints of all named theorems in the pack. |

The root `lake build` includes `WitnessQuorumShowcase` and retains its usual
Mathlib dependency. To build just these proofs offline, put the installed Lean
and Lake from the repository's `lean-toolchain` on `PATH`, then from the root run:

```sh
bash Showcase/WitnessQuorum/check-core.sh
```

The script copies the two original `Lutar` modules, these proofs, and the
toolchain pin into a fresh temporary package without external dependencies.
The exit trap removes that directory, including the generated manifest and
all compiler outputs, on success, failure, or interrupted execution (`INT` or `TERM`).
