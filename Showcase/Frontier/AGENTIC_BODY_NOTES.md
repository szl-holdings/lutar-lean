# AgenticBodyWitness — NOTES

Kernel-checked, Mathlib-free, **zero-sorry** witness binding the four load-bearing
agentic-body claims of the **anatomy shell** (the agentic GPU as the MIND inside a
proven round-9 ORGAN body). Lives in its **own lib root** `AgenticBodyShowcase`
(`Showcase/Frontier/AgenticBodyWitness.lean`) so it does not collide with the open
`#239`/`#240` frontier branches and is **not** counted by
`.github/scripts/lean_numbers.py`. Outside `Lutar/`; says **nothing** about Λ
(Conjecture 1); the locked-proven set stays **exactly 8**.

## What is proved (8 theorems, 4 organ groups)

| # | Organ | Theorem(s) | Statement (discrete witness) | Axioms |
|---|---|---|---|---|
| 1 | IMMUNE ∘ BRAIN | `organ_pipeline_admit_iff` | proactive admitted iff IMMUNE pass **and** BRAIN admit (`immune && brain`) | none |
|   | (pipeline) | `pipeline_monotone` | gate monotone in each organ's verdict (better evidence never flips admit→reject) | `propext` |
| 2 | HEART | `heartbeat_additive` | receipt-beat count additive across two intervals; each ≤ joint (F19 `s₁≤s₁+s₂`) | none |
|   | (receipt bus) | `heartbeat_monotone` | running beat count over a stream is monotone-nondecreasing (no receipt un-counted) | `propext` |
| 3 | FLEET (EULER) | `fleet_tree_euler` | tree on `n` nodes, `n−1` edges ⇒ `V−E = 1` (Int, exact subtraction) | `propext`, `Quot.sound` |
|   | (connectivity) | `fleet_connected_lower_bound` | connected fleet needs `≥ n−1` edges (tree attains the floor) | `propext`, `Quot.sound` |
| 4 | NERVOUS | `drift_implies_honest_posture` | drift detected ⇒ `sovereign = false` (half-state cannot persist) | none |
|   | (self-heal) | `sovereign_iff_honest` | `sovereign = true` iff no-drift **and** local serves (honest sovereignty gate) | none |

Every theorem depends on **only Lean core axioms** (`propext`, `Quot.sound`) or
**none** — no Mathlib axiom, no declared axiom, no `sorry`, no `native_decide`.

## Proven round-9 organ formulas this composes (lutar-lean kernel)
- **BRAIN** `BrainBeliefUpdate` (PAC-Bayes McAllester) — the admit half of the pipeline.
- **IMMUNE** `ImmuneNeymanPearson` (deny-by-default most-powerful test) — the reject-first half.
- **HEART** `HeartReceiptSigma` (σ-algebra receipt bus) — the additive beat count; reuses the
  locked-8 F19 `s ≤ s+d` ledger shape (`Lutar/Puriq/Formulas/ProvedFormulas.lean`).
- **FLEET** `EulerFleetTopology` (round6/7 V−E+F invariant) — the `V−E=1` tree connectivity.
- **NERVOUS** `NervousShannonAlarm` (Λ-signed drift alarm) — drift ⇒ honest-posture self-heal.

## Honest simplifications (NEVER a faked proof)
Each organ's *full* formula is a Real-/measure-typed object proved in its round-9 module.
A bare-kernel witness cannot import `Real`/`exp`/`MeasureTheory` without **declared axioms**
(which a `#print axioms` would surface, proving nothing). So for each organ we extract the
**discrete invariant that carries the doctrine** — a Boolean gate, a Nat fold, an integer
Euler count — and prove THAT from core. Specifically:

- **Pipeline / NERVOUS**: proved over `Bool` by `decide` / case split — exact, total.
- **HEART**: proved over `Nat` by induction, each step the F19 `s ≤ s+d` shape.
- **FLEET**: stated in `Int` so `V−E` is **exact** (no `Nat` truncation); closed by `omega`.
  HONEST NOTE: the precondition `1 ≤ n` records fleet nonemptiness, but the `Int` identity
  `n−(n−1)=1` (and the `n−1 ≤ e` bound) close **unconditionally**, so `omega` does not
  consume the hypothesis. The binder is kept (prefixed `_`) to document the intended domain
  rather than dropped — we state plainly that it is not load-bearing for the arithmetic.

These are honest discrete *witnesses* of each organ's structural shape — not the physics,
not the measure-theoretic proofs.

## Live organ-endpoint mapping (read-only, real; off-box here)
- BRAIN — amaru `/api/amaru/v1/formulas` (`pac_bayes_mcallester`)
- IMMUNE — sentra `/api/sentra/v1/gates` (8 deny-by-default gates)
- HEART — amaru `/api/amaru/receipts` + sentra `/api/sentra/khipu/ledger`
- NERVOUS — amaru `/api/amaru/overwatch/snapshot`
- SKELETON (formal backing) — amaru `/api/amaru/v1/math/lean/theorems`

## Build + verify (reproducible)
```bash
# toolchain leanprover/lean4:v4.18.0 (lean-toolchain), Mathlib-free witness
lake build AgenticBodyShowcase          # → Built AgenticBodyWitness; Build completed successfully
# or, with no deps at all (the file imports nothing):
lean Showcase/Frontier/AgenticBodyWitness.lean   # prints the 8 #print axioms lines, exit 0
```
Observed `#print axioms` (build log): every theorem → `propext` / `Quot.sound` / "does not
depend on any axioms". **No `sorryAx`, no Mathlib axiom.**

## Doctrine floor
EXPERIMENTAL discrete witnesses; Λ = Conjecture 1 (untouched); locked-8 untouched; does NOT
import into `Lutar.lean`; reactive turns NEVER gated (the pipeline is proactive-only — reactive
bypasses it entirely); sovereign:true only when a local node serves (`sovereign_iff_honest`);
the half-state is formally precluded once drift fires (`drift_implies_honest_posture`).
DO NOT merge (keystone branch; founder/CI).
