/-
Copyright © 2026 Lutar, Stephen P. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

# Lutar/Wave11.lean — Wave11 FRONTIER pack aggregator

EXPERIMENTAL / ADDITIVE frontier theorem pack (CF-1, CF-2, CF-3, CF-5).
Aggregates the Wave11 modules so `lake build Lutar.Wave11` exercises them all
and prints their per-theorem `#print axioms` lines.

NOT imported into `Lutar.lean` — the LOCKED v11 baseline (749/14/163 @
c7c0ba17, locked-proven EXACTLY 5 {F1,F11,F12,F18,F19}) is untouched.
Λ remains Conjecture 1.

## Members
- `Lutar.Wave11.GraphAutoDistInvariant` — CF-1 (Λ-graph automorphism / iso
  distance + P-GNN position-encoding equivariance; also closes the two
  PositionAware `:= True` stubs via `Lutar.PositionAware`).
- `Lutar.Wave11.OuroKVCacheSlots` — CF-2 (looped-LM KV-cache slot-indexing
  bijection + decode-equivalence + undersized-cache collision).
- `Lutar.Wave11.OuroLoopEarlyExit` — CF-3 (loop fixed-point uniqueness +
  kᵗ/(1−k) early-exit error envelope).
- `Lutar.Wave11.ImmuneNeymanPearsonOpt` — CF-5 (discrete Neyman-Pearson
  most-powerful immune egress gate).
- `Lutar.Wave11.AxiomDisclosure` — kernel-only meta-ledger + locked-5 reassert.

Signed-off-by: Stephen P. Lutar Jr. <stephenlutar2@gmail.com>
Co-Authored-By: Perplexity Computer Agent <agent@perplexity.ai>
-/

import Lutar.Wave11.GraphAutoDistInvariant
import Lutar.Wave11.OuroKVCacheSlots
import Lutar.Wave11.OuroLoopEarlyExit
import Lutar.Wave11.ImmuneNeymanPearsonOpt
import Lutar.Wave11.AxiomDisclosure
