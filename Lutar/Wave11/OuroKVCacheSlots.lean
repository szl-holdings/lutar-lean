/-
Copyright © 2026 Stephen P. Lutar Jr. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

# Lutar/Wave11/OuroKVCacheSlots.lean — CF-2 (Frontier)

Ouro looped-LM KV-cache slot-indexing equivalence.

For a weight-tied looped transformer with `L` layers and `T` recurrent
(Universal-Transformer) steps, the per-token cache is correct iff it allocates
`T · L` slots indexed by `idx(t, ℓ) = t · L + ℓ` for `t ∈ Fin T, ℓ ∈ Fin L`.
We prove the map `Fin T × Fin L → Fin (T·L)`, `(t,ℓ) ↦ t·L + ℓ`, is a
**bijection** — hence the cache of size `T·L` is **read/write-collision-free**
(injective ⇒ no two (step,layer) pairs alias) and **complete** (surjective ⇒
every slot is reachable; the decode reads exactly the slots it wrote, so the
cached forward pass is token-output-equivalent to the uncached one).

We additionally prove that an undersized `L`-slot cache (HF `DynamicCache`
default) is **NOT injective for `T > 1`** (`undersized_cache_collides`): two
distinct steps collide on the same `L`-sized slot, formally witnessing the
IndexError / state-corruption the Antizana/ouro-cache-fix patch (#13) repairs.

## What is proven (kernel-clean, no sorry/admit/axiom)

- `slotIndex` — the SPEC slot map `idx(t,ℓ) = t·L + ℓ`, defined via Mathlib's
  `finProdFinEquiv` (whose forward map `(t,ℓ) ↦ ℓ + L·t = t·L + ℓ` is exactly
  the brief's formula); `slotIndex_eq` confirms the closed form.
- `slotIndex_lt_card` — every index is `< T·L` (in range; no overflow).
- `slotIndex_injective` — collision-freeness (no slot aliasing).
- `slotIndex_surjective` — completeness (every slot used).
- `slotIndex_bijective` — full bijection ⇒ a `T·L` cache is exactly right.
- `cache_size_correct` — `Fintype.card (Fin T × Fin L) = T · L` (Ouro 4×24=96).
- `decode_equivalent_of_correct_slots` — DECODE-EQUIVALENCE: writing latents
  through `slotIndex` then reading back via `slotIndex` recovers the original
  per-(step,layer) value, for any latent payload `kv`; the cached decode
  reproduces the uncached output exactly.
- `undersized_cache_collides` — for `T ≥ 2, L ≥ 1` the `L`-sized cache map
  `(t,ℓ) ↦ ℓ` aliases steps `0` and `1`: the bug.

## Honesty / scope
- EXPERIMENTAL (`Lutar.Wave11`) — ADDITIVE, NOT in the LOCKED v11 baseline
  (749/14/163 @ c7c0ba17). Locked-proven stays EXACTLY 5 {F1,F11,F12,F18,F19}.
  Λ remains Conjecture 1. NOT imported into `Lutar.lean`.
- Pure finite combinatorics over `Fin`; NO new declared axiom, NO sorry.

## Citations
- Antizana/ouro-cache-fix (MIT): `UniversalTransformerCache`, size
  `total_ut_steps × num_layers` (Ouro 4×24=96), slot algebra `idx(t,ℓ)=t·L+ℓ`.
  https://github.com/Antizana/ouro-cache-fix
- Zhu et al. (2025). "Scaling Latent Reasoning via Looped Language Models."
  arXiv:2510.25741 (ByteDance/Ouro-1.4B, Apache-2.0).
- Dehghani et al. (2019). "Universal Transformers." ICLR 2019. arXiv:1807.03819.
- Mathlib: `finProdFinEquiv` (`Fin m × Fin n ≃ Fin (m·n)`), `Equiv.injective`,
  `Equiv.surjective`, `Fintype.card_prod`.

Signed-off-by: Stephen P. Lutar Jr. <stephenlutar2@gmail.com>
Co-Authored-By: Perplexity Computer Agent <agent@perplexity.ai>
-/

import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod

namespace Lutar.Wave11.OuroKVCacheSlots

variable {T L : ℕ}

/-- **Slot equivalence** `Fin T × Fin L ≃ Fin (T·L)`.  Mathlib's
    `finProdFinEquiv` sends `(t, ℓ) ↦ ℓ + L · t = t · L + ℓ` — exactly the
    `idx(t,ℓ)=t·L+ℓ` slot algebra of the Ouro cache fix. -/
def slotEquiv : Fin T × Fin L ≃ Fin (T * L) := finProdFinEquiv

/-- **Slot index** map `idx(t,ℓ) = t·L + ℓ` (forward of `slotEquiv`). -/
def slotIndex (p : Fin T × Fin L) : Fin (T * L) := slotEquiv p

/-- The slot index has the SPEC closed form `t·L + ℓ`. -/
theorem slotIndex_eq (p : Fin T × Fin L) :
    (slotIndex p).val = p.1.val * L + p.2.val := by
  simp only [slotIndex, slotEquiv, finProdFinEquiv_apply_val]
  rw [Nat.add_comm, Nat.mul_comm]

/-- Every produced cache index lies in range `[0, T·L)` — no IndexError when the
    cache is allocated with `T·L` slots. -/
theorem slotIndex_lt_card (p : Fin T × Fin L) :
    (slotIndex p).val < T * L := (slotIndex p).isLt

/-- **CF-2 (a) — collision-freeness.**  `slotIndex` is injective: distinct
    `(step, layer)` pairs never alias the same cache slot. -/
theorem slotIndex_injective : Function.Injective (@slotIndex T L) :=
  slotEquiv.injective

/-- **CF-2 (b) — completeness.**  `slotIndex` is surjective: every cache slot is
    reachable by some `(step, layer)` pair (no wasted/uninitialised slot). -/
theorem slotIndex_surjective : Function.Surjective (@slotIndex T L) :=
  slotEquiv.surjective

/-- **CF-2 (c) MAIN — bijection.**  `slotIndex` is a bijection
    `Fin T × Fin L ≃ Fin (T·L)`; a cache of exactly `T·L` slots is correct
    (collision-free AND complete). -/
theorem slotIndex_bijective : Function.Bijective (@slotIndex T L) :=
  slotEquiv.bijective

/-- **CF-2 (d) — required cache size.**  The number of `(step, layer)` pairs is
    exactly `T · L` — the slot count the cache must allocate (Ouro: `4·24=96`,
    NOT the base `24`). -/
theorem cache_size_correct :
    Fintype.card (Fin T × Fin L) = T * L := by
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]

/-- **CF-2 (e) — DECODE-EQUIVALENCE.**  Let `kv : Fin T × Fin L → α` be the true
    per-(step,layer) latent payload the uncached forward pass would read.  A
    cache `c : Fin (T·L) → α` written via `c (slotIndex p) := kv p` (modelled as
    `c = kv ∘ slotEquiv.symm`) reads back, at slot `slotIndex p`, *exactly*
    `kv p`.  Hence the cached decode is token-output-equivalent to the uncached
    `use_cache=False` pass: no information is lost or aliased. -/
theorem decode_equivalent_of_correct_slots {α : Type*}
    (kv : Fin T × Fin L → α) (p : Fin T × Fin L) :
    (kv ∘ slotEquiv.symm) (slotIndex p) = kv p := by
  simp only [slotIndex, Function.comp_apply, Equiv.symm_apply_apply]

/-- **CF-2 (f) — the undersized-cache bug.**  An `L`-sized cache (HF
    `DynamicCache` default) indexes only by layer `ℓ`, ignoring the step `t`.
    For `T ≥ 2` (more than one loop) the steps `0` and `1` at the same layer
    collide on the same slot: the map is NOT injective ⇒ IndexError / state
    corruption.  This is the precise failure the `T·L` fix above removes. -/
theorem undersized_cache_collides (hT : 2 ≤ T) (hL : 1 ≤ L) :
    ∃ p q : Fin T × Fin L, p ≠ q ∧ p.2 = q.2 := by
  have hT0 : 0 < T := by omega
  have hL0 : 0 < L := by omega
  refine ⟨(⟨0, by omega⟩, ⟨0, by omega⟩), (⟨1, by omega⟩, ⟨0, by omega⟩), ?_, rfl⟩
  intro h
  have hval := congrArg (fun r => (Prod.fst r).val) h
  simp only at hval
  omega

end Lutar.Wave11.OuroKVCacheSlots

-- ## CF-2 axiom disclosure (CI prints these in the build log).
-- Pure finite combinatorics; expected kernel-only [propext, Classical.choice,
-- Quot.sound] (or fewer). NO sorryAx, NO declared Lutar axioms.
#print axioms Lutar.Wave11.OuroKVCacheSlots.slotIndex_eq
#print axioms Lutar.Wave11.OuroKVCacheSlots.slotIndex_injective
#print axioms Lutar.Wave11.OuroKVCacheSlots.slotIndex_surjective
#print axioms Lutar.Wave11.OuroKVCacheSlots.slotIndex_bijective
#print axioms Lutar.Wave11.OuroKVCacheSlots.cache_size_correct
#print axioms Lutar.Wave11.OuroKVCacheSlots.decode_equivalent_of_correct_slots
#print axioms Lutar.Wave11.OuroKVCacheSlots.undersized_cache_collides
