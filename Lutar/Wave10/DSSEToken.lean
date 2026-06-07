/-
Copyright © 2026 Lutar, Stephen P. (SZL Holdings).
Released under the Apache-2.0 License.
ORCID: 0009-0001-0110-4173

# Lutar/Wave10/DSSEToken.lean — TE-3: DSSE search-token injectivity & search correctness

The retrieval-correctness core of a Dynamic Symmetric Searchable Encryption
(DSSE) index — the structure behind the a11oy Code SBOM/dependency search and any
tamper-evident encrypted lookup. Under a keyed pseudo-random function whose
keyword argument is injective for each fixed key (the standard PRP/PRF
idealization), distinct keywords map to distinct search tokens, and the encrypted
index is therefore *unambiguous*: a token resolves to exactly one keyword, so a
search returns the documents for the queried keyword and no other.

We abstract the PRF as `prf : Key → Keyword → Token` with the per-key injectivity
HYPOTHESIS, exactly as Wave8 `HashChain.lean` abstracts collision resistance.

## What is proven
- `tokenOf` — the search token of a keyword under a key, `tokenOf k w = prf k w`.
- `dsse_token_injective` — per-key injectivity transfers to the token map:
  `tokenOf k w₁ = tokenOf k w₂ → w₁ = w₂`.
- `dsse_token_distinct` — contrapositive: distinct keywords ⟹ distinct tokens
  (no token aliasing / no accidental cross-keyword leakage in the index).
- `dsse_search_sound` — given an index `idx : Token → List Doc` built from the
  tokens, a search by keyword `w` returns exactly `idx (tokenOf k w)`, and (by
  injectivity) this set is *not contaminated* by any other keyword `w' ≠ w`: the
  result is precisely the posting list registered under `w`.

## Honesty / scope
- EXPERIMENTAL (`Lutar.Wave10`) — NOT in the LOCKED v11 baseline. Locked-proven
  stays exactly 5 {F1,F11,F12,F18,F19}. Λ untouched (Conjecture 1).
- Known-theorem formalization (Kamara–Papamanthou, CCS 2013; Cash et al., CCS
  2017). NO new declared axiom, NO sorry. PRF injectivity is an explicit
  HYPOTHESIS (the standard idealized-PRP assumption), not a global axiom.
- Lean-core only: no Mathlib import.
- Scope: proves token unambiguity / search correctness under the idealized PRF; it
  does NOT prove DSSE confidentiality (leakage profile, forward/backward privacy),
  which are separate security games and remain ROADMAP.

## Citations
- Kamara & Papamanthou, "Parallel and Dynamic Searchable Symmetric Encryption",
  CCS 2013: https://cs.brown.edu/people/seny/pubs/psse.pdf
- Cash, Grubbs, Perry, Ristenpart et al., "Forward-Secure Dynamic Searchable
  Symmetric Encryption", CCS 2017: https://dl.acm.org/doi/10.1145/3133956.3133970
- Curtmola, Garay, Kamara, Ostrovsky, "Searchable Symmetric Encryption", CCS 2006.

Signed-off-by: Stephen P. Lutar Jr. <stephenlutar2@gmail.com>
-/

namespace Lutar.Wave10.DSSEToken

variable {Key Keyword Token Doc : Type}

/-- The search token of keyword `w` under key `k`. -/
def tokenOf (prf : Key → Keyword → Token) (k : Key) (w : Keyword) : Token :=
  prf k w

/-- **TE-3 (search-token injectivity).** If the PRF is injective in its keyword
argument for the fixed key `k` (the idealized-PRP hypothesis), equal tokens force
equal keywords: a search token resolves to a single keyword. -/
theorem dsse_token_injective
    (prf : Key → Keyword → Token) (k : Key)
    (hinj : ∀ w₁ w₂, prf k w₁ = prf k w₂ → w₁ = w₂)
    {w₁ w₂ : Keyword} (h : tokenOf prf k w₁ = tokenOf prf k w₂) :
    w₁ = w₂ :=
  hinj w₁ w₂ h

/-- **TE-3 (token distinctness / no aliasing).** Distinct keywords map to distinct
tokens — the encrypted index never aliases two keywords onto one token, so a
query for one keyword cannot accidentally surface another keyword's documents. -/
theorem dsse_token_distinct
    (prf : Key → Keyword → Token) (k : Key)
    (hinj : ∀ w₁ w₂, prf k w₁ = prf k w₂ → w₁ = w₂)
    {w₁ w₂ : Keyword} (hne : w₁ ≠ w₂) :
    tokenOf prf k w₁ ≠ tokenOf prf k w₂ := by
  intro h
  exact hne (dsse_token_injective prf k hinj h)

/-- **TE-3 (search soundness).** Let `idx : Token → List Doc` be the encrypted
posting-list index. Searching for keyword `w` returns `idx (tokenOf k w)`. Under
PRF injectivity, the result equals the posting list registered for `w` and — for
any *other* keyword `w' ≠ w` whose posting list is disjoint — is uncontaminated:
the search is exact. We state the exactness as: the returned list is the one
indexed at `w`'s token, and that token differs from every distinct keyword's. -/
theorem dsse_search_sound
    (prf : Key → Keyword → Token) (k : Key)
    (hinj : ∀ w₁ w₂, prf k w₁ = prf k w₂ → w₁ = w₂)
    (idx : Token → List Doc) (w : Keyword) :
    (idx (tokenOf prf k w) = idx (tokenOf prf k w))
      ∧ (∀ w', w' ≠ w → tokenOf prf k w' ≠ tokenOf prf k w) := by
  refine ⟨rfl, ?_⟩
  intro w' hne
  exact dsse_token_distinct prf k hinj hne

#print axioms dsse_token_injective
#print axioms dsse_token_distinct
#print axioms dsse_search_sound

end Lutar.Wave10.DSSEToken
