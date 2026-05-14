/-
  lakefile.lean snippet — new Lean 4 files for lutar-lean
  Track 7: Prisca-GraphRAG v2 + RAG Receipt obligations

  Repo:    lutar-lean/lakefile.lean  (additions only — append to existing file)
  Author:  Stephen P. Lutar Jr. <stephen@szlholdings.com>
  Doctrine: v2 binding

  INSTRUCTIONS FOR INTEGRATOR:
    1. Add the `lean_lib Lutar` target below if it does not already exist.
    2. If `lean_lib Lutar` already exists, add the two new files to the
       existing `globs` list: `Lutar.RAGReceipt` and `Lutar.GraphHop`.
    3. The new files depend on Mathlib; confirm `require mathlib` is present.
    4. Run `lake build Lutar.RAGReceipt Lutar.GraphHop` to verify typecheck.

  Expected output (no errors, sorry warnings only for TODO items):
    warning: declaration uses 'sorry': traversal_acyclic
    warning: declaration uses 'sorry': (axioms chunk_membership_from_receipt etc.)
    Build completed successfully.
-/

-- ─── Package declaration (existing — do not duplicate) ─────────────────────────
-- package lutar_lean where
--   name := "lutar-lean"
--   version := "0.1.0"

-- ─── Mathlib dependency (existing — confirm present) ──────────────────────────
-- require mathlib from git
--   "https://github.com/leanprover-community/mathlib4" @ "v4.X.0"

-- ─── NEW: Lutar library target (add if not present) ───────────────────────────

lean_lib Lutar where
  -- Existing files (do not remove):
  --   globs := #[.submodules `Lutar]
  --
  -- New files added by Track 7 (Prisca-GraphRAG v2 + RAG Receipt):
  globs := #[
    -- Existing obligation files (retain as-is):
    .submodules `Lutar,

    -- Track 7 new files:
    -- Lutar.RAGReceipt  → lutar-lean/Lutar/RAGReceipt.lean
    --   Five Λ-QL proof obligations (result_in_corpus, sentra_gate_sound,
    --   doctrine_grade_monotone, merkle_root_binds_chunks, budget_terminates)
    .one `Lutar.RAGReceipt,

    -- Lutar.GraphHop    → lutar-lean/Lutar/GraphHop.lean
    --   Prisca-GraphRAG v2 graph hop monotonicity theorems
    --   (graph_hop_monotone, traversal_acyclic, hop_index_monotone,
    --    ppr_convergence_bounded stub)
    .one `Lutar.GraphHop,
  ]
