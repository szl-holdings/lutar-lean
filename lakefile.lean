import Lake
open Lake DSL

package «lutar» where
  -- Lean 4 + Mathlib package for the Lutar Invariant uniqueness theorem.

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «Lutar» where
  -- Library root: Lutar/

@[default_target]
lean_exe «check» where
  root := `Main

lean_exe «ref_vectors» where
  root := `MainRef
  -- Reads reference-vectors.json (TS-generated) and asserts Λ₉ parity
  -- between the Lean-side Float implementation and the production TS
  -- runtime. CI invokes:  lake exe ref_vectors <path-to-json>
