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
