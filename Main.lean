import Lutar

/-!
# Lutar verification entry point

Running `lake exe check` exercises the kernel on the whole `Lutar` library.
If this builds without error, every theorem in `Lutar/*.lean` has been
machine-verified by the Lean kernel.
-/

def main : IO Unit := do
  IO.println "Lutar — kernel-verified invariant theorems"
  IO.println s!"Λ_k formalised for k ∈ \{5, 7, 9\}"
  IO.println "Axioms: A1 monotone · A2 homogeneous · A3 Egyptian-exact · A4 bounded"
  IO.println "Theorem 1 (uniqueness): see Lutar/Uniqueness.lean"
  IO.println "Theorem 2 (bound): see Lutar/Bound.lean"
