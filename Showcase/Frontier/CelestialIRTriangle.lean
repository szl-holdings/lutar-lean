/-
  Showcase.Frontier.CelestialIRTriangle
  =====================================
  EXPERIMENTAL.  Mathlib-free; every theorem closes by `decide` over closed
  Bool/Int terms, so a bare Lean kernel checks it (sorry-free). Compiles against
  `leanprover/lean4:v4.18.0` core.

  MOTIVATION (real, citeable — public arXiv):
    The Pasterski–Strominger–Zhiboedov "infrared triangle" relates three corners
    of infrared physics — asymptotic symmetries, soft theorems, and memory
    effects — pairwise: soft theorems <-> asymptotic symmetries (Ward identity),
    asymptotic symmetries <-> memory effects (vacuum transition), and memory
    effects <-> soft theorems (Fourier transform). References:
      - New Gravitational Memories                     arXiv:1502.06120
        (S. Pasterski, A. Strominger, A. Zhiboedov)
      - Asymptotic Symmetries and Electromagnetic Memory  arXiv:1505.00716
        (S. Pasterski)
      - Flat Space Amplitudes and Conformal Symmetry of the Celestial Sphere
                                                       arXiv:1701.00049
        (S. Pasterski, S.-H. Shao, A. Strominger)
      - Celestial Holography (review)                  arXiv:2111.11392
        (S. Pasterski, M. Pate, A.-M. Raclariu)

  WHAT IS PROVEN (honest scope — read this):
    We do NOT re-derive any physics theorem and we claim NO result about gravity.
    We formalize, as closed integer/Bool identities the kernel checks:
      (1) the *graph structure* of the triangle — three corners, three pairwise
          relations, i.e. the complete graph on three nodes; and
      (2) the discrete arithmetic skeleton of the triangle's "soft <-> memory"
          (Fourier) edge: the memory = the net permanent change of the field =
          the running sum of the "news" increments, and the soft (zero-frequency)
          Fourier mode of the news equals that same sum (because the kernel
          e^{i*0*u} = 1). Hence soft-zero-mode = memory.
    These are honest discrete witnesses of the relations' shape, not the physics.
-/
namespace Showcase.Frontier.CelestialIRTriangle

/-! ## Part 1 — the infrared triangle as a graph (structure only)

    Corners: 0 = asymptotic symmetries, 1 = soft theorems, 2 = memory effects.
    Edges  : the three established pairwise relations. -/

/-- The three corners of the infrared triangle. -/
def corners : List Nat := [0, 1, 2]

/-- The three pairwise relations, as undirected edges `(i, j)` with `i < j`:
    (0,1) Ward identity, (1,2) Fourier transform, (0,2) vacuum transition. -/
def edges : List (Nat × Nat) := [(0, 1), (1, 2), (0, 2)]

/-- Undirected adjacency over the edge set. -/
def adj (i j : Nat) : Bool :=
  edges.any (fun e => (e.1 == i && e.2 == j) || (e.1 == j && e.2 == i))

/-- Every distinct pair of corners is related: the triangle is the complete
    graph on its three corners (K₃). -/
theorem triangle_complete :
    (corners.all (fun a => corners.all (fun b => a == b || adj a b))) = true := by
  decide

/-- Exactly three corners and three relations. -/
theorem triangle_counts : (corners.length == 3 && edges.length == 3) = true := by
  decide

/-! ## Part 2 — the soft <-> memory leg (Fourier edge), discrete skeleton

    The "news" N_n are the retarded-time increments of the asymptotic field.
    Memory = net permanent field change = running sum of the news. The soft
    (zero-frequency) Fourier mode is Σ_n N_n · e^{i·0·n} = Σ_n N_n · 1, the same
    sum. We use a frozen integer sample so the kernel checks exact equalities. -/

/-- A frozen integer sample of the news N_n. -/
def news : List Int := [3, -1, 4, -2, 5, -7, 2]

/-- The MEMORY: the net permanent change of the field = the running sum of the
    news increments (the discrete analogue of ∫ N du). -/
def memory : Int := news.foldl (fun acc x => acc + x) 0

/-- The soft (zero-frequency) Fourier mode of the news: Σ_n N_n · e^{i·0·n}.
    At zero frequency the kernel is 1, written here as the explicit `x * 1`. -/
def softZeroMode : Int := news.foldl (fun acc x => acc + x * 1) 0

/-- The final asymptotic field value built from a base value `h0` by
    accumulating the news (the discrete h(+∞) = h(-∞) + ∫ N). -/
def fieldFinal (h0 : Int) : Int := news.foldl (fun acc x => acc + x) h0

/-- The frozen memory value for this sample. -/
theorem memory_value : (memory == 4) = true := by decide

/-- Soft <-> memory: the zero-frequency Fourier mode of the news equals the
    memory. This is the kernel-checked arithmetic core of the triangle's
    Fourier edge. -/
theorem soft_zero_mode_eq_memory : (softZeroMode == memory) = true := by decide

/-- Memory = net field change, witnessed for `h0 = 10`: the permanent
    displacement `h(+∞) - h(-∞)` equals the memory regardless of the base. -/
theorem memory_eq_net_field_change_h10 :
    (fieldFinal 10 - 10 == memory) = true := by decide

/-- Same identity witnessed for a different (negative) base `h0 = -7`,
    confirming the net change does not depend on the base value. -/
theorem memory_eq_net_field_change_hneg :
    (fieldFinal (-7) - (-7) == memory) = true := by decide

-- Honesty proofs: the axiom footprint is emitted into the build log.
#print axioms triangle_complete
#print axioms soft_zero_mode_eq_memory

end Showcase.Frontier.CelestialIRTriangle
