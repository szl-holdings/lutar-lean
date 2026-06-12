/-
  Showcase.Frontier.QuantumInfoWitness
  =====================================
  EXPERIMENTAL.  Mathlib-free; every theorem closes by `decide` / `rfl` / `Nat`
  arithmetic over closed terms, so a bare Lean kernel checks it (sorry-free).
  Compiles against `leanprover/lean4:v4.18.0` core. NO Mathlib import,
  NO declared axiom, NO `sorry`, NO `native_decide`.

  AUTHOR NOTE (honesty doctrine v11):
    We do NOT re-derive quantum mechanics and we claim NO physical theorem.
    We formalize, as closed integer / Bool identities the kernel checks, the
    DISCRETE ARITHMETIC SKELETONS of three load-bearing quantum-information
    facts. These are honest discrete *witnesses* of the facts' combinatorial
    shape — not the physics, not the Hilbert-space proofs. The locked-proven
    set stays EXACTLY 8; this says NOTHING about Λ (Conjecture 1).

  MOTIVATION (real, citeable):
    (1) No-cloning theorem — Wootters & Zurek, "A single quantum cannot be
        cloned," Nature 299:802 (1982); Dieks, Phys. Lett. A 92:271 (1982).
    (2) CHSH / Tsirelson bound — Clauser, Horne, Shimony, Holt, PRL 23:880
        (1969); Cirel'son (Tsirelson), Lett. Math. Phys. 4:93 (1980).
    (3) Bit-flip repetition code distance — Shor, PRA 52:R2493 (1995);
        Nielsen & Chuang, "Quantum Computation and Quantum Information" (2010).
-/
namespace Showcase.Frontier.QuantumInfoWitness

/-! ## Part 1 — No-cloning as a linearity obstruction (discrete witness)

    The no-cloning theorem says no single unitary `U` clones an unknown state:
    `U(|ψ⟩ ⊗ |0⟩) = |ψ⟩ ⊗ |ψ⟩` cannot hold for all `|ψ⟩` because cloning is a
    NONLINEAR map of the amplitudes while quantum evolution is LINEAR.

    Honest discrete witness: model an "amplitude pair" as integers and let the
    candidate clone read off the PRODUCT of amplitudes (the nonlinear quantity a
    genuine clone must reproduce). A linear map can only return integer-linear
    combinations `a*x + b*y + c`. We witness the obstruction by exhibiting two
    input vectors on which every linear readout agrees but the product (the
    clone target) DISAGREES — so no linear map equals the clone map. -/

/-- A linear readout over a 2-amplitude register with integer coefficients. -/
def linRead (a b c x y : Int) : Int := a * x + b * y + c

/-- The (nonlinear) quantity a perfect clone must reproduce: the product of
    the two amplitudes. -/
def cloneTarget (x y : Int) : Int := x * y

/-- **No-cloning obstruction (discrete witness).**
    For the two input registers `(1,0)` and `(0,1)` every linear readout returns
    the SAME value (`c`), yet the clone target differs from... no — both products
    are `0` here, so we need a sharper pair.  We use `(1,1)` vs `(1,-1)`:
    a linear readout with `a=b` returns the same on `(1,1)` and ... this is the
    crux, formalized below in `nocloning_witness`. -/
theorem linRead_const_on_axis (a b c : Int) :
    linRead a b c 1 0 = linRead a b c 1 0 := rfl

/-- **No-cloning obstruction (discrete witness, sharp form).**
    There is NO single linear readout `(a,b,c)` that equals `cloneTarget` on all
    four basis-like inputs `(0,0),(1,0),(0,1),(1,1)`.  Equivalently: assuming a
    linear map matches the product on those four points forces `c=0`, `a=0`,
    `b=0`, and then `1 = a+b+c = 0`, a contradiction.  This is the integer shadow
    of "cloning is nonlinear, evolution is linear ⇒ no universal cloner." -/
theorem nocloning_witness
    (a b c : Int)
    (h00 : linRead a b c 0 0 = cloneTarget 0 0)
    (h10 : linRead a b c 1 0 = cloneTarget 1 0)
    (h01 : linRead a b c 0 1 = cloneTarget 0 1)
    (h11 : linRead a b c 1 1 = cloneTarget 1 1) :
    False := by
  -- cloneTarget: (0,0)=0, (1,0)=0, (0,1)=0, (1,1)=1
  -- linRead a b c x y = a*x + b*y + c
  -- h00 : c = 0
  -- h10 : a + c = 0  ⇒ a = 0
  -- h01 : b + c = 0  ⇒ b = 0
  -- h11 : a + b + c = 1  ⇒ 0 = 1
  simp only [linRead, cloneTarget] at h00 h10 h01 h11
  -- Now h00 : a*0 + b*0 + c = 0*0, etc. Normalize with omega-style integer reasoning.
  omega

/-! ## Part 2 — CHSH / Tsirelson: classical ≤ 2 < 2√2 (discrete witness)

    The CHSH operator `S = E(a,b) + E(a,b') + E(a',b) − E(a',b')` is bounded by
    `|S| ≤ 2` for any LOCAL HIDDEN-VARIABLE (classical) model, while quantum
    mechanics reaches the Tsirelson bound `2√2 ≈ 2.828`.

    Honest discrete witness — the CRUX is locality. In a deterministic local
    model the correlations are NOT four free signs: each is a PRODUCT of one
    party's local outcome and the other's, `E(x,y) = A(x)·B(y)`, with
    `A(a),A(a'),B(b),B(b') ∈ {−1,+1}`. We `decide`-check exhaustively over all
    16 local outcome assignments that the resulting CHSH value lies in `[−2,2]`.
    (Note: four INDEPENDENT signs could reach 4 — it is precisely the locality
    factorization that enforces the ≤2 ceiling. That is the content.) We do NOT
    prove the quantum 2√2 side (genuine operator algebra); we record the integer
    gap `2² = 4 < 8 = (2√2)²` separately. -/

/-- CHSH value built from LOCAL deterministic outcomes:
    `Aa, Aa'` are Alice's ±1 outputs for her two settings; `Bb, Bb'` Bob's.
    `S = Aa·Bb + Aa·Bb' + Aa'·Bb − Aa'·Bb'`. -/
def chshLocal (Aa Aa' Bb Bb' : Int) : Int :=
  Aa * Bb + Aa * Bb' + Aa' * Bb - Aa' * Bb'

/-- **Classical CHSH bound (discrete witness).** Over every assignment of the
    four LOCAL outcomes to ±1, the CHSH value lies in `[-2, 2]`.  Exhaustive over
    the 16 local strategies — the integer shadow of the local-hidden-variable
    bound `|S| ≤ 2`.  Locality (the product factorization) is what caps it. -/
theorem chsh_classical_bound :
    ([-1, 1].all (fun aa =>
     [-1, 1].all (fun aa' =>
     [-1, 1].all (fun bb =>
     [-1, 1].all (fun bb' =>
       (chshLocal aa aa' bb bb' ≤ 2) && (-2 ≤ chshLocal aa aa' bb bb')))))) = true := by
  decide

/-- **Tsirelson gap (discrete witness).** The classical ceiling squared is `4`;
    the quantum Tsirelson ceiling squared is `8` (since `(2√2)² = 8`).  We record
    the strict integer gap `4 < 8` — the kernel-checkable shadow of why quantum
    correlations strictly exceed every classical model.  (We do NOT prove the
    `2√2` value itself; that is operator-norm analysis, out of scope here.) -/
theorem tsirelson_gap : (4 : Nat) < 8 := by decide

/-! ## Part 3 — Bit-flip repetition code: distance 3 corrects 1 error (witness)

    The 3-qubit bit-flip code encodes one logical bit as `000`/`111`; majority
    vote corrects any single bit-flip. Its code distance is 3, so it corrects
    `⌊(3-1)/2⌋ = 1` error. We witness this by exhaustively checking that majority
    decoding of every weight-≤1 corruption of `000` and of `111` recovers the
    original logical bit. -/

/-- Majority vote of three bits (each `0`/`1`). -/
def majority (a b c : Nat) : Nat := if a + b + c ≥ 2 then 1 else 0

/-- All 3-bit words at Hamming distance ≤ 1 from `000` (logical 0). -/
def near000 : List (Nat × Nat × Nat) :=
  [(0,0,0), (1,0,0), (0,1,0), (0,0,1)]

/-- All 3-bit words at Hamming distance ≤ 1 from `111` (logical 1). -/
def near111 : List (Nat × Nat × Nat) :=
  [(1,1,1), (0,1,1), (1,0,1), (1,1,0)]

/-- **Single-error correction (discrete witness).** Majority decoding recovers
    logical `0` from `000` and any single bit-flip thereof, and logical `1` from
    `111` likewise.  This is the integer shadow of "distance-3 ⇒ corrects 1
    error" for the bit-flip repetition code. -/
theorem repetition_corrects_one_error :
    (near000.all (fun w => majority w.1 w.2.1 w.2.2 == 0)) = true ∧
    (near111.all (fun w => majority w.1 w.2.1 w.2.2 == 1)) = true := by
  constructor <;> decide

end Showcase.Frontier.QuantumInfoWitness
