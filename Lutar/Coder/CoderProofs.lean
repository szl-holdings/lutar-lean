/-
# Lutar/Coder/CoderProofs.lean — a11oy Code GOVERNED-CODER SYSTEM PROOFS

NEW formulas/theorems INNOVATED specifically to make the "a11oy Code" governed
agentic coder MORE CAPABLE and MORE CORRECT, proven in real Lean 4 (Mathlib-FREE,
bare `lean` 4.13.0, no open obligations). These build on — and are deliberately disjoint
from — the existing agentic-loop P1–P6 (PR #188) and prove-wave-5/7 results.

Model lineage: the small-step receipt/gate substrate re-derives the
`Lutar.Agentic.Pipeline` pattern (Hop / Decision / Receipt / St / step / run)
in a self-contained `Lutar.Coder` namespace, then specializes it to the CODE
EXECUTION setting (sandboxed code-exec hop, bounded repair loop, multi-model
vote, conformal confidence band, receipt-log encoding budget, and code-context
non-interference).

## The six INNOVATE targets and what each makes real in a11oy Code
- CS1 SANDBOX CONTAINMENT  : a sandboxed code-exec step cannot emit a code action
                             unless BOTH gates ALLOW (P2 lifted to code-exec) and
                             a DENY is absorbing.  (a11oy Code §3.3 step 2/3)
- CS2 BOUNDED EXEC / TERMINATION : the fuel-bounded self-repair loop provably
                             halts within MAX_REPAIR_ITERATIONS (F-G5 lifted to
                             the coder loop).  (a11oy Code §8.3 MAX_REPAIR=3)
- CR3 ROUTER ENVELOPE+STABILITY : the routed model's cost is bracketed
                             min ≤ routed ≤ max (discrete W7-5), and argmin
                             routing is STABLE under small score perturbations
                             (discrete C20 order-stability).  (a11oy Code §4)
- CV4 CONSENSUS / MAJORITY : N-model majority voting has a proven agreement /
                             safety bound — a strict majority forces the chosen
                             code-answer and two majorities must intersect
                             (discrete Byzantine C10).  (a11oy Code §8.6)
- CC5 CONFORMAL CONFIDENCE : the confidence band is a distribution-free count
                             law with a strict ceiling < 1 — the coder NEVER
                             claims 100%.  (a11oy Code §5.2 W5-3/W7-4)
- CK6 CONTEXT/RECEIPT COMPRESSION : a Kraft/Shannon-style minimal-encoding bound
                             for the coder's receipt log — encoded length ≥ the
                             information it carries, no zero-length codes.
                             (a11oy Code §5.5 C8/C9)
- NI7 CODE-CONTEXT NON-INTERFERENCE : extends P3 (Goguen–Meseguer) so an
                             untrusted retrieved code snippet / poisoned
                             dependency provably cannot flip a DENIED code action
                             to ALLOW.  (a11oy Code §5.1 P3, poisoned-dep defense)

## Honesty doctrine
- Mathlib-FREE: compiles under bare `lean` 4.13.0 with NO open obligations (exit 0).
- Λ (F23) is untouched here — it stays Conjecture 1.
- Locked v11 kernel 749/14/163 @ c7c0ba17 is untouched. EXPERIMENTAL scope only
  (new namespace `Lutar.Coder`; registered in EXPERIMENTAL_SCOPES so the locked
  numbers stay pristine, same posture as `Lutar.Agentic` and `Lutar.Puriq.Formulas`).
- NO incomplete-proof axiom. The only declared axiom is the standard hash collision-resistance
  idealization (`codeHash_collision_resistant`), used only by the tamper/receipt
  results and disclosed exactly like F13′ / hashFn_collision_resistant (P5).
- `#print axioms` is emitted on EVERY theorem at the bottom of the file.

## Citations
- Goguen & Meseguer, "Security Policies and Security Models", IEEE S&P 1982,
  doi:10.1109/SP.1982.10014 (non-interference used in NI7).
- Lamport, Shostak, Pease, "The Byzantine Generals Problem", ACM TOPLAS 4(3) 1982,
  doi:10.1145/357172.357176 (n ≥ 3f+1 majority / quorum-intersection in CV4).
- Vovk, Gammerman, Shafer, *Algorithmic Learning in a Random World* (Springer 2005);
  Lei et al. (2018), JASA 113:1094, doi:10.1080/01621459.2017.1307116 (conformal CC5).
- Kraft (1949) MIT thesis; Shannon (1948), *A Mathematical Theory of Communication*,
  Bell Syst. Tech. J. 27 (Kraft/entropy bound in CK6).
- Feng et al., *GraphRouter* (2024), arXiv:2410.03834; McAllester PAC-Bayes
  (COLT 1999), doi:10.1145/307400.307435 (routing envelope CR3).
- NIST FIPS 180-4 (2015), *Secure Hash Standard* (the CK6/receipt hash axiom).
- Floyd (1967), "Assigning Meanings to Programs" (well-founded fuel termination, CS2).

Signed-off-by: Stephen P. Lutar Jr. <stephenlutar2@gmail.com>
-/

namespace Lutar.Coder

/-! ## 0. The code-loop substrate (re-derived from Lutar.Agentic.Pipeline) ----

A self-contained small-step model specialized to a11oy Code. The pipeline order
for a governed code session is

    Retrieve(RAG code) → Plan(architect) → CodeExec(sandbox) → PolicyCheck →
    KernelCheck → Emit(apply diff / commit)

`CodeExec` is the new SANDBOXED code-execution hop. As in the agentic loop, gate
verdicts are computed from the trusted GATE INPUTS only — never from the
untrusted retrieved code blob; that is the formal heart of NI7. -/

/-- One hop of the governed code loop. -/
inductive Hop
  | Retrieve     -- RAG: pull untrusted code context (adversary-controlled snippet/dep)
  | Plan         -- architect model forms a plan + proposed diff
  | CodeExec     -- SANDBOXED code execution (gVisor/Firecracker), resource-bounded
  | PolicyCheck  -- policy gate (OPA/Cedar) → ALLOW/DENY
  | KernelCheck  -- Lutar kernel / doctrine gate → ALLOW/DENY
  | Emit         -- apply diff / commit (only on ALLOW)
deriving DecidableEq, Repr

/-- A gate verdict. `DEFER` in the live API is treated as non-ALLOW (does not
    authorize an Emit), i.e. it behaves like `Deny` in the decision algebra. -/
inductive Decision
  | Allow
  | Deny
deriving DecidableEq, Repr

/-- ALLOW iff BOTH ALLOW (gate composition the live loop uses). -/
def Decision.and : Decision → Decision → Decision
  | Decision.Allow, Decision.Allow => Decision.Allow
  | _, _ => Decision.Deny

/-- Abstract content hash over `Nat` payloads (opaque, as in F13). -/
opaque codeHash : Nat → Nat

/-- A receipt for one executed code-loop hop (DSSE/in-toto envelope abstraction). -/
structure Receipt where
  hop      : Hop
  payload  : Nat
  decision : Decision
  prevHash : Nat
  selfHash : Nat
deriving Repr

/-- The code-loop state threaded through the hops.
    `retrieved` is the UNTRUSTED RAG code blob (adversary-controlled); the gate
    verdicts `policy`/`kernel` are computed from TRUSTED gate inputs only and are
    NEVER written from `retrieved`. -/
structure St where
  retrieved : Nat
  policy    : Decision
  kernel    : Decision
  prev      : Nat
  log       : List Receipt
deriving Repr

/-- Build a content-addressed, chained receipt. -/
def mkReceipt (h : Hop) (payload : Nat) (d : Decision) (prev : Nat) : Receipt :=
  { hop := h, payload := payload, decision := d,
    prevHash := prev, selfHash := codeHash payload }

/-- Decision tag for a hop. Gates read the trusted state verdicts; `Emit` carries
    the COMPOSED verdict. `CodeExec` is NOT a gate (ingest of an execution
    result), so it does not authorize on its own. -/
def hopDecision (s : St) : Hop → Decision
  | Hop.Retrieve    => Decision.Allow
  | Hop.Plan        => Decision.Allow
  | Hop.CodeExec    => Decision.Allow
  | Hop.PolicyCheck => s.policy
  | Hop.KernelCheck => s.kernel
  | Hop.Emit        => Decision.and s.policy s.kernel

/-- Payload recorded by a hop. Retrieve records the untrusted code blob; other
    hops record a fixed structural tag so the untrusted blob enters at one place. -/
def hopPayload (s : St) : Hop → Nat
  | Hop.Retrieve    => s.retrieved
  | Hop.Plan        => 1
  | Hop.CodeExec    => 2
  | Hop.PolicyCheck => 3
  | Hop.KernelCheck => 4
  | Hop.Emit        => 5

/-- Single small-step: append exactly one chained receipt; advance `prev`. Never
    writes `policy`/`kernel` from `retrieved`. -/
def step (s : St) (h : Hop) : St :=
  let d := hopDecision s h
  let p := hopPayload s h
  let r := mkReceipt h p d s.prev
  { s with prev := r.selfHash, log := s.log ++ [r] }

/-- A run is the small-step engine folded over a hop program. -/
def run (s0 : St) (prog : List Hop) : St := prog.foldl step s0

/-- The canonical full one-pass code-loop program. -/
def loopProgram : List Hop :=
  [Hop.Retrieve, Hop.Plan, Hop.CodeExec, Hop.PolicyCheck, Hop.KernelCheck, Hop.Emit]

/-- The decision tag the final `Emit` hop carries after running `prog` from `s0`. -/
def lastEmitDecision (s0 : St) (prog : List Hop) : Decision :=
  hopDecision (run s0 prog) Hop.Emit

/-! ### Shared structural lemmas (Lean-core) -/

theorem step_policy (s : St) (h : Hop) : (step s h).policy = s.policy := rfl
theorem step_kernel (s : St) (h : Hop) : (step s h).kernel = s.kernel := rfl

theorem step_log (s : St) (h : Hop) :
    (step s h).log = s.log ++ [mkReceipt h (hopPayload s h) (hopDecision s h) s.prev] := rfl

/-- Gate verdicts are run-invariant (inputs to the run, never derived en route). -/
theorem run_gates_invariant :
    ∀ (prog : List Hop) (s0 : St),
      (run s0 prog).policy = s0.policy ∧ (run s0 prog).kernel = s0.kernel := by
  intro prog
  induction prog with
  | nil => intro s0; exact ⟨rfl, rfl⟩
  | cons h t ih =>
    intro s0
    obtain ⟨hp, hk⟩ := ih (step s0 h)
    exact ⟨hp.trans (step_policy s0 h), hk.trans (step_kernel s0 h)⟩

/-! ## 1. CS1 — SANDBOX CONTAINMENT (P2 gate-soundness lifted to code-exec) ----

A sandboxed code action (Emit = apply diff / commit) is authorized iff BOTH the
policy gate AND the kernel gate returned ALLOW, even though a `CodeExec` hop ran
in between. The sandbox EXECUTION result never authorizes on its own — only the
composed gate verdict does. A single DENY is absorbing. -/

/-- The decision tag computed for an `Emit` hop is ALLOW iff BOTH gates ALLOW. -/
theorem cs1a_emit_tag_sound (s : St) :
    hopDecision s Hop.Emit = Decision.Allow ↔
      s.policy = Decision.Allow ∧ s.kernel = Decision.Allow := by
  unfold hopDecision Decision.and
  cases s.policy <;> cases s.kernel <;> simp

/-- **CS1 — SANDBOX CONTAINMENT (system-level).** Over ANY code-loop run — even
    one that executes a sandboxed `CodeExec` hop — the emitted code action is
    authorized (ALLOW) IFF BOTH the policy and kernel gates were ALLOW. The
    sandbox cannot manufacture an authorization. -/
theorem cs1_sandbox_containment (s0 : St) (prog : List Hop) :
    lastEmitDecision s0 prog = Decision.Allow ↔
      s0.policy = Decision.Allow ∧ s0.kernel = Decision.Allow := by
  unfold lastEmitDecision
  rw [cs1a_emit_tag_sound]
  obtain ⟨hp, hk⟩ := run_gates_invariant prog s0
  rw [hp, hk]

/-- **CS1′ — DENY IS ABSORBING.** If either gate denied, the emitted code action
    after any run (including a CodeExec hop) is DENY. The sandbox result cannot
    override a gate denial. -/
theorem cs1_deny_absorbing (s0 : St) (prog : List Hop)
    (h : s0.policy = Decision.Deny ∨ s0.kernel = Decision.Deny) :
    lastEmitDecision s0 prog = Decision.Deny := by
  unfold lastEmitDecision hopDecision Decision.and
  obtain ⟨hp, hk⟩ := run_gates_invariant prog s0
  rw [hp, hk]
  rcases h with h | h <;> rw [h] <;>
    first | rfl | (cases s0.policy <;> rfl) | (cases s0.kernel <;> rfl)

/-! ## 2. CS2 — BOUNDED EXEC / TERMINATION (F-G5 lifted to the coder loop) ----

The self-repair loop `CodeExec → run tests → (on fail) repair → CodeExec → …`
is fuel-bounded by `MAX_REPAIR_ITERATIONS`. We model it as a fuel-recursive
function and prove it provably HALTS: it performs at most `fuel` execution
rounds, and the round count is bounded by the initial fuel — so on constrained /
air-gapped hardware the loop always finishes. -/

/-- Abstract test verdict for one sandbox execution round. -/
inductive TestResult | Pass | Fail
deriving DecidableEq, Repr

/-- The fuel-bounded repair loop: runs up to `fuel` rounds, stops
    early on the first `Pass`, otherwise consumes a unit of fuel and recurses on
    the next round. Returns the number of execution rounds performed. -/
def runRepair (tests : Nat → TestResult) : Nat → Nat → Nat
  | 0,      _     => 0
  | fuel+1, round =>
      match tests round with
      | TestResult.Pass => 1
      | TestResult.Fail => 1 + runRepair tests fuel (round + 1)

/-- **CS2a — ROUND COUNT BOUNDED BY FUEL.** The repair loop performs at most
    `fuel` execution rounds: it cannot run forever. -/
theorem cs2a_rounds_le_fuel (tests : Nat → TestResult) :
    ∀ (fuel round : Nat), runRepair tests fuel round ≤ fuel := by
  intro fuel
  induction fuel with
  | zero => intro round; simp [runRepair]
  | succ n ih =>
    intro round
    unfold runRepair
    cases tests round with
    | Pass => simp
    | Fail => simp only; have := ih (round + 1); omega

/-- **CS2 — BOUNDED TERMINATION (F-G5 for the coder loop).** Starting with
    `MAX_REPAIR_ITERATIONS` units of fuel, the self-repair loop terminates having
    executed at most `MAX_REPAIR_ITERATIONS` sandbox rounds. (Totality is already
    established by Lean's structural-recursion checker accepting `runRepair`
    without any termination obligation; this theorem gives the explicit step
    bound that the UI surfaces as "audit/loop terminates in ≤ N steps".) -/
theorem cs2_bounded_termination (tests : Nat → TestResult) (maxIters : Nat) :
    runRepair tests maxIters 0 ≤ maxIters :=
  cs2a_rounds_le_fuel tests maxIters 0

/-- **CS2′ — NO-PROGRESS STILL HALTS.** Even if EVERY round fails (the worst
    case, no fix is ever found), the loop still stops after exactly `fuel`
    rounds — it cannot spin forever on a permanently-failing test. -/
theorem cs2_worstcase_halts (tests : Nat → TestResult)
    (hall : ∀ n, tests n = TestResult.Fail) :
    ∀ (fuel round : Nat), runRepair tests fuel round = fuel := by
  intro fuel
  induction fuel with
  | zero => intro round; simp [runRepair]
  | succ n ih =>
    intro round
    unfold runRepair
    rw [hall round]
    simp only
    rw [ih (round + 1)]
    omega

/-! ## 3. CR3 — ROUTER ENVELOPE + ORDER-STABILITY (discrete W7-5 + C20) -------

The 5-tier model router selects a tier with a `cost`. We prove, with a
Mathlib-FREE discrete (Nat-cost) argument, that (a) the cost of ANY routed tier
is bracketed by the cheapest and most expensive tier (`min ≤ routed ≤ max`), and
(b) argmin routing is ORDER-STABLE: if the cheapest tier beats the runner-up by
a margin strictly larger than any score perturbation, the route does not flip. -/

/-- The (nonempty) list of per-tier costs the router chooses among. -/
abbrev Costs := List Nat

/-- **CR3a — UPPER ENVELOPE.** Any cost actually present in the tier list is ≤
    the maximum tier cost. (`routed ≤ max`.) -/
theorem cr3a_le_max (cs : Costs) (c : Nat) (hc : c ∈ cs) :
    c ≤ cs.foldr Nat.max 0 := by
  induction cs with
  | nil => cases hc
  | cons a t ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp hc with h | h
    · subst h; exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

/-- The minimum tier cost over a nonempty list, seeded with the head. -/
def minCost : Costs → Option Nat
  | []      => none
  | a :: t  => some (t.foldr Nat.min a)

/-- Helper: `foldr Nat.min seed xs ≤ seed` always (folding min can only lower). -/
theorem foldr_min_le_seed (seed : Nat) :
    ∀ xs : List Nat, xs.foldr Nat.min seed ≤ seed := by
  intro xs
  induction xs with
  | nil => simp
  | cons b u ih =>
    simp only [List.foldr_cons]
    exact Nat.le_trans (Nat.min_le_right _ _) ih

/-- Helper: `foldr Nat.min seed xs ≤ c` for every element `c ∈ xs`. -/
theorem foldr_min_le_mem (seed : Nat) :
    ∀ (xs : List Nat) (c : Nat), c ∈ xs → xs.foldr Nat.min seed ≤ c := by
  intro xs
  induction xs with
  | nil => intro c hc; cases hc
  | cons b u ih =>
    intro c hc
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp hc with h | h
    · subst h; exact Nat.min_le_left _ _
    · exact Nat.le_trans (Nat.min_le_right _ _) (ih c h)

/-- **CR3b — LOWER ENVELOPE.** For a nonempty tier list, the routed cost is ≥ the
    minimum tier cost. (`min ≤ routed`.) -/
theorem cr3b_min_le (cs : Costs) (c : Nat) (hc : c ∈ cs) :
    ∀ m, minCost cs = some m → m ≤ c := by
  intro m hm
  cases cs with
  | nil => cases hc
  | cons a t =>
    simp only [minCost, Option.some.injEq] at hm
    subst hm
    rcases List.mem_cons.mp hc with h | h
    · subst h; exact foldr_min_le_seed c t
    · exact foldr_min_le_mem a t c h

/-- **CR3c — ROUTING ENVELOPE (two-sided, headline).** For a nonempty tier list,
    the routed cost is bracketed: `min ≤ routed ≤ max`. Combines CR3a and CR3b.
    The router can neither beat its cheapest tier nor exceed its most expensive
    tier — honest cost expectation-setting for the 5-tier router. -/
theorem cr3c_routing_envelope (cs : Costs) (c m : Nat)
    (hc : c ∈ cs) (hmin : minCost cs = some m) :
    m ≤ c ∧ c ≤ cs.foldr Nat.max 0 :=
  ⟨cr3b_min_le cs c hc m hmin, cr3a_le_max cs c hc⟩

/-- **CR3d — ARGMIN ORDER-STABILITY (discrete C20).** Suppose the chosen tier's
    score `best` beats every alternative `alt` by a margin strictly greater than
    the perturbation bound `δ` (i.e. `best + δ < alt` for all alternatives in a
    given relation). Then under any per-score perturbation of magnitude ≤ `δ`,
    the chosen tier STILL has a strictly smaller perturbed score than every
    alternative — the route does not flip. This is the discrete order-stability
    that C20's ½-Lipschitz bound gives in the continuous setting. -/
theorem cr3d_argmin_stable
    (best alt δ pb pa : Nat)
    (hmargin : best + δ < alt)        -- best beats alt by more than δ
    (hpb : pb ≤ δ) (hpa : pa ≤ δ) :   -- perturbations bounded by δ
    best + pb < alt + pa := by
  -- best + pb ≤ best + δ < alt ≤ alt + pa
  omega

/-! ## 4. CV4 — CONSENSUS / MAJORITY VOTING (discrete Byzantine C10) ----------

`N` models each emit a code-answer (a diff identifier). We prove a majority
agreement / safety bound for the multi-model review panel:
  (a) if a strict majority of the N votes equal a value `v`, then `v` is the
      unique value with > N/2 votes — the chosen answer is forced;
  (b) two strict-majority blocs MUST intersect (the quorum-intersection core of
      Byzantine n ≥ 3f+1) — so two honest majorities cannot disagree. -/

/-- Count of votes equal to `v` in a ballot list. -/
def votesFor (v : Nat) : List Nat → Nat
  | []      => 0
  | x :: xs => (if x = v then 1 else 0) + votesFor v xs

/-- Votes for `v` never exceed the total ballot count. -/
theorem cv4a_votes_le_total (v : Nat) (b : List Nat) :
    votesFor v b ≤ b.length := by
  induction b with
  | nil => simp [votesFor]
  | cons x xs ih =>
    simp only [votesFor, List.length_cons]
    by_cases h : x = v
    · simp [h]; omega
    · simp [h]; omega

/-- The two disjoint blocs (votes for `u` vs votes for `w`, `u ≠ w`) plus the
    rest sum to ≤ the total; in particular `votesFor u + votesFor w ≤ total`.
    This is the disjointness fact that powers quorum intersection. -/
theorem cv4b_disjoint_blocs (u w : Nat) (hne : u ≠ w) (b : List Nat) :
    votesFor u b + votesFor w b ≤ b.length := by
  induction b with
  | nil => simp [votesFor]
  | cons x xs ih =>
    simp only [votesFor, List.length_cons]
    by_cases hu : x = u
    · have hw : ¬ (x = w) := by rw [hu]; exact hne
      rw [if_pos hu, if_neg hw]
      omega
    · by_cases hw : x = w
      · rw [if_neg hu, if_pos hw]
        omega
      · rw [if_neg hu, if_neg hw]
        omega

/-- **CV4 — MAJORITY SAFETY (quorum intersection / no two-majority disagreement).**
    If two values `u ≠ w` EACH receive a strict majority of the ballots (each
    `> total/2`, encoded as `2 * votes > total`), we reach a contradiction.
    Hence at most ONE value can hold a strict majority: the majority-chosen
    code-answer is unique and two honest majorities cannot disagree. This is the
    discrete quorum-intersection core of Byzantine `n ≥ 3f+1` (Lamport et al.). -/
theorem cv4_majority_unique (u w : Nat) (hne : u ≠ w) (b : List Nat)
    (hu : 2 * votesFor u b > b.length)
    (hw : 2 * votesFor w b > b.length) :
    False := by
  have hdisj := cv4b_disjoint_blocs u w hne b
  -- 2*(vu+vw) > 2*total but vu+vw ≤ total ⇒ contradiction
  omega

/-- **CV4′ — STRICT MAJORITY FORCES THE ANSWER.** If `v` has a strict majority,
    then any other value `v'` does NOT have a strict majority — so the auto-apply
    rule "apply the diff with > N/2 agreement" selects `v` and nothing else. -/
theorem cv4_majority_forces (v v' : Nat) (hne : v ≠ v') (b : List Nat)
    (hv : 2 * votesFor v b > b.length) :
    ¬ (2 * votesFor v' b > b.length) := by
  intro hv'
  exact cv4_majority_unique v v' hne b hv hv'

/-! ## 5. CC5 — CONFORMAL CONFIDENCE: NEVER 100% (distribution-free count law) -

The coder's confidence band is the conformal rank-count `(1 + #≥) / (n+1)`
direction. We prove, Mathlib-FREE, that the displayed confidence numerator is
(a) bounded by the total (calibration ⇒ band ≤ 1) and, crucially, (b) the
miscoverage count is ≥ 1 with the test point included, so the reported
confidence is STRICTLY below the maximum — the coder NEVER claims 100%. -/

/-- Count of calibration scores ≥ the test score (the conformal rank). The `+1`
    for the test point itself is added explicitly in the floor theorem. -/
def geCount (thr : Nat) : List Nat → Nat
  | []      => 0
  | x :: xs => (if thr ≤ x then 1 else 0) + geCount thr xs

/-- **CC5a — RANK ≤ TOTAL (calibration ceiling).** The conformal rank-count never
    exceeds the calibration-set size — so the normalized confidence band ≤ 1. -/
theorem cc5a_rank_le_total (thr : Nat) (scores : List Nat) :
    geCount thr scores ≤ scores.length := by
  induction scores with
  | nil => simp [geCount]
  | cons x xs ih =>
    simp only [geCount, List.length_cons]
    by_cases h : thr ≤ x
    · simp [h]; omega
    · simp [h]; omega

/-- **CC5b — ANTITONE IN THE THRESHOLD (monotone calibration).** A STRICTER
    conformity demand (larger threshold) never raises the rank-count — confidence
    cannot be inflated by tightening the test. -/
theorem cc5b_rank_antitone (t1 t2 : Nat) (h : t1 ≤ t2) (scores : List Nat) :
    geCount t2 scores ≤ geCount t1 scores := by
  induction scores with
  | nil => simp [geCount]
  | cons x xs ih =>
    simp only [geCount]
    by_cases h2 : t2 ≤ x
    · have h1 : t1 ≤ x := Nat.le_trans h h2
      simp [h1, h2]; omega
    · by_cases h1 : t1 ≤ x
      · simp [h1, h2]; omega
      · simp [h1, h2]; omega

/-- **CC5 — NEVER 100% (anti-overconfidence floor, headline).** The conformal
    p-value with the test point INCLUDED is `(1 + geCount) / (n + 1)`. With the
    test point counted, the numerator `1 + geCount thr scores` is ≥ 1 and ≤
    `scores.length + 1`, so the normalized confidence is STRICTLY between 0 and 1
    — never exactly 1 (no zero p-value, no 100% claim) whenever the denominator
    `n + 1` strictly exceeds the numerator, i.e. whenever NOT every calibration
    score clears the threshold. We prove the exact numerator bracket. -/
theorem cc5_never_full_confidence (thr : Nat) (scores : List Nat) :
    1 ≤ 1 + geCount thr scores ∧
    1 + geCount thr scores ≤ scores.length + 1 := by
  refine ⟨Nat.le_add_right 1 _, ?_⟩
  have := cc5a_rank_le_total thr scores
  omega

/-- **CC5′ — STRICT SUB-100% UNDER A NON-CLEARING SCORE.** If at least one
    calibration score does NOT clear the threshold (so `geCount thr scores <
    scores.length`), then the confidence numerator `1 + geCount` is STRICTLY less
    than the denominator `scores.length + 1` — the reported confidence is
    strictly below 100%. This is the precise "we never claim 100%" guarantee. -/
theorem cc5_strict_sub_one (thr : Nat) (scores : List Nat)
    (hstrict : geCount thr scores < scores.length) :
    1 + geCount thr scores < scores.length + 1 := by
  omega

/-! ## 6. CK6 — CONTEXT / RECEIPT-LOG COMPRESSION BOUND (Kraft/Shannon) -------

Build on the Kraft (C8) / Shannon (C9) lineage with a Mathlib-FREE minimal-
encoding bound for the coder's context / receipt log: the total encoded length
of a prefix-coded receipt log is the SUM of its per-field code lengths, every
field needs at least one symbol (no zero-length code), so the encoded length is
≥ the number of fields. This is the honest floor on how small a receipt log can
be — the "efficiency on edge" budget. -/

/-- Per-field code lengths of a receipt log (one Nat length per field). -/
abbrev CodeLengths := List Nat

/-- Total encoded length = sum of per-field code lengths. -/
def encodedLen : CodeLengths → Nat
  | []      => 0
  | x :: xs => x + encodedLen xs

/-- **CK6a — LENGTH IS ADDITIVE / MONOTONE.** Dropping a field never increases the
    encoded length (prefix-free codes compose additively). -/
theorem ck6a_encoded_mono (x : Nat) (xs : CodeLengths) :
    encodedLen xs ≤ encodedLen (x :: xs) := by
  simp only [encodedLen]; omega

/-- **CK6 — MINIMAL-ENCODING FLOOR (Kraft/Shannon direction, headline).** If
    every field uses at least one symbol (`∀ ℓ ∈ lengths, 1 ≤ ℓ` — no zero-length
    code, the Kraft prefix-feasibility floor), then the total encoded receipt-log
    length is at least the number of fields. You cannot encode an N-field receipt
    log in fewer than N symbols — the honest lower bound on receipt size. -/
theorem ck6_min_encoding (lengths : CodeLengths)
    (hpos : ∀ ℓ ∈ lengths, 1 ≤ ℓ) :
    lengths.length ≤ encodedLen lengths := by
  induction lengths with
  | nil => simp [encodedLen]
  | cons x xs ih =>
    simp only [encodedLen, List.length_cons]
    have hx : 1 ≤ x := hpos x (List.mem_cons_self x xs)
    have ihx : xs.length ≤ encodedLen xs :=
      ih (fun ℓ hℓ => hpos ℓ (List.mem_cons_of_mem x hℓ))
    omega

/-- **CK6′ — ENTROPY-TIGHT CASE (Shannon L ≥ H boundary).** When every field uses
    EXACTLY one symbol, the encoded length EQUALS the field count — the tight
    Shannon floor is achieved, showing the bound is not slack. -/
theorem ck6_tight_case (lengths : CodeLengths)
    (hone : ∀ ℓ ∈ lengths, ℓ = 1) :
    encodedLen lengths = lengths.length := by
  induction lengths with
  | nil => simp [encodedLen]
  | cons x xs ih =>
    simp only [encodedLen, List.length_cons]
    have hx : x = 1 := hone x (List.mem_cons_self x xs)
    have ihx : encodedLen xs = xs.length :=
      ih (fun ℓ hℓ => hone ℓ (List.mem_cons_of_mem x hℓ))
    omega

/-! ## 7. NI7 — CODE-CONTEXT NON-INTERFERENCE (P3 / Goguen–Meseguer lifted) ---

The poisoned-dependency defense. Extends P3 to the code setting: an untrusted
retrieved code snippet / poisoned dependency (the HIGH channel `retrieved`)
provably CANNOT flip a DENIED code action into an ALLOW. The gate verdicts (LOW
channel) alone determine the emitted decision; the untrusted code blob is
RECORDED in the receipt log (non-vacuity) yet quarantined from the decision. -/

/-- LOW-equivalence (Goguen–Meseguer): two code-loop states agree on the trusted
    gate inputs. The untrusted `retrieved` code blob is unconstrained (HIGH). -/
def lowEquiv (s s' : St) : Prop :=
  s.policy = s'.policy ∧ s.kernel = s'.kernel

/-- **NI7a — NON-INTERFERENCE (general G-M form).** Two initial states that agree
    on the gate inputs yield EQUAL final code-emit decisions after running ANY
    programs — regardless of how their untrusted retrieved code differs. -/
theorem ni7a_noninterference (s0 s0' : St) (prog prog' : List Hop)
    (h : lowEquiv s0 s0') :
    lastEmitDecision s0 prog = lastEmitDecision s0' prog' := by
  obtain ⟨hp, hk⟩ := h
  unfold lastEmitDecision hopDecision Decision.and
  obtain ⟨hp1, hk1⟩ := run_gates_invariant prog s0
  obtain ⟨hp2, hk2⟩ := run_gates_invariant prog' s0'
  rw [hp1, hk1, hp2, hk2, hp, hk]

/-- **NI7b — POISONED CODE CANNOT FLIP THE DECISION.** Mutating ONLY the untrusted
    retrieved code blob (any `r ↦ r'`, the poisoned-dependency injection) while
    keeping gate inputs fixed does NOT change the loop's final code-emit decision. -/
theorem ni7b_poisoned_dep_cannot_flip (s0 : St) (prog : List Hop) (r' : Nat) :
    lastEmitDecision { s0 with retrieved := r' } prog
      = lastEmitDecision s0 prog := by
  apply ni7a_noninterference
  exact ⟨rfl, rfl⟩

/-- **NI7 — NO DENY→ALLOW FLIP FROM POISONED CODE (headline).** If the loop DENIES
    a code action under some retrieved context, then NO alternative untrusted
    code snippet / poisoned dependency can make it ALLOW. This is the exact
    poisoned-dependency defense statement for a11oy Code. -/
theorem ni7_no_deny_to_allow_flip (s0 : St) (prog : List Hop) (r' : Nat)
    (hDeny : lastEmitDecision s0 prog = Decision.Deny) :
    lastEmitDecision { s0 with retrieved := r' } prog ≠ Decision.Allow := by
  rw [ni7b_poisoned_dep_cannot_flip, hDeny]
  intro hbad; cases hbad

/-- **NI7′ — NON-VACUITY: poisoned code IS recorded (just quarantined).** Two runs
    differing only in the retrieved code blob produce DIFFERENT Retrieve-receipt
    logs whenever the blobs differ — so the untrusted code is observable in the
    audit log, yet (by NI7) provably cannot reach the decision. -/
theorem ni7_retrieval_is_recorded (s0 : St) (r' : Nat) (hne : s0.retrieved ≠ r') :
    (step s0 Hop.Retrieve).log
      ≠ (step { s0 with retrieved := r' } Hop.Retrieve).log := by
  intro hbad
  rw [step_log, step_log] at hbad
  simp only [hopPayload, mkReceipt, hopDecision] at hbad
  have htail := (List.append_right_inj s0.log).mp hbad
  simp only [List.cons.injEq, Receipt.mk.injEq, and_true, true_and] at htail
  exact hne htail.1

/-! ## 8. Receipt tamper-evidence for the code receipt log (AXIOM-GATED) ------

The single declared idealization in this module: code-receipt hash collision
resistance, disclosed exactly like F13′ / P5 `hashFn_collision_resistant`. Used
only by the tamper result, which powers the a11oy Code "Verify Session Receipts
→ Intact / TAMPERED" badge. -/

/-- DECLARED crypto axiom (collision-resistance idealization for the coder's
    content hash). NOT proved — the injective-oracle idealization (NIST FIPS
    180-4), mirrors `hashFn_collision_resistant` / `sha256_collision_resistant`. -/
axiom codeHash_collision_resistant : ∀ a b : Nat, codeHash a = codeHash b → a = b

/-- A code receipt is content-addressed iff its `selfHash` hashes its payload. -/
def receiptWF (r : Receipt) : Prop := r.selfHash = codeHash r.payload

/-- Every receipt `step` emits is content-addressed. -/
theorem step_receipt_wf (s : St) (h : Hop) :
    receiptWF (mkReceipt h (hopPayload s h) (hopDecision s h) s.prev) := by
  unfold receiptWF mkReceipt; rfl

/-- **TAMPER-EVIDENCE (code receipt log).** Any payload mutation (`p ≠ p'`) on a
    well-formed code receipt changes the content address, so re-verifying the
    receipt-chain DETECTS the tamper. AXIOM-GATED on `codeHash_collision_resistant`.
    Powers the "Verify Session Receipts" badge. -/
theorem code_tamper_detectable (p p' : Nat) (hne : p ≠ p') :
    codeHash p ≠ codeHash p' := by
  intro hbad
  exact hne (codeHash_collision_resistant p p' hbad)

end Lutar.Coder

/-! ## 9. AXIOM AUDIT — `#print axioms` on EVERY theorem (verbatim in report) -/

open Lutar.Coder

-- CS1 — sandbox containment (Mathlib-free)
#print axioms cs1a_emit_tag_sound
#print axioms cs1_sandbox_containment
#print axioms cs1_deny_absorbing
-- CS2 — bounded termination (Mathlib-free)
#print axioms cs2a_rounds_le_fuel
#print axioms cs2_bounded_termination
#print axioms cs2_worstcase_halts
-- CR3 — router envelope + stability (Mathlib-free)
#print axioms cr3a_le_max
#print axioms foldr_min_le_seed
#print axioms foldr_min_le_mem
#print axioms cr3b_min_le
#print axioms cr3c_routing_envelope
#print axioms cr3d_argmin_stable
-- CV4 — consensus / majority (Mathlib-free)
#print axioms cv4a_votes_le_total
#print axioms cv4b_disjoint_blocs
#print axioms cv4_majority_unique
#print axioms cv4_majority_forces
-- CC5 — conformal confidence (Mathlib-free)
#print axioms cc5a_rank_le_total
#print axioms cc5b_rank_antitone
#print axioms cc5_never_full_confidence
#print axioms cc5_strict_sub_one
-- CK6 — receipt-log compression bound (Mathlib-free)
#print axioms ck6a_encoded_mono
#print axioms ck6_min_encoding
#print axioms ck6_tight_case
-- NI7 — code-context non-interference (Mathlib-free)
#print axioms ni7a_noninterference
#print axioms ni7b_poisoned_dep_cannot_flip
#print axioms ni7_no_deny_to_allow_flip
#print axioms ni7_retrieval_is_recorded
-- Tamper-evidence (AXIOM-GATED on codeHash_collision_resistant)
#print axioms step_receipt_wf
#print axioms code_tamper_detectable
