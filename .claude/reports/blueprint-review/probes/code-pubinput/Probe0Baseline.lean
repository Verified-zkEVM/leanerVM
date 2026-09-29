/-
  LeanerVM.Protocol.PublicInput

  The public-input phase: the verifier draws a challenge, the prover sends the values it claims
  for the public columns on the line through their first two cells, and the verifier checks
  those values against the public statement and pools the claims. Both halves proved.
-/

module

public import LeanerVM.Protocol.Spine.Phase
public import LeanerVM.Protocol.ToArkLib.GuardedVerdict
public import LeanerVM.Protocol.ToArkLib.KeepOracles
import LeanerVM.Protocol.ToCompPoly.Multilinear
import LeanerVM.Protocol.ToVCVio.UniformSample
import Mathlib.Algebra.CharP.Two

/-!
# The public-input phase

Specification §8.2 (`doc/leanvm/body/08-end-to-end-protocol.tex:27-33`, and the paragraph
"Public input" of the unrolled protocol, `:80-85`, at leanVM
`a386121f84292f6fa663aaa3e570c15bc0240ea2`): the public input is the first two memory cells,
both parties know them, and

1. the verifier samples `r ∈ E`;
2. the prover sends `c₀, c₁`, claiming `c_ℓ` is the extension of memory limb `ℓ` at
   `(r, 0, …, 0)`;
3. the verifier checks `c_ℓ = (1 + r)·mem[g⁰]_ℓ + r·mem[g¹]_ℓ` for `ℓ ∈ {0, 1}`, rejecting
   otherwise, and pools `c₀, c₁`, with `0` for the top limb, as claims on the three memory limbs
   at `(r, 0, …, 0)`.

Over an abstract instance the memory limbs are the instance's public lines, columns whose cells
0 and 1 the statement fixes; each line says whether its value is sent. The prover sends the
values of the lines that are, in order, as one message. The verifier checks that message
against the lines' values, which fixes its length too, and pools one claim per line at the
line's value: for a line whose value was sent that is the value sent, since the check has just
passed, and for the others it is the value the verifier computes.

Perfect completeness: on a stack whose lines hold, every pooled claim is true, by the identity
`q̃(r, 0, …, 0) = (1 - r)·q(0) + r·q(1)` and `-1 = 1` in `E`. Knowledge soundness at `1/|E|`:
the extractor keeps the trivial witness, since the stack is the oracle; if the pooled claims
hold and some line's cells differ from the statement's, that line's claim is a nonzero
polynomial of degree one in `r`, true at one challenge at most, whatever the number of lines.

Written from the specification; the Rust verifier was read afterwards. It reads the same
transcript and checks one equation on the two public words instead of one per limb,
`c₀ + y·c₁ = (1 + r)·w₀ + r·w₁` (`crates/lean_vm/src/cpu/mod.rs:752-755`). The two equations
here imply that one, and it accepts transcripts they reject, so the theorems below are about
the specification's verifier.
-/

namespace LeanerVM.Protocol.Probe0

open LeanerVM.Parameters CompPoly OracleComp OracleSpec ProtocolSpec
open scoped NNReal ENNReal

@[expose] public section

namespace PublicInput

/-! ## The line through cells 0 and 1 -/

/-- The point `(r, 0, …, 0)` of `E^n`, at which §8.2 evaluates the memory limbs. -/
def linePoint {n : ℕ} (hn : 0 < n) (r : E) : Vector E n :=
  Vector.cast (by omega : 1 + (n - 1) = n) (#v[r] ++ Vector.replicate (n - 1) (0 : E))

/-- The extension of a column on the line through its cells 0 and 1:
`q̃(r, 0, …, 0) = (1 - r)·q(0) + r·q(1)`. The zero coordinates select the first two cells, and
the first coordinate interpolates between them. -/
theorem eval₂Mle_linePoint {n : ℕ} (hn : 0 < n) (q : CMlPolynomialEval K n) (r : E) :
    CMlPolynomialEval.eval₂Mle q (algebraMap K E) (linePoint hn r) =
      (1 - r) * ofK (q.get ⟨0, Nat.two_pow_pos n⟩) +
        r * ofK (q.get ⟨1, Nat.one_lt_two_pow hn.ne'⟩) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h : 1 + m = m + 1 := Nat.add_comm 1 m
  -- The column as a table on `1 + m` variables, and the point as `(r)` followed by `m` zeros.
  have hq : CMlPolynomialEval.eval₂Mle q (algebraMap K E) (linePoint hn r) =
      CMlPolynomialEval.eval₂Mle
        (Vector.cast (congrArg (2 ^ ·) h) (Vector.cast (congrArg (2 ^ ·) h.symm) q))
        (algebraMap K E) (Vector.cast h (#v[r] ++ Vector.replicate m (0 : E))) := by
    simp only [linePoint, Nat.add_one_sub_one, Vector.cast_cast, Vector.cast_rfl]
  -- The zero coordinates select the slice at index zero; one variable is left.
  rw [hq, eval₂Mle_cast (algebraMap K E) h, CMlPolynomialEval.eval₂Mle, ← boolVec_zero,
    evalMle_append_boolVec, CMlPolynomialEval.evalMle_succ, CMlPolynomialEval.evalMle_zero,
    CMlPolynomialEval.evalMleLayer_get]
  simp only [Vector.head, Nat.reduceAdd, Vector.getElem_mk, List.getElem_toArray,
    List.getElem_cons_zero, Nat.reducePow, slice, CMlPolynomialEval.map,
    Extension.Ext.algebraMap_eq_ofBase, cubeIndex, pow_one, mul_zero, add_zero, Fin.getElem_fin,
    Vector.getElem_map, Vector.getElem_cast, Fin.zero_eta, Fin.isValue, Vector.get_eq_getElem,
    Fin.coe_ofNat_eq_mod, Nat.zero_mod, Vector.getElem_ofFn, zero_add, Fin.mk_one, Nat.mod_succ,
    Fin.mk_zero']

/-! ## The schedule -/

/-- The schedule: the verifier's challenge in `E`, then the prover's values. The message is a
list; the verifier's check fixes its length, one value per line whose value is sent. -/
@[reducible]
def pSpec : ProtocolSpec 2 := ⟨!v[.V_to_P, .P_to_V], !v[E, List E]⟩

instance : ∀ i, OracleInterface (pSpec.Message i)
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => OracleInterface.instDefault

instance : ∀ i, SampleableType (pSpec.Challenge i)
  | ⟨0, _⟩ => (inferInstance : SampleableType E)
  | ⟨1, h⟩ => nomatch h

/-- The knowledge error: `1/|E|`, charged to the one challenge. A real number, so
`noncomputable`; the prover, the verifier, the check and the pool are computable. -/
noncomputable def error : ℝ≥0 := 1 / Fintype.card E

/-! ## Values, check and claims -/

variable (I : M3Instance)

/-- The value of a public line at the challenge `r`: the line through the statement's two
cells, `(1 + r)·cell0 + r·cell1`. -/
def lineValue (r : E) (l : PublicLine I.toShape) : E :=
  (1 + r) * ofK l.cell0 + r * ofK l.cell1

/-- The claim that a line's column takes the line's value at `(r, 0, …, 0)`. -/
def lineClaim (r : E) (l : PublicLine I.toShape) : ColumnClaim I :=
  ⟨l.col, linePoint l.pos r, lineValue I r l⟩

/-- What the verifier pools: the claims it received, then one claim per public line. -/
def pooled (s : I.Stmt × TableOut I) (r : E) : I.Stmt × PubOut I :=
  (s.1, ⟨s.2.columns ++ (I.publicLines s.1).map (lineClaim I r)⟩)

/-- The values the verifier expects in the prover's message: the values at the challenge of the
lines whose value is sent, in order. -/
def expectedValues (input : I.Stmt) (r : E) : List E :=
  ((I.publicLines input).filter (·.sent)).map (lineValue I r)

/-- The verifier's check: the prover's message is the expected values. -/
def check (s : I.Stmt × TableOut I) (r : E) (cs : List E) : Bool :=
  decide (cs = expectedValues I s.1 r)

/-- A line's claim holds of the stack exactly when the line through the stack's two cells,
evaluated at `r`, is the line through the statement's. -/
private theorem lineClaim_holds_iff (q : Column I.μ) (r : E) (l : PublicLine I.toShape) :
    (lineClaim I r l).Holds q ↔
      (1 - r) * ofK ((I.column q l.col).values.get ⟨0, Nat.two_pow_pos _⟩) +
          r * ofK ((I.column q l.col).values.get ⟨1, Nat.one_lt_two_pow l.pos.ne'⟩) =
        (1 + r) * ofK l.cell0 + r * ofK l.cell1 := by
  unfold ColumnClaim.Holds lineClaim
  rw [eval₂Mle_linePoint l.pos]
  exact Iff.rfl

/-- Two lines through cells in `K` that differ agree at one challenge at most: the difference is
a polynomial of degree one in `r` with a nonzero coefficient. -/
private theorem line_challenge_unique {a b c0 c1 : K} (hne : ¬ (a = c0 ∧ b = c1)) {r₁ r₂ : E}
    (h₁ : (1 - r₁) * ofK a + r₁ * ofK b = (1 + r₁) * ofK c0 + r₁ * ofK c1)
    (h₂ : (1 - r₂) * ofK a + r₂ * ofK b = (1 + r₂) * ofK c0 + r₂ * ofK c1) : r₁ = r₂ := by
  have e₁ : (ofK a - ofK c0) + r₁ * (ofK b - ofK a - ofK c0 - ofK c1) = 0 := by
    linear_combination h₁
  have e₂ : (ofK a - ofK c0) + r₂ * (ofK b - ofK a - ofK c0 - ofK c1) = 0 := by
    linear_combination h₂
  by_cases hβ : ofK b - ofK a - ofK c0 - ofK c1 = 0
  · exfalso
    apply hne
    have hα : ofK a = ofK c0 := by
      rw [hβ, mul_zero, add_zero, sub_eq_zero] at e₁
      exact e₁
    refine ⟨ofK_injective hα, ofK_injective ?_⟩
    have hb : ofK b = ofK c0 + ofK c0 + ofK c1 := by linear_combination hβ + hα
    rw [hb, CharTwo.add_self_eq_zero, zero_add]
  · have h : (r₁ - r₂) * (ofK b - ofK a - ofK c0 - ofK c1) = 0 := by
      linear_combination e₁ - e₂
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hβ)

/-- On a stack in the table seam, the pool is in the public seam: the received claims still
hold, and each line's claim holds by the line identity. -/
private theorem pooled_mem_pub (s : I.Stmt × TableOut I) (o : ∀ i, TheOracle I i)
    (h : ((s, o), ()) ∈ Seam.table I) (r : E) : ((pooled I s r, o), ()) ∈ Seam.pub I := by
  obtain ⟨hcols, hlines, haux⟩ := h
  refine ⟨fun c hc ↦ ?_, haux⟩
  rcases List.mem_append.mp hc with hc | hc
  · exact hcols c hc
  · obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hc
    obtain ⟨h0, h1⟩ := hlines l hl
    rw [lineClaim_holds_iff, h0, h1, CharTwo.sub_eq_add]

/-- A challenge is bad for a stack and statement outside the table seam when the pool at that
challenge is inside the public seam; two bad challenges are equal. -/
private theorem bad_challenge_unique (s : I.Stmt × TableOut I) (o : ∀ i, TheOracle I i)
    (hin : ((s, o), ()) ∉ Seam.table I) {r₁ r₂ : E}
    (h₁ : ((pooled I s r₁, o), ()) ∈ Seam.pub I)
    (h₂ : ((pooled I s r₂, o), ()) ∈ Seam.pub I) : r₁ = r₂ := by
  obtain ⟨hcols₁, haux⟩ := h₁
  obtain ⟨hcols₂, -⟩ := h₂
  have hold : ∀ c ∈ s.2.columns, c.Holds (theStack o) := fun c hc ↦
    hcols₁ c (List.mem_append_left _ hc)
  have hlines : ¬ I.PublicLinesHold s.1 (theStack o) := fun hl ↦ hin ⟨hold, hl, haux⟩
  simp only [M3Instance.PublicLinesHold, not_forall] at hlines
  obtain ⟨l, hl, hne⟩ := hlines
  have hc₁ := hcols₁ _ (List.mem_append_right _ (List.mem_map_of_mem hl))
  have hc₂ := hcols₂ _ (List.mem_append_right _ (List.mem_map_of_mem hl))
  rw [lineClaim_holds_iff] at hc₁ hc₂
  exact line_challenge_unique hne hc₁ hc₂

/-! ## The reduction -/

/-- The prover: receives the challenge, sends the values of the lines whose value is sent,
keeps the stack, and outputs the pool. The values are functions of the public statement and the
challenge; on a stack whose lines hold they are the extensions of its columns at
`(r, 0, …, 0)`. -/
def prover : OracleProver []ₒ (I.Stmt × TableOut I) (TheOracle I) Unit
    (I.Stmt × PubOut I) (TheOracle I) Unit pSpec where
  PrvState
    | ⟨0, _⟩ => ((I.Stmt × TableOut I) × ∀ i, TheOracle I i) × Unit
    | _ => E × (((I.Stmt × TableOut I) × ∀ i, TheOracle I i) × Unit)
  input := _root_.id
  receiveChallenge
    | ⟨0, _⟩ => fun st ↦ pure fun r ↦ (r, st)
    | ⟨1, h⟩ => nomatch h
  sendMessage
    | ⟨0, h⟩ => nomatch h
    | ⟨1, _⟩ => fun st ↦ pure (expectedValues I st.2.1.1.1 st.1, st)
  output := fun st ↦ pure ((pooled I st.2.1.1 st.1, st.2.1.2), ())

/-- The verifier reads the prover's message. -/
def queryValues : OracleComp [pSpec.Message]ₒ (List E) :=
  liftM <| OracleSpec.query
    (show [pSpec.Message]ₒ.Domain from ⟨⟨1, by rfl⟩, (by change Unit; exact ())⟩)

/-- The verifier: reads the prover's values, rejects unless they are the expected values at the
challenge, pools one claim per line, and keeps the stack as the oracle. -/
def verifier : OracleVerifier []ₒ (I.Stmt × TableOut I) (TheOracle I)
    (I.Stmt × PubOut I) (TheOracle I) pSpec where
  verify := fun s chals ↦ do
    let cs ← liftM queryValues
    if check I s (chals ⟨0, rfl⟩) cs then pure (pooled I s (chals ⟨0, rfl⟩)) else failure
  outputOracle := .inl (keepOracles (TheOracle I) pSpec)

/-! ## The verifier's verdict -/

/-- Reading the prover's message returns the transcript's entry. -/
private theorem simulateQ_queryValues (o : ∀ i, TheOracle I i) (tr : pSpec.FullTranscript) :
    simulateQ (OracleInterface.simOracle2 []ₒ o tr.messages)
      (OptionT.lift (liftM queryValues :
        OracleComp ([]ₒ + ([TheOracle I]ₒ + [pSpec.Message]ₒ)) (List E))).run =
      (pure (tr 1) : OptionT (OracleComp []ₒ) (List E)) := by
  have h : simulateQ (OracleInterface.simOracle2 []ₒ o tr.messages)
      (liftM queryValues :
        OracleComp ([]ₒ + ([TheOracle I]ₒ + [pSpec.Message]ₒ)) (List E)) =
      pure (tr 1) := rfl
  rw [OptionT.run_lift, simulateQ_bind, h, pure_bind, simulateQ_pure]
  rfl

/-- As an ordinary verifier: if the transcript's values pass the check at the transcript's
challenge, the verdict is the pool at that challenge and the stack; otherwise it rejects. -/
theorem verifier_verify (s : I.Stmt × TableOut I) (o : ∀ i, TheOracle I i)
    (tr : pSpec.FullTranscript) :
    (verifier I).toVerifier.verify (s, o) tr =
      if check I s (tr 0) (tr 1) then pure (pooled I s (tr 0), o) else failure := by
  simp only [OracleVerifier.toVerifier]
  rw [OracleVerifier.materializeOutput_of_keepOracles _ rfl]
  simp only [verifier]
  rw [show (liftM queryValues :
        OptionT (OracleComp ([]ₒ + ([TheOracle I]ₒ + [pSpec.Message]ₒ))) (List E)) =
      OptionT.lift (liftM queryValues :
        OracleComp ([]ₒ + ([TheOracle I]ₒ + [pSpec.Message]ₒ)) (List E)) from
    (OracleComp.monadLift_liftM_OptionT _).symm]
  rw [simulateQ_optionT_bind_run, simulateQ_queryValues, pure_bind]
  by_cases h : check I s (tr 0) (tr 1) = true
  · rw [if_pos h, if_pos h]
    rfl
  · rw [if_neg h, if_neg h]
    rfl

/-- The verifier is a check followed by a verdict, as data. -/
def guarded : (verifier I).toVerifier.GuardedForm where
  check := fun p tr ↦ check I p.1 (tr 0) (tr 1)
  out := fun p tr ↦ (pooled I p.1 (tr 0), p.2)
  verify_eq := fun ⟨s, o⟩ tr ↦ verifier_verify I s o tr

/-! ## Completeness -/

/-- In every run of the prover, the message is the expected values at the transcript's
challenge and the output is the pool at that challenge, with the stack. -/
private theorem prover_run_support (s : I.Stmt × TableOut I) (o : ∀ i, TheOracle I i)
    (pr : pSpec.FullTranscript × ((I.Stmt × PubOut I) × ∀ i, TheOracle I i) × Unit)
    (hpr : pr ∈ support ((prover I).run (s, o) ())) :
    pr.1 1 = expectedValues I s.1 (pr.1 0) ∧ pr.2 = ((pooled I s (pr.1 0), o), ()) := by
  have h0 : pSpec.dir 0 = .V_to_P := rfl
  have h1 : pSpec.dir 1 = .P_to_V := rfl
  simp only [Prover.run, Prover.runToRound, Fin.induction_two,
    Prover.processRound_of_dir_eq_V_to_P 0 h0, Prover.processRound_of_dir_eq_P_to_V 1 h1] at hpr
  simp only [ChallengeIdx, Fin.vcons_fin_zero, Nat.reduceAdd, Challenge, Fin.reduceLast, prover,
    Fin.isValue, MessageIdx, Message, Fin.castSucc_zero, Fin.succ_zero_eq_one, Fin.castSucc_one,
    Fin.succ_one_eq_two, id_eq, HasQuery.instOfMonadLift_query, toPFunctor_emptySpec, liftM_pure,
    bind_pure_comp, map_pure, pure_bind, Functor.map_map, support_map, Set.mem_image] at hpr
  obtain ⟨r, -, rfl⟩ := hpr
  -- The transcript is the challenge followed by the message; its two entries are read off.
  exact ⟨rfl, rfl⟩

/-- Perfect completeness: from the table seam, the prover's values pass the check at every
challenge and the pool lands in the public seam. -/
theorem complete {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (OracleReduction.mk (prover I) (verifier I)).perfectCompleteness init impl (Seam.table I)
      (Seam.pub I) := by
  apply Reduction.perfectCompleteness_of_run_support
  intro stmtIn witIn hIn x hx
  obtain ⟨s, o⟩ := stmtIn
  obtain ⟨pr, hpr, rfl⟩ := Reduction.mem_support_run_of_guarded _ (guarded I) (s, o) witIn hx
  obtain ⟨hmsg, hout⟩ := prover_run_support I s o pr hpr
  have hc : (guarded I).check (s, o) pr.1 = true := decide_eq_true hmsg
  rw [if_pos hc]
  exact ⟨_, rfl, pooled_mem_pub I s o hIn (pr.1 0), congrArg Prod.fst hout⟩

/-! ## Knowledge soundness -/

/-- The extractor keeps the trivial witness: the stack is the oracle. The shared oracle is
written `OracleSpec.emptySpec.{0, 0}` rather than `[]ₒ` to pin a universe
`Extractor.RoundByRound` leaves free. -/
def extractor : Extractor.RoundByRound (OracleSpec.emptySpec.{0, 0})
    ((I.Stmt × TableOut I) × ∀ i, TheOracle I i) Unit Unit pSpec (fun _ ↦ Unit) where
  eqIn := rfl
  extractMid := fun _ _ _ _ ↦ ()
  extractOut := fun _ _ _ ↦ ()

variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))

/-- The knowledge state function: before the challenge, the table seam; after the challenge,
the public seam of the pool; after the prover's values, that the check passes as well. -/
def stateFunction :
    (verifier I).toVerifier.KnowledgeStateFunction init impl (Seam.table I) (Seam.pub I)
      (extractor I) where
  toFun := fun m stmt tr _ ↦
    if h0 : m.val = 0 then ((stmt, ()) ∈ Seam.table I)
    else if h1 : m.val = 1 then
      ((pooled I stmt.1 (tr ⟨0, by omega⟩), stmt.2), ()) ∈ Seam.pub I
    else
      check I stmt.1 (tr ⟨0, by omega⟩) (tr ⟨1, by omega⟩) = true ∧
        ((pooled I stmt.1 (tr ⟨0, by omega⟩), stmt.2), ()) ∈ Seam.pub I
  toFun_empty := fun _ _ ↦ Iff.rfl
  toFun_next := fun m hm stmt tr msg w h ↦ by
    have hm1 : m = 1 := by
      fin_cases m
      · exact absurd hm (by decide)
      · rfl
    subst hm1
    exact h.2
  toFun_full := fun stmt tr _ h ↦
    Verifier.GuardedForm.of_probEvent_pos (guarded I) init impl stmt tr _ h

/-- Round-by-round knowledge soundness at `1/|E|`: a bad transition is a bad challenge, and
there is at most one. -/
theorem rbr :
    (verifier I).toVerifier.rbrKnowledgeSoundnessWorstCaseWith init impl (Seam.table I)
      (Seam.pub I) (fun _ ↦ Unit) (extractor I) (stateFunction I init impl)
      (fun _ ↦ error) := by
  intro stmtIn i tr
  obtain ⟨s, o⟩ := stmtIn
  obtain ⟨i, hi⟩ := i
  have hi0 : i = 0 := by
    fin_cases i
    · rfl
    · exact absurd hi (by decide)
  subst hi0
  refine le_trans (probEvent_mono ?_) (probEvent_uniformSample_le_of_subsingleton (α := E)
    (fun r ↦ ((s, o), ()) ∉ Seam.table I ∧ ((pooled I s r, o), ()) ∈ Seam.pub I)
    fun r₁ r₂ h₁ h₂ ↦ bad_challenge_unique I s o h₁.1 h₁.2 h₂.2)
  rintro r - ⟨_, hin, hout⟩
  exact ⟨hin, hout⟩

end PublicInput

/-! ## The phase -/

variable (I : M3Instance)

/-- The public-input phase: one challenge, one prover message, error `1/|E|`. `noncomputable`
because of the error alone: its prover and its verifier run. -/
noncomputable def publicInputPhase :
    Phase.Def I (I.Stmt × TableOut I) (I.Stmt × PubOut I) where
  n := 2
  pSpec := PublicInput.pSpec
  red := ⟨PublicInput.prover I, PublicInput.verifier I⟩
  err := fun _ ↦ PublicInput.error

/-- The completeness half. -/
def publicInputComplete :
    Phase.Complete I (publicInputPhase I) (Seam.table I) (Seam.pub I) where
  outputPure := ⟨_, fun _ ↦ rfl⟩
  guarded := PublicInput.guarded I
  complete := PublicInput.complete I

/-- The security half, with the extractor that keeps the trivial witness. -/
def publicInputSecurity :
    Phase.Security I (publicInputPhase I) (Seam.table I) (Seam.pub I) where
  toComplete := publicInputComplete I
  witMid := fun _ ↦ Unit
  extractor := PublicInput.extractor I
  kSF := PublicInput.stateFunction I
  rbr := PublicInput.rbr I

end
end LeanerVM.Protocol.Probe0

open LeanerVM.Protocol.Probe0 in
#print axioms publicInputSecurity
open LeanerVM.Protocol.Probe0 in
#print axioms publicInputComplete
