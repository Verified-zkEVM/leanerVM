/-
  LeanerVM.Protocol.Opening

  The opening phase: the verifier draws the batching challenge, combines the pooled claims by
  its powers into one weighted claim on the stack, and asks the stack that one question. Both
  halves, at the slot's schedule and error.
-/

module

public import LeanerVM.Protocol.Spine.Phase
public import LeanerVM.Protocol.Spine.Errors
public import LeanerVM.Protocol.ClaimWeights
public import LeanerVM.Protocol.ToArkLib.SampleQuery
public import LeanerVM.Protocol.ToArkLib.WeightBatch

/-!
# The opening phase

Specification §8.5, the paragraph "Opening" of the unrolled protocol
(`doc/leanvm/body/08-end-to-end-protocol.tex:94-101` at leanVM
`a386121f84292f6fa663aaa3e570c15bc0240ea2`): every pooled claim is a weighted claim on the stack
`⟨W_j, q⟩ = c_j`, a column claim through the stacking selectors (`ColumnClaim.holds_iff_weighted`)
and the ring-switched claim as it arrives; the verifier sends one batching challenge `λ`; claim
`j` takes the weight `λ^j`, counting from zero, the ring-switched claims first and the column
claims after; the verifier forms `W_λ = Σ_j λ^j·W_j` and `C_λ = Σ_j λ^j·c_j`, asks the stack
`⟨W_λ, q⟩`, and accepts when the answer is `C_λ`. There is no reduction sumcheck: the
inner-product oracle answers the one question, and the compilation replaces the question by an
opening of the commitment.

The phase is `Component.sampleQuery` at the slot's schedule `draw E`: the prover sends nothing,
the verifier draws `ρ` (the specification's `λ`, a keyword in Lean), asks `question` and checks
the answer against `value`. The claim values were sent by the earlier phases, so they are in
the statement before `ρ` is drawn. The pool's order (`pool_weighted`, `pool_column`) is the
deployed verifier's, which takes the powers in two ranges, the ring-switched claims' first
(`crates/pcs/src/stack_open.rs:518-526`).

Perfect completeness: on the Flock seam every pooled claim holds, and the answer to the combined
weight is the combination of the answers (`Weight.pair_batch`). Knowledge soundness at the
slot's error `(J - 1)/|E|`, `J = I.poolSize`: the extractor keeps the trivial witness, since the
stack is the oracle; outside the Flock seam some pooled claim is false, so the claimed values and
the stack's answers differ, and their combinations agree at a root of a nonzero polynomial of
degree less than `J` in `ρ` (`card_false_batch_le`).

Written from the specification; the Rust verifier was read afterwards for the order of the
powers.
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters CompPoly OracleComp OracleSpec ProtocolSpec
open scoped NNReal

@[expose] public section

namespace Opening

variable (I : M3Instance)

/-! ## The pool and the question -/

/-- A column claim as the weighted claim on the stack at the equality kernel of its point
lifted through the layout. -/
def columnWeighted (c : ColumnClaim I) : WeightedClaim I :=
  ⟨eqWeight (I.layout.extend c.col c.point), c.value⟩

/-- The pool in the order of the powers of the challenge: the weighted claims, then the column
claims as weighted claims. -/
def poolList (s : FlockOut I) : List (WeightedClaim I) :=
  s.weighted.toList ++ s.columns.toList.map (columnWeighted I)

theorem length_poolList (s : FlockOut I) : (poolList I s).length = I.poolSize := by
  simp only [poolList, List.length_append, Vector.length_toList, List.length_map,
    M3Instance.poolSize]
  omega

/-- Claim `j` of the pool, the one the `j`-th power of the challenge weighs. -/
def pool (s : FlockOut I) (j : Fin I.poolSize) : WeightedClaim I :=
  (poolList I s)[j.val]'((length_poolList I s).symm ▸ j.isLt)

/-- The weight the stack is asked: the pool's weights combined by the powers of `ρ`. -/
def weight (s : FlockOut I) (ρ : E) : Weight E I.μ :=
  Weight.batch (fun j ↦ (pool I s j).weight) ρ

/-- The value the answer must equal: the pool's values combined by the powers of `ρ`. -/
def value (s : FlockOut I) (ρ : E) : E :=
  powerBatch (fun j ↦ (pool I s j).value) ρ

/-- The question that asks the stack for its inner product with `W`. -/
def ask (W : Weight E I.μ) : [TheOracle I]ₒ.Domain := ⟨0, W⟩

/-- The question to the stack at the challenge `ρ`: the combined weight. -/
def question (s : I.Stmt × FlockOut I) (ρ : E) : [TheOracle I]ₒ.Domain :=
  ask I (weight I s.2 ρ)

/-- An answer is accepted when it is the combined value. -/
def accepts (s : FlockOut I) (ρ a : E) : Bool := decide (a = value I s ρ)

theorem accepts_iff (s : FlockOut I) (ρ a : E) : accepts I s ρ a = true ↔ a = value I s ρ :=
  decide_eq_true_iff

/-- The check on the stack's answer to the question. -/
def check (s : I.Stmt × FlockOut I) (ρ : E) (a : [TheOracle I]ₒ.Range (question I s ρ)) :
    Bool :=
  accepts I s.2 ρ a

/-! ## The order of the powers -/

/-- The weighted claims take the first powers. -/
theorem pool_weighted (s : FlockOut I) (j : Fin I.flockClaims) :
    pool I s ⟨j.val, by have := j.isLt; simp only [M3Instance.poolSize]; omega⟩ =
      s.weighted[j.val] := by
  simp only [pool, poolList]
  rw [List.getElem_append_left (by simp)]
  simp

/-- The column claims take the powers after them, in their order. -/
theorem pool_column (s : FlockOut I) (j : Fin I.pubClaims) :
    pool I s ⟨I.flockClaims + j.val, by have := j.isLt; simp only [M3Instance.poolSize]; omega⟩ =
      columnWeighted I s.columns[j.val] := by
  simp only [pool, poolList]
  rw [List.getElem_append_right (by simp)]
  simp

/-! ## What the claims say -/

/-- A column claim's weighted claim holds exactly when the column claim does. -/
theorem columnWeighted_holds_iff (q : Column I.μ) (c : ColumnClaim I) :
    (columnWeighted I c).Holds q ↔ c.Holds q :=
  (ColumnClaim.holds_iff_weighted q c).symm

/-- Every claim of the pool holds of the stack exactly when every claim the Flock seam carries
does. -/
theorem pool_holds_iff (s : FlockOut I) (q : Column I.μ) :
    (∀ j, (pool I s j).Holds q) ↔
      (∀ c ∈ s.columns.toList, c.Holds q) ∧ ∀ c ∈ s.weighted.toList, c.Holds q := by
  have hpool : (∀ j, (pool I s j).Holds q) ↔ ∀ c ∈ poolList I s, c.Holds q := by
    rw [List.forall_mem_iff_getElem]
    refine ⟨fun h i hi ↦ h ⟨i, length_poolList I s ▸ hi⟩, fun h j ↦ h j.val _⟩
  rw [hpool, poolList, List.forall_mem_append, List.forall_mem_map, and_comm]
  simp only [columnWeighted, ← ColumnClaim.holds_iff_weighted]

/-- Asked a weighted claim's weight, the stack answers the claimed value exactly when the claim
holds. -/
theorem answer_weight_iff (o : ∀ i, TheOracle I i) (c : WeightedClaim I) :
    @Eq E (Component.answerOf (TheOracle I) o (ask I c.weight)) c.value ↔
      c.Holds (theStack o) :=
  Iff.rfl

/-- The stack's answer to the question is the combination of its answers to the pool's
weights. -/
theorem answer_question (s : I.Stmt × FlockOut I) (o : ∀ i, TheOracle I i) (ρ : E) :
    (Component.answerOf (TheOracle I) o (question I s ρ) : E) =
      powerBatch (fun j ↦ (pool I s.2 j).weight.pair (algebraMap K E) (theStack o).values) ρ :=
  Weight.pair_batch (algebraMap K E) _ ρ (theStack o).values

end Opening

/-! ## The phase -/

variable (I : M3Instance)

/-- The opening phase, at its slot: one challenge, then one question to the stack. -/
def openingPhase : Phase.Def I (I.Stmt × FlockOut I) Unit openingSpec :=
  Component.sampleQuery (TheOracle I) E (Opening.question I) (Opening.check I) fun _ _ ↦ ()

namespace Opening

/-- On the Flock seam the check passes at every challenge: every pooled claim holds, so the
answer to the combined weight is the combined value. -/
theorem check_of_flock {s : I.Stmt × FlockOut I} {o : ∀ i, TheOracle I i}
    (h : ((s, o), ()) ∈ Seam.flock I) (ρ : E) :
    check I s ρ (Component.answerOf (TheOracle I) o (question I s ρ)) = true := by
  have hall := (pool_holds_iff I s.2 (theStack o)).mpr h
  exact (accepts_iff I s.2 ρ _).mpr
    ((answer_question I s o ρ).trans (congrArg (powerBatch · ρ) (funext hall)))

/-- Outside the Flock seam at most `J - 1` challenges pass the check, `J` the size of the pool:
the claimed values and the stack's answers differ, and their combinations agree at a root of
their difference. -/
theorem card_badQuery_le (s : I.Stmt × FlockOut I) (o : ∀ i, TheOracle I i) :
    Nat.card {ρ // Component.badQuery (TheOracle I) E (question I) (check I) (fun _ _ ↦ ())
      (relIn := Seam.flock I) (relOut := Seam.done I) s o ρ} ≤ I.poolSize - 1 := by
  classical
  rw [natCard_subtype_eq_card_filter]
  by_cases hin : ((s, o), ()) ∈ Seam.flock I
  · refine le_trans (le_of_eq ?_) (Nat.zero_le _)
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro ρ - ⟨w, hw, -⟩
    exact hw hin
  · have hfalse : ∃ j, (pool I s.2 j).weight.pair (algebraMap K E) (theStack o).values ≠
        (pool I s.2 j).value := by
      by_contra hall
      exact hin ((pool_holds_iff I s.2 (theStack o)).mp fun j ↦
        not_not.mp fun hj ↦ hall ⟨j, hj⟩)
    refine (Finset.card_le_card fun ρ hρ ↦ ?_).trans (card_false_batch_le _ _ hfalse)
    obtain ⟨-, -, hc, -⟩ := (Finset.mem_filter.mp hρ).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (answer_question I s o ρ).symm.trans ((accepts_iff I s.2 ρ _).mp hc)⟩

end Opening

/-- The completeness half. -/
def openingComplete : Phase.Complete I (openingPhase I) (Seam.flock I) (Seam.done I) :=
  Component.sampleQueryComplete (TheOracle I) E (Opening.question I) (Opening.check I) _
    fun _ _ _ h ρ ↦ ⟨Opening.check_of_flock I h ρ, trivial⟩

/-- The security half, at the slot's error, with the extractor that keeps the trivial
witness. -/
def openingSecurity :
    Phase.Security I (openingPhase I) (Seam.flock I) (Seam.done I) (openingError I) :=
  Component.Security.mono
    (fun _ ↦ le_of_eq (by rw [drawError, openingError, drawError, overE,
      Nat.card_eq_fintype_card]))
    (Component.sampleQuerySecurity (TheOracle I) E (Opening.question I) (Opening.check I) _
      (I.poolSize - 1) (Opening.card_badQuery_le I))

/-
The protocol's five phases, once the bus phase, the table sumcheck and the Flock phase exist,
with the bus phase's side conditions as hypotheses:

def leanVmPhases (I : M3Instance) (h₁ : 1 ≤ I.d) (h₂ : …) : Phases I where
  bus := busPhase I h₁ h₂
  table := tableSumcheck I
  pub := deployedPublicInputPhase I
  flock := flockPhase I
  opening := openingPhase I
-/

end
end LeanerVM.Protocol
