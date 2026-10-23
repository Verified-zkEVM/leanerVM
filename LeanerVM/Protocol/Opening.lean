/-
  LeanerVM.Protocol.Opening

  The opening phase: the verifier draws the batching challenge, combines the pooled claims by
  its powers into one weighted claim on the stack, and asks the stack that one question. Both
  halves, at the slot's schedule and error.
-/

module

public import LeanerVM.Protocol.Spine.Phase
public import LeanerVM.Protocol.Spine.Errors
public import LeanerVM.Protocol.ToArkLib.QueryCheck
public import LeanerVM.Protocol.ToArkLib.WeightBatch
public import LeanerVM.Protocol.ToCompPoly.EqBatch
import LeanerVM.Protocol.ClaimWeights

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

The phase is batching by powers followed by a query check (`Component.batchQuery`), at the
slot's schedule `draw E`: `Component.batch` draws `ρ` (the specification's `λ`, a keyword in
Lean) and combines the pooled values into the batched claim `⟨W_ρ, C_ρ⟩` (`batched`); the query
check asks the stack the batched claim's weight and accepts when the answer is its value. The
claim values were sent by the earlier phases, so they are in the statement before `ρ` is drawn.
The pool's order (`pool_weighted`, `pool_column`) is the deployed verifiers': the ring-switched
claims take the first powers (`crates/pcs/src/stack_open.rs:518-526`,
`python-verifier/verifier.py:1409-1413`).

Perfect completeness: on the Flock seam every pooled claim holds, so the batched claim holds at
every challenge (`Weight.pair_batch`), and the stack's answer is its value. Knowledge soundness
at the slot's error `(J - 1)/|E|`, `J = I.poolSize`, with the extractor that keeps the trivial
witness, since the stack is the oracle: before the challenge, every pooled claim holds; after
it, the batched claim holds (`BatchedHolds`). The stack's answers to the pooled weights are
fixed before the challenge; outside the Flock seam they differ from the claimed values, and the
batched claim holds only at a root of their difference, a nonzero polynomial of degree less
than `J` in `ρ` (`batchSecurity`).

Compiled code computes the batched weight's values by `weightCube` (`weight_eq_weightFast`,
`@[csimp]`, registered before `batched`): a column claim's point read through the layout has the
block's selector bits as coordinates, so its equality kernel vanishes off the block, and
`eqBatch` combines the column claims' kernels on their blocks (`weightCube_eq`).

Written from the specification; the Rust and Python verifiers were read afterwards for the
order of the powers.
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters CompPoly OracleComp OracleSpec ProtocolSpec
open scoped NNReal

@[expose] public section

namespace Opening

variable (I : M3Instance)

/-! ## The pool and the batched claim -/

/-- A column claim as the weighted claim on the stack at the equality kernel of its point
lifted through the layout. -/
def columnWeighted (c : ColumnClaim I) : WeightedClaim I :=
  ⟨eqWeight (I.layout.extend c.col c.point), c.value⟩

/-- The pool in the order of the powers of the challenge: the weighted claims, then the column
claims as weighted claims. -/
def poolList (s : FlockOut I) : List (WeightedClaim I) :=
  s.weighted.toList ++ s.columns.toList.map (columnWeighted I)

/-- The pool has `I.poolSize` claims. -/
theorem length_poolList (s : FlockOut I) : (poolList I s).length = I.poolSize := by
  simp only [poolList, List.length_append, Vector.length_toList, List.length_map,
    M3Instance.poolSize]
  omega

/-- Claim `j` of the pool, the one the `j`-th power of the challenge weighs. -/
def pool (s : FlockOut I) (j : Fin I.poolSize) : WeightedClaim I :=
  (poolList I s)[j.val]'((length_poolList I s).symm ▸ j.isLt)

/-- The pool's claimed values. -/
def values (s : I.Stmt × FlockOut I) (j : Fin I.poolSize) : E := (pool I s.2 j).value

/-- The pool's weights combined by the powers of `ρ`. -/
def weight (s : I.Stmt × FlockOut I) (ρ : E) : Weight E I.μ :=
  Weight.batch (fun j ↦ (pool I s.2 j).weight) ρ

/-- The batched weight's values: the weighted claims' values combined by the powers of `ρ`, the
column claims' equality kernels combined coordinate by coordinate (`eqBatch`), each on the block
its point's selector bits pick. -/
def weightCube (s : I.Stmt × FlockOut I) (ρ : E) : CMlPolynomialEval E I.μ :=
  let dense := batchWeight (fun j : Fin I.flockClaims ↦ s.2.weighted[j].weight.onCube) ρ
  let cols := eqBatch I.μ ((List.finRange I.pubClaims).map fun j ↦
    (ρ ^ (I.flockClaims + j.val), I.layout.extend s.2.columns[j].col s.2.columns[j].point))
  Vector.ofFn fun x ↦ dense[x] + cols[x]

/-- A sum over the pool: the weighted claims, then the column claims. -/
private theorem sum_pool (s : FlockOut I) (G : WeightedClaim I → ℕ → E) :
    ∑ j : Fin I.poolSize, G (pool I s j) j.val =
      ∑ j : Fin I.flockClaims, G s.weighted[j] j.val +
        ∑ j : Fin I.pubClaims, G (columnWeighted I s.columns[j]) (I.flockClaims + j.val) := by
  have hlen := length_poolList I s
  let g : ℕ → E := fun j ↦ if h : j < (poolList I s).length then G (poolList I s)[j] j else 0
  have hg : ∀ j : Fin I.poolSize, G (pool I s j) j.val = g j.val := fun j ↦ by
    simp only [g, pool, hlen, j.isLt, dite_true]
  have hps : I.poolSize = I.pubClaims + I.flockClaims := rfl
  have hw : ∀ j : Fin I.flockClaims, G s.weighted[j] j.val = g j.val := fun j ↦ by
    have hj : j.val < (poolList I s).length := by rw [hlen, hps]; omega
    simp only [g, hj, dite_true]
    congr 1
    simp [poolList, List.getElem_append_left]
  have hc : ∀ j : Fin I.pubClaims, G (columnWeighted I s.columns[j]) (I.flockClaims + j.val) =
      g (I.flockClaims + j.val) := fun j ↦ by
    have hj : I.flockClaims + j.val < (poolList I s).length := by rw [hlen, hps]; omega
    simp only [g, hj, dite_true]
    congr 1
    simp [poolList, List.getElem_append_right]
  simp only [hg, hw, hc]
  rw [Fin.sum_univ_eq_sum_range g, Fin.sum_univ_eq_sum_range g,
    Fin.sum_univ_eq_sum_range (fun j ↦ g (I.flockClaims + j)), M3Instance.poolSize,
    Nat.add_comm I.pubClaims, Finset.sum_range_add]

/-- The values so computed are the batched weight's. -/
theorem weightCube_eq (s : I.Stmt × FlockOut I) (ρ : E) :
    weightCube I s ρ = batchWeight (fun j ↦ (pool I s.2 j).weight.onCube) ρ := by
  refine Vector.ext fun x hx ↦ ?_
  have hcols : ∀ L : List (Fin I.pubClaims),
      ((L.map fun j ↦ (ρ ^ (I.flockClaims + j.val),
        I.layout.extend s.2.columns[j.val].col s.2.columns[j.val].point)).map
        fun t ↦ t.1 * (CMlPolynomialEval.lagrangeBasis t.2)[x]).sum =
      (L.map fun j ↦ (columnWeighted I s.2.columns[j]).weight.onCube[x] *
        ρ ^ (I.flockClaims + j.val)).sum := by
    intro L
    induction L with
    | nil => rfl
    | cons j L ih =>
      rw [List.map_cons, List.map_cons, List.sum_cons, ih, List.map_cons, List.sum_cons,
        mul_comm (ρ ^ (I.flockClaims + j.val))]
      rfl
  simp only [weightCube, batchWeight, powerBatch, Fin.getElem_fin, Vector.getElem_ofFn]
  rw [sum_pool I s.2 fun c j ↦ c.weight.onCube[x] * ρ ^ j, eqBatch_getElem _ _ x hx]
  exact congrArg₂ (· + ·) rfl ((hcols _).trans (Fin.sum_univ_def _).symm)

/-- The batched weight with its values computed by `weightCube`. -/
def weightFast (s : I.Stmt × FlockOut I) (ρ : E) : Weight E I.μ where
  cube := .mk fun _ ↦ weightCube I s ρ
  mle := (weight I s ρ).mle
  mle_eq r := by
    rw [(weight I s ρ).mle_eq r]
    exact congrArg (CMlPolynomialEval.evalMle · r) (weightCube_eq I s ρ).symm

/-- Compiled code computes the batched weight's values by `weightCube`: the column claims'
equality kernels on their blocks, not `I.poolSize` tables of `2 ^ I.μ` entries. -/
@[csimp] theorem weight_eq_weightFast : @weight = @weightFast := by
  funext I s ρ
  unfold weightFast
  conv_lhs => unfold weight Weight.batch
  congr 1
  exact congrArg Thunk.mk (funext fun _ ↦ (weightCube_eq I s ρ).symm)

/-- The batched claim at `ρ`: the combined weight, claimed to answer `c`, the combined value
batching by powers computes. -/
def batched (s : I.Stmt × FlockOut I) (ρ c : E) : WeightedClaim I := ⟨weight I s ρ, c⟩

/-- After the challenge: the batched claim holds of the stack. -/
def BatchedHolds : Set ((WeightedClaim I × ∀ i, TheOracle I i) × Unit) :=
  {p | p.1.1.Holds (theStack p.1.2)}

/-- The question a weighted claim asks the stack: its inner product with the claim's weight. -/
def question (c : WeightedClaim I) : [TheOracle I]ₒ.Domain := ⟨0, c.weight⟩

/-- An answer is accepted when it is the claim's value. -/
def accepts (c : WeightedClaim I) (a : E) : Bool := decide (a = c.value)

/-- The acceptance is the equality. -/
theorem accepts_iff (c : WeightedClaim I) (a : E) : accepts I c a = true ↔ a = c.value :=
  decide_eq_true_iff

/-- The check on the stack's answer to a claim's weight. -/
def check (c : WeightedClaim I) (a : [TheOracle I]ₒ.Range (question I c)) : Bool :=
  accepts I c a

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

/-- Asked a weighted claim's weight, the stack answers the claimed value exactly when the claim
holds. -/
theorem answer_weight_iff (o : ∀ i, TheOracle I i) (c : WeightedClaim I) :
    @Eq E (Component.answerOf (TheOracle I) o (question I c)) c.value ↔
      c.Holds (theStack o) :=
  Iff.rfl

/-- Every claim of the pool holds of the stack exactly when every claim the Flock seam carries
does. -/
private theorem pool_holds_iff (s : FlockOut I) (q : Column I.μ) :
    (∀ j, (pool I s j).Holds q) ↔
      (∀ c ∈ s.columns.toList, c.Holds q) ∧ ∀ c ∈ s.weighted.toList, c.Holds q := by
  have hpool : (∀ j, (pool I s j).Holds q) ↔ ∀ c ∈ poolList I s, c.Holds q := by
    rw [List.forall_mem_iff_getElem]
    refine ⟨fun h i hi ↦ h ⟨i, length_poolList I s ▸ hi⟩, fun h j ↦ h j.val _⟩
  rw [hpool, poolList, List.forall_mem_append, List.forall_mem_map, and_comm]
  simp only [columnWeighted, ← ColumnClaim.holds_iff_weighted]

/-- The batched claim holds exactly when the stack's answers to the pooled weights, combined by
the powers of `ρ`, are the claimed combination. -/
theorem batched_holds_iff (s : I.Stmt × FlockOut I) (ρ c : E) (q : Column I.μ) :
    (batched I s ρ c).Holds q ↔
      powerBatch (fun j ↦ (pool I s.2 j).weight.pair (algebraMap K E) q.values) ρ = c := by
  unfold batched weight WeightedClaim.Holds
  rw [Weight.pair_batch]

/-- On the Flock seam the batched claim holds at every challenge. -/
theorem batched_of_flock {s : I.Stmt × FlockOut I} {o : ∀ i, TheOracle I i}
    (h : ((s, o), ()) ∈ Seam.flock I) (ρ : E) :
    (batched I s ρ (powerBatch (values I s) ρ)).Holds (theStack o) :=
  (batched_holds_iff I s ρ _ _).mpr
    (congrArg (powerBatch · ρ) (funext ((pool_holds_iff I s.2 (theStack o)).mpr h)))

/-- The stack's answers to the pooled weights, fixed before the challenge: outside the Flock
seam they are not the claimed values, and the batched claim holds only where their combination
is the claimed one. -/
theorem answers_of_not_flock (s : I.Stmt × FlockOut I) (o : ∀ i, TheOracle I i) :
    ∃ a : Fin I.poolSize → E, ∀ w ρ, ((s, o), w) ∉ Seam.flock I →
      ((batched I s ρ (powerBatch (values I s) ρ), o), w) ∈ BatchedHolds I →
        a ≠ values I s ∧ powerBatch (values I s) ρ = powerBatch a ρ := by
  refine ⟨fun j ↦ (pool I s.2 j).weight.pair (algebraMap K E) (theStack o).values,
    fun w ρ hin hb ↦ ⟨fun ha ↦ hin ?_, ((batched_holds_iff I s ρ _ _).mp hb).symm⟩⟩
  cases w
  exact (pool_holds_iff I s.2 (theStack o)).mp (congrFun ha)

end Opening

/-! ## The phase -/

variable (I : M3Instance)

/-- The opening phase, at its slot: batching by powers, then one question to the stack. -/
def openingPhase : Phase.Def I (I.Stmt × FlockOut I) Unit openingSpec :=
  Component.batchQuery (TheOracle I) E (Opening.values I) (Opening.batched I)
    (Opening.question I) (Opening.check I) fun _ ↦ ()

/-- The completeness half. -/
def openingComplete : Phase.Complete I (openingPhase I) (Seam.flock I) (Seam.done I) :=
  Component.batchQueryComplete (TheOracle I) E (Opening.values I) (Opening.batched I) _
    (Opening.check I) _ (relMid := Opening.BatchedHolds I)
    (fun _ _ _ h ρ ↦ Opening.batched_of_flock I h ρ)
    fun c o _ h ↦ ⟨(Opening.accepts_iff I c _).mpr ((Opening.answer_weight_iff I o c).mpr h),
      trivial⟩

/-- The security half, at the slot's error, with the extractor that keeps the trivial
witness. -/
def openingSecurity :
    Phase.Security I (openingPhase I) (Seam.flock I) (Seam.done I) (openingError I) :=
  Component.Security.mono
    (fun _ ↦ le_of_eq (by rw [drawError, openingError, drawError, overE,
      Nat.card_eq_fintype_card]))
    (Component.batchQuerySecurity (TheOracle I) E (Opening.values I) (Opening.batched I) _
      (Opening.check I) _ (relMid := Opening.BatchedHolds I) (Opening.answers_of_not_flock I)
      fun c o _ hc _ ↦ (Opening.answer_weight_iff I o c).mp ((Opening.accepts_iff I c _).mp hc))

end
end LeanerVM.Protocol
