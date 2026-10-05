import LeanerVM.Protocol.Opening
import LeanerVM.Protocol.PublicInput
import LeanerVM.Protocol.Spine.Toy
import LeanerVM.Protocol.Spine.Compose
import Mathlib.Algebra.CharP.Two

/-!
# Opening phase tests

Every guard changes one thing.

* **An honest pool is accepted** on the toy: four true column claims on the honest stack,
  combined at two challenges.
* **A false claim is rejected**: one value changed by one, at a challenge that is no root of the
  difference.
* **The bound is attained.** Two copies of one false claim combine to a false claim at every
  challenge but `λ = 1`, where they cancel in characteristic two: the one bad challenge exists.
* **The empty pool** on an instance with no table: the question is the zero weight, the value
  `0`, every stack is accepted, and the slot's error is `0`.
* **The order of the powers.** On an instance with a Flock region, the weighted claim takes
  `λ^0` and the column claim `λ^1`, and the swapped order gives another value.
* **The phase fills its slot**: its two halves typecheck against the spine's seams at the slot's
  error, compute at `E`, and with the deployed public-input phase make a bundle the master
  theorems apply to, given the three other phases.
* **The check is load-bearing.** On a statement outside the Flock seam, the verifier with no
  check, the verifier that checks the first claim only, and the verifier that combines the
  claims with unit weights each accept at every challenge, so none has a round-by-round
  knowledge error below one, whatever extractor and state function it is given. The verifier
  that also rejects `λ = 0` rejects the honest prover there: it is not perfectly complete.

A plain file, so `#guard` evaluates the compiled definitions.
-/

namespace LeanerVMTests.Protocol.Opening

open LeanerVM.Parameters LeanerVM.Protocol LeanerVM.Protocol.Toy CompPoly OracleComp
open scoped NNReal

/-- A column claim is decided by evaluating the column's extension. -/
instance {I : M3Instance} (q : Column I.μ) (c : ColumnClaim I) : Decidable (c.Holds q) :=
  inferInstanceAs (Decidable (CMlPolynomialEval.eval₂Mle (I.column q c.col).values
    (algebraMap K E) c.point = c.value))

/-! ## Claims on the toy -/

/-- The claim on column `c` of the toy at the point `(z)`, with the honest stack's value. -/
def trueClaim (c : toy.ColumnId) (z : E) : ColumnClaim toy :=
  ⟨c, #v[z], CMlPolynomialEval.eval₂Mle (toy.column honest c).values (algebraMap K E) #v[z]⟩

/-- The same claim with its value off by one: false of the honest stack. -/
def falseClaim (c : toy.ColumnId) (z : E) : ColumnClaim toy :=
  ⟨c, #v[z], (trueClaim c z).value + 1⟩

/-- A statement of the Flock seam on the toy: four column claims and no weighted claim. -/
def stmtOf (a b c d : ColumnClaim toy) : K × FlockOut toy :=
  (1, ⟨#v[a, b, c, d], #v[]⟩)

/-- Four true claims, two on the public line's column. -/
def honestStmt : K × FlockOut toy :=
  stmtOf (trueClaim ⟨0, 0⟩ y) (trueClaim ⟨0, 1⟩ y) (trueClaim ⟨0, 2⟩ y) (trueClaim ⟨0, 2⟩ (y + 1))

/-- The same with the second claim false. -/
def badStmt : K × FlockOut toy :=
  stmtOf (trueClaim ⟨0, 0⟩ y) (falseClaim ⟨0, 1⟩ y) (trueClaim ⟨0, 2⟩ y) (trueClaim ⟨0, 2⟩ (y + 1))

/-- Two copies of one false claim, then two true claims. -/
def dupStmt : K × FlockOut toy :=
  stmtOf (falseClaim ⟨0, 0⟩ y) (falseClaim ⟨0, 0⟩ y) (trueClaim ⟨0, 1⟩ y) (trueClaim ⟨0, 2⟩ y)

/-- The honest stack's answer to the question at `ρ`. -/
def answer (s : K × FlockOut toy) (ρ : E) : E :=
  (Opening.weight toy s.2 ρ).pair (algebraMap K E) honest.values

/-- A second challenge, `y² + 1`. -/
def ρ₂ : E := y * y + 1

/-! ## Honest and false pools -/

#guard ∀ c ∈ honestStmt.2.columns.toList, c.Holds honest
#guard Opening.accepts toy honestStmt.2 y (answer honestStmt y)
#guard Opening.accepts toy honestStmt.2 ρ₂ (answer honestStmt ρ₂)

#guard ¬ ∀ c ∈ badStmt.2.columns.toList, c.Holds honest
#guard !Opening.accepts toy badStmt.2 y (answer badStmt y)
#guard !Opening.accepts toy badStmt.2 ρ₂ (answer badStmt ρ₂)

-- The duplicated false claim: rejected at `y`, accepted at `1`, where `1 + λ = 0`.
#guard ¬ ∀ c ∈ dupStmt.2.columns.toList, c.Holds honest
#guard !Opening.accepts toy dupStmt.2 y (answer dupStmt y)
#guard Opening.accepts toy dupStmt.2 1 (answer dupStmt 1)

/-! ## The empty pool -/

/-- An instance with no table, on a stack of one cell: nothing to pool. -/
abbrev empty : M3Instance where
  toShape := ⟨0, Fin.elim0, Fin.elim0⟩
  Stmt := Unit
  constraints := fun j ↦ j.elim0
  flushes := fun j ↦ j.elim0
  d := 0
  constraints_degree := fun j ↦ j.elim0
  flushes_degree := fun j ↦ j.elim0
  counts := fun j ↦ j.elim0
  boundary := []
  μ := 0
  layout := ⟨fun c ↦ c.1.elim0, fun _ c ↦ c.1.elim0⟩
  nLines := 0
  publicLines := fun _ ↦ #v[]
  flock := none

example : empty.poolSize = 0 := by decide

/-- The empty pool. -/
def emptyPool : FlockOut empty := ⟨#v[], #v[]⟩

/-- A stack of one nonzero cell. -/
def one : Column 0 := ⟨#v[1]⟩

-- The question is the zero weight and the value `0`, so every stack is accepted.
#guard (Opening.weight empty emptyPool y).onCube = #v[0]
#guard Opening.value empty emptyPool y = 0
#guard Opening.accepts empty emptyPool y
  ((Opening.weight empty emptyPool y).pair (algebraMap K E) one.values)

/-- The slot's error on the empty pool is `0`. -/
example (i : openingSpec.ChallengeIdx) : openingError empty i = 0 := by
  rw [openingError, show empty.poolSize - 1 = 0 by decide]
  simp [drawError, overE]

/-! ## The order of the powers -/

/-- One table of height `2^8` and width one, with a count column so that the table sumcheck
visits it, and the whole table as the Flock region. -/
abbrev flockShape : Shape := ⟨1, fun _ ↦ 8, fun _ ↦ 1⟩

/-- The stack is the one column. -/
theorem readWith_id (q : Column 8) (c : flockShape.ColumnId) :
    Layout.readWith (fun (_ : flockShape.ColumnId) (z : Vector E 8) ↦ z) q c = q := by
  obtain ⟨v⟩ := q
  apply congrArg Column.mk
  apply Vector.ext
  intro i hi
  rw [Vector.getElem_ofFn, boolIndex_boolVec]
  rfl

/-- An instance with one column claim and one weighted claim to pool. -/
abbrev flocky : M3Instance where
  toShape := flockShape
  Stmt := Unit
  constraints := fun _ ↦ []
  flushes := fun _ ↦ []
  d := 0
  constraints_degree := fun _ _ h ↦ absurd h (List.not_mem_nil)
  flushes_degree := fun _ _ h ↦ absurd h (List.not_mem_nil)
  counts := fun _ ↦ [0]
  boundary := []
  μ := 8
  layout := ⟨fun _ z ↦ z, fun q c z ↦ by rw [readWith_id]⟩
  nLines := 0
  publicLines := fun _ ↦ #v[]
  flock := some ⟨⟨0, 0⟩, 0, rfl, fun _ ↦ True, inferInstance⟩

example : flocky.pubClaims = 1 := by decide
example : flocky.flockClaims = 1 := rfl

/-- The point `(y, …, y)`. -/
def ys : Vector E 8 := Vector.replicate 8 y

/-- A weighted claim with value `y` and a column claim with value `1`. -/
def flockyPool : FlockOut flocky := ⟨#v[⟨⟨0, 0⟩, ys, 1⟩], #v[⟨eqWeight ys, y⟩]⟩

-- The weighted claim takes `λ^0`, the column claim `λ^1`; the swapped order differs.
#guard Opening.value flocky flockyPool ρ₂ = y + ρ₂ * 1
#guard Opening.value flocky flockyPool ρ₂ ≠ 1 + ρ₂ * y

example : Opening.pool flocky flockyPool ⟨0, by decide⟩ = ⟨eqWeight ys, y⟩ :=
  Opening.pool_weighted flocky flockyPool ⟨0, by decide⟩

example : Opening.pool flocky flockyPool ⟨1, by decide⟩ =
    Opening.columnWeighted flocky ⟨⟨0, 0⟩, ys, 1⟩ :=
  Opening.pool_column flocky flockyPool ⟨0, by decide⟩

/-! ## The phase fills its slot -/

/-- The completeness half, at the spine's seams. -/
def complete : Phase.Complete toy (openingPhase toy) (Seam.flock toy) (Seam.done toy) :=
  openingComplete toy

/-- The security half, at the spine's seams and the slot's error; a plain definition, so it
computes at `E`. -/
def security : Phase.Security toy (openingPhase toy) (Seam.flock toy) (Seam.done toy)
    (openingError toy) :=
  openingSecurity toy

/-- The slot's error on the toy: three, for the four pooled claims. -/
example : ∑ i, openingError toy i = overE 3 := by
  rw [openingError, sum_drawError]
  rfl

/-- With the deployed public-input phase and the opening phase in their slots, the master
theorems hold of the bundle, given the three other phases' proofs. -/
example (bus : Phase.FrontDef toy K (K × BusOut toy) (busSpec toy))
    (table : Phase.FrontDef toy (K × BusOut toy) (K × TableOut toy) (tableSpec toy))
    (flock : Phase.FrontDef toy (K × PubOut toy) (K × FlockOut toy) (flockSpec toy))
    (cb : Phase.Complete toy bus.toDef (Seam.commit toy) (Seam.bus toy))
    (ct : Phase.Complete toy table.toDef (Seam.bus toy) (Seam.table toy))
    (cf : Phase.Complete toy flock.toDef (Seam.pub toy) (Seam.flock toy))
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (leanVmPiop ⟨bus, table, deployedPublicInputPhase toy, flock, openingPhase toy⟩)
      |>.perfectCompleteness init impl (M3Rel toy) (Seam.done toy) :=
  piop_perfectCompleteness _ ⟨cb, ct, deployedPublicInputComplete toy, cf, openingComplete toy⟩
    init impl

example (bus : Phase.FrontDef toy K (K × BusOut toy) (busSpec toy))
    (table : Phase.FrontDef toy (K × BusOut toy) (K × TableOut toy) (tableSpec toy))
    (flock : Phase.FrontDef toy (K × PubOut toy) (K × FlockOut toy) (flockSpec toy))
    (sb : Phase.Security toy bus.toDef (Seam.commit toy) (Seam.bus toy) (busError toy))
    (st : Phase.Security toy table.toDef (Seam.bus toy) (Seam.table toy) (tableError toy))
    (sf : Phase.Security toy flock.toDef (Seam.pub toy) (Seam.flock toy) (flockError toy))
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    let S : Phases.Security ⟨bus, table, deployedPublicInputPhase toy, flock, openingPhase toy⟩ :=
      ⟨sb, st, deployedPublicInputSecurity toy, sf, openingSecurity toy⟩
    (leanVmVerifier _).toVerifier.rbrKnowledgeSoundnessWorstCaseWith init impl (M3Rel toy)
      (Seam.done toy) S.extraction.witMid (piopExtractor _ S) (S.extraction.kSF init impl)
      (piopError toy) :=
  piop_rbrKnowledgeSoundness _ _ init impl


/-! ## The check is load-bearing -/

/-- Two copies of one pooled claim cancel under unit weights in characteristic two: when every
other pooled claim holds, the combination at `1` is accepted, whether or not the copies hold. -/
theorem accepts_one_of_copies (I : M3Instance) (s : I.Stmt × FlockOut I)
    (o : ∀ i, TheOracle I i) (i j : Fin I.poolSize) (hij : i ≠ j)
    (heq : Opening.pool I s.2 i = Opening.pool I s.2 j)
    (hrest : ∀ k, k ≠ i → k ≠ j → (Opening.pool I s.2 k).Holds (theStack o)) :
    Opening.accepts I s.2 1 (Component.answerOf (TheOracle I) o (Opening.question I s 1)) =
      true := by
  refine (Opening.accepts_iff I s.2 1 _).mpr ((Opening.answer_question I s o 1).trans ?_)
  simp only [Opening.value, powerBatch, one_pow, mul_one]
  change @Eq E _ _
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib,
    Finset.sum_eq_add i j hij (fun k _ hk ↦ sub_eq_zero.mpr (hrest k hk.1 hk.2)) (by simp)
      (by simp), heq]
  exact CharTwo.add_self_eq_zero _

/-- The honest stack as the one oracle. -/
def theHonest : ∀ i, TheOracle toy i := fun _ ↦ honest

/-- A true claim holds of the honest stack. -/
theorem trueClaim_holds (c : toy.ColumnId) (z : E) : (trueClaim c z).Holds honest := rfl

/-- `badStmt` is outside the Flock seam: its second claim is false of the honest stack. -/
theorem badStmt_not_flock (w : Unit) : ((badStmt, theHonest), w) ∉ Seam.flock toy := by
  rintro ⟨h, -⟩
  have h1 := h (falseClaim ⟨0, 1⟩ y) (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  exact one_ne_zero (add_left_cancel ((add_zero _).trans h1)).symm

/-- `dupStmt` is outside the Flock seam: its first claim is false of the honest stack. -/
theorem dupStmt_not_flock (w : Unit) : ((dupStmt, theHonest), w) ∉ Seam.flock toy := by
  rintro ⟨h, -⟩
  have h0 := h (falseClaim ⟨0, 0⟩ y) (List.mem_cons_self ..)
  exact one_ne_zero (add_left_cancel ((add_zero _).trans h0)).symm

/-- `honestStmt` is on the Flock seam. -/
theorem honestStmt_flock : ((honestStmt, theHonest), ()) ∈ Seam.flock toy := by
  refine ⟨?_, fun c hc ↦ absurd hc List.not_mem_nil⟩
  have hl : honestStmt.2.columns.toList = [trueClaim ⟨0, 0⟩ y, trueClaim ⟨0, 1⟩ y,
      trueClaim ⟨0, 2⟩ y, trueClaim ⟨0, 2⟩ (y + 1)] := rfl
  intro c hc
  rw [hl] at hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> exact trueClaim_holds _ _

/-- On the toy the pool is the column claims, in order. -/
theorem pool_toy (s : FlockOut toy) (j : Fin toy.poolSize) :
    Opening.pool toy s j = Opening.columnWeighted toy (s.columns[j.val]'j.isLt) :=
  (congrArg (Opening.pool toy s) (Fin.ext (Nat.zero_add j.val).symm)).trans
    (Opening.pool_column toy s ⟨j.val, j.isLt⟩)

/-- Whether an answer equals a value. -/
def eqCheck (v a : E) : Bool := decide (a = v)

theorem eqCheck_iff (v a : E) : eqCheck v a = true ↔ a = v := decide_eq_true_iff

/-- The verifier with no check. -/
abbrev unchecked : Phase.Def toy (K × FlockOut toy) Unit openingSpec :=
  Component.sampleQuery (TheOracle toy) E (Opening.question toy) (fun _ _ _ ↦ true) fun _ _ ↦ ()

/-- Without the check, a false pool is accepted at every challenge: no knowledge error below
one. -/
theorem unchecked_not_rbr {σ : Type} {init : ProbComp σ}
    {impl : QueryImpl []ₒ (StateT σ ProbComp)} {WitMid : Fin 2 → Type}
    {Ex : Extractor.RoundByRound (OracleSpec.emptySpec.{0, 0}) ((K × FlockOut toy) ×
      ∀ i, TheOracle toy i) Unit Unit openingSpec WitMid}
    {kSF : unchecked.red.verifier.toVerifier.KnowledgeStateFunction init impl (Seam.flock toy)
      (Seam.done toy) Ex}
    {ε : openingSpec.ChallengeIdx → ℝ≥0}
    (h : unchecked.red.verifier.toVerifier.rbrKnowledgeSoundnessWorstCaseWith init impl
      (Seam.flock toy) (Seam.done toy) WitMid Ex kSF ε) : 1 ≤ ε ⟨0, rfl⟩ :=
  Component.sampleQuery_not_rbr (TheOracle toy) E _ _ _ init impl h badStmt theHonest
    badStmt_not_flock () fun _ ↦ ⟨rfl, trivial⟩

/-- The first claim of `badStmt` holds of the honest stack. -/
theorem badStmt_first : (Opening.pool toy badStmt.2 ⟨0, by decide⟩).Holds honest := by
  rw [pool_toy, Opening.columnWeighted_holds_iff]
  exact trueClaim_holds _ _

/-- The question of the verifier that checks the first pooled claim alone. -/
def firstQuery (s : K × FlockOut toy) (_ : E) : [TheOracle toy]ₒ.Domain :=
  Opening.ask toy (Opening.pool toy s.2 ⟨0, by decide⟩).weight

/-- Its check: the answer is the first claim's value. -/
def firstCheck (s : K × FlockOut toy) (ρ : E) (a : [TheOracle toy]ₒ.Range (firstQuery s ρ)) :
    Bool :=
  eqCheck (Opening.pool toy s.2 ⟨0, by decide⟩).value a

/-- The verifier that checks the first pooled claim alone. -/
abbrev firstOnly : Phase.Def toy (K × FlockOut toy) Unit openingSpec :=
  Component.sampleQuery (TheOracle toy) E firstQuery firstCheck fun _ _ ↦ ()

/-- The first claim of `badStmt`, asked alone, is accepted. -/
theorem badStmt_first_accepted (ρ : E) :
    firstCheck badStmt ρ (Component.answerOf (TheOracle toy) theHonest (firstQuery badStmt ρ)) =
      true :=
  (eqCheck_iff _ _).mpr ((Opening.answer_weight_iff toy theHonest _).mpr badStmt_first)

/-- Checking the first claim alone, a pool whose first claim is true is accepted at every
challenge: no knowledge error below one. -/
theorem firstOnly_not_rbr {σ : Type} {init : ProbComp σ}
    {impl : QueryImpl []ₒ (StateT σ ProbComp)} {WitMid : Fin 2 → Type}
    {Ex : Extractor.RoundByRound (OracleSpec.emptySpec.{0, 0}) ((K × FlockOut toy) ×
      ∀ i, TheOracle toy i) Unit Unit openingSpec WitMid}
    {kSF : firstOnly.red.verifier.toVerifier.KnowledgeStateFunction init impl (Seam.flock toy)
      (Seam.done toy) Ex}
    {ε : openingSpec.ChallengeIdx → ℝ≥0}
    (h : firstOnly.red.verifier.toVerifier.rbrKnowledgeSoundnessWorstCaseWith init impl
      (Seam.flock toy) (Seam.done toy) WitMid Ex kSF ε) : 1 ≤ ε ⟨0, rfl⟩ :=
  Component.sampleQuery_not_rbr (TheOracle toy) E firstQuery firstCheck (fun _ _ ↦ ()) init impl
    h badStmt theHonest badStmt_not_flock () fun ρ ↦ ⟨badStmt_first_accepted ρ, trivial⟩

/-- The verifier that combines the claims with unit weights, whatever the challenge. -/
abbrev unitWeights : Phase.Def toy (K × FlockOut toy) Unit openingSpec :=
  Component.sampleQuery (TheOracle toy) E (fun s _ ↦ Opening.question toy s 1)
    (fun s _ a ↦ Opening.accepts toy s.2 1 a) fun _ _ ↦ ()

/-- The two false claims of `dupStmt` are copies, and its other claims hold: unit weights
accept it. -/
theorem dupStmt_unit :
    Opening.accepts toy dupStmt.2 1
      (Component.answerOf (TheOracle toy) theHonest (Opening.question toy dupStmt 1)) = true := by
  refine accepts_one_of_copies toy dupStmt theHonest ⟨0, by decide⟩ ⟨1, by decide⟩
    (by decide) (by rw [pool_toy, pool_toy]; rfl) fun ⟨k, hk⟩ h0 h1 ↦ ?_
  rw [pool_toy, Opening.columnWeighted_holds_iff]
  have hk4 : k < 4 := (show toy.poolSize = 4 by decide) ▸ hk
  interval_cases k
  · exact absurd rfl h0
  · exact absurd rfl h1
  · exact trueClaim_holds _ _
  · exact trueClaim_holds _ _

/-- With unit weights, two copies of one false claim cancel in characteristic two, so the pool
is accepted at every challenge: no knowledge error below one. -/
theorem unitWeights_not_rbr {σ : Type} {init : ProbComp σ}
    {impl : QueryImpl []ₒ (StateT σ ProbComp)} {WitMid : Fin 2 → Type}
    {Ex : Extractor.RoundByRound (OracleSpec.emptySpec.{0, 0}) ((K × FlockOut toy) ×
      ∀ i, TheOracle toy i) Unit Unit openingSpec WitMid}
    {kSF : unitWeights.red.verifier.toVerifier.KnowledgeStateFunction init impl (Seam.flock toy)
      (Seam.done toy) Ex}
    {ε : openingSpec.ChallengeIdx → ℝ≥0}
    (h : unitWeights.red.verifier.toVerifier.rbrKnowledgeSoundnessWorstCaseWith init impl
      (Seam.flock toy) (Seam.done toy) WitMid Ex kSF ε) : 1 ≤ ε ⟨0, rfl⟩ :=
  Component.sampleQuery_not_rbr (TheOracle toy) E (fun s _ ↦ Opening.question toy s 1)
    (fun s _ a ↦ Opening.accepts toy s.2 1 a) (fun _ _ ↦ ()) init impl h dupStmt theHonest
    dupStmt_not_flock () fun _ ↦ ⟨dupStmt_unit, trivial⟩

/-- The verifier that also rejects the challenge `0`. -/
abbrev rejectsZero : Phase.Def toy (K × FlockOut toy) Unit openingSpec :=
  Component.sampleQuery (TheOracle toy) E (Opening.question toy)
    (fun s ρ a ↦ Opening.check toy s ρ a && decide (ρ ≠ 0)) fun _ _ ↦ ()

/-- Rejecting the challenge `0` rejects the honest prover there: no perfect completeness. -/
theorem rejectsZero_not_complete {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    ¬ rejectsZero.red.perfectCompleteness init impl (Seam.flock toy) (Seam.done toy) :=
  Component.sampleQuery_not_complete (TheOracle toy) E _ _ _ init impl honestStmt_flock 0
    (by simp)

end LeanerVMTests.Protocol.Opening
