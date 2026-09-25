import LeanerVM.Protocol.Spine.Toy
import LeanerVM.Protocol.Spine.Compose
import LeanerVM.Protocol.Spine.Transport

/-!
# Protocol spine tests: the toy instance and the composition

Acceptance test 27 of the protocol roadmap: `M3Holds` holds of the toy's honest stack and fails
for a stack with one cell changed, each of the four checkable clauses failing alone, and balance
is a multiset equality, not a field sum. Decided by evaluation (`#guard`), since the relation is
decidable. Then the composition: `Phases toy` and `Phases.Complete` are inhabited by pass-through
phases (so `piop_perfectCompleteness` has an instance, and the seams line up: the inhabitant's
`Complete` typechecks only against the spine's seams, acceptance test 26), the commit phase has
one round and no challenge, its extractor reads the stack off the message, and a refinement
transports an extracted witness slot.

This is a plain file so that `#guard` evaluates the compiled decision procedure.
-/

namespace LeanerVMTests.Protocol.Spine

open LeanerVM.Parameters LeanerVM.Protocol LeanerVM.Protocol.Toy CompPoly CPoly OracleComp

/-! ## The toy instance is honest -/

-- The honest stack satisfies the relation at statement `1` (cell 0 of column 2 is `1`).
#guard M3Holds toy (1 : K) honest

-- Each clause can fail alone.

/-- Column 2 changed to `[2, 0]`, where `2 : K` is the polynomial `x`, not Boolean. At the
statement `2` (so that the public cell still holds) only the constraint clause fails. -/
def badConstraint : Column 3 := ⟨#v[1, 1, 1, 1, 2, 0, 0, 0]⟩

#guard ¬ toy.ConstraintsVanish badConstraint
#guard toy.Balanced badConstraint
#guard toy.CountsNonzero badConstraint
#guard toy.PublicCellsHold (2 : K) badConstraint
#guard ¬ M3Holds toy (2 : K) badConstraint

/-- Column 0 changed to `[1, 0]`: pushed `{1, 0}` against pulled `{1, 1}`, only balance fails. -/
def badBalance : Column 3 := ⟨#v[1, 0, 1, 1, 1, 0, 0, 0]⟩

#guard toy.ConstraintsVanish badBalance
#guard ¬ toy.Balanced badBalance
#guard toy.CountsNonzero badBalance
#guard toy.PublicCellsHold (1 : K) badBalance
#guard ¬ M3Holds toy (1 : K) badBalance

/-- Column 1 changed to `[1, 0]`: only the count clause fails. -/
def badCount : Column 3 := ⟨#v[1, 1, 1, 0, 1, 0, 0, 0]⟩

#guard toy.ConstraintsVanish badCount
#guard toy.Balanced badCount
#guard ¬ toy.CountsNonzero badCount
#guard toy.PublicCellsHold (1 : K) badCount
#guard ¬ M3Holds toy (1 : K) badCount

-- The honest stack at the wrong statement: only the public clause fails.
#guard toy.PublicCellsHold (1 : K) honest
#guard ¬ toy.PublicCellsHold (0 : K) honest
#guard ¬ M3Holds toy (0 : K) honest

/-- Column 0 changed to `[0, 0]`: the pushed separators `0, 0` against the pulled `1, 1`. Their
sum in `K` is `0` on both sides, so a field-summed balance (Clean's, over characteristic two)
would accept it; the multiset balance rejects it, and only it fails. -/
def badBalanceSum : Column 3 := ⟨#v[0, 0, 1, 1, 1, 0, 0, 0]⟩

#guard toy.ConstraintsVanish badBalanceSum
#guard ¬ toy.Balanced badBalanceSum
#guard toy.CountsNonzero badBalanceSum
#guard toy.PublicCellsHold (1 : K) badBalanceSum
#guard ¬ M3Holds toy (1 : K) badBalanceSum
-- The separator coordinates of both sides sum to zero: the sum does not see the imbalance.
#guard ((toy.tuples badBalanceSum .push).map fun t ↦ t.get 0).sum =
  ((toy.tuples badBalanceSum .pull).map fun t ↦ t.get 0).sum

-- The layout reads the three slices.
#guard (toy.column honest ⟨0, 0⟩).values = #v[1, 1]
#guard (toy.column honest ⟨0, 2⟩).values = #v[1, 0]
#guard toy.row honest 0 1 = ![1, 1, 0]

-- One pushed tuple per row of the table, one pulled tuple per row of the boundary block; the
-- separator slot carries column 0, the other slots are zero.
#guard (toy.tuples honest .push).length = 2
#guard (toy.tuples honest .pull).length = 2
#guard toy.tuples honest .push = toy.tuples honest .pull
#guard (toy.tuples honest .push).map (fun t ↦ t.get 0) = [1, 1]
#guard (toy.tuples honest .push).map (fun t ↦ t.get 1) = [0, 0]

/-! ## The composition is inhabited and typechecks against the seams -/

/-- Five pass-through phases: each maps the statement to an empty claim set. -/
def trivPhases : Phases toy where
  bus := Phase.passThrough toy fun s ↦ (s, ⟨[], []⟩)
  table := Phase.passThrough toy fun p ↦ (p.1, ⟨[]⟩)
  pub := Phase.passThrough toy fun p ↦ (p.1, ⟨[]⟩)
  flock := Phase.passThrough toy fun p ↦ (p.1, ⟨[], []⟩)
  opening := Phase.passThrough toy fun _ ↦ ()

/-- Their completeness halves against the spine's seams: dropping every claim is complete
(and not knowledge sound, which is why `Phases.Security` has no such inhabitant). This
typechecks only because each `passThroughComplete` is stated against the seam the previous one
outputs (acceptance test 26). -/
def trivComplete : trivPhases.Complete where
  bus := Phase.passThroughComplete toy _ fun _ _ h ↦ ⟨by simp, by simp, h.2.2.2.1, h.2.2.2.2⟩
  table := Phase.passThroughComplete toy _ fun _ _ h ↦ ⟨by simp, h.2.2.1, h.2.2.2⟩
  pub := Phase.passThroughComplete toy _ fun _ _ h ↦ ⟨by simp, h.2.2⟩
  flock := Phase.passThroughComplete toy _ fun _ _ _ ↦ ⟨by simp, by simp⟩
  opening := Phase.passThroughComplete toy _ fun _ _ _ ↦ trivial

/-- The composed protocol of the trivial phases has the commit phase's one round. -/
example : trivPhases.toDef.n = 1 := rfl

/-- The master completeness theorem has an instance. -/
example {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (leanVmPiop trivPhases).perfectCompleteness init impl (M3Rel toy) (Seam.done toy) :=
  piop_perfectCompleteness trivPhases trivComplete init impl

/-- The commit phase has one round, a prover message. -/
example : (commitSpec toy).dir 0 = .P_to_V := rfl

/-- The commit phase has no challenge, so its error is the empty function. -/
example (i : (commitSpec toy).ChallengeIdx) : (commitDef toy).err i = 0 := rfl

/-- The transcript of the commit phase on the honest stack: one message, the stack. -/
def honestTranscript : (commitSpec toy).FullTranscript := fun i ↦ match i with
  | ⟨0, _⟩ => honest

/-- What the commit phase's extractor returns on the honest transcript. -/
def extracted : Column 3 :=
  (commitExtractor toy).extractOut ((1 : K), fun i : Fin 0 ↦ i.elim0) honestTranscript ()

-- The commit phase's extractor reads the stack off the message: acceptance test 24's first
-- instance, computable.
#guard extracted.values = honest.values

/-- The relation the protocol starts from is `M3Holds`, in ArkLib's shape. -/
example (input : K) (q : Column 3) :
    ((input, fun i : Fin 0 ↦ i.elim0), q) ∈ M3Rel toy ↔ M3Holds toy input q := Iff.rfl

/-- The commit seam pins the oracle to the witness of record. -/
example (input : K) (q : Column 3) :
    ((input, fun _ : Fin 1 ↦ q), ()) ∈ Seam.commit toy ↔ M3Holds toy input q := Iff.rfl

/-- The last seam leaves nothing to check. -/
example (o : ∀ i, TheOracle toy i) : (((), o), ()) ∈ Seam.done toy := trivial

/-! ## Refinements -/

/-- A refinement transports an extracted witness slot: the doubled relation on `ℕ`. -/
def double :
    Refinement (Stmt := Unit) {p : Unit × ℕ | p.2 % 2 = 0} {p : Unit × ℕ | p.2 % 4 = 0} where
  map := fun _ w ↦ 2 * w
  map_valid := fun _ w h ↦ by simp only [Set.mem_ofPred_eq] at h ⊢; omega

example : ∀ w' ∈ (some 6).map (double.map ()), ((), w') ∈ {p : Unit × ℕ | p.2 % 4 = 0} :=
  double.map_option_valid () (some 6) (by decide)

end LeanerVMTests.Protocol.Spine
