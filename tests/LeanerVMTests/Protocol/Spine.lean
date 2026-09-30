import LeanerVM.Protocol.Spine.Toy
import LeanerVM.Protocol.Spine.Compose
import LeanerVM.Protocol.PublicInput
import LeanerVM.Protocol.ToArkLib.Refinement

/-!
# Protocol spine tests

`M3Holds` on the toy: the honest stack passes, each of the four checkable clauses fails alone on
a stack with one cell changed (the public line on either of its two cells), and balance is a
multiset equality (a stack a field-summed balance would accept is rejected). The instance's
closed forms on the toy: one sumcheck table of height 2 and width 3, one constraint, two push
leaves, no boundary column, four pooled claims. The slots: their round and challenge counts on
the toy and on a bus of `2 ^ 4` leaves (the grand-product argument draws `μ²/4 + μ + 1`
challenges for even `μ`), the opening's one challenge, and the numeric bound on the whole
protocol's error. The composition: the commit phase has one round and no challenge, its
extractor reads the stack back; the public-input phase fills its slot, so the master theorems
have a bundle with a real phase in it; a pass-through that keeps the statement is knowledge
sound at any seam; a refinement transports an extracted witness slot. A plain file, so
`#guard` evaluates the compiled decision procedures and the kernel computes degrees.
-/

namespace LeanerVMTests.Protocol.Spine

open LeanerVM.Parameters LeanerVM.Protocol LeanerVM.Protocol.Toy CompPoly CPoly OracleComp
  ProtocolSpec
open scoped NNReal

/-! ## The toy instance is honest -/

-- The honest stack satisfies the relation at statement `1` (cell 0 of column 2 is `1`).
#guard M3Holds toy (1: K) honest

-- Each clause can fail alone.

/-- Column 2 changed to `[2, 0]`, where `2 : K` is the polynomial `x`, not Boolean. At statement
`2`, so that the public line still holds, only the constraint clause fails. -/
def badConstraint : Column 3 := ⟨#v[1, 1, 1, 1, K.ofBits 2, 0, 0, 0]⟩

#guard ¬ toy.ConstraintsVanish badConstraint
#guard toy.Balanced badConstraint
#guard toy.CountsNonzero badConstraint
#guard toy.PublicLinesHold (K.ofBits 2 : K) badConstraint
#guard ¬ M3Holds toy (K.ofBits 2 : K) badConstraint

/-- Column 0 changed to `[1, 0]`: pushed `{1, 0}` against pulled `{1, 1}`, only balance fails. -/
def badBalance : Column 3 := ⟨#v[1, 0, 1, 1, 1, 0, 0, 0]⟩

#guard toy.ConstraintsVanish badBalance
#guard ¬ toy.Balanced badBalance
#guard toy.CountsNonzero badBalance
#guard toy.PublicLinesHold (1: K) badBalance
#guard ¬ M3Holds toy (1: K) badBalance

/-- Column 1 changed to `[1, 0]`: only the count clause fails. -/
def badCount : Column 3 := ⟨#v[1, 1, 1, 0, 1, 0, 0, 0]⟩

#guard toy.ConstraintsVanish badCount
#guard toy.Balanced badCount
#guard ¬ toy.CountsNonzero badCount
#guard toy.PublicLinesHold (1: K) badCount
#guard ¬ M3Holds toy (1: K) badCount

-- The honest stack at the wrong statement: only the public clause fails.
#guard toy.PublicLinesHold (1: K) honest
#guard ¬ toy.PublicLinesHold (0: K) honest
#guard ¬ M3Holds toy (0: K) honest

/-- Column 2 changed to `[1, 1]`: still Boolean, so the constraint holds, and balance and counts
are untouched; cell 1 of the public line is not `0`, so only the line clause fails. -/
def badLine : Column 3 := ⟨#v[1, 1, 1, 1, 1, 1, 0, 0]⟩

#guard toy.ConstraintsVanish badLine
#guard toy.Balanced badLine
#guard toy.CountsNonzero badLine
#guard ¬ toy.PublicLinesHold (1: K) badLine
#guard ¬ M3Holds toy (1: K) badLine

/-- Column 0 changed to `[0, 0]`: the pushed separators `0, 0` against the pulled `1, 1`. Their
sum in `K` is `0` on both sides, so a field-summed balance (Clean's, over characteristic two)
would accept it; the multiset balance rejects it, and only it fails. -/
def badBalanceSum : Column 3 := ⟨#v[0, 0, 1, 1, 1, 0, 0, 0]⟩

#guard toy.ConstraintsVanish badBalanceSum
#guard ¬ toy.Balanced badBalanceSum
#guard toy.CountsNonzero badBalanceSum
#guard toy.PublicLinesHold (1: K) badBalanceSum
#guard ¬ M3Holds toy (1: K) badBalanceSum
-- The separator coordinates of both sides sum to zero: the sum does not see the imbalance.
#guard ((toy.tuples badBalanceSum .push).map fun t ↦ t.get 0).sum =
  ((toy.tuples badBalanceSum .pull).map fun t ↦ t.get 0).sum

-- The toy has no Flock region, so its Flock predicate holds of every stack.
#guard toy.aux badBalanceSum

-- The layout reads the three slices, through the lift alone.
#guard (toy.column honest ⟨0, 0⟩).values = #v[1, 1]
#guard (toy.column honest ⟨0, 2⟩).values = #v[1, 0]
#guard toy.row honest 0 1 = ![1, 1, 0]
#guard boolIndex (toy.layout.extend ⟨0, 2⟩ (boolVec (1 : Fin 2))) = (5 : Fin 8)

-- One pushed tuple per row of the table, one pulled tuple per row of the boundary block; the
-- separator slot carries column 0, the other slots are zero.
#guard (toy.tuples honest .push).length = 2
#guard (toy.tuples honest .pull).length = 2
#guard toy.tuples honest .push = toy.tuples honest .pull
#guard (toy.tuples honest .push).map (fun t ↦ t.get 0) = [1, 1]
#guard (toy.tuples honest .push).map (fun t ↦ t.get 1) = [0, 0]

/-! ## What the schedule reads off the toy -/

-- The one table has a constraint, so it is a sumcheck table; its height is the largest.
#guard toy.SumcheckTable 0
example : toy.τmax = 1 := by decide
example : toy.B = 1 := by decide
-- Two push leaves (the flush on two rows), no pushing boundary block: leaf stacks of height 2.
example : toy.pushLeaves = 2 := by decide
example : toy.μBus = 1 := by decide
-- No committed boundary column; three table columns; one public line; no Flock claim.
example : toy.boundaryColumns = [] := by decide
example : toy.tableColumns = 3 := by decide
example : toy.poolSize = 4 := by decide

/-! ## The slots -/

-- The bus phase on the toy: `(α, β)`, the roots, one binary layer (its combiner, no round, the
-- descendants, one combination challenge), the last combiner, the boundary values.
example : busRounds toy = 7 := by decide
example : Fintype.card (busSpec toy).ChallengeIdx = 4 := by decide
-- The table sumcheck on the toy: `ξ`, one cubic round, the final values.
example : tableRounds toy = 4 := by decide
example : Fintype.card (tableSpec toy).ChallengeIdx = 2 := by decide
-- The public-input phase: a challenge, then the values.
example : pubSpec.dir 0 = .V_to_P := rfl
example : pubSpec.dir 1 = .P_to_V := rfl
-- No Flock region, no Flock rounds; the opening is one challenge.
example : flockRounds toy toy.flock = 0 := by decide
example : Fintype.card openingSpec.ChallengeIdx = 1 := by decide
-- The whole protocol on the toy.
example : piopRounds toy = 15 := by decide

-- The grand-product argument for trees of `2 ^ 4` leaves draws `(μ/2 + 1)² = 9` challenges:
-- two radix-four layers of `3` and `5`, and the last combiner. For `2 ^ 5` leaves a binary
-- layer of `2` comes first and deepens the others by one: `2 + 4 + 6 + 1 = 13`.
example : Fintype.card (gkrSpec 3 4).ChallengeIdx = 9 := by decide
example : Fintype.card (gkrSpec 3 5).ChallengeIdx = 13 := by decide +kernel
-- The Flock phase for `2 ^ 3` compressions draws `2·3 + 25` challenges over `3·3 + 44` rounds.
example : Fintype.card (flockSpecOf 3).ChallengeIdx = 31 := by decide +kernel
example : flockRoundsOf 3 = 53 := by decide

/-- The bound of `piopError_le`, with `|E| = 2^192`, is below `2^{-159}`. -/
example : overE (2 ^ 32 + 2 ^ 31 + 2 ^ 20) < 1 / 2 ^ 159 := by
  rw [overE, card_E]
  norm_num

/-! ## The composition -/

/-- The commit phase has one round, a prover message. -/
example : (commitSpec toy).dir 0 = .P_to_V := rfl

/-- The commit phase has no challenge, so its error is the empty function. -/
example (i : (commitSpec toy).ChallengeIdx) : commitError toy i = 0 := rfl

/-- The transcript of the commit phase on the honest stack: one message, the stack. -/
def honestTranscript : (commitSpec toy).FullTranscript := fun i ↦ match i with
  | ⟨0, _⟩ => honest

/-- What the commit phase's extractor returns on the honest transcript. -/
def extracted : Column 3 :=
  (commitExtractor toy).extractOut ((1: K), fun i : Fin 0 ↦ i.elim0) honestTranscript ()

-- The commit phase's extractor reads the stack off the message, and it computes.
#guard extracted.values = honest.values

/-- The commit phase's extractor, folded to the input, reads the stack off the message. -/
example : (commitExtractor toy).extractIn ((1: K), fun i : Fin 0 ↦ i.elim0) honestTranscript () =
    honest := rfl

/-- The public-input phase fills its slot: its two halves typecheck against the spine's seams
and at the slot's error. -/
example : Phase.Complete toy (publicInputPhase toy).toDef (Seam.table toy) (Seam.pub toy) :=
  publicInputComplete toy

example : Phase.Security toy (publicInputPhase toy).toDef (Seam.table toy) (Seam.pub toy)
    pubError :=
  publicInputSecurity toy

/-- A bundle whose public-input phase is the built one has both master theorems, given the four
other phases' proofs: the slots line up. -/
example (P : Phases toy) (C : P.Complete) {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (leanVmPiop P).perfectCompleteness init impl (M3Rel toy) (Seam.done toy) :=
  piop_perfectCompleteness P C init impl

example (P : Phases toy) (S : P.Security) {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (leanVmVerifier P).toVerifier.rbrKnowledgeSoundnessWorstCaseWith init impl (M3Rel toy)
      (Seam.done toy) S.extraction.witMid (piopExtractor P S) (S.extraction.kSF init impl)
      (piopError toy) :=
  piop_rbrKnowledgeSoundness P S init impl

/-- The stack the whole protocol's extractor returns is the committed message. -/
example (P : Phases toy) (S : P.Security) (s : K × ∀ i, NoOracle i)
    (tr : (piopSpec toy).FullTranscript) :
    piopExtractedStack P S s tr = tr.fst.fst.fst.fst.fst 0 :=
  piopExtractedStack_eq P S s tr

/-- A pass-through that keeps the statement is knowledge sound at any seam, at error zero: the
identity at the public-input seam. -/
example : Phase.Security toy (Phase.passThrough toy id) (Seam.pub toy) (Seam.pub toy)
    (fun i ↦ Fin.elim0 i.1) :=
  Phase.passThroughSecurity toy id (fun _ _ h ↦ h) fun _ _ h ↦ h

/-- The relation the protocol starts from is `M3Holds`, in ArkLib's shape. -/
example (input : K) (q : Column 3) :
    ((input, fun i : Fin 0 ↦ i.elim0), q) ∈ M3Rel toy ↔ M3Holds toy input q := Iff.rfl

/-- The commit seam pins the oracle to the witness of record. -/
example (input : K) (q : Column 3) :
    ((input, fun _ : Fin 1 ↦ q), ()) ∈ Seam.commit toy ↔ M3Holds toy input q := Iff.rfl

/-- The last seam leaves nothing to check. -/
example (o : ∀ i, TheOracle toy i) : (((), o), ()) ∈ Seam.done toy := trivial

/-! ## The bus seam bounds the degree of its row polynomials -/

/-- The toy's constraint is a row polynomial of the bus seam: degree at most `d = 2`. -/
example : toy.RowPoly 0 := ⟨constraint, by decide +kernel⟩

/-- The cubic `X₂³` is not: the bound is not vacuous at `d = 2`. -/
example : ¬ ((CMvPolynomial.X 2 * CMvPolynomial.X 2 * CMvPolynomial.X 2 :
    CMvPolynomial 3 K).totalDegree ≤ toy.d) := by decide +kernel

/-! ## Refinements -/

/-- A refinement transports an extracted witness slot: the doubled relation on `ℕ`. -/
def double :
    Refinement (Stmt := Unit) {p : Unit × ℕ | p.2 % 2 = 0} {p : Unit × ℕ | p.2 % 4 = 0} where
  map := fun _ w ↦ 2 * w
  map_valid := fun _ w h ↦ by simp only [Set.mem_ofPred_eq] at h ⊢; omega

example : ∀ w' ∈ (some 6).map (double.map ()), ((), w') ∈ {p : Unit × ℕ | p.2 % 4 = 0} :=
  double.map_option_valid () (some 6) (by decide)

end LeanerVMTests.Protocol.Spine
