/-
  LeanerVM.Protocol.Whir.LevelSound

  Round-by-round soundness of one level of WHIR's opening for the list relation, composed from the
  fold rounds and the boundary, followed by the rest of the opening. Candidate for ArkLib.
-/

module

public import LeanerVM.Protocol.Whir.BoundarySound

/-!
# A level is sound for the list relation

Category B: `levelSecurity` is the security half of `levelDef`, from the language at the start of
the level (`foldRelMid P 0`: the batched claim's polynomial received) to the rest of the opening's
output relation, given the rest's own security. Its error (`levelErr`) is, challenge by challenge,
the one the schedule assigns it:

* the fold challenges: `(2 L + 2 ^ (ℓ - j - 1) N) / |E|` at the `j`-th (`foldErr`);
* the out-of-domain point: `C(L', 2) / |E|` at each of its `κ` coordinates, `L'` the list bound of
  the next word (`pointSecurity`);
* the query positions: `a ^ t / (2 ^ (κ + R)) ^ t`, that is `(1 - γ) ^ t` (`positionsSecurity`);
* the batching challenge: `(t + 1) L' / |E|` (`batchingSecurity`).

No other round has an error: the messages (the residual claim's polynomial, the commitment, the
answer and the polynomial of the out-of-domain claim, the nonce, the query batch's polynomial)
carry nothing into the language, and the reading of the old word and the glue have no round.
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters CompPoly CMlPolynomialEval OracleComp OracleSpec ProtocolSpec
  StepSchedule
open scoped NNReal

@[expose] public section

namespace Whir

variable {sh sh' : Shape} {κ' : ℕ} (P : Par sh (Kap sh' κ')) (P' : Par sh' κ')

variable {ι₃ : Type} {O₃ : ι₃ → Type} [∀ i, OracleInterface (O₃ i)] {S₃ W₃ : Type}
  {k : List Step}

/-- The errors of a level followed by the rest of the opening, whose errors are `errR`. -/
noncomputable def levelErr (errR : (seqSpec k).ChallengeIdx → ℝ≥0) :
    (seqSpec (levelSteps sh sh' κ' k)).ChallengeIdx → ℝ≥0 :=
  errAppend (drawError E (foldErr P 0)) <| errAppend (foldRoundsErr P sh.lm1 1) <|
  errAppend (sayError (SumcheckRound.Message E 2)) <|
  errAppend (Component.sayOError (WordOf sh' κ')) <|
  errAppend (drawsError E ((Nat.choose P'.L 2 : ℕ) / (Nat.card E : ℝ≥0)) (Kap sh' κ')) <|
  errAppend (sayError E) <| errAppend (sayError (SumcheckRound.Message E 2)) <|
  errAppend (sayError E) <|
  errAppend (drawError (Fin sh.t → Fin (2 ^ (Kap sh' κ' + sh.R)))
    ((P.a ^ sh.t : ℕ) / (Nat.card (Fin sh.t → Fin (2 ^ (Kap sh' κ' + sh.R))) : ℝ≥0))) <|
  errAppend (drawError E (((sh.t + 1) * P'.L : ℕ) / (Nat.card E : ℝ≥0))) <|
  errAppend (fun i ↦ Fin.elim0 i.1) <| errAppend (sayError (SumcheckRound.Message E 2)) <|
  errAppend (fun i ↦ Fin.elim0 i.1) errR

/-- **A level followed by the rest of the opening is sound for the list relation**, given the
rest's security, at the errors `levelErr`. -/
noncomputable def levelSecurity
    {R : Component.Def (SumcheckRound.MidStmt (Weight E (sh'.ℓ + κ')) E 0 2) (OneW sh' κ')
      (Tab (sh'.ℓ + κ')) S₃ O₃ W₃ (seqSpec k)}
    {rel₃ : Set ((S₃ × ∀ i, O₃ i) × W₃)} {errR : (seqSpec k).ChallengeIdx → ℝ≥0}
    (SR : Component.Security R (foldRelMid P' 0) rel₃ errR) :
    Component.Security (levelDef sh sh' κ' R) (foldRelMid P 0) rel₃
      (levelErr P P' errR) := by
  unfold levelDef
  exact (foldDrawSecurity P (j := 0) (by simp [Shape.ℓ])).append <|
  (foldRoundsSecurity P sh.lm1 1 (by simp only [Shape.ℓ]; omega)).append <|
  (resSecurity P).append <| (commitSecurity P).append <| (pointSecurity P P').append <|
  (oodSecurity P P').append <| (oodPolySecurity P P').append <|
  (nonceSecurity P P').append <| (positionsSecurity P P').append <|
  (batchingSecurity P P').append <| (readSecurity P').append <|
  (queryPolySecurity P').append <| (glueSecurity P').append SR

end Whir

end

end LeanerVM.Protocol
