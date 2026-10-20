/-
  LeanerVM.Protocol.Whir.FinalSound

  Round-by-round soundness of the last level of WHIR's opening for the list relation: the fold
  rounds, the plaintext table, the positions, the final batching challenge and the tail sumcheck.
  Candidate for ArkLib.
-/

module

public import LeanerVM.Protocol.Whir.BoundarySound
public import LeanerVM.Protocol.Whir.Final

/-!
# The last level is sound for the list relation

Category B: Annex B, proof of `thm:rbr`, "final level": the plaintext table is transmitted, not a
codeword near an oracle, so there is no union over a list.

After the folds and the residual claim (the language of `FoldSound`), the prover sends the plaintext
table `ff`, then the verifier draws the positions. The language after the positions asks that `ff`
satisfy the residual claim and the consistency claims there (`FinalClaims`); outside the residual
claim's language that happens for at most `a ^ t` choices of the positions
(`card_final_positions_le`:
if `ff` satisfies the residual claim its encoding agrees with the folded word on fewer than `a`
positions, every position would have to be one of them). The batching challenge draws the
`t + 1` claims into one: a vector of `t + 1` discrepancies, not all zero, vanishes at at most `t`
challenges (`card_false_batch_le`, no list to union over). What remains is a sumcheck on tables the
verifier holds, with the family of `ProductSum`: `SumcheckRound.roundsSecurity` at `2 / |E|` a round,
and the terminal check is the sumcheck's last claim.
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters CompPoly CMlPolynomialEval OracleComp OracleSpec ProtocolSpec
  StepSchedule
open scoped NNReal

@[expose] public section

namespace Whir

variable {sh : Shape} {nf : ℕ} (P : Par sh (nf + 1))

/-! ## The languages of the last level -/

/-- The claims the plaintext table must satisfy at the glue: the residual claim and the consistency
claims at the positions, whose folded symbols are `cqf`. -/
def FinalClaims (s : FBd sh (nf + 1)) (cqf : Fin sh.t → E) : Prop :=
  s.resid.pair (RingHom.id E) s.ff = s.c ∧
    ∀ q, encode (algebraMap K E) (nf + 1) sh.R s.ff (s.pos q) = cqf q

/-- The language after the positions: the residual claim's language, or the plaintext table
satisfies the residual and consistency claims. -/
def FinalQLang (s : FBd sh (nf + 1)) (o : ∀ i, OneW sh (nf + 1) i) : Prop :=
  ResLang P s.toBd o ∨ FinalClaims s (cqAt s.toBd o)

/-- The batched claim about the plaintext table. -/
def FinalBLang (s : FBd sh (nf + 1)) (cqf : Fin sh.t → E) : Prop :=
  (Weight.batch ![s.resid, queryWeight (nf + 1) sh.R s.pos s.lam] s.lam).pair (RingHom.id E)
      s.ff = powerBatch ![s.c, powerBatch cqf s.lam] s.lam

/-- The relation before the positions: the residual claim's language, on the record with the
plaintext table. -/
def relResF : Set ((FBd sh (nf + 1) × ∀ i, OneW sh (nf + 1) i) × Tab (sh.ℓ + (nf + 1))) :=
  Component.indep _ _ _ fun p ↦ ResLang P p.1.toBd p.2

/-- The relation after the positions. -/
def relFQ : Set ((FBd sh (nf + 1) × ∀ i, OneW sh (nf + 1) i) × Tab (sh.ℓ + (nf + 1))) :=
  Component.indep _ _ _ fun p ↦ FinalQLang P p.1 p.2

/-- The relation after the batching challenge, before the last word is read. -/
def relFB : Set ((FBd sh (nf + 1) × ∀ i, OneW sh (nf + 1) i) × Tab (sh.ℓ + (nf + 1))) :=
  Component.indep _ _ _ fun p ↦ FinalBLang p.1 (cqAt p.1.toBd p.2)

/-- The relation after the last word is read: the recorded folded symbols. -/
def relFBR : Set ((FBd sh (nf + 1) × ∀ i, Component.keptOracles (OneW sh (nf + 1))
    (Function.Embedding.refl (Fin 1)) i) × Tab (sh.ℓ + (nf + 1))) :=
  Component.indep _ _ _ fun p ↦ FinalBLang p.1 p.1.cq

/-- The relation after the query batch's polynomial: the tail's start, the glued claim and
polynomial being the honest ones for the plaintext table. -/
def relFP : Set ((FBd sh (nf + 1) × ∀ i, Component.keptOracles (OneW sh (nf + 1))
    (Function.Embedding.refl (Fin 1)) i) × Tab (sh.ℓ + (nf + 1))) :=
  Component.indep _ _ _ fun p ↦
    powerBatch ![p.1.c, powerBatch p.1.cq p.1.lam] p.1.lam = ProductSum.claim
        (Weight.batch ![p.1.resid, queryWeight (nf + 1) sh.R p.1.pos p.1.lam] p.1.lam).onCube
        p.1.ff 0 #v[] ∧
      batchMessage ![p.1.p1, p.1.p3] p.1.lam = ProductSum.roundPoly
        (Weight.batch ![p.1.resid, queryWeight (nf + 1) sh.R p.1.pos p.1.lam] p.1.lam).onCube
        p.1.ff 0 #v[]

/-! ## The counts -/

/-- **The final positions.** If the residual claim's language does not hold, at most `a ^ t` choices
of the positions let the plaintext table satisfy the residual and consistency claims. -/
theorem card_final_positions_le (s : FBd sh (nf + 1)) (o : ∀ i, OneW sh (nf + 1) i)
    (hres : ¬ ResLang P s.toBd o) :
    Nat.card {x : Fin sh.t → Fin (2 ^ (nf + 1 + sh.R)) //
      FinalClaims { s with pos := x } (cqAt { s with pos := x }.toBd o)} ≤ P.a ^ sh.t := by
  classical
  rw [natCard_subtype_eq_card_filter]
  by_cases hr0 : s.resid.pair (RingHom.id E) s.ff = s.c
  · let S : Finset (Fin (2 ^ (nf + 1 + sh.R))) := Finset.univ.filter fun y ↦
      encode (algebraMap K E) (nf + 1) sh.R s.ff y = foldRow s.r ((o 0).row y)
    have hS : S.card ≤ P.a := card_agree_folded_le P s.toBd o hres s.ff hr0
    refine le_trans (Finset.card_le_card (t := Finset.univ.filter fun x :
        Fin sh.t → Fin (2 ^ (nf + 1 + sh.R)) ↦ ∀ q, x q ∈ S) fun x hx ↦ ?_) ?_
    · obtain ⟨-, hc⟩ := (Finset.mem_filter.mp hx).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun q ↦ Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hc q⟩⟩
    · rw [← natCard_subtype_eq_card_filter]
      exact card_positions_le S hS
  · refine le_trans (le_of_eq ?_) (Nat.zero_le _)
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro x - ⟨h, -⟩
    exact hr0 h

/-- The batching of two claims is the batching of the coefficients, the residual claim first. -/
private theorem powerBatch_glue_one {t : ℕ} (x₀ lam : E) (xs : Fin t → E) :
    powerBatch ![x₀, powerBatch xs lam] lam =
      powerBatch (Fin.cons x₀ xs : Fin (t + 1) → E) lam := by
  have hy : powerBatch xs lam * lam = ∑ q : Fin t, xs q * lam ^ (q.val + 1) := by
    simp only [powerBatch, Finset.sum_mul]
    exact Finset.sum_congr rfl fun q _ ↦ by ring
  generalize powerBatch xs lam = y at hy ⊢
  simp only [powerBatch, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.cons_zero, Fin.cons_succ,
    Fin.val_zero, Fin.val_succ, Matrix.cons_val_zero, Matrix.cons_val_succ]
  rw [← hy]
  ring

/-- **The final batching challenge.** If the language before it does not hold, at most `t`
challenges make the plaintext table satisfy the batched claim: it violates one of the `t + 1`
claims, so its batched discrepancy is a nonzero polynomial of degree at most `t`. -/
theorem card_final_batch_le (s : FBd sh (nf + 1)) (o : ∀ i, OneW sh (nf + 1) i)
    (hnot : ¬ FinalQLang P s o) :
    Nat.card {x : E // FinalBLang { s with lam := x } (cqAt { s with lam := x }.toBd o)} ≤ sh.t := by
  classical
  have := Fintype.ofFinite E
  unfold FinalQLang at hnot
  push Not at hnot
  obtain ⟨-, hall⟩ := hnot
  let claims : Fin (sh.t + 1) → E :=
    (Fin.cons (s.resid.pair (RingHom.id E) s.ff) (fun q ↦
      encode (algebraMap K E) (nf + 1) sh.R s.ff (s.pos q)) : Fin (sh.t + 1) → E)
  let target : Fin (sh.t + 1) → E := (Fin.cons s.c (cqAt s.toBd o) : Fin (sh.t + 1) → E)
  have hne : ∃ i, claims i ≠ target i := by
    by_contra hall'
    push Not at hall'
    refine hall ⟨hall' 0, fun q ↦ hall' q.succ⟩
  have key := card_false_batch_le claims target hne
  have hJ : sh.t + 1 - 1 = sh.t := by omega
  rw [hJ] at key
  rw [natCard_subtype_eq_card_filter]
  refine le_trans (Finset.card_le_card fun x hx ↦ ?_) key
  have he := (Finset.mem_filter.mp hx).2
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  unfold FinalBLang at he
  change (Weight.batch ![s.resid, queryWeight (nf + 1) sh.R s.pos x] x).pair (RingHom.id E)
      s.ff = powerBatch ![s.c, powerBatch (cqAt s.toBd o) x] x at he
  have hL : (Weight.batch ![s.resid, queryWeight (nf + 1) sh.R s.pos x] x).pair (RingHom.id E)
      s.ff = powerBatch ![s.resid.pair (RingHom.id E) s.ff, powerBatch (fun q ↦
        encode (algebraMap K E) (nf + 1) sh.R s.ff (s.pos q)) x] x := by
    rw [Weight.pair_batch]
    congr 1
    funext i
    fin_cases i
    · rfl
    · exact pair_queryWeight _ _ _
  rw [hL, powerBatch_glue_one, powerBatch_glue_one] at he
  exact he


/-! ## The security of the last level -/

/-- The tail's family is sound: its invariant is trivially true. -/
theorem tailSound (sh : Shape) (nf : ℕ) : (tailFamily sh nf).Sound (nf + 1) :=
  fun _ _ _ _ hn ↦ absurd trivial hn

/-- The plaintext table: the message carries nothing into the language. -/
def tableSecurity : Component.Security (sendTable sh nf) (relRes P) (relResF P)
    (sayError (Tab (nf + 1))) :=
  Component.sendCheckedSecurity (OneW sh (nf + 1)) (Tab (nf + 1)) _ _ _ fun _ _ _ _ _ h ↦ h

/-- The grinding nonce of the last level. -/
def finalNonceSecurity : Component.Security (finalNonce sh nf)
    (relResF P) (relResF P) (sayError E) :=
  Component.sendCheckedSecurity _ E _ _ _ fun _ _ _ _ _ h ↦ h

/-- **The positions of the last level**, at `(1 - γ) ^ t`. -/
noncomputable def finalPositionsSecurity : Component.Security
    (finalPositions sh nf) (relResF P) (relFQ P)
    (drawError (Fin sh.t → Fin (2 ^ (nf + 1 + sh.R)))
      ((P.a ^ sh.t : ℕ) / (Nat.card (Fin sh.t → Fin (2 ^ (nf + 1 + sh.R))) : ℝ≥0))) :=
  Component.sampleChallengeSecurity _ _ _ _ (P.a ^ sh.t) fun s o _ ↦
    Component.card_badChallenge_le_of_indep _ _ _ _ _ _ s o fun hnot ↦
      le_trans (natCard_subtype_mono fun x hx ↦ by
        rcases hx with hx | hx
        · exact absurd hx hnot
        · exact hx) (card_final_positions_le P s o hnot)

/-- **The final batching challenge**, at `t / |E|`. -/
noncomputable def finalBatchingSecurity : Component.Security
    (finalBatch sh nf) (relFQ P) (relFB (sh := sh) (nf := nf))
    (drawError E ((sh.t : ℕ) / (Nat.card E : ℝ≥0))) :=
  Component.sampleChallengeSecurity _ _ _ _ sh.t fun s o _ ↦
    Component.card_badChallenge_le_of_indep _ _ _ _ _ _ s o fun hnot ↦
      card_final_batch_le P s o hnot

/-- What the reading of the last word records: the folded rows at the positions. -/
private theorem readFinalOut_answer (s : FBd sh (nf + 1)) (o : ∀ i, OneW sh (nf + 1) i) :
    readFinalOut sh nf s (Component.answerOf (OneW sh (nf + 1)) o (readFinalQuery sh nf s)) =
      { s with cq := cqAt s.toBd o } := rfl

/-- The reading of the last word. -/
def finalReadSecurity : Component.Security (readFinal sh nf) (relFB (sh := sh) (nf := nf))
    (relFBR (sh := sh) (nf := nf)) (fun i ↦ Fin.elim0 i.1) :=
  Component.queryRecordSecurity (OneW sh (nf + 1)) (Function.Embedding.refl (Fin 1))
    (readFinalQuery sh nf) (fun _ _ ↦ true) (readFinalOut sh nf)
    (relIn := relFB (sh := sh) (nf := nf)) (relOut := relFBR (sh := sh) (nf := nf))
    fun s o w _ h ↦ by
      simp only [relFBR, Component.indep, Set.mem_ofPred_eq, readFinalOut_answer] at h
      exact h

/-- The query batch's polynomial: the message carries nothing into the language. -/
def finalQueryPolySecurity : Component.Security
    (finalQueryPoly sh nf) (relFBR (sh := sh) (nf := nf)) (relFP (sh := sh) (nf := nf))
    (sayError (SumcheckRound.Message E 2)) :=
  Component.sendCheckedSecurity _ (SumcheckRound.Message E 2) _ _ _ fun s o w msg _ hout ↦ by
    have h1 := hout.1
    rw [claim_zero] at h1
    exact h1.symm

/-- The glue: the tail's language at its start, with the glued claim and polynomial. -/
def finalGlueSecurity : Component.Security (glueFinal sh nf) (relFP (sh := sh) (nf := nf))
    (SumcheckRound.relMid (tailFamily sh nf) 0) (fun i ↦ Fin.elim0 i.1) :=
  Component.mapWitnessSecurity _ _ _ (fun _ ↦ Vector.replicate _ 0)
    fun _ _ _ hout ↦ ⟨hout.1.2, hout.2⟩

/-- The first challenge of the tail, at `2 / |E|`. -/
noncomputable def tailFirstSecurity : Component.Security (tailFirst sh nf)
    (SumcheckRound.relMid (tailFamily sh nf) 0) (SumcheckRound.rel (tailFamily sh nf) 1)
    (drawError E ((2 : ℕ) / (Nat.card E : ℝ≥0))) :=
  SumcheckRound.drawChallengeSecurity 0 (tailFamily sh nf) (tailHonest sh nf).toConsistent
    (tailSound sh nf) (by omega)

/-- The remaining rounds of the tail, each at `2 / |E|`. -/
noncomputable def tailRestSecurity : Component.Security (tailRest sh nf)
    (SumcheckRound.rel (tailFamily sh nf) 1) (SumcheckRound.rel (tailFamily sh nf) (nf + 1))
    (roundsError E 2 ((2 : ℕ) / (Nat.card E : ℝ≥0)) nf) :=
  SumcheckRound.roundsSecurity (tailFamily sh nf) (nf + 1) (tailHonest sh nf).toConsistent
    (tailSound sh nf) nf 1 (by omega)

/-- The terminal check: a statement that passes it has the sumcheck's last claim. -/
def terminalSecurity : Component.Security (terminal sh nf)
    (SumcheckRound.rel (tailFamily sh nf) (nf + 1)) Set.univ (fun i ↦ Fin.elim0 i.1) :=
  Component.passCheckSecurity (OneW sh (nf + 1)) _ _ fun s o w hc _ ↦ by
    have h := of_decide_eq_true hc
    refine ⟨trivial, ?_⟩
    show s.2.2 = ProductSum.claim s.1.1.onCube s.1.2 (nf + 1) s.2.1
    rw [← h, ProductSum.claim, plainSum_self, ProductSum.summand, s.1.1.mle_eq]

/-- The errors of the last level. -/
noncomputable def finalErr : (seqSpec (finalSteps sh nf)).ChallengeIdx → ℝ≥0 :=
  errAppend (drawError E (foldErr P 0)) <| errAppend (foldRoundsErr P sh.lm1 1) <|
  errAppend (sayError (SumcheckRound.Message E 2)) <| errAppend (sayError (Tab (nf + 1))) <|
  errAppend (sayError E) <|
  errAppend (drawError (Fin sh.t → Fin (2 ^ (nf + 1 + sh.R)))
    ((P.a ^ sh.t : ℕ) / (Nat.card (Fin sh.t → Fin (2 ^ (nf + 1 + sh.R))) : ℝ≥0))) <|
  errAppend (drawError E ((sh.t : ℕ) / (Nat.card E : ℝ≥0))) <|
  errAppend (fun i ↦ Fin.elim0 i.1) <| errAppend (sayError (SumcheckRound.Message E 2)) <|
  errAppend (fun i ↦ Fin.elim0 i.1) <|
  errAppend (drawError E ((2 : ℕ) / (Nat.card E : ℝ≥0))) <|
  errAppend (roundsError E 2 ((2 : ℕ) / (Nat.card E : ℝ≥0)) nf) (fun i ↦ Fin.elim0 i.1)

/-- **The last level is sound for the list relation**, at the errors `finalErr`: from the language
at its start to acceptance. -/
noncomputable def finalSecurity :
    Component.Security (finalDef sh nf) (foldRelMid P 0) Set.univ (finalErr P) := by
  unfold finalDef
  exact (foldDrawSecurity P (j := 0) (by simp [Shape.ℓ])).append <|
    (foldRoundsSecurity P sh.lm1 1 (by simp only [Shape.ℓ]; omega)).append <|
    (resSecurity P).append <| (tableSecurity P).append <| (finalNonceSecurity P).append <|
    (finalPositionsSecurity P).append <| (finalBatchingSecurity P).append <|
    (finalReadSecurity).append <| (finalQueryPolySecurity).append <| (finalGlueSecurity).append <|
    (tailFirstSecurity).append <| (tailRestSecurity).append terminalSecurity

end Whir

end

end LeanerVM.Protocol
