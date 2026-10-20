/-
  LeanerVM.Protocol.Whir.FoldSound

  Round-by-round soundness of a level's fold rounds for the list relation: the language of a
  stage, and for each fold challenge the count of challenges that let a prover escape. Candidate
  for ArkLib.
-/

module

public import LeanerVM.Protocol.Whir.Level
public import LeanerVM.Protocol.Whir.Stage
public import LeanerVM.Protocol.ToArkLib.PushSecurity

/-!
# The fold rounds are sound for the list relation

Category B: Annex B, proof of `thm:rbr`, "fold challenge `c_j`", with the invariant "every
codeword close to the current fold violates the current claim".

A level reads a word `ω` with `ℓ` lanes and a running claim about a table of `ℓ + κ` variables.
Its **parameters** (`Par`) are the agreement threshold `a`, the list bound `L` and the
mutual-correlated-agreement bound `N` of its code, with the facts the proof needs of them:
`2 ^ κ ≤ a` (the lists are of codewords that determine their messages) and `κ + R ≤ 64`.

The **language** of stage `j`, after the fold challenges `cs` (`FoldLang`), is what a cheating
prover has gained: either some interleaved codeword within `a` of `ω` decodes to a table whose
running claim after `cs` is the claimed one, or the folded lists no longer correspond (`FoldOK`
fails: a bad challenge has already happened). Read in the Annex's terms, its complement is the
invariant: at stage `0` the complement is "every codeword near `ω` violates the claim"; at stage
`j` "every codeword near the fold violates the claim" (`FoldOK` makes the codewords near the fold
the folds of the codewords near `ω`, whose claims are the claims of the sumcheck on the table).
With the polynomial of the next round received (`FoldLangMid`) the first alternative asks that
it be the honest one.

For a statement outside `FoldLangMid` whose polynomial passes the verifier's check, the challenges
that carry it into `FoldLang` at the next stage are few (`card_fold_challenge_le`): those at which
the received polynomial agrees with the honest polynomial of a codeword in the list (at most two
for each of the at most `L`: a polynomial of degree two is determined by three values), and those
at which the correspondence of the lists breaks (`card_fold_bad_le`, at most `2 ^ (ℓ - j - 1) N`).
The security halves of the round, and of the `i` rounds from a stage, follow from the generic
`Component.sendCheckedSecurity` and `Component.sampleChallengeSecurity`, with the error of the
stage in `roundsErrorFn`.
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters CompPoly CMlPolynomialEval OracleComp OracleSpec ProtocolSpec
open scoped NNReal

@[expose] public section

namespace Whir

/-- The parameters of a level's code in the soundness proof: the agreement threshold `a`
(`a = (1 - γ) · 2 ^ (κ + R)` for the radius `γ`), the list bound `L` and the
mutual-correlated-agreement bound `N` (the interfaces of `LeanerVM.Protocol.Whir.Lanes`),
with `2 ^ κ ≤ a ≤ 2 ^ (κ + R)` and `κ + R ≤ 64`. A threshold above the number of positions would
leave no codeword within it, so the list relation would be empty and every fold, out-of-domain and
batching error would be zero. -/
structure Par (sh : Shape) (κ : ℕ) where
  /-- The agreement threshold. -/
  a : ℕ
  /-- The list bound of the Johnson bound. -/
  L : ℕ
  /-- The bound on the bad folds of mutual correlated agreement. -/
  N : ℕ
  /-- A codeword within the threshold determines its message. -/
  hdist : 2 ^ κ ≤ a
  /-- The threshold is at most the number of positions: otherwise no codeword is within it, the
  list relation is empty, and the fold, out-of-domain and batching errors are all zero. -/
  hle : a ≤ 2 ^ (κ + sh.R)
  /-- The domain is `2 ^ (κ + R)` points of `K`. -/
  hb : κ + sh.R ≤ 64
  /-- The list bound. -/
  hlist : ListBound κ sh.R a sh.ℓ L
  /-- Mutual correlated agreement. -/
  hmca : McaBound κ sh.R a N

variable {sh : Shape} {κ : ℕ}

/-- The lane word of the level's oracle. -/
abbrev lanesOf (o : ∀ i, OneW sh κ i) : LW (κ + sh.R) := (o 0).lanes

section Language

variable (P : Par sh κ)

/-- The language of stage `j`: some interleaved codeword within the threshold of the oracle
decodes to a table whose running claim after the challenges `cs` is the claimed one, or the
correspondence of the folded lists has failed. -/
def FoldLang (j : ℕ) (W : Weight E (sh.ℓ + κ)) (cs : Vector E j) (claim : E)
    (o : ∀ i, OneW sh κ i) : Prop :=
  (∃ g : Msgs sh.ℓ κ, Cl κ sh.R P.a sh.ℓ (lanesOf o) g ∧
      ProductSum.claim W.onCube (ofLanes g) j cs = claim) ∨
    ¬ FoldOK κ sh.R P.a sh.ℓ cs (lanesOf o)

/-- The language of stage `j` with the next round's polynomial received: the codeword's running
claim is the claimed one and the polynomial is its honest round polynomial, or the correspondence of
the folded lists has failed. -/
def FoldLangMid (j : ℕ) (W : Weight E (sh.ℓ + κ)) (cs : Vector E j) (claim : E)
    (p : SumcheckRound.Message E 2) (o : ∀ i, OneW sh κ i) : Prop :=
  (∃ g : Msgs sh.ℓ κ, Cl κ sh.R P.a sh.ℓ (lanesOf o) g ∧
      ProductSum.claim W.onCube (ofLanes g) j cs = claim ∧
      p = ProductSum.roundPoly W.onCube (ofLanes g) j cs) ∨
    ¬ FoldOK κ sh.R P.a sh.ℓ cs (lanesOf o)

/-- The stage's relation, ignoring the witness. -/
def foldRel (j : ℕ) :
    Set ((SumcheckRound.Stmt (Weight E (sh.ℓ + κ)) E j × ∀ i, OneW sh κ i) ×
      Tab (sh.ℓ + κ)) :=
  Component.indep _ _ _ fun p ↦ FoldLang P j p.1.1 p.1.2.1 p.1.2.2 p.2

/-- The stage's relation with the next round's polynomial received, ignoring the witness. -/
def foldRelMid (j : ℕ) :
    Set ((SumcheckRound.MidStmt (Weight E (sh.ℓ + κ)) E j 2 × ∀ i, OneW sh κ i) ×
      Tab (sh.ℓ + κ)) :=
  Component.indep _ _ _ fun p ↦ FoldLangMid P j p.1.1.1 p.1.1.2.1 p.1.1.2.2 p.1.2 p.2

/-! ## The count of escapes at a fold challenge -/

/-- **A fold challenge.** For a statement outside the language with the polynomial received that
passes the verifier's check, at most `2 L + 2 ^ (ℓ - j - 1) N` challenges carry it into the
language at the next stage: the polynomial agrees with the honest polynomial of a codeword in the
list at at most two values (the codeword's claim or polynomial is not the received one, since the
statement is outside the language and the check passes), and the correspondence of the lists breaks
at at most `2 ^ (ℓ - j - 1) N` values (`card_fold_bad_le`). -/
theorem card_fold_challenge_le {j : ℕ} (hj : j < sh.ℓ) (W : Weight E (sh.ℓ + κ))
    (cs : Vector E j) (claim : E) (p : SumcheckRound.Message E 2) (o : ∀ i, OneW sh κ i)
    (hcheck : SumcheckRound.weightedSum 2 unitDom p = claim)
    (hnot : ¬ FoldLangMid P j W cs claim p o) :
    Nat.card {c : E // FoldLang P (j + 1) W (cs.push c) (SumcheckRound.evaluate 2 p c) o} ≤
      2 * P.L + 2 ^ (sh.ℓ - j - 1) * P.N := by
  classical
  have := Fintype.ofFinite E
  unfold FoldLangMid at hnot
  push Not at hnot
  obtain ⟨hno, hfold⟩ := hnot
  -- the codewords near the oracle
  let Gs := {g : Msgs sh.ℓ κ // Cl κ sh.R P.a sh.ℓ (lanesOf o) g}
  have := Fintype.ofFinite Gs
  have hGs : Fintype.card Gs ≤ P.L := by
    rw [← Nat.card_eq_fintype_card]
    exact P.hlist (lanesOf o)
  -- the received polynomial is not the honest polynomial of any codeword in the list
  have hne : ∀ g : Gs, p ≠ ProductSum.roundPoly W.onCube (ofLanes g.1) j cs := by
    intro g hp
    by_cases hc : ProductSum.claim W.onCube (ofLanes g.1) j cs = claim
    · exact hno g.1 g.2 hc hp
    · apply hc
      rw [← hcheck, hp]
      exact (ProductSum.roundPoly_check _ _
        (by have := hj; simp only [Shape.ℓ] at this ⊢; omega) cs).symm
  rw [natCard_subtype_eq_card_filter]
  set m0 := sh.ℓ - j - 1 with hm0
  calc _ ≤ (Finset.univ.biUnion fun g : Gs ↦ Finset.univ.filter fun c : E ↦
          SumcheckRound.evaluate 2 p c =
            SumcheckRound.evaluate 2 (ProductSum.roundPoly W.onCube (ofLanes g.1) j cs) c).card +
        (Finset.univ.filter fun c : E ↦ ¬ ∀ V : Msgs m0 κ,
          Cl κ sh.R P.a m0 (fold1W c (foldW cs (lanesOf o))) V →
            ∃ V₀ : Msgs (m0 + 1) κ, Cl κ sh.R P.a (m0 + 1) (foldW cs (lanesOf o)) V₀ ∧
              fold1M c V₀ = V).card := by
        refine le_trans (Finset.card_le_card fun c hc ↦ ?_) (Finset.card_union_le _ _)
        have hc' := (Finset.mem_filter.mp hc).2
        by_cases hstep : ∀ V : Msgs m0 κ,
            Cl κ sh.R P.a m0 (fold1W c (foldW cs (lanesOf o))) V →
              ∃ V₀ : Msgs (m0 + 1) κ, Cl κ sh.R P.a (m0 + 1) (foldW cs (lanesOf o)) V₀ ∧
                fold1M c V₀ = V
        · rcases hc' with ⟨g, hg, hcl⟩ | hnok
          · refine Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨⟨g, hg⟩, Finset.mem_univ _, ?_⟩)
            refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
            rw [ProductSum.roundPoly_eval _ _
              (by have := hj; simp only [Shape.ℓ] at this ⊢; omega)]
            exact hcl.symm
          · exact absurd (foldOK_push κ sh.R P.a sh.ℓ cs c (lanesOf o) hfold fun m hm V hV ↦ by
              obtain rfl : m = m0 := by omega
              exact hstep V hV) hnok
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hstep⟩)
    _ ≤ 2 * P.L + 2 ^ m0 * P.N := by
        refine add_le_add ?_ ?_
        · refine Finset.card_biUnion_le.trans ?_
          calc _ ≤ ∑ _g : Gs, 2 := Finset.sum_le_sum fun g _ ↦
                SumcheckRound.card_filter_evaluate_eq_le _ _ (hne g)
            _ = 2 * Fintype.card Gs := by simp [mul_comm]
            _ ≤ 2 * P.L := Nat.mul_le_mul_left 2 hGs
        · have := card_fold_bad_le (m := m0) P.hmca P.hdist P.hb (foldW cs (lanesOf o))
          rw [natCard_subtype_eq_card_filter] at this
          exact this

/-- The residual claim's language: after all the folds of the level, some interleaved codeword
near the level's word satisfies the residual claim, or the folded lists have failed to
correspond. -/
def ResLang (s : Bd sh κ) (o : ∀ i, OneW sh κ i) : Prop :=
  FoldLang P sh.ℓ s.W s.r s.c o

/-- The residual claim's language, as a relation on the record and the level's oracle. -/
def relRes : Set ((Bd sh κ × ∀ i, OneW sh κ i) × Tab (sh.ℓ + κ)) :=
  Component.indep _ _ _ fun p ↦ ResLang P p.1 p.2

/-- **The folded word's agreement with a table that satisfies the residual claim.** If the residual
claim's language does not hold, a table of `κ` variables that satisfies the residual claim has an
encoding that agrees with the folded word on fewer than `a` positions: otherwise it would be a
codeword near the folded word, hence the fold of a codeword near the word, whose claim is the
residual claim. -/
theorem card_agree_folded_le (s : Bd sh κ) (o : ∀ i, OneW sh κ i) (hres : ¬ ResLang P s o)
    (T : Tab κ) (hT : s.resid.pair (RingHom.id E) T = s.c) :
    (Finset.univ.filter fun y : Fin (2 ^ (κ + sh.R)) ↦
      encode (algebraMap K E) κ sh.R T y = foldRow s.r ((o 0).row y)).card ≤ P.a := by
  classical
  have hres' : (∀ g : Msgs sh.ℓ κ, Cl κ sh.R P.a sh.ℓ (lanesOf o) g →
        ProductSum.claim s.W.onCube (ofLanes g) sh.ℓ s.r ≠ s.c) ∧
      FoldOK κ sh.R P.a sh.ℓ s.r (lanesOf o) := by
    unfold ResLang FoldLang at hres
    push Not at hres
    exact hres
  by_contra hlt
  push Not at hlt
  have hcl : Cl κ sh.R P.a 0 (foldW s.r (lanesOf o)) (fun _ ↦ T) := by
    refine le_trans hlt.le (Finset.card_le_card fun y hy ↦ ?_)
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun u ↦ ?_⟩
    have hu : u.val = 0 := by simp
    simp only [hu, lanesOf, foldW_lane0]
    exact (Finset.mem_filter.mp hy).2
  obtain ⟨g0, hg0, hV⟩ := hres'.2 0 (by omega) (fun _ ↦ T) hcl
  have hV0 := (hV ⟨0, by norm_num⟩).trans (foldM_zero s.r g0)
  refine hres'.1 g0 hg0 ?_
  rw [claim_fold, ← hV0]
  exact hT

end Language

/-! ## The security of the fold rounds -/

section Security

variable (P : Par sh κ)

/-- The error at the fold challenge that follows `j` challenges: the escapes of
`card_fold_challenge_le` over the size of the field. -/
noncomputable def foldErr (j : ℕ) : ℝ≥0 :=
  ((2 * P.L + 2 ^ (sh.ℓ - j - 1) * P.N : ℕ) : ℝ≥0) / (Nat.card E : ℝ≥0)

/-- The residual claim's polynomial: the message carries nothing into the language. -/
def resSecurity : Component.Security (sendResidual sh κ) (foldRel P sh.ℓ) (relRes P)
    (sayError (SumcheckRound.Message E 2)) :=
  Component.sendCheckedSecurity (OneW sh κ) (SumcheckRound.Message E 2) _ _ _
    fun _ _ _ _ _ h ↦ h

/-- The fold error is the pinned `thm:rbr` entry: `2 L / |E|` and the mutual-correlated-agreement
error `N / |E|` times the `2 ^ (ℓ - j - 1)` lane pairs. -/
theorem foldErr_eq (j : ℕ) :
    foldErr P j = (2 * P.L : ℝ≥0) / (Nat.card E : ℝ≥0) +
      2 ^ (sh.ℓ - j - 1) * ((P.N : ℝ≥0) / (Nat.card E : ℝ≥0)) := by
  unfold foldErr
  push_cast
  rw [add_div]
  congr 1
  rw [mul_div_assoc]

/-- The security half of the message of a round's polynomial: the language with the polynomial
received implies the language. -/
def foldSendSecurity (j : ℕ) :
    Component.Security (SumcheckRound.sendPoly (levelFamily sh κ).poly j) (foldRel P j)
      (foldRelMid P j) (sayError (SumcheckRound.Message E 2)) :=
  Component.sendCheckedSecurity (OneW sh κ) (SumcheckRound.Message E 2) _ _ _ fun _ _ _ _ _ h ↦ by
    rcases h with ⟨g, hg, hc, -⟩ | hn
    · exact Or.inl ⟨g, hg, hc⟩
    · exact Or.inr hn

/-- The security half of a fold challenge: at most `2 L + 2 ^ (ℓ - j - 1) N` challenges let a
statement outside the language, with a polynomial that passes the check, into the language. -/
def foldDrawSecurity {j : ℕ} (hj : j < sh.ℓ) :
    Component.Security (SumcheckRound.drawChallenge j (levelFamily sh κ).weight)
      (foldRelMid P j) (foldRel P (j + 1)) (drawError E (foldErr P j)) :=
  Component.sampleChallengeSecurity (OneW sh κ) E _ _ (2 * P.L + 2 ^ (sh.ℓ - j - 1) * P.N)
    fun s o hc ↦ Component.card_badChallenge_le_of_indep (OneW sh κ) E _ _ _ _ s o fun hnot ↦
      card_fold_challenge_le P hj s.1.1 s.1.2.1 s.1.2.2 s.2 o (of_decide_eq_true hc) hnot

/-- The security half of a round: the polynomial, then the challenge. -/
def foldRoundSecurity {j : ℕ} (hj : j < sh.ℓ) :
    Component.Security (SumcheckRound.round (levelFamily sh κ).poly j (levelFamily sh κ).weight)
      (foldRel P j) (foldRel P (j + 1))
      (errAppend (sayError (SumcheckRound.Message E 2)) (drawError E (foldErr P j))) :=
  (foldSendSecurity P j).append (foldDrawSecurity P hj)

/-- The errors of `i` rounds from the stage `j`. -/
noncomputable def foldRoundsErr : (i j : ℕ) → (roundsSpec E 2 i).ChallengeIdx → ℝ≥0
  | 0, _ => fun i ↦ Fin.elim0 i.1
  | i + 1, j => errAppend (errAppend (sayError (SumcheckRound.Message E 2))
      (drawError E (foldErr P j))) (foldRoundsErr i (j + 1))

/-- The security half of the `i` rounds from the stage `j` to the last lane. -/
def foldRoundsSecurity : (i j : ℕ) → (h : j + i = sh.ℓ) →
    Component.Security (SumcheckRound.rounds (levelFamily sh κ).poly (levelFamily sh κ).weight
      sh.ℓ i j h) (foldRel P j) (foldRel P sh.ℓ) (foldRoundsErr P i j)
  | 0, j, h => by
    have hjm : j = sh.ℓ := by omega
    subst hjm
    exact Component.passThroughSecurityOfImp (OneW sh κ) _ fun s o w hout ↦ by
      simpa only [Vector.cast_rfl] using hout
  | i + 1, j, h => (foldRoundSecurity P (by omega)).append (foldRoundsSecurity i (j + 1) (by omega))

end Security

end Whir

end

end LeanerVM.Protocol
