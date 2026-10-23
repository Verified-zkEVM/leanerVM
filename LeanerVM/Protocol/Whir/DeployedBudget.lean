/-
  LeanerVM.Protocol.Whir.DeployedBudget

  The errors of WHIR's opening at leanVM's parameters, one challenge at a time: every challenge
  below `2^-128` but the query positions, which are below `2^-110`.
-/

module

public import LeanerVM.Protocol.Whir.Deployed
public import LeanerVM.Protocol.ToArkLib.ScheduleBounds

/-!
# The opening's errors challenge by challenge, at leanVM's parameters

Category A, on the errors of `LeanerVM.Protocol.Whir.OpenSound` and the chains of
`LeanerVM.Protocol.Whir.Deployed`. A random-oracle argument charges each Fiat–Shamir challenge
the error of its round, so it needs a bound on every challenge, not on their sum.

* `levelMark`, `finalMark`, `Ladder.mark`, `openMark` mark the query positions of each level,
  the one challenge a proof of work precedes, as `levelErr`, `finalErr`, `Ladder.err` and
  `openErr` assign the errors.
* `Ladder.fits` checks a chain's numbers against the budgets (`budget`): with `|E| = 2^192`, a
  fold challenge `2 L + 2^(ℓ-1) N ≤ 2^64`, an out-of-domain coordinate `L'^2 ≤ 2^64`, a batching
  challenge `(t + 1) L' ≤ 2^64`, and the positions `(a - 1)^t · 2^110 ≤ (2^(κ+R))^t`.
* `openErr_le_budget`: on a chain that fits, every challenge's error is at most the budget its
  mark selects: `2^-128`, or `2^-110` for the query positions.
* `deployed_fits`: every admissible chain fits, and its level-0 list bound is at most `128`; one
  decision on the window. `deployedChain_openErr_le` is the bound with no hypothesis.

The query positions' error is `((a - 1) / n)^t` for a level's threshold `a` and its `n` positions:
a word outside the list relation agrees with each codeword on fewer than `a` positions.
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters LeanerVM.Parameters.Whir OracleComp OracleSpec ProtocolSpec StepSchedule
open scoped NNReal

@[expose] public section

namespace Whir

/-! ## The query positions -/

/-- The marks of a level followed by the rest of the opening, whose marks are `bR`: the query
positions marked, as `levelErr` assigns the errors. -/
def levelMark {sh sh' : Shape} {κ' : ℕ} {k : List Step} (bR : (seqSpec k).ChallengeIdx → Bool) :
    (seqSpec (levelSteps sh sh' κ' k)).ChallengeIdx → Bool :=
  markAppend (fun _ ↦ false) <| markAppend (fun _ ↦ false) <| markAppend (fun _ ↦ false) <|
  markAppend (fun _ ↦ false) <| markAppend (fun _ ↦ false) <| markAppend (fun _ ↦ false) <|
  markAppend (fun _ ↦ false) <| markAppend (fun _ ↦ false) <| markAppend (fun _ ↦ true) <|
  markAppend (fun _ ↦ false) <| markAppend (fun _ ↦ false) <| markAppend (fun _ ↦ false) <|
  markAppend (fun _ ↦ false) bR

/-- The marks of the last level: its query positions marked. -/
def finalMark {sh : Shape} {nf : ℕ} : (seqSpec (finalSteps sh nf)).ChallengeIdx → Bool :=
  markAppend (fun _ ↦ false) <| markAppend (fun _ ↦ false) <| markAppend (fun _ ↦ false) <|
  markAppend (fun _ ↦ false) <| markAppend (fun _ ↦ false) <| markAppend (fun _ ↦ true) <|
  markAppend (fun _ ↦ false) <| markAppend (fun _ ↦ false) <| markAppend (fun _ ↦ false) <|
  markAppend (fun _ ↦ false) <| markAppend (fun _ ↦ false) <| markAppend (fun _ ↦ false)
    (fun _ ↦ false)

/-- The marks of a chain: every level's query positions. -/
def Ladder.mark : {sh : Shape} → {κ : ℕ} → (L : Ladder sh κ) → (seqSpec L.steps).ChallengeIdx → Bool
  | _, _, .last _ _ => finalMark
  | _, _, .cons _ L => levelMark L.mark

/-- The marks of the opening: the chain's, after the relayout and the opening claim's
polynomial. -/
def openMark {sh : Shape} {κ : ℕ} (L : Ladder sh κ) :
    (seqSpec (.skip :: .msg (SumcheckRound.Message E 2) :: L.steps)).ChallengeIdx → Bool :=
  markAppend (fun _ ↦ false) <| markAppend (fun _ ↦ false) L.mark

/-! ## The budgets -/

/-- The budget of a challenge: `2^-110` for the query positions, `2^-128` for every other. -/
noncomputable def budget : Bool → ℝ≥0
  | true => (2 ^ 110)⁻¹
  | false => (2 ^ 128)⁻¹

/-- A level's numbers within the budgets, with `|E| = 2^192`: a fold challenge,
`2 L + 2^(ℓ-1) N ≤ 2^64`; an out-of-domain coordinate, `L'^2 ≤ 2^64` for the next level's list
bound `L'`; the batching challenge, `(t + 1) L' ≤ 2^64`; the positions,
`(a - 1)^t · 2^110 ≤ (2^(κ+R))^t`. -/
def levelFits {sh : Shape} {κ : ℕ} (P : Par sh κ) (L' : ℕ) : Bool :=
  decide (2 * P.L + 2 ^ (sh.ℓ - 1) * P.N ≤ 2 ^ 64) && decide (L' * L' ≤ 2 ^ 64) &&
    decide ((sh.t + 1) * L' ≤ 2 ^ 64) && decide ((P.a - 1) ^ sh.t * 2 ^ 110 ≤ (2 ^ (κ + sh.R)) ^ sh.t)

/-- The last level's numbers within the budgets: a fold challenge, the batching challenge
`t ≤ 2^64`, and the positions. -/
def finalFits {sh : Shape} {nf : ℕ} (P : Par sh (nf + 1)) : Bool :=
  decide (2 * P.L + 2 ^ (sh.ℓ - 1) * P.N ≤ 2 ^ 64) && decide (sh.t ≤ 2 ^ 64) &&
    decide ((P.a - 1) ^ sh.t * 2 ^ 110 ≤ (2 ^ (nf + 1 + sh.R)) ^ sh.t)

/-- Every level of a chain within the budgets. -/
def Ladder.fits : {sh : Shape} → {κ : ℕ} → (L : Ladder sh κ) → L.Pars → Bool
  | _, _, .last _ _, P => finalFits P
  | _, _, .cons _ L, P => levelFits P.1 (L.headPar P.2).L && L.fits P.2

/-! ## From the numbers to the errors -/

/-- `x / |E| ≤ 2^-128` when `x ≤ 2^64`. -/
theorem natCast_div_card_le {x : ℕ} (h : x ≤ 2 ^ 64) :
    (x : ℝ≥0) / (Nat.card E : ℝ≥0) ≤ (2 ^ 128)⁻¹ := by
  rw [Nat.card_eq_fintype_card, card_E, div_le_iff₀ (by positivity)]
  calc (x : ℝ≥0) ≤ 2 ^ 64 := by exact_mod_cast h
    _ = (2 ^ 128)⁻¹ * ((2 ^ 192 : ℕ) : ℝ≥0) := by
      rw [Nat.cast_pow, Nat.cast_ofNat, show (2 : ℝ≥0) ^ 192 = 2 ^ 128 * 2 ^ 64 by ring,
        ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]

/-- The positions' error `a^t / (2^b)^t ≤ 2^-110` when `a^t · 2^110 ≤ (2^b)^t`. -/
theorem positions_div_le {a t b : ℕ} (h : a ^ t * 2 ^ 110 ≤ (2 ^ b) ^ t) :
    ((a ^ t : ℕ) : ℝ≥0) / (Nat.card (Fin t → Fin (2 ^ b)) : ℝ≥0) ≤ (2 ^ 110)⁻¹ := by
  rw [Nat.card_fun, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_fin,
    Fintype.card_fin, div_le_iff₀ (by positivity), ← div_eq_inv_mul,
    le_div_iff₀ (by positivity)]
  exact_mod_cast h

/-- The fold error is largest at the first fold round. -/
theorem foldErr_le_zero {sh : Shape} {κ : ℕ} (P : Par sh κ) (j : ℕ) :
    foldErr P j ≤ foldErr P 0 := by
  unfold foldErr
  refine div_le_div_of_nonneg_right (Nat.cast_le.mpr ?_) zero_le
  exact Nat.add_le_add_left
    (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega))) _

/-- Every fold round's challenge has at most the first fold round's error. -/
theorem foldRoundsErr_le {sh : Shape} {κ : ℕ} (P : Par sh κ) :
    (i j : ℕ) → ∀ x, foldRoundsErr P i j x ≤ foldErr P 0
  | 0, _ => fun x ↦ Fin.elim0 x.1
  | i + 1, j => errAppend_le_const
      (errAppend_le_const (sayError_le _ _) fun _ ↦ foldErr_le_zero P j)
      (foldRoundsErr_le P i (j + 1))

/-- A message queried through its own interface has no challenge: any bound holds. -/
private theorem sayOError_le (M : Type) [OracleInterface M] (c : ℝ≥0) :
    ∀ i, Component.sayOError M i ≤ c := fun i ↦ (IsEmpty.false i).elim

/-- A fold challenge of a level within the budget. -/
private theorem foldErr_le_budget {sh : Shape} {κ : ℕ} (P : Par sh κ)
    (h : 2 * P.L + 2 ^ (sh.ℓ - 1) * P.N ≤ 2 ^ 64) : foldErr P 0 ≤ budget false := by
  unfold foldErr
  exact natCast_div_card_le h

/-- **A level within the budgets keeps every challenge within its budget**, given the rest of the
opening does. -/
theorem levelErr_le_budget {sh sh' : Shape} {κ' : ℕ} (P : Par sh (Kap sh' κ')) (P' : Par sh' κ')
    {k : List Step} {errR : (seqSpec k).ChallengeIdx → ℝ≥0} {bR : (seqSpec k).ChallengeIdx → Bool}
    (h : levelFits P P'.L = true) (hR : ∀ i, errR i ≤ budget (bR i)) :
    ∀ i, levelErr P P' errR i ≤ budget (levelMark (sh := sh) (sh' := sh') (κ' := κ') bR i) := by
  simp only [levelFits, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hfold, hood⟩, hbatch⟩, hpos⟩ := h
  have hf := foldErr_le_budget P hfold
  have hood' : ((Nat.choose P'.L 2 : ℕ) : ℝ≥0) / (Nat.card E : ℝ≥0) ≤ budget false :=
    natCast_div_card_le ((Nat.choose_le_pow P'.L 2).trans (by rw [pow_two]; exact hood))
  unfold levelErr levelMark
  refine errAppend_le_mark _ (fun _ ↦ hf) <| errAppend_le_mark _
    (fun x ↦ (foldRoundsErr_le P _ _ x).trans hf) <| errAppend_le_mark _
    (sayError_le _ _) <| errAppend_le_mark _ (sayOError_le _ _) <|
    errAppend_le_mark _ (fun x ↦ (drawsError_le E _ _ x).trans hood') <| errAppend_le_mark _
    (sayError_le _ _) <| errAppend_le_mark _ (sayError_le _ _) <|
    errAppend_le_mark _ (sayError_le _ _) <| errAppend_le_mark _
    (fun _ ↦ positions_div_le hpos) <| errAppend_le_mark _ (fun _ ↦ natCast_div_card_le hbatch) <|
    errAppend_le_mark _ (fun x ↦ Fin.elim0 x.1) <| errAppend_le_mark _
    (sayError_le _ _) <| errAppend_le_mark _ (fun x ↦ Fin.elim0 x.1) hR

/-- **The last level within the budgets keeps every challenge within its budget.** -/
theorem finalErr_le_budget {sh : Shape} {nf : ℕ} (P : Par sh (nf + 1)) (h : finalFits P = true) :
    ∀ i, finalErr P i ≤ budget (finalMark (sh := sh) (nf := nf) i) := by
  simp only [finalFits, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hfold, hbatch⟩, hpos⟩ := h
  have hf := foldErr_le_budget P hfold
  have h2 : ((2 : ℕ) : ℝ≥0) / (Nat.card E : ℝ≥0) ≤ budget false :=
    natCast_div_card_le (by norm_num)
  unfold finalErr finalMark
  refine errAppend_le_mark _ (fun _ ↦ hf) <| errAppend_le_mark _
    (fun x ↦ (foldRoundsErr_le P _ _ x).trans hf) <| errAppend_le_mark _
    (sayError_le _ _) <| errAppend_le_mark _ (sayError_le _ _) <|
    errAppend_le_mark _ (sayError_le _ _) <| errAppend_le_mark _
    (fun _ ↦ positions_div_le hpos) <| errAppend_le_mark _ (fun _ ↦ natCast_div_card_le hbatch) <|
    errAppend_le_mark _ (fun x ↦ Fin.elim0 x.1) <| errAppend_le_mark _
    (sayError_le _ _) <| errAppend_le_mark _ (fun x ↦ Fin.elim0 x.1) <|
    errAppend_le_mark _ (fun _ ↦ h2) <| errAppend_le_mark _
    (fun x ↦ (roundsError_le E _ _ _ x).trans h2) fun x ↦ Fin.elim0 x.1

/-- **A chain within the budgets keeps every challenge within its budget.** -/
theorem Ladder.err_le_budget : {sh : Shape} → {κ : ℕ} → (L : Ladder sh κ) → (ps : L.Pars) →
    L.fits ps = true → ∀ i, L.err ps i ≤ budget (L.mark i)
  | _, _, .last _ _, P, h => finalErr_le_budget P h
  | _, _, .cons _ L, P, h => by
    simp only [Ladder.fits, Bool.and_eq_true] at h
    exact levelErr_le_budget P.1 (L.headPar P.2) h.1 (Ladder.err_le_budget L P.2 h.2)

/-- **The opening within the budgets**: on a chain that fits, every challenge of the opening has
at most `2^-128`, its query positions at most `2^-110`. -/
theorem openErr_le_budget {sh : Shape} {κ : ℕ} (L : Ladder sh κ) (ps : L.Pars)
    (h : L.fits ps = true) : ∀ i, openErr L ps i ≤ budget (openMark L i) :=
  errAppend_le_mark _ (fun x ↦ Fin.elim0 x.1) <|
    errAppend_le_mark _ (sayError_le _ _) (L.err_le_budget ps h)

/-! ## At leanVM's parameters -/

/-- Every admissible chain fits the budgets, and its level-0 list bound is at most `128`: one
decision on the window. -/
theorem deployed_fits {μ r : ℕ} (h : Admissible μ r) :
    (deployed μ r).all
      (fun c ↦ c.ladder.fits c.pars && decide ((c.ladder.headPar c.pars).L ≤ 128)) := by
  have key : ∀ μ < maxLogStack + 1, ∀ r < maxLogInvRate + 1, Admissible μ r →
      (deployed μ r).all
        (fun c ↦ c.ladder.fits c.pars && decide ((c.ladder.headPar c.pars).L ≤ 128)) := by
    decide +kernel
  exact key μ (Nat.lt_succ_of_le h.2.1) r (Nat.lt_succ_of_le h.2.2.2) h

/-- The deployed chain fits the budgets, and its level-0 list bound is at most `128`. -/
theorem deployedChain_fits {μ r : ℕ} (h : Admissible μ r) :
    (deployedChain μ r h).ladder.fits (deployedChain μ r h).pars = true ∧
      ((deployedChain μ r h).ladder.headPar (deployedChain μ r h).pars).L ≤ 128 := by
  have := (Option.all_eq_true_iff_get _ _).mp (deployed_fits h) (deployed_isSome h)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  exact this

/-- **The opening at leanVM's parameters, challenge by challenge**: every challenge's error is at
most `2^-128`, the query positions' at most `2^-110`, at every admissible stack size and rate. -/
theorem deployedChain_openErr_le {μ r : ℕ} (h : Admissible μ r) :
    ∀ i, openErr (deployedChain μ r h).ladder (deployedChain μ r h).pars i ≤
      budget (openMark (deployedChain μ r h).ladder i) :=
  openErr_le_budget _ _ (deployedChain_fits h).1

end Whir

end

end LeanerVM.Protocol
