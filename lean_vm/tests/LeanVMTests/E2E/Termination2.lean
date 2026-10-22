import LeanVM.E2E.Deployed2
import LeanVM.E2E.Vis.Deployed2

/-!
# Tests: termination from two challenges (T3, cubic)

* The end lemmas of the two-challenge T3, its W-vis threading (`visError2`, `sec0ErrorGame2`) and
  its non-vis threading (`aggBadError2`, `closedError2`) rest on Lean's three axioms.
* **The guest's offsets**: the last two matrix coordinates of a deferred claim of the guest's
  shape sit at bytes `1272` and `1296` of its statement bytes, and the guest's shape has
  `28 ≥ 2` matrix coordinates.
* **The event**: one entry never makes a two-challenge prediction (the two predicted answers are
  distinct entries); two entries do when the first input carries both answers' challenges. A
  two-challenge prediction is a prediction.
* **The bound**: the budget `B (0, Q) = (Q³ - Q)/6` (`B (0, 3) = 4`), the potential of the empty
  log, and the term `Q³ / (6 · 2^384)` at `Q = 2^64` below `2^-194`.
* **The statements**: T3's probability, T4 at the trace with `RankOK2`, and the bounds of the
  end theorems, restated.
-/

namespace LeanVMTests.E2E.Termination2

open OracleComp OracleSpec LeanVM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Compile.Rom LeanVM.Node LeanVM.E2E
open scoped ENNReal

/-! ## Axioms -/

/-- info: 'LeanVM.E2E.rank_lt_of_child2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rank_lt_of_child2

/-- info: 'LeanVM.E2E.split_batchRoundsWith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms split_batchRoundsWith

/-- info: 'LeanVM.E2E.slice_stmtInput_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms slice_stmtInput_two

/-- info: 'LeanVM.E2E.pot2_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pot2_step

/-- info: 'LeanVM.E2E.prEvent_game_pred2V_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms prEvent_game_pred2V_le

/-- info: 'LeanVM.E2E.prEvent_game_pred2_le_cube' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms prEvent_game_pred2_le_cube

/-- info: 'LeanVM.E2E.rank_lt_of_child_vis2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rank_lt_of_child_vis2

/-- info: 'LeanVM.E2E.rankOK2_of_vis2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rankOK2_of_vis2

/-- info: 'LeanVM.E2E.rankOK2_of_pred2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rankOK2_of_pred2

/-- info: 'LeanVM.E2E.prEvent_runGame_t3_2_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms prEvent_runGame_t3_2_le

/-- info: 'LeanVM.E2E.prEvent_gameRec_aggBadV2_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms prEvent_gameRec_aggBadV2_le

/-- info: 'LeanVM.E2E.aggregate_no_forgery_vis2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms aggregate_no_forgery_vis2

/-- info: 'LeanVM.E2E.aggregate_no_forgery_vis2_game' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms aggregate_no_forgery_vis2_game

/-- info: 'LeanVM.E2E.sec0ErrorGame2_lifetime_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sec0ErrorGame2_lifetime_le

/-- info: 'LeanVM.E2E.aggregate_no_forgery_vis2_deployed_full_game' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms aggregate_no_forgery_vis2_deployed_full_game

/-- info: 'LeanVM.E2E.aggregate_no_forgery_vis2_one_slot_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms aggregate_no_forgery_vis2_one_slot_full

/-- info: 'LeanVM.E2E.aggregate_no_forgery_vis2_lifetime_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms aggregate_no_forgery_vis2_lifetime_full

/-- info: 'LeanVM.E2E.aggregate_no_forgery_vis2_lifetime_xmss_56' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms aggregate_no_forgery_vis2_lifetime_xmss_56

/-- info: 'LeanVM.E2E.aggregate_knowledge2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms aggregate_knowledge2

/-- info: 'LeanVM.E2E.prEvent_game_aggBad2_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms prEvent_game_aggBad2_le

/-- info: 'LeanVM.E2E.aggregate_no_forgery2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms aggregate_no_forgery2

/-- info: 'LeanVM.E2E.aggregate_no_forgery_closed2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms aggregate_no_forgery_closed2

/-- info: 'LeanVM.E2E.aggregate_no_forgery2_deployed_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms aggregate_no_forgery2_deployed_full

/-- info: 'LeanVM.E2E.aggregate_no_forgery2_one_slot_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms aggregate_no_forgery2_one_slot_full

/-! ## The guest's offsets and shape -/

/-- The guest's two offsets are bytes `1272` and `1296`. -/
example : predOffset (bytecodeWords Guest.guest) - 24 = 1272 ∧
    predOffset (bytecodeWords Guest.guest) = 1296 := by
  rw [predOffset, show (bytecodeWords Guest.guest).length = 2 ^ 22 from
    Guest.End.bytecode_length, Nat.log2_two_pow]
  exact ⟨rfl, rfl⟩

/-- A deferred claim of the guest's shape has at least two matrix coordinates. -/
example {d : DeferredClaim} (h : d.Shaped (bytecodeWords Guest.guest)) :
    2 ≤ d.matrixPoint.length :=
  two_le_matrixPoint_of_shaped h

/-! ## The event -/

/-- One entry is no two-challenge prediction: the predicted answers are distinct entries. -/
example (o₁ o₂ : ℕ) (e : Bytes × Digest) : ¬ Pred2 o₁ o₂ [e] := by
  rintro ⟨i₂, h₂, i₁, h₁, -⟩
  simp at h₂
  omega

/-- Two entries are one when the first input carries both answers' challenges. -/
example (u v : Digest) :
    Pred2 0 24 [(eBytes (challengeOf u) ++ eBytes (challengeOf v), u), ([], v)] := by
  have h24 : (eBytes (challengeOf u)).length = 24 := rfl
  refine ⟨1, by simp, 0, by omega, 0, le_rfl, trivial, trivial, trivial, ?_, ?_⟩
  · simp only [List.getElem_cons_zero, List.drop_zero]
    rw [List.take_left' h24]
  · simp only [List.getElem_cons_zero, List.getElem_cons_succ]
    rw [List.drop_left' h24]
    exact List.take_of_length_le (le_of_eq rfl)

/-- A two-challenge prediction is a prediction at its second offset. -/
example (o₁ o₂ : ℕ) (ℓ : Log) (h : Pred2 o₁ o₂ ℓ) : Pred o₂ ℓ := pred_of_pred2V h

/-- The restricted event is in the old restricted one. -/
example {nx ns : ℕ} [Sphincs.Params] (keys : Keys nx ns) (o₁ o₂ : ℕ) (ℓ : Log)
    (h : PredS2 keys o₁ o₂ ℓ) : PredS keys o₂ ℓ := predS_of_predS2 h

/-! ## The bound -/

/-- The budget from the start: `B (0, 3) = 4 = (27 - 3)/6`. -/
example : budget2 0 3 = 4 := rfl

/-- `6 B (0, Q) + Q = Q³`. -/
example (Q : ℕ) : 6 * budget2 0 Q + Q = Q ^ 3 := budget2_zero Q

/-- The potential of the empty log is `(Q³ - Q) / (6 · 2^384)`. -/
example (V : Bytes → Prop) (o₁ o₂ Q : ℕ) :
    pot2 V o₁ o₂ Q [] = ((Q ^ 3 - Q : ℕ) : ℝ≥0∞) / (6 * 2 ^ 384) := by
  rw [pot2_nil, budget2_zero_div]

/-- At `Q = 2^64` the T3 term is below `2^-194` (the birthday term was `≈ 2^-65`). -/
example : predError2 (2 ^ 64) ≤ (2 : ℝ≥0∞)⁻¹ ^ 194 := by
  refine (predError2_le_num _).trans ?_
  rw [two_inv_pow_eq_div 194 (by norm_num)]
  exact div_two_pow_256_le (by norm_num)

/-- Below `2^128` queries the T3 term is below a 256-bit birthday term. -/
example (Q : ℕ) (hQ : Q ≤ 2 ^ 128) : predError2 Q ≤ ((Q ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 :=
  predError2_le_sq hQ

/-! ## The statements -/

section Statements

variable {nx ns : ℕ} [Sphincs.Params]

/-- T3's probability from two challenges, at any offsets. -/
example (o₁ o₂ : ℕ) (guest : Semantics.Program) (fuel budget : ℕ) (A : GameAdversary nx ns)
    (Q : ℕ) (hQ : IsQueryBoundP (gameComp guest fuel budget A) IsHash Q) :
    Pr{let z ← game guest fuel budget A}[Pred2 o₁ o₂ z.2] ≤
      ((Q ^ 3 : ℕ) : ℝ≥0∞) / (6 * 2 ^ 384) :=
  prEvent_game_pred2_le_cube o₁ o₂ guest fuel budget A Q hQ

/-- `RankOK` gives `RankOK2`, the hypothesis of T4 at the trace. -/
example (ℓ : Log) (h : RankOK ℓ) : RankOK2 ℓ := RankOK.toRankOK2 h

/-- The new errors differ from the old only in T3's term. -/
example (Qv Q n : ℕ) :
    visError2 Qv Q n + Qv * (Qv + 1) / 2 ^ 193 = visError Qv Q n + predError2 Qv :=
  visError2_add Qv Q n

example (Q nx ns : ℕ) :
    closedError2 Q nx ns + Q * (Q + 1) / 2 ^ 193 = closedError Q nx ns + predError2 Q :=
  closedError2_add Q nx ns

/-- The new bad events are contained in the old ones. -/
example (ℓ : Log) (h : AggBad2 ℓ) : AggBad ℓ := aggBad_of_aggBad2 h

example (keys : Keys nx ns) (ℓ : Log) (h : AggBadV2 keys ℓ) : AggBadV keys ℓ :=
  aggBadV_of_aggBadV2 h

end Statements

end LeanVMTests.E2E.Termination2
