/-
  LeanVM.Guest.B1.Opening.QueriesSound

  One query is `QueryOpens`; the soundness direction of `opening_queries`.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesCap
public import LeanVM.Guest.AcceptableChild

/-!
# One query, assembled (`opening_query`, lean_ethereum.py:1351-1394 at c4f4bc92)

`oqQuery_sound`: the statements of `oqQueryT` (the row, the dot product, the padding run, the
leaf hash, the path's windows, the cap leaf) give `QueryOpens` at the position whose windows the
window pointer's run holds. `oqQuery_winLoads`: a query reads each of its position's windows.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader} {σ : Val}

/-- The query's pieces, by membership. -/
theorem oqQuery_pieces {s : Oq} {bp cap flags wp : V} {b : ℕ} {emit : Bool} {pr : ℕ}
    (hA : BlockOk rd σ (oqQueryT s bp cap flags wp b emit pr)) :
    (∀ a, Stmt.atom a ∈ oqPacksT b s.R → a.Holds rd σ) ∧
      (∀ a, Stmt.atom a ∈ oqDotT s wp b → a.Holds rd σ) ∧
      (emit = true → ∀ a, Stmt.atom a ∈ oqPadT (oqK1 b s.R + s.D) → a.Holds rd σ) ∧
      (∀ a, Stmt.atom a ∈ oqLeafT s b (oqPr s b emit pr) (oqKL s b emit) → a.Holds rd σ) ∧
      BlockOk rd σ (oqPathT s bp (oqPr s b emit pr) (oqKL s b emit) (oqCh s b emit)) ∧
      (∀ a, Stmt.atom a ∈ oqCapT s bp cap flags (oqKL s b emit) (oqCh s b emit) → a.Holds rd σ) := by
  refine ⟨fun a h => hA.atom ?_, fun a h => hA.atom ?_, fun he a h => hA.atom ?_,
    fun a h => hA.atom ?_, hA.mono fun x h => ?_, fun a h => hA.atom ?_⟩ <;>
    simp only [oqQueryT, List.mem_append] <;> simp_all

/-- A path window's place and width: `(6i, oqWw s i)`. -/
theorem qwWin_path {s : Oq} {i : ℕ} (hi : i < oqNpw s) :
    qwWin (s.pd + s.cd) s.cd i = (6 * i, oqWw s i) := by
  unfold oqNpw at hi
  simp only [qwWin, qwNp, Nat.add_sub_cancel, oqWw, oqNpw]
  simp only [show ¬ i = (s.pd + 5) / 6 by omega, show ¬ i = (s.pd + 5) / 6 + 1 by omega,
    ↓reduceIte]
  split <;> simp_all

/-- A path window's value has the position's bits from `6i`. -/
theorem qwVal_path {s : Oq} {i : ℕ} (hi : i < oqNpw s) (q : ℕ) :
    qwVal (s.pd + s.cd) s.cd q i < 2 ^ oqWw s i ∧
      ∀ r < oqWw s i, (qwVal (s.pd + s.cd) s.cd q i).testBit r = q.testBit (6 * i + r) := by
  rw [qwVal, qwWin_path hi]
  refine ⟨Nat.mod_lt _ (by positivity), fun r hr ↦ ?_⟩
  rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, decide_eq_true hr, Bool.true_and]

theorem oqPathT_mem_load {s : Oq} {bp : V} {pr kL ch i : ℕ} (hi : i < oqNpw s) :
    Stmt.atom (.load (.n (oqWk s ch i)) bp i) ∈ oqPathT s bp pr kL ch :=
  oqPathT_mem_win hi (by simp [oqWinT])

theorem qwN_eq (s : Oq) : qwN (s.pd + s.cd) s.cd = oqNpw s + 2 := by
  simp [qwN, qwNp, oqNpw]

/-- **A query reads each of its position's windows.** -/
theorem oqQuery_winLoads {s : Oq} {bp cap flags wp : V} {b : ℕ} {emit : Bool} {pr : ℕ}
    (hA : BlockOk rd σ (oqQueryT s bp cap flags wp b emit pr)) :
    ∀ i < qwN (s.pd + s.cd) s.cd, ∃ v, LoadHolds rd (σ bp) i v := by
  obtain ⟨-, -, -, -, hPa, hC⟩ := oqQuery_pieces hA
  intro i hi
  rw [qwN_eq] at hi
  by_cases h1 : i < oqNpw s
  · exact ⟨_, hPa.atom (oqPathT_mem_load h1)⟩
  by_cases h2 : i = oqNpw s
  · subst h2
    exact ⟨_, hC _ (by simp [oqCapT] : Stmt.atom (.load (.n (oqCq s (oqCh s b emit))) bp
      (oqNpw s)) ∈ _)⟩
  obtain rfl : i = oqNpw s + 1 := by omega
  exact ⟨_, hC _ (by simp [oqCapT] : Stmt.atom (.load (.n (oqCq s (oqCh s b emit) + 1)) bp
    (oqNpw s + 1)) ∈ _)⟩

/-- **The walk and the cap leaf of a query** whose window pointer's run holds the windows of
`q < 2^(pd + cd)`: the siblings off the walk's side, the cap leaf and the flag. -/
theorem oqQuery_walk {s : Oq} (hcd : 1 ≤ s.cd) {bp cap flags wp : V} {b : ℕ} {emit : Bool}
    {pr : ℕ} (hA : BlockOk rd σ (oqQueryT s bp cap flags wp b emit pr))
    (hpad : σ (.n (oqPr s b emit pr)) = word 1 0 0)
    (hz : ∀ i < 4, σ (.n (oqPr s b emit pr + 1 + i)) = 0)
    {q : ℕ} (hq : q < 2 ^ (s.pd + s.cd))
    (hwin : ∀ i v, LoadHolds rd (σ bp) i v → i < qwN (s.pd + s.cd) s.cd →
      v = gen ^ qwVal (s.pd + s.cd) s.cd q i) {leaf : Digest}
    (hleaf : (σ (.n (oqNd s (oqKL s b emit) (oqCh s b emit) 0 0)),
      σ (.n (oqNd s (oqKL s b emit) (oqCh s b emit) 0 1))) = digestHalves leaf) :
    ∃ sibs : List Digest, sibs.length = s.pd ∧
      (∀ l < s.pd, SibAt σ (oqCh s b emit) q l (sibs.getD l default)) ∧
      LoadHolds rd (σ flags) (2 ^ (s.cd - 1) + q / 2 ^ (s.pd + 1)) 1 ∧
      LoadHolds rd (σ cap) (2 * (2 ^ s.cd + q / 2 ^ s.pd)) (digestHalves (climbD leaf q sibs)).1 ∧
      LoadHolds rd (σ cap) (2 * (2 ^ s.cd + q / 2 ^ s.pd) + 1)
        (digestHalves (climbD leaf q sibs)).2 := by
  obtain ⟨-, -, -, -, hPa, hC⟩ := oqQuery_pieces hA
  obtain ⟨sibs, hsl, hsib, hnd⟩ := oqPath_sound hPa hpad hz (q := q) (fun i hi ↦
    ⟨_, (qwVal_path hi q).1, hwin _ _ (hPa.atom (oqPathT_mem_load hi)) (by rw [qwN_eq]; omega),
      (qwVal_path hi q).2⟩) hleaf
  obtain ⟨hflag, hc0, hc1⟩ := oqCap_sound hcd hC hq hwin
  rw [show σ (.n (oqNd s (oqKL s b emit) (oqCh s b emit) (oqNpw s) 0)) =
    (digestHalves (climbD leaf q sibs)).1 by rw [← hnd]] at hc0
  rw [show σ (.n (oqNd s (oqKL s b emit) (oqCh s b emit) (oqNpw s) 1)) =
    (digestHalves (climbD leaf q sibs)).2 by rw [← hnd]] at hc1
  exact ⟨sibs, hsl, hsib, hflag, hc0, hc1⟩

/-- The row's packed cells and the leaf's digest of a query. -/
theorem oqQuery_leaf {s : Oq} (hs : s.RowShape) {bp cap flags wp : V} {b : ℕ} {emit : Bool}
    {pr : ℕ} (hA : BlockOk rd σ (oqQueryT s bp cap flags wp b emit pr))
    (hpad : σ (.n (oqPr s b emit pr)) = word 1 0 0)
    (hz : ∀ i < 4, σ (.n (oqPr s b emit pr + 1 + i)) = 0) :
    (σ (.n (oqNd s (oqKL s b emit) (oqCh s b emit) 0 0)),
      σ (.n (oqNd s (oqKL s b emit) (oqCh s b emit) 0 1))) =
      digestHalves (merkleLeafDigest (oqRow b s.R σ)) := by
  obtain ⟨hP, -, -, hL, -, -⟩ := oqQuery_pieces hA
  have hR2 : s.R % 2 = 0 := by rcases hs with ⟨hb, hI⟩ | ⟨hb, hI⟩ <;> simp [Oq.R, hb, hI]
  have hpk : ∀ j < s.ncells, σ (.n (oqPk b s.R j)) =
      E.ofLimbs ((oqRow b s.R σ).getD (2 * j) 0) ((oqRow b s.R σ).getD (2 * j + 1) 0) 0 :=
    fun j hj => by
      have hj' : j < s.R / 2 := hj
      rw [(oqPack_sound hP hj').2.2, getD_oqRow (by omega), getD_oqRow (by omega)]
      rfl
  have := oqLeaf_sound hs hL hpad hz (by simp [oqRow, Oq.ncells]; omega) hpk
  simpa [oqNd] using this

/-- **One query is `QueryOpens`** (`opening_query`): with the padding run `1, 0, 0, 0, 0` and the
window pointer's run holding the windows of `q < 2^(pd + cd)`, the query opens the hinted row at
`q` and its value is the row's dot product with the weights. -/
theorem oqQuery_sound {s : Oq} (hs : s.RowShape) (hcd : 1 ≤ s.cd)
    {bp cap flags wp : V} {b : ℕ} {emit : Bool} {pr : ℕ}
    (hA : BlockOk rd σ (oqQueryT s bp cap flags wp b emit pr))
    (hpad : σ (.n (oqPr s b emit pr)) = word 1 0 0)
    (hz : ∀ i < 4, σ (.n (oqPr s b emit pr + 1 + i)) = 0)
    {q : ℕ} (hq : q < 2 ^ (s.pd + s.cd))
    (hwin : ∀ i v, LoadHolds rd (σ bp) i v → i < qwN (s.pd + s.cd) s.cd →
      v = gen ^ qwVal (s.pd + s.cd) s.cd q i) :
    QueryOpens rd s.base s.I (s.pd + s.cd) s.cd (σ cap) (σ flags) (σ wp) q (oqRow b s.R σ)
      (σ (.n (oqDot s b))) := by
  obtain ⟨hP, hD, -, -, -, -⟩ := oqQuery_pieces hA
  have hrl : (oqRow b s.R σ).length = s.R := by simp [oqRow]
  have hW := oqWord_sound hs hP hD
  obtain ⟨hw, hdot⟩ := oqDot_sound hs hD hW
  obtain ⟨sibs, hsl, -, hflag, hc0, hc1⟩ :=
    oqQuery_walk hcd hA hpad hz hq hwin (oqQuery_leaf hs hA hpad hz)
  unfold QueryOpens
  rw [show s.pd + s.cd - s.cd = s.pd by omega]
  refine ⟨by rw [hrl]; rfl, sibs, oqW s b σ, hsl, fun l hl => hw l (by simpa [Oq.lo] using hl),
    hc0, hc1, hflag, ?_⟩
  rw [hdot, rowDot_eq]
  congr 1

end
end LeanVM.Guest.B1
