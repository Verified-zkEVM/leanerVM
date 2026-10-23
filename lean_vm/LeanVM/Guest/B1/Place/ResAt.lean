/-
  LeanVM.Guest.B1.Place.ResAt

  `open_stacked`'s residual loop, honestly and placed.
-/

module

public import LeanVM.Guest.B1.Place.SqAt
public import LeanVM.Guest.B1.Whir.CFinResQ
public import LeanVM.Guest.B1.Whir.CLoop
public import LeanVM.Guest.B1.Whir.ResLoop

/-!
# The residual loop, honestly and placed

`resIter_complete`: one iteration at `x` whose memory is the iteration's meaning (`ResIter`, the
row's words `D` at `bd`) holds at a valuation, with the guard `x·g + N` and the next arguments.
`resLoop_rel`: the loop entered at `1 :: g^n :: rest` holds (`loop_complete`).
`resLoop_pure`: the loop helper places nothing and calls only itself, so it is complete placed
on every memory holding the caller's words where every iteration's meaning holds
(`resLoop_completeAtD`, `completeAt_of_rel_pureD`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier hiding Layout
open LeanVM.Guest.B1.Main (Layout MemL RegionL)
open LeanVM.Guest.B1.Whir

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-- A materialized pointer, as a block of named values. -/
theorem osMat_blk {base off k : ℕ} (hoff : off < u128Bound) (hb : base < k) (σ : Val) :
    BlkF C rd σ k (osMat base off k).2.2 (matVal σ base off k) (osMat base off k).1
      (fun σ' ↦ σ' (.n (osMat base off k).2.1) = σ (.n base) * gen ^ off ∧ AgreeBelow k σ σ') :=
  fun _ ha hv ↦ let h := osMat_complete (C := C) (rd := rd) hoff hb ha hv; ⟨h.1, h.2, ha⟩

theorem osMat_v_lt (b o k : ℕ) (hb : b < k) : (osMat b o k).2.1 < (osMat b o k).2.2 := by
  unfold osMat; split_ifs
  · exact hb
  · show k + 1 < k + 2; omega

/-- One atom writing the next value. -/
theorem atom1_complete {k : ℕ} {a : Atom} (σ : Val) (v : E)
    (h : ∀ σ', AgreeBelow k σ σ' → σ' (.n k) = v → a.Holds rd σ') :
    BlkF C rd σ k (k + 1) (fun _ ↦ v) [.atom a] (fun σ' ↦ σ' (.n k) = v ∧ AgreeBelow k σ σ') :=
  fun σ' ha hr ↦ by
    have v0 := hr k le_rfl (by omega)
    exact ⟨allOk_cons.mpr ⟨h σ' ha v0, allOk_nil⟩, v0, ha⟩

theorem osResQuery_k_bounds (pos bd row vo n k : ℕ) :
    k + 2 ≤ (osResQuery pos bd row vo n k).2.2 ∧
      (osResQuery pos bd row vo n k).2.1 < (osResQuery pos bd row vo n k).2.2 := by
  have h := osResQ_k pos bd row vo (n - 1) 1 (k + 1) (k + 2)
  show k + 2 ≤ (osResQ pos bd row vo (n - 1) 1 (k + 1) (k + 2)).2.2 ∧
    (osResQ pos bd row vo (n - 1) 1 (k + 1) (k + 2)).2.1 <
      (osResQ pos bd row vo (n - 1) 1 (k + 1) (k + 2)).2.2
  rcases Nat.eq_zero_or_pos (n - 1) with h0 | h0
  · rw [h.1, h.2.1 h0]; omega
  · rw [h.1, h.2.2 h0]; omega

/-- Two blocks in sequence, their values chosen. -/
theorem BlkF.thenE {σ : Val} {k k1 k2 : ℕ} {A B : List Stmt} {OutA Out : Val → Prop}
    (h1 : k ≤ k1) (h2 : k1 ≤ k2) (hA : ∃ fA, BlkF C rd σ k k1 fA A OutA)
    (hB : ∀ σ1, AgreeBelow k σ σ1 → OutA σ1 → ∃ fB, BlkF C rd σ1 k1 k2 fB B Out) :
    ∃ f, BlkF C rd σ k k2 f (A ++ B) Out := by
  obtain ⟨fA, hA⟩ := hA
  have hB' : ∀ σ1, ∃ fB : ℕ → E, AgreeBelow k σ σ1 → OutA σ1 → BlkF C rd σ1 k1 k2 fB B Out :=
    fun σ1 ↦ by
      by_cases h : AgreeBelow k σ σ1 ∧ OutA σ1
      · obtain ⟨fB, hf⟩ := hB σ1 h.1 h.2; exact ⟨fB, fun _ _ ↦ hf⟩
      · exact ⟨fun _ ↦ 0, fun ha ho ↦ absurd ⟨ha, ho⟩ h⟩
  exact ⟨_, BlkF.then (fB := fun σ1 ↦ Classical.choose (hB' σ1)) h1 h2 hA
    fun σ1 ha ho ↦ Classical.choose_spec (hB' σ1) ha ho⟩

/-- **One iteration of the residual loop, honestly.** -/
theorem resIter_complete (c : OsCfg) (lvl : ℕ) (lv : OsLv) (hml : 1 ≤ lv.logCols)
    (hpo : lv.posOff < u128Bound) (hwo : lvl * c.maxQ < u128Bound) {D : ℕ → E}
    (x N qpos qw bd acc : E)
    (hD : ∀ s < lv.logCols, LoadHolds rd bd (lvl * ligColsCap + s) (D s))
    (hit : ResIter rd D lv.vanish lv.logCols lv.posOff (lvl * c.maxQ) qpos qw acc x) :
    ∃ σ : Val, (osParams 6).map σ = [x, N, qpos, qw, bd, acc] ∧
      AllOk C rd σ (resLoopA c lvl lv ++ osLoopTailA (resLoopR c lvl lv)) ∧
      σ (.n (resLoopR c lvl lv + 2)) = x * gen + N ∧
      (.n (resLoopR c lvl lv + 4) :: (List.range (6 - 1)).map fun i ↦ V.n (i + 1)).map σ =
        x * gen :: [N, qpos, qw, bd, acc] := by
  obtain ⟨p0, p1, w0, w1, a, hp0, hp1, hw0, hw1, ha0, hout⟩ := hit
  set σ0 := segVal [(6, fun i ↦ [x, N, qpos, qw, bd, acc].getD i 0)] with hσ0
  have g : ∀ i < 6, σ0 (.n i) = [x, N, qpos, qw, bd, acc].getD i 0 := fun i hi ↦ by
    rw [hσ0, segVal_n]; simp [segLookup, hi]
  have g0 := g 0 (by omega); have g1 := g 1 (by omega); have g2 := g 2 (by omega)
  have g3 := g 3 (by omega); have g4 := g 4 (by omega); have g5 := g 5 (by omega)
  simp only [List.getD_cons_zero, List.getD_cons_succ] at g0 g1 g2 g3 g4 g5
  set pp := osMat 2 lv.posOff 7 with hpp
  set wp := osMat 3 (lvl * c.maxQ) (pp.2.2 + 1) with hwp
  set k := wp.2.2 + 1 with hk
  set e0 := osResQuery k 4 (lvl * ligColsCap) lv.vanish lv.logCols (k + 1) with he0
  set e1 := osResQuery e0.2.2 4 (lvl * ligColsCap) lv.vanish lv.logCols (e0.2.2 + 1) with he1
  set r := e1.2.2 with hr
  have hR : resLoopR c lvl lv = r + 9 := rfl
  have o1 : 7 ≤ pp.2.2 := osMat_next _ _ _
  have o1' : pp.2.1 < pp.2.2 := osMat_v_lt _ _ _ (by omega)
  have o2 : pp.2.2 + 1 ≤ wp.2.2 := osMat_next _ _ _
  have o2' : wp.2.1 < wp.2.2 := osMat_v_lt _ _ _ (by omega)
  have o3 := osResQuery_k_bounds k 4 (lvl * ligColsCap) lv.vanish lv.logCols (k + 1)
  have o4 := osResQuery_k_bounds e0.2.2 4 (lvl * ligColsCap) lv.vanish lv.logCols (e0.2.2 + 1)
  have o3a : k + 1 + 2 ≤ e0.2.2 := o3.1
  have o3b : e0.2.1 < e0.2.2 := o3.2
  have o4a : e0.2.2 + 1 + 2 ≤ r := o4.1
  have o4b : e1.2.1 < r := o4.2
  have eA : resLoopA c lvl lv ++ osLoopTailA (resLoopR c lvl lv) =
      [.atom (.mul (.n 6) (.n 0) (.n 0))] ++ (pp.1 ++ ([.atom (.mul (.n pp.2.2) (.n pp.2.1) (.n 6))] ++
      (wp.1 ++ ([.atom (.mul (.n wp.2.2) (.n wp.2.1) (.n 6))] ++
      ([.atom (.load (.n k) (.n pp.2.2) 0)] ++ (e0.1 ++
      ([.atom (.load (.n e0.2.2) (.n pp.2.2) 1)] ++ (e1.1 ++
      ([.atom (.mul (.n r) (.n 5) (.n 0)), .atom (.load (.n (r + 1)) (.n r) 0),
        .atom (.load (.n (r + 2)) (.n wp.2.2) 0), .atom (.mul (.n (r + 3)) (.n (r + 2)) (.n e0.2.1)),
        .atom (.add (.n (r + 4)) (.n (r + 1)) (.n (r + 3))), .atom (.load (.n (r + 5)) (.n wp.2.2) 1),
        .atom (.mul (.n (r + 6)) (.n (r + 5)) (.n e1.2.1)),
        .atom (.add (.n (r + 7)) (.n (r + 4)) (.n (r + 6))),
        .atom (.mul (.n (r + 8)) (.n 5) (.n 0)), .atom (.load (.n (r + 7)) (.n (r + 8)) 1)] ++
      osLoopTailA (r + 9)))))))))) := by
    rw [hR]; simp only [resLoopA, List.append_assoc]; rfl
  -- the blocks
  have hB : ∃ f, BlkF C rd σ0 6 (r + 9 + 5) f (resLoopA c lvl lv ++ osLoopTailA (resLoopR c lvl lv))
      (fun _ ↦ True) := by
    rw [eA]
    refine BlkF.thenE (k1 := 7) (by omega) (by omega)
      ⟨_, atom1_complete (C := C) (rd := rd) (k := 6) σ0 (x * x) fun σ' ha v ↦ by
        show σ' (.n 6) = σ' (.n 0) * σ' (.n 0); rw [v, ha 0 (by omega), g0]⟩
      fun σ1 ha1 hO1 ↦ ?_
    refine BlkF.thenE (k1 := pp.2.2) o1 (by omega)
      ⟨_, osMat_blk (C := C) (rd := rd) hpo (show 2 < 7 by omega) σ1⟩ fun σ2 ha2 hO2 ↦ ?_
    have hq2 : σ2 (.n pp.2.1) = qpos * gen ^ lv.posOff := by
      rw [hO2.1, ha1 2 (by omega), g2]
    refine BlkF.thenE (k1 := pp.2.2 + 1) (by omega) (by omega)
      ⟨_, atom1_complete (C := C) (rd := rd) (k := pp.2.2) σ2 (qpos * gen ^ lv.posOff * (x * x))
        fun σ' ha v ↦ by
          show σ' (.n pp.2.2) = σ' (.n pp.2.1) * σ' (.n 6)
          rw [v, ha _ o1', hq2, ha 6 (by omega), hO2.2 6 (by omega), hO1.1]⟩ fun σ3 ha3 hO3 ↦ ?_
    refine BlkF.thenE (k1 := wp.2.2) o2 (by omega)
      ⟨_, osMat_blk (C := C) (rd := rd) hwo (show 3 < pp.2.2 + 1 by omega) σ3⟩ fun σ4 ha4 hO4 ↦ ?_
    have hw4 : σ4 (.n wp.2.1) = qw * gen ^ (lvl * c.maxQ) := by
      rw [hO4.1, ha3 3 (by omega), ha2 3 (by omega), ha1 3 (by omega), g3]
    have e6 : σ4 (.n 6) = x * x := by
      rw [ha4 6 (by omega), ha3 6 (by omega), ha2 6 (by omega), hO1.1]
    refine BlkF.thenE (k1 := k) (by omega) (by omega)
      ⟨_, atom1_complete (C := C) (rd := rd) (k := wp.2.2) σ4 (qw * gen ^ (lvl * c.maxQ) * (x * x))
        fun σ' ha v ↦ by
          show σ' (.n wp.2.2) = σ' (.n wp.2.1) * σ' (.n 6)
          rw [v, ha _ o2', hw4, ha 6 (by omega), e6]⟩ fun σ5 ha5 hO5 ↦ ?_
    have ePP : ∀ σ', AgreeBelow k σ5 σ' → σ' (.n pp.2.2) = qpos * gen ^ lv.posOff * x ^ 2 :=
      fun σ' ha ↦ by
        rw [ha _ (by omega), ha5 _ (by omega), ha4 _ (by omega), hO3.1, sq]
    refine BlkF.thenE (k1 := k + 1) (by omega) (by omega)
      ⟨_, load_complete (C := C) (rd := rd) (k := k) (p := pp.2.2) (off := 0) σ5 (by omega)
        (by rw [ePP σ5 (fun _ _ ↦ rfl)]; exact hp0)⟩ fun σ6 ha6 hO6 ↦ ?_
    have hbd6 : ∀ s < lv.logCols, LoadHolds rd (σ6 (.n 4)) (lvl * ligColsCap + s) (D s) := by
      intro s hs
      rw [ha6 4 (by omega), ha5 4 (by omega), ha4 4 (by omega), ha3 4 (by omega), ha2 4 (by omega),
        ha1 4 (by omega), g4]
      exact hD s hs
    refine BlkF.thenE (k1 := e0.2.2) (by omega) (by omega)
      ⟨_, osResQuery_complete (C := C) (rd := rd) (pos := k) (bd := 4) (row := lvl * ligColsCap)
        (vo := lv.vanish) (n := lv.logCols) (k := k + 1) (D := D) σ6 hml (by omega) (by omega)
        (by omega) hbd6⟩ fun σ7 ha7 hO7 ↦ ?_
    have hR0 : σ7 (.n e0.2.1) = residualProd (osVals lv.vanish lv.logCols) p0 D lv.logCols := by
      rw [hO7.1, hO6.1]
    refine BlkF.thenE (k1 := e0.2.2 + 1) (by omega) (by omega)
      ⟨_, load_complete (C := C) (rd := rd) (k := e0.2.2) (p := pp.2.2) (off := 1) σ7 (by omega)
        (by rw [ha7 _ (by omega), ePP σ6 ha6]; exact hp1)⟩ fun σ8 ha8 hO8 ↦ ?_
    have hbd8 : ∀ s < lv.logCols, LoadHolds rd (σ8 (.n 4)) (lvl * ligColsCap + s) (D s) := by
      intro s hs
      rw [ha8 4 (by omega), ha7 4 (by omega)]
      exact hbd6 s hs
    refine BlkF.thenE (k1 := r) (by omega) (by omega)
      ⟨_, osResQuery_complete (C := C) (rd := rd) (pos := e0.2.2) (bd := 4) (row := lvl * ligColsCap)
        (vo := lv.vanish) (n := lv.logCols) (k := e0.2.2 + 1) (D := D) σ8 hml (by omega) (by omega)
        (by omega) hbd8⟩ fun σ9 ha9 hO9 ↦ ?_
    have hR1 : σ9 (.n e1.2.1) = residualProd (osVals lv.vanish lv.logCols) p1 D lv.logCols := by
      rw [hO9.1, hO8.1]
    -- everything below `r` from `σ0`'s parameters
    have hpar : ∀ i < 6, σ9 (.n i) = σ0 (.n i) := fun i hi ↦ by
      rw [ha9 i (by omega), ha8 i (by omega), ha7 i (by omega), ha6 i (by omega), ha5 i (by omega),
        ha4 i (by omega), ha3 i (by omega), ha2 i (by omega), ha1 i (by omega)]
    have hWP : σ9 (.n wp.2.2) = qw * gen ^ (lvl * c.maxQ) * x ^ 2 := by
      rw [ha9 _ (by omega), ha8 _ (by omega), ha7 _ (by omega), ha6 _ (by omega), hO5.1, sq]
    have hE0 : σ9 (.n e0.2.1) = residualProd (osVals lv.vanish lv.logCols) p0 D lv.logCols := by
      rw [ha9 _ (by omega), ha8 _ (by omega), hR0]
    set R0 := residualProd (osVals lv.vanish lv.logCols) p0 D lv.logCols
    set R1 := residualProd (osVals lv.vanish lv.logCols) p1 D lv.logCols
    refine BlkF.thenE (k1 := r + 9) (by omega) (by omega) (OutA := fun _ ↦ True)
      ⟨fun i ↦ [acc * x, a, w0, w0 * R0, a + w0 * R0, w1, w1 * R1, a + w0 * R0 + w1 * R1,
        acc * x].getD (i - r) 0, ?_⟩ fun σ10 ha10 _ ↦
        ⟨fun i ↦ [word 2 0 0, x * word 2 0 0, x * word 2 0 0 + N, word 2 0 0,
          x * word 2 0 0].getD (i - (r + 9)) 0, ?_⟩
    · intro σ' ha hv
      have V : ∀ j < 9, σ' (.n (r + j)) =
          [acc * x, a, w0, w0 * R0, a + w0 * R0, w1, w1 * R1, a + w0 * R0 + w1 * R1, acc * x].getD j 0 :=
        fun j hj ↦ by rw [hv _ (by omega) (by omega)]; simp only [Nat.add_sub_cancel_left]
      have v0 := V 0 (by omega); have v1 := V 1 (by omega); have v2 := V 2 (by omega)
      have v3 := V 3 (by omega); have v4 := V 4 (by omega); have v5 := V 5 (by omega)
      have v6 := V 6 (by omega); have v7 := V 7 (by omega); have v8 := V 8 (by omega)
      simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at v0 v1 v2 v3 v4 v5 v6 v7 v8
      have p0' : σ' (.n 0) = x := by rw [ha 0 (by omega), hpar 0 (by omega), g0]
      have p5' : σ' (.n 5) = acc := by rw [ha 5 (by omega), hpar 5 (by omega), g5]
      have w' : σ' (.n wp.2.2) = qw * gen ^ (lvl * c.maxQ) * x ^ 2 := by rw [ha _ (by omega), hWP]
      have e0' : σ' (.n e0.2.1) = R0 := by rw [ha _ (by omega), hE0]
      have e1' : σ' (.n e1.2.1) = R1 := by rw [ha _ o4b, hR1]
      refine ⟨?_, trivial⟩
      simp only [allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds]
      refine ⟨by rw [v0, p5', p0'], by rw [v0, v1]; exact ha0, by rw [w', v2]; exact hw0,
        by rw [v3, v2, e0'], by rw [v4, v1, v3], by rw [w', v5]; exact hw1, by rw [v6, v5, e1'],
        by rw [v7, v4, v6], by rw [v8, p5', p0'], by rw [v8, v7]; exact hout⟩
    · intro σ' ha hv
      have V : ∀ j < 5, σ' (.n (r + 9 + j)) =
          [word 2 0 0, x * word 2 0 0, x * word 2 0 0 + N, word 2 0 0, x * word 2 0 0].getD j 0 :=
        fun j hj ↦ by rw [hv _ (by omega) (by omega)]; simp only [Nat.add_sub_cancel_left]
      have v0 := V 0 (by omega); have v1 := V 1 (by omega); have v2 := V 2 (by omega)
      have v3 := V 3 (by omega); have v4 := V 4 (by omega)
      simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at v0 v1 v2 v3 v4
      have p0' : σ' (.n 0) = x := by
        rw [ha 0 (by omega), ha10 0 (by omega), hpar 0 (by omega), g0]
      have p1' : σ' (.n 1) = N := by
        rw [ha 1 (by omega), ha10 1 (by omega), hpar 1 (by omega), g1]
      refine ⟨?_, trivial⟩
      simp only [osLoopTailA, allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds]
      exact ⟨v0, by rw [v1, p0', v0], by rw [v2, v1, p1'], v3, by rw [v4, p0', v3]⟩
  obtain ⟨f, hf⟩ := hB
  set σ := fill σ0 6 (r + 9 + 5) f
  have hA := (hf σ (agree_fill _ _ _ _) (range_fill _ _ _ _)).1
  have hlow : ∀ i < 6, σ (.n i) = σ0 (.n i) := fun i hi ↦ fill_lt hi
  obtain ⟨t2, t4⟩ := osLoopTailA_val (allOk_append.mp hA).2
  refine ⟨σ, ?_, hA, ?_, ?_⟩
  · simp only [osParams, List.range_succ, List.range_zero, List.map_cons, List.map_nil,
      List.nil_append, List.cons_append, hlow 0 (by omega), hlow 1 (by omega), hlow 2 (by omega),
      hlow 3 (by omega), hlow 4 (by omega), hlow 5 (by omega), g0, g1, g2, g3, g4, g5]
  · rw [t2, hlow 0 (by omega), hlow 1 (by omega), g0, g1]
  · simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.nil_append,
      List.cons_append, Nat.zero_add, t4, hlow 0 (by omega), hlow 1 (by omega), hlow 2 (by omega),
      hlow 3 (by omega), hlow 4 (by omega), hlow 5 (by omega), g0, g1, g2, g3, g4, g5]

/-- **The residual loop, honestly**: entered from `1` with the bound `g^n`, `0 < n`, on a memory
where every iteration's meaning holds. -/
theorem resLoop_rel {name : String} {fn : Fn} (hf : coreProgram.find? name = some fn)
    (c : OsCfg) (lvl : ℕ) (lv : OsLv) (hps : fn.params = osParams 6)
    (hb : fn.body = resLoopBody c lvl lv name) (hml : 1 ≤ lv.logCols)
    (hpo : lv.posOff < u128Bound) (hwo : lvl * c.maxQ < u128Bound) {D : ℕ → E} {n : ℕ}
    (hn0 : 0 < n) (qpos qw bd acc : E)
    (hD : ∀ s < lv.logCols, LoadHolds rd bd (lvl * ligColsCap + s) (D s))
    (hit : ∀ j < n, ResIter rd D lv.vanish lv.logCols lv.posOff (lvl * c.maxQ) qpos qw acc (gen ^ j)) :
    IsInK (1 + gen ^ n) ∧ (1 + gen ^ n ≠ 0 →
      coreProgram.Rel rd name [1, gen ^ n, qpos, qw, bd, acc] []) := by
  rw [resLoopBody_split] at hb
  refine loop_complete (rest := [qpos, qw, bd, acc]) hf (resLoopA_flat c lvl lv) hb hn0 rfl
    fun j hj ↦ ?_
  obtain ⟨σ, hp, hA, hg, ha⟩ := resIter_complete (C := coreProgram.Rel rd) c lvl lv hml hpo hwo
    (gen ^ j) (gen ^ n) qpos qw bd acc hD (hit j hj)
  exact ⟨σ, by rw [hps]; exact hp, hA, hg, ha⟩

/-! ## Placed -/

theorem pureList_eq_all (S : List String) : ∀ l : List Stmt, Stmt.pureList S l = l.all (Stmt.pure S)
  | [] => rfl
  | s :: l => by simp [Stmt.pureList, pureList_eq_all S l]

theorem osResQ_mem (pos bd row vo : ℕ) : ∀ (n t pe k : ℕ), ∀ s ∈ (osResQ pos bd row vo n t pe k).1,
    ∃ a, s = .atom a ∧ atomUnplaced a = true
  | 0, _, _, _, s, hs => by simp [osResQ] at hs
  | n + 1, t, pe, k, s, hs => by
    simp only [osResQ, List.cons_append, List.mem_cons, List.nil_append] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | hs
    all_goals first
      | exact ⟨_, rfl, rfl⟩
      | exact osResQ_mem pos bd row vo n (t + 1) (k + 5) (k + 6) s hs

theorem resLoopBody_pure (c : OsCfg) (lvl : ℕ) (lv : OsLv) (name : String) :
    Stmt.pureList [name] (resLoopBody c lvl lv name) = true := by
  have hq : ∀ pos bd row vo n k, ∀ s ∈ (osResQuery pos bd row vo n k).1, Stmt.pure [name] s = true := by
    intro pos bd row vo n k s hs
    simp only [osResQuery, List.cons_append, List.nil_append, List.mem_cons] at hs
    rcases hs with rfl | rfl | hs
    · rfl
    · rfl
    · obtain ⟨a, rfl, ha⟩ := osResQ_mem pos bd row vo _ _ _ _ s hs; exact ha
  have hm : ∀ b o k, ∀ s ∈ (osMat b o k).1, Stmt.pure [name] s = true := by
    intro b o k s hs
    rcases osMat_mem b o k s hs with ⟨d, c, rfl⟩ | ⟨d, a, b, rfl⟩ <;> rfl
  rw [pureList_eq_all, resLoopBody_split]
  simp only [resLoopA, osLoopTailA, List.all_append, List.all_cons, List.all_nil, Bool.and_true,
    List.all_eq_true.mpr (hm _ _ _), List.all_eq_true.mpr (hq _ _ _ _ _ _)]
  simp [Stmt.pure, atomUnplaced]

/-- **The residual loop helper is pure.** -/
theorem resLoop_pureIn {name : String} {fn : Fn} (hf : coreProgram.find? name = some fn)
    (c : OsCfg) (lvl : ℕ) (lv : OsLv) (hb : fn.body = resLoopBody c lvl lv name) :
    coreProgram.PureIn [name] := by
  intro g hg fn' hf'
  rw [List.mem_singleton] at hg
  subst hg
  rw [hf] at hf'
  cases hf'
  rw [hb]
  exact resLoopBody_pure c lvl lv g

/-- **The residual loop, placed**: on every memory holding the caller's words `Lin` where the
row's words and every iteration's meaning hold, entered behind a nonzero guard. -/
theorem resLoop_completeAtD (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) {name : String}
    {fn : Fn} (hf : coreProgram.find? name = some fn) (c : OsCfg) (lvl : ℕ) (lv : OsLv)
    (hps : fn.params = osParams 6) (hb : fn.body = resLoopBody c lvl lv name)
    (hml : 1 ≤ lv.logCols) (hpo : lv.posOff < u128Bound) (hwo : lvl * c.maxQ < u128Bound)
    {D : ℕ → E} {n : ℕ} (hn0 : 0 < n) (hne : 1 + gen ^ n ≠ 0) {qpos qw bd acc : E} {Lin : Layout}
    (hmem : ∀ rd, MemL rd Lin → (∀ s < lv.logCols, LoadHolds rd bd (lvl * ligColsCap + s) (D s)) ∧
      ∀ j < n, ResIter rd D lv.vanish lv.logCols lv.posOff (lvl * c.maxQ) qpos qw acc (gen ^ j)) :
    CompleteAtD fs cert k name Lin [1, gen ^ n, qpos, qw, bd, acc] (Returns []) :=
  completeAt_of_rel_pureD (resLoop_pureIn hf c lvl lv hb) (List.mem_singleton_self name)
    (fun rd hm ↦ (resLoop_rel hf c lvl lv hps hb hml hpo hwo hn0 qpos qw bd acc (hmem rd hm).1
      (hmem rd hm).2).2 hne) k

end
end LeanVM.Guest.B1
