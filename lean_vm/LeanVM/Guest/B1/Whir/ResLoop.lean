/-
  LeanVM.Guest.B1.Whir.ResLoop

  The residual loop of `open_stacked` (two queries' `residual_query` an iteration), soundly.
-/

module

public import LeanVM.Guest.B1.Whir.Loops
public import LeanVM.Guest.B1.Whir.ResQuery

/-!
# The residual loop (G:1573-1583)

At `x = g^j` the iteration reads the positions `2j, 2j + 1` at `qpos·g^po·x²` and their
weights at `qw·g^wo·x²`, evaluates both queries' `residual_query` on the level's `basis_d` row,
and stores `acc[j + 1] = acc[j] + w₀·R(p₀) + w₁·R(p₁)` (`ResIter`; `resLoop_sound`).
`resChain`: from `acc[0] = 0`, `acc[j] = Σ_{i < 2j} w_i·R(p_i)`.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader}

/-- **One iteration of the residual loop at `x`**, the row's words `D`: two positions and weights
read, `acc·x` advanced by both weighted residuals. -/
def ResIter (rd : Reader) (D : ℕ → E) (vo ml po wo : ℕ) (qpos qw acc x : E) : Prop :=
  ∃ p0 p1 w0 w1 a : E, LoadHolds rd (qpos * gen ^ po * x ^ 2) 0 p0 ∧
    LoadHolds rd (qpos * gen ^ po * x ^ 2) 1 p1 ∧ LoadHolds rd (qw * gen ^ wo * x ^ 2) 0 w0 ∧
    LoadHolds rd (qw * gen ^ wo * x ^ 2) 1 w1 ∧ LoadHolds rd (acc * x) 0 a ∧
    LoadHolds rd (acc * x) 1 (a + w0 * residualProd (osVals vo ml) p0 D ml +
      w1 * residualProd (osVals vo ml) p1 D ml)

/-- The residual loop's body before its tail. -/
def resLoopA (c : OsCfg) (lvl : ℕ) (lv : OsLv) : List Stmt :=
  let pp := osMat 2 lv.posOff 7
  let wp := osMat 3 (lvl * c.maxQ) (pp.2.2 + 1)
  let k := wp.2.2 + 1
  let e0 := osResQuery k 4 (lvl * ligColsCap) lv.vanish lv.logCols (k + 1)
  let e1 := osResQuery e0.2.2 4 (lvl * ligColsCap) lv.vanish lv.logCols (e0.2.2 + 1)
  let r := e1.2.2
  [.atom (.mul (.n 6) (.n 0) (.n 0))] ++ pp.1 ++ [.atom (.mul (.n pp.2.2) (.n pp.2.1) (.n 6))] ++
    wp.1 ++ [.atom (.mul (.n wp.2.2) (.n wp.2.1) (.n 6))] ++
    [.atom (.load (.n k) (.n pp.2.2) 0)] ++ e0.1 ++
    [.atom (.load (.n e0.2.2) (.n pp.2.2) 1)] ++ e1.1 ++
    [.atom (.mul (.n r) (.n 5) (.n 0)), .atom (.load (.n (r + 1)) (.n r) 0),
      .atom (.load (.n (r + 2)) (.n wp.2.2) 0), .atom (.mul (.n (r + 3)) (.n (r + 2)) (.n e0.2.1)),
      .atom (.add (.n (r + 4)) (.n (r + 1)) (.n (r + 3))), .atom (.load (.n (r + 5)) (.n wp.2.2) 1),
      .atom (.mul (.n (r + 6)) (.n (r + 5)) (.n e1.2.1)), .atom (.add (.n (r + 7)) (.n (r + 4)) (.n (r + 6))),
      .atom (.mul (.n (r + 8)) (.n 5) (.n 0)), .atom (.load (.n (r + 7)) (.n (r + 8)) 1)]

/-- The tail's first value. -/
def resLoopR (c : OsCfg) (lvl : ℕ) (lv : OsLv) : ℕ :=
  (osResQuery (osResQuery ((osMat 3 (lvl * c.maxQ) ((osMat 2 lv.posOff 7).2.2 + 1)).2.2 + 1) 4
    (lvl * ligColsCap) lv.vanish lv.logCols
    ((osMat 3 (lvl * c.maxQ) ((osMat 2 lv.posOff 7).2.2 + 1)).2.2 + 1 + 1)).2.2 4
    (lvl * ligColsCap) lv.vanish lv.logCols
    ((osResQuery ((osMat 3 (lvl * c.maxQ) ((osMat 2 lv.posOff 7).2.2 + 1)).2.2 + 1) 4
      (lvl * ligColsCap) lv.vanish lv.logCols
      ((osMat 3 (lvl * c.maxQ) ((osMat 2 lv.posOff 7).2.2 + 1)).2.2 + 1 + 1)).2.2 + 1)).2.2 + 9

theorem resLoopBody_split (c : OsCfg) (lvl : ℕ) (lv : OsLv) (name : String) :
    resLoopBody c lvl lv name = (resLoopA c lvl lv ++ osLoopTailA (resLoopR c lvl lv)) ++
      [.callIf (.n (resLoopR c lvl lv + 2)) name
        (.n (resLoopR c lvl lv + 4) :: (List.range (6 - 1)).map fun i ↦ .n (i + 1)), .ret []] := by
  simp only [resLoopBody, resLoopA, resLoopR, osLoopTail_split, List.append_assoc]

theorem osResQ_flat (pos bd row vo : ℕ) : ∀ n t pe k,
    (osResQ pos bd row vo n t pe k).1.all Stmt.flat = true
  | 0, _, _, _ => rfl
  | n + 1, t, pe, k => by
    simp [osResQ, Stmt.flat, osResQ_flat pos bd row vo n (t + 1) (k + 5) (k + 6)]

theorem osResQuery_flat (pos bd row vo n k : ℕ) :
    (osResQuery pos bd row vo n k).1.all Stmt.flat = true := by
  simp [osResQuery, Stmt.flat, osResQ_flat]

theorem resLoopA_flat (c : OsCfg) (lvl : ℕ) (lv : OsLv) :
    (resLoopA c lvl lv ++ osLoopTailA (resLoopR c lvl lv)).all Stmt.flat = true := by
  have hm : ∀ b o k, (osMat b o k).1.all Stmt.flat = true := by
    intro b o k; unfold osMat; split_ifs <;> rfl
  simp [resLoopA, osLoopTailA, hm, osResQuery_flat, Stmt.flat]

/-- **The residual loop's iteration**: from its body's atoms at `x`, the iteration's meaning, the
guard `x·g + N` and the next call's arguments. -/
theorem resLoop_step (c : OsCfg) (lvl : ℕ) (lv : OsLv) (hml : 1 ≤ lv.logCols)
    (hpo : lv.posOff < u128Bound) (hwo : lvl * c.maxQ < u128Bound) {D : ℕ → E}
    (σ : Val) (x N qpos qw bd acc : E) (hp : (osParams 6).map σ = [x, N, qpos, qw, bd, acc])
    (hD : ∀ s < lv.logCols, LoadHolds rd bd (lvl * ligColsCap + s) (D s))
    {C : CallRel} (hA : AllOk C rd σ (resLoopA c lvl lv ++ osLoopTailA (resLoopR c lvl lv))) :
    ResIter rd D lv.vanish lv.logCols lv.posOff (lvl * c.maxQ) qpos qw acc x ∧
      σ (.n (resLoopR c lvl lv + 2)) = x * gen + N ∧
      (.n (resLoopR c lvl lv + 4) :: (List.range (6 - 1)).map fun i ↦ V.n (i + 1)).map σ =
        x * gen :: [N, qpos, qw, bd, acc] := by
  simp only [osParams, List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.nil_append, List.cons.injEq, and_true, List.cons_append] at hp
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hp
  rw [allOk_append] at hA
  obtain ⟨hA, hT⟩ := hA
  obtain ⟨t2, t4⟩ := osLoopTailA_val hT
  refine ⟨?_, by rw [t2, h0, h1], ?_⟩
  · unfold resLoopA at hA
    set pp := osMat 2 lv.posOff 7
    set wp := osMat 3 (lvl * c.maxQ) (pp.2.2 + 1)
    set k := wp.2.2 + 1
    set e0 := osResQuery k 4 (lvl * ligColsCap) lv.vanish lv.logCols (k + 1)
    set e1 := osResQuery e0.2.2 4 (lvl * ligColsCap) lv.vanish lv.logCols (e0.2.2 + 1)
    set r := e1.2.2
    simp only [allOk_append, allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds, and_assoc] at hA
    obtain ⟨m6, hpp, mpp, hwp, mwp, lk, he0, le0, he1, mr, l1, l2, m3, a4, l5, m6', a7, m8, s7⟩ := hA
    have hD' : ∀ s < lv.logCols, LoadHolds rd (σ (.n 4)) (lvl * ligColsCap + s) (D s) := by
      rw [h4]; exact hD
    have v0 := osResQuery_val hml hD' he0
    have v1 := osResQuery_val hml hD' he1
    have hP : σ (.n pp.2.2) = qpos * gen ^ lv.posOff * x ^ 2 := by
      rw [mpp, osMat_val hpo hpp, m6, h0, h2, sq]
    have hW : σ (.n wp.2.2) = qw * gen ^ (lvl * c.maxQ) * x ^ 2 := by
      rw [mwp, osMat_val hwo hwp, m6, h0, h3, sq]
    have hR : σ (.n r) = acc * x := by rw [mr, h5, h0]
    have hR8 : σ (.n (r + 8)) = acc * x := by rw [m8, h5, h0]
    rw [hP] at lk le0
    rw [hW] at l2 l5
    rw [hR] at l1
    rw [hR8] at s7
    refine ⟨_, _, _, _, _, lk, le0, l2, l5, l1, ?_⟩
    rw [a7, a4, m3, m6', v0, v1] at s7
    exact s7
  · simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.nil_append,
      List.cons_append, Nat.zero_add, t4, h0, h1, h2, h3, h4, h5]

/-- **The residual loop, soundly**: entered from `1` with the bound `g^n`, `0 < n < ord g`, the
iteration's meaning holds at every `g^j`, `j < n`. -/
theorem resLoop_sound {name : String} {fn : Fn} (hf : coreProgram.find? name = some fn)
    (c : OsCfg) (lvl : ℕ) (lv : OsLv) (hps : fn.params = osParams 6)
    (hb : fn.body = resLoopBody c lvl lv name) (hml : 1 ≤ lv.logCols)
    (hpo : lv.posOff < u128Bound) (hwo : lvl * c.maxQ < u128Bound) {D : ℕ → E}
    {n : ℕ} (hn0 : 0 < n) (hn : n < ordG) (qpos qw bd acc : E)
    (hD : ∀ s < lv.logCols, LoadHolds rd bd (lvl * ligColsCap + s) (D s))
    (hg : 1 + gen ^ n ≠ 0 → coreProgram.Rel rd name [1, gen ^ n, qpos, qw, bd, acc] []) :
    ∀ j < n, ResIter rd D lv.vanish lv.logCols lv.posOff (lvl * c.maxQ) qpos qw acc (gen ^ j) := by
  rw [resLoopBody_split] at hb
  refine loop_guarded (rest := [qpos, qw, bd, acc]) hn0 hn rfl
    (loop_sound_flat hf (resLoopA_flat c lvl lv) hb ?_) hg
  intro σ x hp hA
  rw [hps] at hp
  exact resLoop_step c lvl lv hml hpo hwo σ x (gen ^ n) qpos qw bd acc hp hD hA

/-- **The accumulator**: from `acc[0] = 0`, after `j ≤ n` iterations
`acc[j] = Σ_{i < 2j} W_i·R(P_i)`, the positions `P` and weights `W` in memory. -/
theorem resChain {D : ℕ → E} {vo ml po wo : ℕ} {qpos qw acc : E} {n : ℕ} {P W : ℕ → E}
    (hP : ∀ i < 2 * n, LoadHolds rd qpos (po + i) (P i))
    (hW : ∀ i < 2 * n, LoadHolds rd qw (wo + i) (W i))
    (h0 : LoadHolds rd acc 0 0)
    (hit : ∀ j < n, ResIter rd D vo ml po wo qpos qw acc (gen ^ j)) :
    ∀ j ≤ n, LoadHolds rd acc j
      (∑ i ∈ Finset.range (2 * j), W i * residualProd (osVals vo ml) (P i) D ml) := by
  intro j
  induction j with
  | zero => intro _; simpa using h0
  | succ j ih =>
    intro hj
    obtain ⟨p0, p1, w0, w1, a, lp0, lp1, lw0, lw1, la, ls⟩ := hit j (by omega)
    have hx : (gen ^ j) ^ 2 = gen ^ (2 * j) := by rw [← pow_mul, Nat.mul_comm]
    rw [hx, mul_assoc, ← pow_add, loadHolds_mul_gen_pow] at lp0 lp1 lw0 lw1
    rw [loadHolds_mul_gen_pow] at la ls
    have ep0 := loadHolds_unique lp0 (hP (2 * j) (by omega))
    rw [Nat.add_assoc] at lp1 lw1
    have ep1 := loadHolds_unique lp1 (hP (2 * j + 1) (by omega))
    have ew0 := loadHolds_unique lw0 (hW (2 * j) (by omega))
    have ew1 := loadHolds_unique lw1 (hW (2 * j + 1) (by omega))
    have ea := loadHolds_unique la (by simpa using ih (by omega))
    rw [ep0, ep1, ew0, ew1, ea] at ls
    rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ]
    exact ls

end
end LeanVM.Guest.B1.Whir
