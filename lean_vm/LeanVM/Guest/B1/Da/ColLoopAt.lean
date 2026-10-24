/-
  LeanVM.Guest.B1.Da.ColLoopAt

  `da_verify`'s column loops (`__loop20`, `__loop21`) in the uniform placed form: the rest of the
  loop after the frame, the column after it.
-/

module

public import LeanVM.Guest.B1.Da.AtBase
public import LeanVM.Guest.B1.Da.VerifyLoopsComplete

/-!
# The column loops, placed

A column loop at the counter `g^k` calls column `k`, then itself at `g^(k+1)` unless `k + 1` is
its end `m`. A loop helper's tail sits right after its frame and its other callees after the tail
(`relAtIn_of_walk_loop`). `colLoop_completeAt`: when every column `a ≤ k < m` is `CompleteAtD`
reading `Lin`, so is the loop from every such `k`, by induction from the end.
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Fwd
open LeanVM.Guest.B1 (CompleteAtD Returns DisjL Within disj_append within_append)
open LeanVM.Guest.B1.Main (Layout MemL RegionL memL_append)

@[expose] public section

/-- A column loop's statements before its `ret`. -/
def colLoopPre (col loop : String) (endLo : ℕ) : List Stmt :=
  [.call col ((List.range 9).map V.n) [],
    .atom (.const (.n 9) (word 2 0 0)), .atom (.mul (.n 10) (.n 0) (.n 9)),
    .atom (.const (.n 11) (word endLo 0 0)), .atom (.add (.n 12) (.n 10) (.n 11)),
    .atom (.const (.n 13) (word 2 0 0)), .atom (.mul (.n 14) (.n 0) (.n 13)),
    .callIf (.n 12) loop (.n 14 :: (List.range 8).map fun k => V.n (k + 1))]

theorem colLoopBody_split (col loop : String) (endLo : ℕ) :
    colLoopBody col loop endLo = colLoopPre col loop endLo ++ [.ret []] := rfl

theorem colLoopPre_straight (col loop : String) (endLo : ℕ) :
    (colLoopPre col loop endLo).all Main.Stmt.straight = true := rfl

theorem fn_name_of_find {f : String} {fn : Fn} (h : coreProgram.find? f = some fn) : fn.name = f := by
  have := List.find?_some h
  simpa using this

/-- A column loop's valuation at the counter `g^k`. -/
def clσ (k endLo : ℕ) (p1 p2 p3 p4 p5 p6 p7 p8 : E) : Val :=
  Val.ofArgs [gen ^ k, p1, p2, p3, p4, p5, p6, p7, p8, word 2 0 0, gen ^ k * word 2 0 0,
    word endLo 0 0, gen ^ k * word 2 0 0 + word endLo 0 0, word 2 0 0, gen ^ k * word 2 0 0]

variable (fs : String → ℕ) (cert : String → V → ℕ)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
/-- **One step of a column loop, placed**: column `k` and the rest of the loop. -/
theorem colLoop_stepAt {f col : String} {j endLo : ℕ} (hj : j < coreProgram.length)
    (hok : (colLoopOk (coreProgram.getD j default) col f endLo &&
      decide (coreProgram.indexOf? f = some j)) = true)
    {p1 p2 p3 p4 p5 p6 p7 p8 : E} {Lin : Layout} {k m : ℕ} (hw : word endLo 0 0 = gen ^ m)
    (hkm : k + 1 ≤ m) (hm : m < 2 ^ 34)
    (hcol : CompleteAtD fs cert 16 col Lin [gen ^ k, p1, p2, p3, p4, p5, p6, p7, p8] (Returns []))
    (htail : k + 1 < m →
      CompleteAtD fs cert 16 f Lin [gen ^ (k + 1), p1, p2, p3, p4, p5, p6, p7, p8] (Returns [])) :
    CompleteAtD fs cert 16 f Lin [gen ^ k, p1, p2, p3, p4, p5, p6, p7, p8] (Returns []) := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hok, hidx⟩ := hok
  have hf := find_of_idx hidx hj
  unfold colLoopOk at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hparams, hbody⟩ := hok
  have hbody' := stmtsEqb_sound hbody
  have hloop : coreProgram.loop f = true := by
    rw [Program.loop_of_find? hf, Fn.loop, hbody', fn_name_of_find hf]
    simp [colLoopBody]
  intro fp
  -- the rest of the loop
  obtain ⟨nt, Lt, hWt, hDt, hRt⟩ : ∃ nt Lt, Within Lt (fp + fs f) nt ∧ DisjL Lt ∧
      ∀ rd, B1.LowDef 16 rd → MemL rd (Lt ++ Lin) →
        if decide (k + 1 ≠ m) = true then
          RelAtIn coreProgram fs cert rd (RegionL Lin) (RegionL []) (fp + fs f) nt f
            [gen ^ (k + 1), p1, p2, p3, p4, p5, p6, p7, p8] []
        else nt = fs f := by
    by_cases hlast : k + 1 = m
    · exact ⟨fs f, [], fun q hq => by simp at hq, List.Pairwise.nil, fun _ _ _ => by
        simp [hlast]⟩
    · obtain ⟨nt, Lt, rt, Lot, ⟨rfl, rfl⟩, hW, hD, hR⟩ := htail (by omega) (fp + fs f)
      refine ⟨nt, Lt, by simpa using hW, by simpa using hD, fun rd hl hm => ?_⟩
      simp only [ne_eq, hlast, not_false_eq_true, decide_true, ↓reduceIte]
      exact hR rd hl (by simpa using hm)
  -- the column
  obtain ⟨nc, Lc, rc, Loc, ⟨rfl, rfl⟩, hWc, hDc, hRc⟩ := hcol (fp + fs f + nt)
  simp only [List.nil_append] at hWc hDc hRc
  refine ⟨fs f + nt + nc, Lt ++ Lc, [], [], ⟨rfl, rfl⟩, ?_,
    by simpa using disj_append hDt hDc hWt hWc le_rfl, fun rd hlow hm => ?_⟩
  · rw [List.nil_append, within_append]
    exact ⟨hWt.mono (by omega) (by omega), hWc.mono (by omega) (by omega)⟩
  simp only [List.nil_append] at hm
  obtain ⟨hm1, hLin⟩ := memL_append.mp hm
  obtain ⟨hmt, hmc⟩ := memL_append.mp hm1
  have ht := hRt rd hlow (memL_append.mpr ⟨hmt, hLin⟩)
  have hc := hRc rd hlow (memL_append.mpr ⟨hmc, hLin⟩)
  -- the path
  set σ := clσ k endLo p1 p2 p3 p4 p5 p6 p7 p8 with hσ
  have hw' := Main.walk_straight σ [] (colLoopPre col f endLo) (colLoopPre_straight col f endLo)
  rw [← colLoopBody_split, ← hbody'] at hw'
  obtain ⟨hpd, hpa, hpad, hpc⟩ := Main.straight_parts σ _ (colLoopPre_straight col f endLo)
  have h12 : σ (.n 12) = gen ^ (k + 1) + gen ^ m := by
    show gen ^ k * word 2 0 0 + word endLo 0 0 = _
    rw [word_gen, gen_pow_mul_gen, hw]
  have htk : decide (σ (.n 12) ≠ 0) = decide (k + 1 ≠ m) := by
    rw [h12]
    refine decide_eq_decide.mpr ⟨fun h he => h (by rw [he]; exact e_add_eq_zero_iff.mpr rfl),
      fun h he => h ?_⟩
    exact gen_pow_inj' (by omega) (by omega) (e_add_eq_zero_iff.mp he)
  have hcalls : calls ((colLoopPre col f endLo).flatMap (Main.slEvs σ)) =
      [⟨col, (List.range 9).map V.n, [], true⟩] ++
        [⟨f, .n 14 :: (List.range 8).map fun k => V.n (k + 1), [], decide (k + 1 ≠ m)⟩] := by
    rw [hpc, show (colLoopPre col f endLo).filterMap Main.Stmt.callS =
      [(none, col, (List.range 9).map V.n, []),
        (some (.n 12), f, .n 14 :: (List.range 8).map fun k => V.n (k + 1), [])] from rfl]
    simp only [List.map_cons, List.map_nil, Main.mkCall, htk, List.cons_append, List.nil_append]
  have hal : allocs σ ((colLoopPre col f endLo).flatMap (Main.slEvs σ)) = [] := by
    rw [hpa, show (colLoopPre col f endLo).filterMap Main.Stmt.allocSz = [] from rfl]; rfl
  have hev : ∀ e ∈ (colLoopPre col f endLo).flatMap (Main.slEvs σ), e.Holds rd σ := by
    refine slEvs_holds fun s hs => ?_
    simp only [colLoopPre, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp only [SlOk, Atom.Holds, hσ, clσ, ofArgs_n, List.getD_cons_succ,
      List.getD_cons_zero]
    rw [word_gen, gen_pow_mul_gen, hw]
    exact gen_pow_add_isInK _ _
  have hargs : (.n 14 :: (List.range 8).map fun k => V.n (k + 1)).map σ =
      [gen ^ (k + 1), p1, p2, p3, p4, p5, p6, p7, p8] := by
    show [gen ^ k * word 2 0 0, p1, p2, p3, p4, p5, p6, p7, p8] = _
    rw [word_gen, gen_pow_mul_gen]
  have h := relAtIn_of_walk_loop (P := coreProgram) (fs := fs) (cert := cert) (σ := σ) (rd := rd)
    (R := RegionL Lin) (D := RegionL []) (Dk := fun _ => False) (Rt := RegionL Lin)
    (Dt := RegionL []) (fp := fp) (m := nt) (N := nc)
    (args := [gen ^ k, p1, p2, p3, p4, p5, p6, p7, p8]) coreProgram_wf hf hloop
    (by rw [hparams]; rfl) hw' rfl hev hcalls
    (by
      by_cases hlast : k + 1 = m
      · simpa [hlast] using ht
      · simp only [ne_eq, hlast, not_false_eq_true, decide_true, ↓reduceIte] at ht ⊢
        rw [hargs]; exact ht)
    (by
      rw [hal, hpd, show (colLoopPre col f endLo).filterMap Main.Stmt.allocSz = [] from rfl]; rfl)
    (fun q hq => by
      rw [hpad, show (colLoopPre col f endLo).filterMap Main.Stmt.addrS = [] from rfl] at hq
      simp at hq)
    (by
      rw [hal]
      refine ⟨nc, 0, RegionL Lin, fun _ => False, rfl, fun i hi => Or.inl (Or.inl hi), ?_,
        ⟨rfl, fun i hi => hi.elim⟩⟩
      simp only [ite_true, List.sum_nil, Nat.add_zero]
      exact B1.relAtIn_dmono hc fun _ h => h.elim)
    (fun i hi => Or.inl hi)
    (fun A hA => by
      rw [B1.loadAddrs_straight σ _ (colLoopPre_straight col f endLo),
        show (colLoopPre col f endLo).filterMap B1.Stmt.loadS = [] from rfl] at hA
      simp at hA)
    (fun i hi => by obtain ⟨q, hq, -⟩ := hi; simp at hq)
  rw [hal] at h
  simp only [List.sum_nil, Nat.add_zero] at h
  exact h

/-- **A column loop is complete, placed**, from every counter `a ≤ k < m`, when its columns are. -/
theorem colLoop_completeAt {f col : String} {j endLo : ℕ} (hj : j < coreProgram.length)
    (hok : (colLoopOk (coreProgram.getD j default) col f endLo &&
      decide (coreProgram.indexOf? f = some j)) = true)
    {p1 p2 p3 p4 p5 p6 p7 p8 : E} {Lin : Layout} {a m : ℕ} (hw : word endLo 0 0 = gen ^ m)
    (hm : m < 2 ^ 34)
    (hcol : ∀ k, a ≤ k → k < m →
      CompleteAtD fs cert 16 col Lin [gen ^ k, p1, p2, p3, p4, p5, p6, p7, p8] (Returns [])) :
    ∀ k, a ≤ k → k < m →
      CompleteAtD fs cert 16 f Lin [gen ^ k, p1, p2, p3, p4, p5, p6, p7, p8] (Returns []) := by
  have key : ∀ t k, a ≤ k → k + 1 + t = m →
      CompleteAtD fs cert 16 f Lin [gen ^ k, p1, p2, p3, p4, p5, p6, p7, p8] (Returns []) := by
    intro t
    induction t with
    | zero => intro k hak hk
              exact colLoop_stepAt fs cert hj hok hw (by omega) hm (hcol k hak (by omega))
                fun h => absurd h (by omega)
    | succ t ih => intro k hak hk
                   exact colLoop_stepAt fs cert hj hok hw (by omega) hm (hcol k hak (by omega))
                     fun _ => ih (k + 1) (by omega) (by omega)
  intro k hak hk
  exact key (m - k - 1) k hak (by omega)

end
end LeanVM.Guest.B1.Da
