/-
  LeanVM.Guest.B1.Da.ColLoopAtT

  `da_verify`'s column loops (`__loop19`, `__loop20`) placed, by trees of their honest shape
  (`Budget.NodeHonest`): each iteration's node at its counter, its calls (the column, the rest of
  the loop), no `HeapBuf`.

  `da_verify` checks Benedikt Wagner's LeanDA witnesses (`Da.MatrixWitness.Opens`), as ported here.
-/

module

public import LeanVM.Guest.B1.Da.ColLoopAt
public import LeanVM.Guest.B1.Da.AtT

/-!
# The column loops, their honest shapes

`colLoopNH f col k m Tc Tt`: the loop's node at the counter `v0 = g^k`, its calls `colLoopCalls`
(column `k`, then the loop at `k + 1` when `k + 1 ≠ m`), no `HeapBuf`, the column's tree
satisfying `Tc` and the rest's `Tt`. `colFrom f col m Tc t k`: the `t` iterations from `k` (`False` at `0`: the last iteration's tail
call is not taken).
`colLoop_stepAtT`, `colLoop_completeAtT`: `colLoop_stepAt`, `colLoop_completeAt` (same proofs) by
such trees.
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Fwd
open LeanVM.Guest.Budget (NodeHonest)
open LeanVM.Guest.B1 (CompleteAtD CompleteAtDT Returns DisjL Within disj_append within_append)
open LeanVM.Guest.B1.Main (Layout MemL RegionL memL_append)

@[expose] public section

/-- A column loop's calls at the counter `g^k`. -/
def colLoopCalls (col f : String) (k m : ℕ) : List Call :=
  [⟨col, (List.range 9).map V.n, [], true⟩] ++
    [⟨f, .n 14 :: (List.range 8).map fun i => V.n (i + 1), [], decide (k + 1 ≠ m)⟩]

/-- **A column loop's iteration's honest shape.** -/
def colLoopNH (f col : String) (k m : ℕ) (Tc Tt : Tree → Prop) : Tree → Prop :=
  NodeHonest coreProgram f (fun σ => σ (.n 0) = gen ^ k) (fun _ => colLoopCalls col f k m)
    (fun _ => []) [Tc, Tt]

/-- **A column loop's `t` iterations from `k`**, each of its honest shape; none (`False`) past
the last, so the last iteration's tail call is not taken. -/
def colFrom (f col : String) (m : ℕ) (Tc : Tree → Prop) : ℕ → ℕ → Tree → Prop
  | 0, _ => fun _ => False
  | t + 1, k => colLoopNH f col k m Tc (colFrom f col m Tc t (k + 1))

variable (fs : String → ℕ) (cert : String → V → ℕ)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
/-- **One step of a column loop, placed, by a tree of its honest shape** (`colLoopNH`). -/
theorem colLoop_stepAtT {Tc Tt : Tree → Prop} {f col : String} {j endLo : ℕ} (hj : j < coreProgram.length)
    (hok : (colLoopOk (coreProgram.getD j default) col f endLo &&
      decide (coreProgram.indexOf? f = some j)) = true)
    {p1 p2 p3 p4 p5 p6 p7 p8 : E} {Lin : Layout} {k m : ℕ} (hw : word endLo 0 0 = gen ^ m)
    (hkm : k + 1 ≤ m) (hm : m < 2 ^ 34)
    (hcol : CompleteAtDT fs cert 16 col Lin [gen ^ k, p1, p2, p3, p4, p5, p6, p7, p8] (Returns []) Tc)
    (htail : k + 1 < m →
      CompleteAtDT fs cert 16 f Lin [gen ^ (k + 1), p1, p2, p3, p4, p5, p6, p7, p8] (Returns []) Tt) :
    CompleteAtDT fs cert 16 f Lin [gen ^ k, p1, p2, p3, p4, p5, p6, p7, p8] (Returns [])
      (colLoopNH f col k m Tc Tt) := by
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
          RelAtInT coreProgram fs cert rd (RegionL Lin) (RegionL []) (fp + fs f) nt f
            [gen ^ (k + 1), p1, p2, p3, p4, p5, p6, p7, p8] [] Tt
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
  have h := relAtInWT_of_walk_loop (P := coreProgram) (Ts := [Tc]) (Tt := Tt) (fs := fs) (cert := cert) (σ := σ) (rd := rd)
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
    rfl
    (by
      rw [hal]
      refine ⟨nc, 0, RegionL Lin, fun _ => False, rfl, fun i hi => Or.inl (Or.inl hi), ?_,
        ⟨rfl, fun i hi => hi.elim⟩⟩
      simp only [ite_true, List.sum_nil, Nat.add_zero]
      exact relAtInT_dmono hc fun _ h => h.elim)
    (fun i hi => Or.inl hi)
    (fun A hA => by
      rw [B1.loadAddrs_straight σ _ (colLoopPre_straight col f endLo),
        show (colLoopPre col f endLo).filterMap B1.Stmt.loadS = [] from rfl] at hA
      simp at hA)
    (fun i hi => by obtain ⟨q, hq, -⟩ := hi; simp at hq)
  have h' := relAtInT_nodeHonest (Q := fun σ => σ (.n 0) = gen ^ k)
    (cs := fun _ => colLoopCalls col f k m) (bs := fun _ => []) (Ts := [Tc, Tt]) h hf hw' rfl hcalls
    hal (by simp [colLoopCalls])
  rw [hal] at h'
  simp only [List.sum_nil, Nat.add_zero] at h'
  exact h'

/-- **A column loop is complete, placed, by trees of its honest shape** (`colFrom`), from every
counter `a ≤ k < m`, when its columns are by trees satisfying `Tc`. -/
theorem colLoop_completeAtT {Tc : Tree → Prop} {f col : String} {j endLo : ℕ} (hj : j < coreProgram.length)
    (hok : (colLoopOk (coreProgram.getD j default) col f endLo &&
      decide (coreProgram.indexOf? f = some j)) = true)
    {p1 p2 p3 p4 p5 p6 p7 p8 : E} {Lin : Layout} {a m : ℕ} (hw : word endLo 0 0 = gen ^ m)
    (hm : m < 2 ^ 34)
    (hcol : ∀ k, a ≤ k → k < m →
      CompleteAtDT fs cert 16 col Lin [gen ^ k, p1, p2, p3, p4, p5, p6, p7, p8] (Returns []) Tc) :
    ∀ k, a ≤ k → k < m →
      CompleteAtDT fs cert 16 f Lin [gen ^ k, p1, p2, p3, p4, p5, p6, p7, p8] (Returns [])
        (colFrom f col m Tc (m - k) k) := by
  have key : ∀ t k, a ≤ k → k + 1 + t = m →
      CompleteAtDT fs cert 16 f Lin [gen ^ k, p1, p2, p3, p4, p5, p6, p7, p8] (Returns [])
        (colFrom f col m Tc (t + 1) k) := by
    intro t
    induction t with
    | zero => intro k hak hk
              exact colLoop_stepAtT (Tt := colFrom f col m Tc 0 (k + 1)) fs cert hj hok hw (by omega)
                hm (hcol k hak (by omega)) fun h => absurd h (by omega)
    | succ t ih => intro k hak hk
                   exact colLoop_stepAtT fs cert hj hok hw (by omega) hm (hcol k hak (by omega))
                     fun _ => ih (k + 1) (by omega) (by omega)
  intro k hak hk
  have := key (m - k - 1) k hak (by omega)
  rwa [show m - k - 1 + 1 = m - k by omega] at this


end
end LeanVM.Guest.B1.Da
