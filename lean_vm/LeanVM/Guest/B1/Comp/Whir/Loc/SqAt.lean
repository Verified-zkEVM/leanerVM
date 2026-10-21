/-
  LeanVM.Guest.B1.Comp.Whir.Loc.SqAt

  The query-position loop, placed, over a completeness model (`Whir/SqAt.lean`)
-/

module

public import LeanVM.Guest.B1.Whir.SqAt
public import LeanVM.Guest.B1.Comp.Whir.Loc.OsCallees
public import LeanVM.Guest.B1.Comp.Whir.Loc.QueriesAt
public import LeanVM.Guest.B1.Comp.Whir.SqIter

/-!
# The query-position loop, placed, over a completeness model (`Whir/SqAt.lean`)
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Main (MemL RegionL)
open LeanVM.E2E.Complete
open LeanVM.Protocol.Compile (Bytes)
open LeanVM.Protocol (Digest)

@[expose] public section

variable {Ht : Bytes → Digest} {CM : CompModel}

/-- **One iteration of a squeeze loop, placed at `fp`**: its tail at `fp + fs L` (or skipped at
the last), its decoder after the tail's `m` words, its loads through the row in `R`. -/
theorem sqLoop_iterC (fs : String → ℕ) (cert : String → V → ℕ) {lv : OsLvl} (hpl : SqPlace lv)
    {fn : Fn} (hfind : coreProgram.find? lv.sqLoop = some fn) (hp : fn.params = [.n 0, .n 1, .n 2, .n 3, .n 4])
    (hb : fn.body = sqLoopOf lv) (hlp : coreProgram.loop lv.sqLoop = true) (hpo : lv.posOff < 2 ^ 128)
    (hdig : osDigitsVal 1 (osPowDigits (192 / lv.depth)) = 192 / lv.depth) {rd : Reader}
    {R Rd Dd Dt : ℕ → Prop} {x N sqz qpos qbp : E} {cv : Digest} (fp : ℕ) {m : ℕ}
    (l0 : LoadHolds rd (sqz * (x * x)) 0 (digestScalars cv).1)
    (l1 : LoadHolds rd (sqz * (x * x)) 1 (digestScalars cv).2)
    (l2 : LoadHolds rd (sqz * (x * x)) 2 (digestScalars (sqCvW Ht cv)).1)
    (l3 : LoadHolds rd (sqz * (x * x)) 3 (digestScalars (sqCvW Ht cv)).2)
    (asq : sqCvM CM.hm cv = some (sqCvW Ht cv))
    (hdec : RelAtInB CM.sem coreProgram fs cert rd Rd Dd (fp + fs lv.sqLoop + m) (fs lv.decode) lv.decode
      [challengeOf (sqCvW Ht cv), qpos * gen ^ lv.posOff * x ^ (192 / lv.depth),
        qbp * gen ^ lv.posOff * x ^ (192 / lv.depth)] [])
    (hRd : ∀ i, Rd i → R i) (hK : IsInK (x * gen + N))
    (htail : if x * gen + N ≠ 0 then RelAtInB CM.sem coreProgram fs cert rd R Dt (fp + fs lv.sqLoop) m lv.sqLoop
      [x * gen, N, sqz, qpos, qbp] [] else m = fs lv.sqLoop)
    (hreg : ∀ t < 4, OqIn R ((sqz * (x * x)).limb 0 * Parameters.gpow t)) :
    RelAtInB CM.sem coreProgram fs cert rd R (fun i => Dd i ∨ (x * gen + N ≠ 0 ∧ Dt i)) fp
      (fs lv.sqLoop + m + fs lv.decode) lv.sqLoop [x, N, sqz, qpos, qbp] [] := by
  obtain ⟨σ, hσ⟩ : ∃ σ, σ = sqIterValW Ht lv x N sqz qpos qbp cv := ⟨_, rfl⟩
  obtain ⟨parg, p6, p24, pp1, pp2, pe2, pe4⟩ := sqIterVal_ptrsW hpo hdig x N sqz qpos qbp cv
  rw [← hσ] at parg p6 p24 pp1 pp2 pe2 pe4
  have hargs : ([.n 0, .n 1, .n 2, .n 3, .n 4] : List V).map σ = [x, N, sqz, qpos, qbp] := by
    simp only [List.map_cons, List.map_nil, parg 0 (by omega), parg 1 (by omega), parg 2 (by omega),
      parg 3 (by omega), parg 4 (by omega)]
    rfl
  have hholds : Stmt.HoldsListB CM.sem (coreProgram.RelB CM.sem rd) rd σ fn.body False (fun rs => rs = []) := by
    rw [hb, hσ]
    refine sqIter_holdsC (CM := CM) hpo hdig l0 l1 l2 l3 asq hdec.relAt.rel hK fun hne => ?_
    rw [ite_pos' hne] at htail
    exact htail.relAt.rel
  have hbody : fn.body = sqLoopPre lv ++ [.ret []] := hb.trans (sqLoopOf_split lv)
  set es := (sqLoopPre lv).flatMap (Main.slEvs σ)
  have hw' : walk σ fn.body = .ret es [] := by rw [hbody]; exact Main.walk_straight σ [] _ hpl.straight
  have hev := oq_holds_eventsB hfind hholds hw'
  obtain ⟨had, hal, hadr, hcl⟩ := Main.straight_parts σ _ hpl.straight
  have hal0 : allocs σ es = [] := by rw [hal, hpl.allocs]; rfl
  have hcalls : calls es = [⟨lv.decode, [.n 24, .n (sqP1 lv).2.1, .n (sqP2 lv).2.1], [], true⟩] ++
      [⟨lv.sqLoop, [.n (sqE lv + 4), .n 1, .n 2, .n 3, .n 4], [], decide (σ (.n (sqE lv + 2)) ≠ 0)⟩] := by
    rw [hcl, hpl.calls]; rfl
  have hdargs : ([.n 24, .n (sqP1 lv).2.1, .n (sqP2 lv).2.1] : List V).map σ =
      [challengeOf (sqCvW Ht cv), qpos * gen ^ lv.posOff * x ^ (192 / lv.depth),
        qbp * gen ^ lv.posOff * x ^ (192 / lv.depth)] := by
    simp only [List.map_cons, List.map_nil, p24, pp1, pp2]
  have h := relAtInB_of_walk_loop (P := coreProgram) (fs := fs) (cert := cert) (σ := σ) (rd := rd) coreProgram_wf
    (R := R) (D := fun i => Dd i ∨ (x * gen + N ≠ 0 ∧ Dt i)) (Dk := fun i => False ∨ (true = true ∧ Dd i))
    (Rt := R) (Dt := Dt) (fp := fp) (m := m) (N := fs lv.decode) hfind hlp (hp ▸ hargs) hw' rfl hev hcalls ?_
    (by rw [had, hpl.allocs, hal0]; rfl)
    (fun q hq' => by rw [hadr, hpl.addrs] at hq'; simp at hq')
    ?_ (fun i hi => Or.inl hi) (fun A hA => ?_) ?_
  · rwa [hal0, List.sum_nil, Nat.add_zero] at h
  · by_cases ht : x * gen + N ≠ 0
    · rw [ite_pos' ht] at htail
      simp only [pe2]
      rw [ite_pos' (decide_eq_true ht), List.map_nil]
      have : ([.n (sqE lv + 4), .n 1, .n 2, .n 3, .n 4] : List V).map σ = [x * gen, N, sqz, qpos, qbp] := by
        simp only [List.map_cons, List.map_nil, pe4, parg 1 (by omega), parg 2 (by omega), parg 3 (by omega),
          parg 4 (by omega)]
        rfl
      rw [this]; exact htail
    · rw [ite_neg' ht] at htail
      simp only [pe2]
      rw [ite_neg' (by simpa using ht)]
      exact htail
  · rw [hal0, List.sum_nil, Nat.add_zero]
    refine ⟨fs lv.decode, 0, Rd, Dd, rfl, fun i hi => Or.inl (Or.inl (hRd i hi)), ?_, rfl, fun i hi => hi⟩
    simp only [↓reduceIte, List.map_nil]
    rw [hdargs]; exact hdec
  · rw [loadAddrs_straight σ _ hpl.straight] at hA
    obtain ⟨⟨p, off⟩, hq', rfl⟩ := List.mem_map.mp hA
    have hb' := List.all_eq_true.mp hpl.loads _ hq'
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hb'
    obtain ⟨rfl, ho⟩ := hb'
    obtain ⟨i, hi, hR⟩ := hreg off ho
    exact ⟨i, by rw [p6]; exact hi, Or.inr (Or.inl hR)⟩
  · intro i hi
    rcases hi with hi | ⟨ht, hi⟩
    · exact Or.inr (Or.inl (Or.inr ⟨rfl, hi⟩))
    · refine Or.inr (Or.inr ⟨?_, hi⟩)
      simp only [pe2]
      exact decide_eq_true ht

/-- The challenge of iteration `j` from the chain state `cv`. -/
def sqWW (Ht : Bytes → Digest) (cv : Digest) (j : ℕ) : E := challengeOf (sqCvW Ht (sqAllW Ht j cv).2)

/-- **A level's squeeze loop, placed** from its first iteration at `fp`: on every memory holding
the state chain at `sqz` and, at `qpos` and `qbp`, what each decoder stores (the positions and
the pointers into its frame run at `sqDecAt`), the loop holds, its decoders' frame runs its data
(`sqRuns`). -/
theorem sqLoop_relAtInC (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) {lv : OsLvl} (hpl : SqPlace lv)
    {fn : Fn} (hfind : coreProgram.find? lv.sqLoop = some fn) (hp : fn.params = [.n 0, .n 1, .n 2, .n 3, .n 4])
    (hb : fn.body = sqLoopOf lv) (hlp : coreProgram.loop lv.sqLoop = true) (hpo : lv.posOff < 2 ^ 128)
    (hdig : osDigitsVal 1 (osPowDigits (192 / lv.depth)) = 192 / lv.depth)
    (hdec : OsDecodeAtDC CM fs cert k lv.depth lv.decode) {n : ℕ} (hn : 0 < n) (hn' : n + 1 < ordG)
    {sqz qpos qbp : E} {cv : Digest} {Lin : Main.Layout} (fp : ℕ)
    (hmem : ∀ rd, LowDef k rd → MemL rd Lin → ∀ j < n,
      LoadHolds rd sqz (2 * j) (digestScalars (sqAllW Ht j cv).2).1 ∧
        LoadHolds rd sqz (2 * j + 1) (digestScalars (sqAllW Ht j cv).2).2 ∧
        LoadHolds rd sqz (2 * j + 2) (digestScalars (sqCvW Ht (sqAllW Ht j cv).2)).1 ∧
        LoadHolds rd sqz (2 * j + 3) (digestScalars (sqCvW Ht (sqAllW Ht j cv).2)).2)
    (hdmem : ∀ rd, LowDef k rd → MemL rd Lin → ∀ j < n, ∀ i < 192 / lv.depth,
      LoadHolds rd (qpos * gen ^ (lv.posOff + j * (192 / lv.depth))) i
          (eOfNat ((eToNat (sqWW Ht cv j) >>> (i * lv.depth)) % 2 ^ lv.depth)) ∧
        LoadHolds rd (qbp * gen ^ (lv.posOff + j * (192 / lv.depth))) i
          (ofK (Parameters.gpow (sqDecAt fs lv n fp j + cert lv.decode (.n 3))) * gen ^ (i * lv.depth)))
    (hreg : ∀ j < n, ∀ t < 4, OqIn (RegionL Lin) (sqz.limb 0 * Parameters.gpow (2 * j + t)))
    (hasq : ∀ j < n, sqCvM CM.hm (sqAllW Ht j cv).2 = some (sqCvW Ht (sqAllW Ht j cv).2)) :
    ∃ Lown : Main.Layout, Within (sqRuns fs cert lv n fp (sqWW Ht cv) 0 ++ Lown) fp (sqTot fs lv n 0) ∧
      DisjL (sqRuns fs cert lv n fp (sqWW Ht cv) 0 ++ Lown) ∧ ∀ rd, LowDef k rd → MemL rd (sqRuns fs cert lv n fp (sqWW Ht cv) 0 ++ Lown ++ Lin) →
        RelAtInB CM.sem coreProgram fs cert rd (RegionL Lin) (RegionL (sqRuns fs cert lv n fp (sqWW Ht cv) 0)) fp
          (sqTot fs lv n 0) lv.sqLoop [1, gen ^ n, sqz, qpos, qbp] [] := by
  have hn'' : n + 1 < 2 ^ 64 - 1 := hn'
  have hptr : ∀ j, ∀ (b : E), b * gen ^ lv.posOff * (gen ^ j) ^ (192 / lv.depth) =
      b * gen ^ (lv.posOff + j * (192 / lv.depth)) := fun j b => by
    rw [← pow_mul, mul_assoc, ← pow_add]
  have hdecj : ∀ j < n, ∃ Lj : Main.Layout,
      Within (dqRunL cert lv.decode (sqDecAt fs lv n fp j) (sqWW Ht cv j) ++ Lj) (sqDecAt fs lv n fp j) (fs lv.decode) ∧
      DisjL (dqRunL cert lv.decode (sqDecAt fs lv n fp j) (sqWW Ht cv j) ++ Lj) ∧ ∀ rd, LowDef k rd → MemL rd (dqRunL cert lv.decode (sqDecAt fs lv n fp j) (sqWW Ht cv j) ++ Lj ++ Lin) →
        RelAtInB CM.sem coreProgram fs cert rd (RegionL Lin)
          (RegionL (dqRunL cert lv.decode (sqDecAt fs lv n fp j) (sqWW Ht cv j))) (sqDecAt fs lv n fp j) (fs lv.decode)
          lv.decode [sqWW Ht cv j, qpos * gen ^ lv.posOff * (gen ^ j) ^ (192 / lv.depth),
            qbp * gen ^ lv.posOff * (gen ^ j) ^ (192 / lv.depth)] [] := fun j hj => by
    rw [hptr, hptr]
    exact hdec _ _ _ Lin _ fun rd hl hm i hi => hdmem rd hl hm j hj i hi
  classical
  let Lj : ℕ → Main.Layout := fun j => if h : j < n then Classical.choose (hdecj j h) else []
  have hLj : ∀ j (h : j < n), Lj j = Classical.choose (hdecj j h) := fun j h => by simp [Lj, h]
  let Lown : Main.Layout := ((List.range n).map Lj).flatten
  refine ⟨Lown, ?_, ?_, fun rd hlow hL => ?_⟩
  · rw [within_append]
    refine ⟨fun q hq => ?_, fun q hq => ?_⟩
    · simp only [sqRuns, List.mem_flatten, List.mem_map, List.mem_range] at hq
      obtain ⟨_, ⟨j, hj, rfl⟩, hq⟩ := hq
      simp only [Nat.zero_add] at hq
      have hw := (Classical.choose_spec (hdecj j (by omega))).1 q (List.mem_append_left _ hq)
      have := sqTot_le fs lv (n := n) (j := j) (by omega)
      have := sqTot_step fs lv (n := n) (j := j) (by omega)
      simp only [sqDecAt] at hw ⊢
      omega
    · simp only [Lown, List.mem_flatten, List.mem_map, List.mem_range] at hq
      obtain ⟨_, ⟨j, hj, rfl⟩, hq⟩ := hq
      rw [hLj j hj] at hq
      have hw := (Classical.choose_spec (hdecj j hj)).1 q (List.mem_append_right _ hq)
      have := sqTot_le fs lv (n := n) (j := j) (by omega)
      have := sqTot_step fs lv (n := n) (j := j) hj
      simp only [sqDecAt] at hw ⊢
      omega
  · have e1 : sqRuns fs cert lv n fp (sqWW Ht cv) 0 =
        ((List.range n).map fun j => dqRunL cert lv.decode (sqDecAt fs lv n fp j) (sqWW Ht cv j)).flatten := by
      simp [sqRuns]
    rw [e1]
    refine os_disj_windows _ Lj (fun j => sqDecAt fs lv n fp j) (fun _ => fs lv.decode) (fun j hj => ?_)
      (fun j hj => ?_) (fun i hi j hj hij => ?_)
    · rw [hLj j hj]; exact (Classical.choose_spec (hdecj j hj)).2.1
    · rw [hLj j hj]; exact (Classical.choose_spec (hdecj j hj)).1
    · rw [sqDecAt_eq fs lv fp hi, sqDecAt_eq fs lv fp hj]
      rcases Nat.lt_or_gt_of_ne hij with h | h
      · right
        have : (n - 1 - j + 1) * fs lv.decode ≤ (n - 1 - i) * fs lv.decode := Nat.mul_le_mul_right _ (by omega)
        rw [Nat.add_mul, Nat.one_mul] at this
        omega
      · left
        have : (n - 1 - i + 1) * fs lv.decode ≤ (n - 1 - j) * fs lv.decode := Nat.mul_le_mul_right _ (by omega)
        rw [Nat.add_mul, Nat.one_mul] at this
        omega
  obtain ⟨h12, hLin⟩ := Main.memL_append.mp hL
  obtain ⟨hR, hO⟩ := Main.memL_append.mp h12
  have hd := hmem rd hlow hLin
  have hrel : ∀ j (hj : j < n), RelAtInB CM.sem coreProgram fs cert rd (RegionL Lin)
      (RegionL (dqRunL cert lv.decode (sqDecAt fs lv n fp j) (sqWW Ht cv j))) (sqDecAt fs lv n fp j) (fs lv.decode)
      lv.decode [sqWW Ht cv j, qpos * gen ^ lv.posOff * (gen ^ j) ^ (192 / lv.depth),
        qbp * gen ^ lv.posOff * (gen ^ j) ^ (192 / lv.depth)] [] := fun j hj => by
    refine (Classical.choose_spec (hdecj j hj)).2.2 rd hlow (Main.memL_append.mpr ⟨Main.memL_append.mpr ⟨?_, ?_⟩, hLin⟩)
    · intro q hq
      exact hR q (by
        simp only [sqRuns, List.mem_flatten, List.mem_map, List.mem_range]
        exact ⟨_, ⟨j, hj, by simp⟩, hq⟩)
    · intro q hq
      rw [← hLj j hj] at hq
      exact hO q (by
        simp only [Lown, List.mem_flatten, List.mem_map, List.mem_range]
        exact ⟨_, ⟨j, hj, rfl⟩, hq⟩)
  have hstep : ∀ t j, j + t + 1 = n →
      RelAtInB CM.sem coreProgram fs cert rd (RegionL Lin) (fun i => RegionL (sqRuns fs cert lv n fp (sqWW Ht cv) j) i)
        (fp + j * fs lv.sqLoop) (sqTot fs lv n j) lv.sqLoop [gen ^ j, gen ^ n, sqz, qpos, qbp] [] := by
    intro t
    induction t with
    | zero =>
      intro j hj
      obtain ⟨m0, m1, m2, m3⟩ := hd j (by omega)
      have h0 : gen ^ j * gen + gen ^ n = 0 := by rw [gen_pow_add_eq_zero_iff]; congr 1; omega
      have := sqLoop_iterC (Ht := Ht) (CM := CM) fs cert hpl hfind hp hb hlp hpo hdig (rd := rd) (R := RegionL Lin) (Dt := fun _ => False)
        (N := gen ^ n) (sqz := sqz) (qpos := qpos) (qbp := qbp) (cv := (sqAllW Ht j cv).2) (fp + j * fs lv.sqLoop)
        (m := fs lv.sqLoop)
        (by rw [os_gen_pow_sq, loadHolds_mul_gen_pow, Nat.add_zero]; exact m0)
        (by rw [os_gen_pow_sq, loadHolds_mul_gen_pow]; exact m1)
        (by rw [os_gen_pow_sq, loadHolds_mul_gen_pow]; exact m2)
        (by rw [os_gen_pow_sq, loadHolds_mul_gen_pow]; exact m3) (hasq j (by omega))
        (by
          have := hrel j (by omega)
          rwa [sqDecAt, sqTailTot, ite_neg' (by omega)] at this)
        (fun i h => h) (by rw [h0]; exact (isInK_iff _).mpr ⟨0, ofK_zero.symm⟩)
        (by rw [ite_neg' (by simp [h0])])
        (fun t ht => by
          obtain ⟨i, hi, hR'⟩ := hreg j (by omega) t ht
          refine ⟨i, ?_, hR'⟩
          rw [os_gen_pow_sq, oq_limb_mul_gen_pow m0.1]; exact hi)
      rw [show sqTot fs lv n j = fs lv.sqLoop + fs lv.sqLoop + fs lv.decode by
        rw [sqTot_step fs lv (by omega), sqTailTot, ite_neg' (by omega)]]
      refine relAtInS_dmono this fun i hi => ?_
      obtain ⟨j', h1, h2, hi'⟩ := regionL_sqRuns.mp hi
      obtain rfl : j' = j := by omega
      exact Or.inl (by rwa [sqDecAt, sqTailTot, ite_neg' (by omega)] at hi')
    | succ t ih =>
      intro j hj
      obtain ⟨m0, m1, m2, m3⟩ := hd j (by omega)
      have hne : gen ^ j * gen + gen ^ n ≠ 0 := by
        rw [ne_eq, gen_pow_add_eq_zero_iff]
        intro he
        have := gen_pow_inj (by omega) (by omega) he
        omega
      have ht := ih (j + 1) (by omega)
      rw [Nat.add_mul, Nat.one_mul, ← Nat.add_assoc] at ht
      have := sqLoop_iterC (Ht := Ht) (CM := CM) fs cert hpl hfind hp hb hlp hpo hdig (rd := rd) (R := RegionL Lin)
        (Dt := fun i => RegionL (sqRuns fs cert lv n fp (sqWW Ht cv) (j + 1)) i)
        (N := gen ^ n) (sqz := sqz) (qpos := qpos) (qbp := qbp) (cv := (sqAllW Ht j cv).2) (fp + j * fs lv.sqLoop)
        (m := sqTot fs lv n (j + 1))
        (by rw [os_gen_pow_sq, loadHolds_mul_gen_pow, Nat.add_zero]; exact m0)
        (by rw [os_gen_pow_sq, loadHolds_mul_gen_pow]; exact m1)
        (by rw [os_gen_pow_sq, loadHolds_mul_gen_pow]; exact m2)
        (by rw [os_gen_pow_sq, loadHolds_mul_gen_pow]; exact m3) (hasq j (by omega))
        (by
          have := hrel j (by omega)
          rwa [sqDecAt, sqTailTot, ite_pos' (by omega)] at this)
        (fun i h => h) (isInK_add (by rw [gen_pow_mul_gen]; exact gen_pow_isInK _) (gen_pow_isInK _))
        (by rw [ite_pos' hne, gen_pow_mul_gen]; exact ht)
        (fun t ht => by
          obtain ⟨i, hi, hR'⟩ := hreg j (by omega) t ht
          refine ⟨i, ?_, hR'⟩
          rw [os_gen_pow_sq, oq_limb_mul_gen_pow m0.1]; exact hi)
      rw [show sqTot fs lv n j = fs lv.sqLoop + sqTot fs lv n (j + 1) + fs lv.decode by
        rw [sqTot_step fs lv (by omega), sqTailTot, ite_pos' (by omega)]]
      refine relAtInS_dmono this fun i hi => ?_
      obtain ⟨j', h1, h2, hi'⟩ := regionL_sqRuns.mp hi
      rcases Nat.eq_or_lt_of_le h1 with rfl | h1
      · exact Or.inl (by rwa [sqDecAt, sqTailTot, ite_pos' (by omega)] at hi')
      · exact Or.inr ⟨hne, regionL_sqRuns.mpr ⟨j', by omega, h2, hi'⟩⟩
  have := hstep (n - 1) 0 (by omega)
  simpa using this

end
end LeanVM.Guest.B1
