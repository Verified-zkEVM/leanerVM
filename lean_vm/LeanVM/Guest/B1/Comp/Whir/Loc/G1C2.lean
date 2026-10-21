/-
  LeanVM.Guest.B1.Comp.Whir.Loc.G1C2

  `grind_check`, placed, over a completeness model.
-/

module

public import LeanVM.Guest.B1.Comp.Whir.Loc.G1C
public import LeanVM.Guest.B1.Comp.Grind
public import LeanVM.Guest.B1.GrindPlaced

/-!
# `grind_check`, placed, over a completeness model

`gc_holdsC`: `GrindPlaced.lean`'s honest valuation of `grind_check`'s body over a model, the base
and the digest the model's answers (`grind_check_comp`'s valuation). `grind_check_completeRelBC`:
`grind_check_completeRelB` over the model, on `GrindPreC CM`, its frame run the lane's bits of the
model's digest (`gcBitsD`), its loop `__loop6` free of `BLAKE2S`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Main (MemL RegionL)
open LeanVM.E2E.Complete

@[expose] public section

/-- **`grind_check`'s body holds over the model** at the honest valuation, the run pointer `p`
holding the lane's bits of the model's digest `D`. -/
theorem gc_holdsC {CM : CompModel} (rd : Reader) (s0 s1 nonce N : E) (m : ℕ) (hm : m < ordG) (hN : N = gen ^ m)
    (cv B D : Digest) (hcv : (s0, s1) = digestScalars cv) (hB : CM.H (digestBytes cv ++ blockOf 0 3) = some B)
    (hD : CM.H (digestBytes B ++ blockOf nonce 4) = some D) (hpow : powOk m nonce D = true)
    (p : E) (hpK : IsInK p)
    (hfr : ∀ k < 64, ∀ w, rd (p.limb 0 * Parameters.gpow k) = some w →
      w = bitE ((kToNat ((digestScalars D).1.limb 0)).testBit k))
    (hloads : ∀ j < m, LoadHolds rd p j 0) :
    ∃ τ : Val, (τ (.n 287) = p ∧ τ (.n 289) = 1 + N ∧ τ (.n 290) = 1 ∧ τ (.n 3) = N) ∧
      (Fn.params Data.core3).map τ = [s0, s1, nonce, N] ∧
      Stmt.HoldsListB CM.sem (coreProgram.RelB CM.sem rd) rd τ gcBody False (fun rs => rs = []) := by
  rw [show Fn.params Data.core3 = [.n 0, .n 1, .n 2, .n 3] from rfl]
  suffices H : ∃ τ : Val, (τ (.n 287) = p ∧ τ (.n 289) = 1 + N ∧ τ (.n 290) = 1 ∧ τ (.n 3) = N) ∧
      ([.n 0, .n 1, .n 2, .n 3] : List V).map τ = [s0, s1, nonce, N] ∧
      Stmt.HoldsListB CM.sem (coreProgram.RelB CM.sem rd) rd τ gcBody False (fun rs => rs = []) from H
  rw [gcBody]
  simp only [holdsListB_append, Stmt.HoldsListB]
  simp only [ite_holdsB_noRet (.n 5) [.atom (.const (.n 6) (word 0 0 0)),
    .atom (.assertEq (.n 2) (.n 6))] [] rfl rfl]
  simp only [Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, holdsB_canonicalLimbsT,
    range_flatten_holdsListB 64 gcBit (fun i => by cases i <;> rfl), holdsB_gcBit, List.map_cons,
    List.map_nil, word_one, word_zero, true_and]
  set o0 := (digestScalars D).1
  set L := kToNat (o0.limb 0)
  have hL : L < 2 ^ 64 := (o0.limb 0).toBitVec.isLt
  set τ := setl (setv (setv (setl (setv (setv (setl (Val.ofArgs [s0, s1, nonce, N]) 4
    [1, N + 1, 0, s0, s1]) 9 7 (sqStateValsD B 3)) 16 14 (fsValsD nonce D 4)) 30
    [ofK (o0.limb 0), o0 + ofK (o0.limb 0), word 1 0 1, ofK (o0.limb 1)]) 34 64
    (fun i => bitE (L.testBit i))) 98 189 (gcVals L)) 287 [p, 1, 1 + N, 1]
  have tb : ∀ i < 64, τ (.n (34 + i)) = bitE (L.testBit i) := fun i hi => by
    simp only [τ, setl, List.length_cons, List.length_nil]
    rw [set_n_lt (by omega), set_n_lt (by omega), set_n_in (by omega) (by omega),
      Nat.add_sub_cancel_left]
  have tg : ∀ t < 189, τ (.n (98 + t)) = gcVals L t := fun t ht => by
    simp only [τ, setl, List.length_cons, List.length_nil]
    rw [set_n_lt (by omega), set_n_in (by omega) (by omega), Nat.add_sub_cancel_left]
  have t28 : τ (.n 28) = o0 := by simp only [τ]; b1_look; rfl
  have t30 : τ (.n 30) = ofK (o0.limb 0) := by simp only [τ]; b1_look
  have t2 : τ (.n 2) = nonce := by simp only [τ]; b1_look
  have t5 : τ (.n 5) = N + 1 := by simp only [τ]; b1_look
  have t6 : τ (.n 6) = 0 := by simp only [τ]; b1_look
  have t287 : τ (.n 287) = p := by simp only [τ]; b1_look
  have hcall := (guarded_loop_iff (loop6_step rd N p)).mpr ⟨m, hm, hN, fun j hj => by
    rw [loadHolds_mul_gen_pow, Nat.add_zero]; exact hloads j hj⟩
  have hfree := fun args rets => relB_iff_rel_of_freeOn (S := CM.sem) (rd := rd) freeOn_loop6
    (List.mem_singleton_self "__loop6") args rets
  refine ⟨τ, ⟨by simp only [τ]; b1_look, by simp only [τ]; b1_look, by simp only [τ]; b1_look,
    by simp only [τ]; b1_look⟩, ?_⟩
  refine ⟨?_, ?_, ?_, ⟨?_, fun h5 => ?_, fun _ => trivial⟩, ?_, ?_,
    holdsB_squeezeStateT_comp _ _ _ (show 3 < 256 by decide) ⟨⟨cv, B, ?_, hB, fun k hk => ?_⟩,
    holdsB_fsCompressT_comp _ _ _ _ (show 4 < 256 by decide) ⟨⟨B, D, ?_, ?_, fun k hk1 hk2 => ?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_⟩, fun i hi => ?_, ?_, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, trivial⟩⟩⟩
  · simp only [τ]; b1_look
  · simp only [τ]; b1_look
  · simp only [τ]; b1_look
  · rw [t5, hN]; exact isInK_add (gen_pow_isInK m) (by rw [← pow_zero gen]; exact gen_pow_isInK 0)
  · rw [t5, hN, e_add_eq_zero_iff, ← pow_zero gen] at h5
    have hm0 : m = 0 := gen_pow_inj (by omega) (by decide) h5
    subst hm0
    unfold powOk at hpow
    simp only [↓reduceIte, decide_eq_true_eq] at hpow
    have hn : nonce = 0 := by rw [eq_ofLimbs nonce, hpow.1, hpow.2.1, hpow.2.2, ← zero_eq_ofLimbs]
    rw [t6, t2, hn]
    exact ⟨rfl, add_zero 0, trivial⟩
  · simp only [τ]; b1_look
  · simp only [τ]; b1_look
  · simp only [τ]; b1_look; exact hcv
  · simp only [τ]; b1_look
  · simp only [τ]; b1_look
    show ((digestScalars B).1, (digestScalars B).2) = _
    rw [Prod.mk.eta]
  · rw [t2]; exact hD
  · simp only [τ]; b1_look
  · rw [t28]; exact (isCanonical128_digestScalars _).1
  · rw [t30, t28]
  · simp only [τ]; b1_look; rfl
  · simp only [τ]; b1_look
  · simp only [τ]; b1_look; rfl
  · cases i with
    | zero =>
      show τ (.n (34 + 0)) = τ (.n (34 + 0)) * τ (.n (34 + 0))
      rw [tb 0 hi, bitE_mul_self]
    | succ i =>
      have e1 := tb (i + 1) hi
      have e2 := tg (3 * i) (by omega)
      have e3 := tg (3 * i + 1) (by omega)
      have e4 := tg (3 * i + 2) (by omega)
      rw [gcVals_0] at e2
      rw [gcVals_1] at e3
      rw [gcVals_2] at e4
      rw [show 34 + (i + 1) = 35 + i by omega] at e1
      rw [show 98 + (3 * i + 1) = 99 + 3 * i by omega] at e3
      rw [show 98 + (3 * i + 2) = 100 + 3 * i by omega] at e4
      have ea : τ (.n (gcAcc i)) = gcAccV L i := by
        cases i with
        | zero => exact tb 0 (by omega)
        | succ i =>
          have := tg (3 * i + 2) (by omega)
          rw [gcVals_2, show 98 + (3 * i + 2) = 100 + 3 * i by omega] at this
          exact this
      refine ⟨by rw [e1, bitE_mul_self], e2, by rw [e3, e1, e2], by rw [e4, ea, e3, gcAccV]⟩
  · have e := tg 188 (by omega)
    rw [show (188 : ℕ) = 3 * 62 + 2 by rfl, gcVals_2, gcAccV_eq L 63 (by omega)] at e
    rw [show 98 + (3 * 62 + 2) = 286 by rfl] at e
    have hr := reconstruct_bits 0 hL
    simp only [Nat.zero_add, pow_zero, one_mul] at hr
    rw [e, t30, show (63 : ℕ) + 1 = 64 from rfl, hr, eOfNat192_of_lt hL]
    have : eOfNat L = ofK (o0.limb 0) := by rw [eOfNat, ofBits_kToNat]
    rw [this]
    exact e_add_self _
  · rw [t287]; exact hpK
  · intro k hk w hw
    rw [t287] at hw
    rw [gcRun_getElem, tb k (by rw [length_gcRun] at hk; exact hk)]
    exact hfr k (by rw [length_gcRun] at hk; exact hk) w hw
  · simp only [τ]; b1_look
  · simp only [τ]; b1_look
  · simp only [τ]; b1_look
  · simp only [τ]; b1_look; exact hcall.1
  · simp only [τ]; b1_look
    exact fun h => (hfree _ _).mpr (hcall.2 h)

/-- The lane's 64 bits of a digest. -/
noncomputable def gcBitsD (D : Digest) : List E :=
  (List.range 64).map fun i => bitE ((kToNat ((digestScalars D).1.limb 0)).testBit i)

/-- **`grind_check`, placed**: on `GrindPre` (the state the cells of `cv`, `powOk bits` of the digest,
`bits ≤ 64`), it returns nothing and no buffer, its frame run the lane's bits. -/
theorem grind_check_completeRelBC {CM : CompModel} (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) (hc : cert "grind_check" (.n 34) + 64 ≤ fs "grind_check") (B6 : E → ℕ)
    (h6 : TotalLeOnB CM.sem coreProgram fs "__loop6" LoopPre fun a => B6 (a.getD 1 0)) :
    ∀ (args rets : List E) (Lin : Main.Layout), (∀ rd, LowDef k rd → MemL rd Lin → GrindPreC CM rd args rets) →
      CompleteAtBS CM.sem fs cert k "grind_check" Lin args (Returns rets)
        (fs "grind_check" + max (B6 (args.getD 3 0)) (fs "__loop6")) := by
  intro args rets Lin hpre fp
  classical
  by_cases hex : ∃ rd1, LowDef k rd1 ∧ MemL rd1 Lin
  swap
  · exact ⟨0, [], rets, [], ⟨rfl, rfl⟩, by simp [Within], disj_nil, Nat.zero_le _, fun rd hl hL =>
      absurd ⟨rd, hl, by simpa using hL⟩ hex⟩
  obtain ⟨rd1, hl1, hL1⟩ := hex
  obtain ⟨s0, s1, nonce, N, rfl⟩ : ∃ s0 s1 nonce N, args = [s0, s1, nonce, N] := by
    match args, hpre rd1 hl1 hL1 with
    | [a, b, c, d], _ => exact ⟨a, b, c, d, rfl⟩
  obtain ⟨rfl, m, hm, hm64, hN, cv, B, D, hcv, hB, hD, hpow⟩ := hpre rd1 hl1 hL1
  set c := cert "grind_check" (.n 34) with hcdef
  set p : E := ofK (Parameters.gpow (fp + c)) with hpdef
  set Lrun : Main.Layout := [(fp + c, gcBitsD D)] with hLrun
  have hrd_run : ∀ rd, MemL rd Lrun → ∀ j < 64, LoadHolds rd p j ((gcBitsD D).getD j 0) := by
    intro rd h j hj
    have := h _ List.mem_cons_self j (by simpa [gcBitsD] using hj)
    rwa [List.getD_eq_getElem _ _ (by simpa [gcBitsD] using hj)]
  have hzero : ∀ rd, MemL rd Lrun → ∀ j < m, LoadHolds rd p j 0 := by
    intro rd h j hj
    have := hrd_run rd h j (by omega)
    rwa [gcBitsD, List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map, List.getElem_range,
      gc_bits_of_powOk (by omega) hpow j hj] at this
  -- The loop, placed after the frame, when entered.
  have hloop : 0 < m → CompleteAtBS CM.sem fs cert k "__loop6" Lrun [1, N, p] (Returns []) (B6 N) := fun h0 =>
    completeAtS_of_rel_pureBat find_loop6_pure (by simp) (fun rd hL => (relB_iff_rel_of_freeOn (S := CM.sem)
      (rd := rd) freeOn_loop6 (List.mem_singleton_self _) _ _).mpr (((guarded_loop_iff
      (loop6_step rd N p)).mpr ⟨m, hm, hN, fun j hj => by
        rw [loadHolds_mul_gen_pow, Nat.add_zero]; exact hzero rd hL j hj⟩).2 (by
          rw [hN]; intro h
          rw [e_add_eq_zero_iff, ← pow_zero gen] at h
          have := gen_pow_inj (by omega) (by decide) h.symm
          omega))) k fun rd t hn hv hb =>
      h6 rd t _ [] hn (by rw [hN]; exact loopPre_gen h0 hm _) hv hb
  set b := fp + fs "grind_check"
  obtain ⟨nl, Ll, hWl, hDl, hnb, hRl, hnl⟩ : ∃ (nl : ℕ) (Ll : Main.Layout), Within Ll b nl ∧ DisjL Ll ∧
      nl ≤ max (B6 N) (fs "__loop6") ∧ (0 < m → ∀ rd, LowDef k rd →
      MemL rd ([] ++ Ll ++ Lrun) →
        RelAtInB CM.sem coreProgram fs cert rd (RegionL Lrun) (RegionL []) b nl "__loop6" [1, N, p] []) ∧
      (m = 0 → nl = fs "__loop6") := by
    by_cases h0 : 0 < m
    · obtain ⟨n', Lo, rets', Lout', ⟨rfl, rfl⟩, hw, hd, hnb, hr⟩ := hloop h0 b
      exact ⟨n', Lo, by simpa using hw, by simpa using hd, le_trans hnb (le_max_left _ _), fun _ => hr, fun h => absurd h (by omega)⟩
    · exact ⟨fs "__loop6", [], by simp [Within], disj_nil, le_max_right _ _, fun h => absurd h h0, fun _ => rfl⟩
  have hWr : Within Lrun (fp + c) 64 := fun q hq => by
    rw [hLrun, List.mem_singleton] at hq
    subst hq
    simp only [gcBitsD, List.length_map, List.length_range]
    omega
  refine ⟨fs "grind_check" + nl, Lrun ++ Ll, [], [], ⟨rfl, rfl⟩, ?_, ?_, Nat.add_le_add_left hnb _, fun rd hl hM => ?_⟩
  · rw [List.nil_append, within_append]
    exact ⟨fun q hq => by have := hWr q hq; omega, hWl.mono (by omega) (by omega)⟩
  · rw [List.nil_append]
    exact disj_append (by simp [hLrun, DisjL]) hDl hWr hWl (by omega)
  rw [List.nil_append] at hM
  obtain ⟨hM1, hLin⟩ := Main.memL_append.mp hM
  obtain ⟨hRun, hLl⟩ := Main.memL_append.mp hM1
  have hfr : ∀ k < 64, ∀ w, rd (p.limb 0 * Parameters.gpow k) = some w →
      w = bitE ((kToNat ((digestScalars D).1.limb 0)).testBit k) := by
    intro j hj w hw
    have := (hrd_run rd hRun j hj).2
    rw [hw, Option.some.injEq] at this
    rw [this, gcBitsD, List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map, List.getElem_range]
  obtain ⟨τ, ⟨t287, t289, t290, t3⟩, hpar, hh⟩ := gc_holdsC (CM := CM) rd s0 s1 nonce N m hm hN cv B D hcv hB hD hpow p
    (ofK_isInK _) hfr (hzero rd hRun)
  have hwf : Stmt.wfList coreProgram (Fn.body Data.core3) = true :=
    coreProgram_wf Data.core3 (List.mem_of_find?_eq_some find_grind_check)
  rw [core3_body] at hwf
  have hs := walkB_sat _ hwf hh
  rw [walk_gcBody] at hs
  obtain ⟨hst, hal, had, hca, hru, hlo⟩ := gcRest_shape
  obtain ⟨e1, e2, e3, e4⟩ := Main.straight_parts τ gcRest hst
  set es := gcHead τ ++ gcRest.flatMap (Main.slEvs τ) with hes_def
  have hAD : allocDsts es = [] := by
    rw [allocDsts, hes_def, filterMap_gcHead τ (fun e he => (gcHead_none τ e he).1)]
    exact e1.trans (by rw [g1_filterMap_nil hal]; rfl)
  have hAL : allocs τ es = [] := by
    rw [allocs, hes_def, filterMap_gcHead τ (fun e he => (gcHead_none τ e he).2.1)]
    exact e2.trans (by rw [g1_filterMap_nil hal]; rfl)
  have hAA : addrs es = [(.n 287, .n 34)] := by
    rw [addrs, hes_def, filterMap_gcHead τ (fun e he => (gcHead_none τ e he).2.2.1)]
    exact e3.trans had
  have hCA : calls es = [⟨"__loop6", [.n 290, .n 3, .n 287], [], decide (τ (.n 289) ≠ 0)⟩] := by
    rw [calls, hes_def, filterMap_gcHead τ (fun e he => (gcHead_none τ e he).2.2.2.1)]
    exact e4.trans (by rw [hca]; rfl)
  have hRU : runs es = [(.n 34, 64)] := by
    rw [runs, hes_def, filterMap_gcHead τ (fun e he => (gcHead_none τ e he).2.2.2.2.1)]
    exact (Digest.runs_straight τ gcRest hst).trans hru
  have hLA : loadAddrs τ es = [] := by
    rw [loadAddrs, hes_def, filterMap_gcHead τ (fun e he => (gcHead_none τ e he).2.2.2.2.2)]
    exact (loadAddrs_straight τ gcRest hst).trans (by rw [g1_filterMap_nil hlo]; rfl)
  have h := relAtInB_of_walk (P := coreProgram) (fs := fs) (cert := cert) (σ := τ) (R := RegionL Lin)
    (D := RegionL []) (Dk := fun _ => False) (fp := fp) (N := nl) (es := es) (args := [s0, s1, nonce, N])
    (rets := []) coreProgram_wf
    find_grind_check (Or.inl not_loop_grind_check) hpar (by rw [core3_body]; exact walk_gcBody τ) rfl
    (fun e he => (hs.1 e he).1) (by rw [hAD, hAL]; rfl)
    (fun q hq => by
      rw [hAA, List.mem_singleton] at hq
      subst hq
      exact t287)
    (by
      rw [hCA, hAL, List.sum_nil, Nat.add_zero]
      refine ⟨nl, 0, RegionL Lrun, RegionL [], (Nat.add_zero nl).symm, fun i hi => ?_, ?_,
        rfl, fun _ h => h.elim⟩
      · obtain ⟨q, hq, h1, h2⟩ := hi
        rw [hLrun, List.mem_singleton] at hq
        subst hq
        refine Or.inl (Or.inr (Or.inr ⟨(.n 34, 64), by rw [hRU]; exact List.mem_singleton_self _,
          h1, ?_⟩))
        simpa [gcBitsD] using h2
      · by_cases h0 : 0 < m
        · have hne : τ (.n 289) ≠ 0 := by
            rw [t289, hN]; intro h
            rw [e_add_eq_zero_iff, ← pow_zero gen] at h
            have := gen_pow_inj (by omega) (by decide) h.symm
            omega
          simp only [hne, ne_eq, not_false_eq_true, decide_true, ↓reduceIte, List.map_cons,
            List.map_nil, t290, t3, t287]
          exact hRl h0 rd hl (by rw [List.nil_append]; exact Main.memL_append.mpr ⟨hLl, hRun⟩)
        · have hz : τ (.n 289) = 0 := by
            rw [t289, hN, show m = 0 by omega, pow_zero]; exact e_add_self 1
          simp only [hz, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
          exact hnl (by omega))
    (fun A hA => by rw [hLA] at hA; exact absurd hA (List.not_mem_nil))
    (fun i hi => by obtain ⟨q, hq, _⟩ := hi; simp at hq)
  rwa [hAL, List.sum_nil, Nat.add_zero] at h

end
end LeanVM.Guest.B1
