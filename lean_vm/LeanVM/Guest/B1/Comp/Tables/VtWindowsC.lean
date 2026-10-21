/-
  LeanVM.Guest.B1.Comp.Tables.VtWindowsC

  `verify_tables`' windows that hash, over a completeness model: the memory block, the pull side,
  the table sumcheck, a column evaluation and the tail.
-/

module

public import LeanVM.Guest.B1.Comp.Tables.VtLoopsC
public import LeanVM.Guest.B1.Comp.Tables.VtTraceC
public import LeanVM.Guest.B1.Tables.VtCGlue4
public import LeanVM.Guest.B1.Tables.VtCEv
public import LeanVM.Guest.B1.Tables.VtZcC
public import LeanVM.Guest.B1.Tables.VerifyTablesCTail
public import LeanVM.Guest.B1.Tables.VerifyTablesBaseM

/-!
# `verify_tables`' hashing windows over a completeness model

The windows of `verify_tables` holding a `BLAKE2S` (an `fs_next` or a `squeeze` item), forward over
the items at a completeness model's total hash (`completes_itemsC`), their absorbs and squeezes
answered: `vt_glue2C` (`vt_glue2_of`: the three memory words), `vt_glue4C` (`vt_glue4`: the two
final counters), `vt_ev_completeC` (`vt_ev_complete`: a column evaluation), `vt_zc_completeC`
(`vt_zc_complete`: `ξ` and the rounds, `__loop79` over the model), `vt_c_tailC` (`vt_c_tail`: the
public input's challenge). Their calls of functions free of `BLAKE2S` are the deployed ones
(`relB_vtFree`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Sig LeanVM.E2E.Complete

@[expose] public section

/-! ## An `fs_next` item over a completeness model -/

/-- **An `fs_next` item's values at the total hash** (`vtc_fs_vals`). -/
theorem vtc_fs_valsC {M : HashModel} {rd : Reader} {hv : ℕ → E} {σf : Val} {s0 s1 cur : V}
    {j b : ℕ} (h : FEq.HoldsC M rd hv σf (.item (.fs s0 s1 cur j b))) {cv : Digest}
    (hcv : (σf s0, σf s1) = digestScalars cv) {w : E} (hw : LoadHolds rd (σf cur) j w) :
    σf (.n b) = w ∧ (σf (.n (b + 13)), σf (.n (b + 14))) = digestScalars (obsCvT M cv w) := by
  have hdec : decodeCv (σf s0) (σf s1) = cv :=
    digestScalars_injective ((decodeCv_spec ⟨cv, hcv⟩).symm.trans hcv)
  have e0 := h 0 (by simp [FItem.sets]) (by simp [FItem.valsC])
  simp only [FItem.sets, FItem.valsC, List.getElem_map, List.getElem_range, List.getElem_cons_zero,
    Nat.add_zero] at e0
  have ek : ∀ k < 14, σf (.n (b + (k + 1))) = fsValsD w (obsCvT M cv w) 1 k := fun k hk => by
    have := h (k + 1) (by simp [FItem.sets]; omega) (by simp [FItem.valsC]; omega)
    simp only [FItem.sets, FItem.valsC, List.getElem_map, List.getElem_range,
      List.getElem_cons_succ] at this
    rw [this, hdec, memAt_of_loadHolds hw]
  refine ⟨by rw [e0, memAt_of_loadHolds hw], ?_⟩
  rw [show b + 13 = b + (12 + 1) by ring, show b + 14 = b + (13 + 1) by ring, ek 12 (by omega),
    ek 13 (by omega)]
  rfl

/-- An `fs_next` item's obligation over a completeness model (`vtc_fs_ob`). -/
theorem vtc_fs_obC {M : HashModel} {C : CallRel} {rd : Reader} {σf : Val} {s0 s1 cur : V} {j : ℕ}
    {cv : Digest} {w : E} (hcv : (σf s0, σf s1) = digestScalars cv)
    (hw : LoadHolds rd (σf cur) j w) (hans : obsCvM M cv w = some (obsCvT M cv w)) :
    IOb.HoldsC M C rd σf (.fs s0 s1 cur j) :=
  ⟨hw.1, isSome_of_loadHolds hw, cv, hcv, by rw [memAt_of_loadHolds hw]; exact hans⟩

theorem vtc_fpw_obC {M : HashModel} {C : CallRel} {rd : Reader} {σf : Val} {fpw : E}
    (h11 : σf (.n 11) = fpw) (hfpw : ∀ i < 16, ∃ v, LoadHolds rd fpw i v) {i : ℕ} (hi : i < 16) :
    IOb.HoldsC M C rd σf (.ob (.ld (.n 11) i)) :=
  vtc_fpw_ob (C := C) h11 hfpw hi

theorem vtc_ld_obC {M : HashModel} {C : CallRel} {rd : Reader} {σf : Val} {p : V} {off : ℕ} {w : E}
    (h : LoadHolds rd (σf p) off w) : IOb.HoldsC M C rd σf (.ob (.ld p off)) :=
  vtc_ld_ob (C := C) h

/-! ## The memory block -/

set_option maxHeartbeats 1000000 in
/-- **The memory block completes over a completeness model** (`vt_glue2_of`), its log-size at
most `32`, the three words' absorbs answered. -/
theorem vt_glue2C {CM : CompModel} {rd : Reader} {σ : Val} {cur fpw pool cplen zeta idxc bim pI m0 m1 m2 : E}
    {point : List E} {logMem : ℕ} {cv : Digest}
    (h2 : σ (.n 2) = cur) (h5 : σ (.n 5) = zeta) (h11 : σ (.n 11) = fpw) (h13 : σ (.n 13) = pool)
    (h14 : σ (.n 14) = cplen) (h1817 : σ (.n 1817) = idxc) (h1852 : σ (.n 1852) = bim)
    (h1893 : σ (.n 1893) = gen ^ logMem) (hcv : (σ (.n 19), σ (.n 20)) = digestScalars cv)
    (hl0 : 0 < logMem) (hlp : logMem ≤ point.length) (hz : ReadsAt rd zeta point)
    (hidx : ∀ t < 34, LoadHolds rd idxc t (1 + gen ^ 2 ^ t)) (hpI : ReadsAt rd pI (idxChainW point logMem))
    (hbim : LoadHolds rd bim 1 ((idxChainW point logMem).getD logMem 0))
    (hfpw : ∀ i < 16, ∃ v, LoadHolds rd fpw i v) (hcur : ReadsAt rd cur [m0, m1, m2])
    (hpool : ReadsAt rd pool [m0, m1, m2]) (hcpl : ∀ j < 3, LoadHolds rd cplen j (gen ^ logMem))
    (hl32 : logMem ≤ 32) (hA : ObsAns CM.hm cv [m0, m1, m2]) :
    CompletesB CM.sem (coreProgram.RelB CM.sem rd) rd 1920 1997 ((vtPre.drop 1644).take 80) σ (fun σ' =>
      σ' (.n 1925) = pI ∧ σ' (.n 1937) = m0 ∧ σ' (.n 1955) = m1 ∧ σ' (.n 1973) = m2 ∧
        (σ' (.n 1986), σ' (.n 1987)) = digestScalars (obsAllT CM.hm cv [m0, m1, m2])) := by
  rw [← vtcG2_eq]
  have Cm := completes_itemsC (CM := CM) (C := coreProgram.RelB CM.sem rd) (rd := rd) (fun _ => pI) vtcG2 vtcG2_ok σ
  generalize hσf : fRunIC CM.hm rd 1920 (fun _ => pI) [] σ vtcG2 = σf at Cm
  have hf : ∀ u, fRunIC CM.hm rd 1920 (fun _ => pI) [] σ vtcG2 u = σf u := fun u => by rw [hσf]
  have E := fRunIC_eqs rd (fun _ => pI) σf vtcG2 [] σ vtcG2_ok hf
  have FR : ∀ k < 1920, σf (.n k) = σ (.n k) := fun k hk =>
    fRunIC_eq_of_def rd _ vtcG2_ok hf (by simp [fDef, vNum, hk])
  have hB := vtcG2_eqsB
  simp only [List.all_eq_true] at hB
  have Ed := fun e (he : e ∈ vtcG2Eq) => E e (mem_of_any feqEqb_sound (hB e he))
  simp only [vtcG2Eq, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at Ed
  obtain ⟨d25, d26, d27, d28, d29, d30, d31, f1, f2, f3⟩ := Ed
  have e25 : σf (.n 1925) = pI := by
    have := d25 0 (by show 0 < 1; omega) (by show 0 < 1; omega)
    simpa [FItem.sets, FItem.valsC, hintCells] using this
  have e1893 : σf (.n 1893) = gen ^ logMem := by rw [FR 1893 (by omega), h1893]
  have e2 : σf (.n 2) = cur := by rw [FR 2 (by omega), h2]
  have L : ∀ t < 42, LoadHolds rd pI t ((idxChainW point logMem).getD t 0) := fun t ht =>
    vtc_reads_getD hpI (by rw [vtc_idxW_length]; exact ht)
  have M : LoadHolds rd (pI * gen ^ logMem) 0 ((idxChainW point logMem).getD logMem 0) :=
    loadHolds_gen_pow_mul.mpr (by rw [Nat.add_zero]; exact L logMem (by omega))
  have e30 : σf (.n 1930) = pI * gen ^ logMem := by
    rw [show σf (.n 1930) = σf (.n 1925) * σf (.n 1893) from d30, e25, e1893]
  have e31 : σf (.n 1931) = (idxChainW point logMem).getD logMem 0 := by
    rw [show σf (.n 1931) = memAt rd (σf (.n 1930)) 0 from d31, e30, memAt_of_loadHolds M]
  have c0 : LoadHolds rd (σf (.n 2)) 0 m0 := by rw [e2]; simpa using hcur 0 (by simp)
  have c1 : LoadHolds rd (σf (.n 2)) 1 m1 := by rw [e2]; simpa using hcur 1 (by simp)
  have c2 : LoadHolds rd (σf (.n 2)) 2 m2 := by rw [e2]; simpa using hcur 2 (by simp)
  have hcv' : (σf (.n 19), σf (.n 20)) = digestScalars cv := by rw [FR 19 (by omega), FR 20 (by omega)]; exact hcv
  have F1 := vtc_fs_valsC f1 hcv' c0
  have F2 := vtc_fs_valsC f2 F1.2 c1
  have F3 := vtc_fs_valsC f3 F2.2 c2
  have e13 : σf (.n 13) = pool := by rw [FR 13 (by omega), h13]
  have e14 : σf (.n 14) = cplen := by rw [FR 14 (by omega), h14]
  refine (Cm (IOblsC_of_obs _ _ ?_)).mono le_rfl le_rfl fun σ' h => ?_
  · rw [vtcG2_obs]
    intro o ho
    simp only [vtcG2Ob, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
    all_goals first | exact vtc_fpw_obC (by rw [FR 11 (by omega), h11]) hfpw (by norm_num) | skip
    · simp only [IOb.HoldsC, Ob.Holds, Atom.Holds]
      rw [e25, show σf (.n 1926) = word 1 0 0 from d26, word_one]
      have := L 0 (by omega)
      rwa [vtc_idxW_getD point (t := 0) (κ := logMem) (by omega) (by omega), Finset.prod_range_zero] at this
    · simp only [IOb.HoldsC, List.map_cons, List.map_nil]
      rw [show σf (.n 1928) = σf (.n 1927) + σf (.n 1893) from d28, show σf (.n 1927) = word 1 0 0 from d27,
        e1893, show σf (.n 1929) = word 1 0 0 from d29, e25, FR 5 (by omega), h5, FR 1817 (by omega), h1817,
        word_one]
      refine ⟨isInK_add (by simpa using gen_pow_isInK 0) (gen_pow_isInK logMem), fun _ => ?_⟩
      exact (relB_vtFree (by decide) _ _).mpr
        (idx_complete idx_ok.1 hl0 rfl fun j hj => vtc_idxBody_honest hz hidx hpI hj (by omega) (by omega))
    · simp only [IOb.HoldsC, Ob.Holds]; rw [e30]; exact ⟨M.1, isSome_of_loadHolds M⟩
    · simp only [IOb.HoldsC, Ob.Holds, Atom.Holds]
      rw [e31, FR 1852 (by omega), h1852]; exact hbim
    · exact vtc_fs_obC hcv' c0 (hA 0 (by simp))
    · simp only [IOb.HoldsC, Ob.Holds, Atom.Holds]
      rw [e13, F1.1]; simpa using hpool 0 (by simp)
    · simp only [IOb.HoldsC, Ob.Holds, Atom.Holds]; rw [e14, e1893]; exact hcpl 0 (by omega)
    · exact vtc_fs_obC F1.2 c1 (hA 1 (by simp))
    · simp only [IOb.HoldsC, Ob.Holds, Atom.Holds]
      rw [e13, F2.1]; simpa using hpool 1 (by simp)
    · simp only [IOb.HoldsC, Ob.Holds, Atom.Holds]; rw [e14, e1893]; exact hcpl 1 (by omega)
    · exact vtc_fs_obC F2.2 c2 (hA 2 (by simp))
    · simp only [IOb.HoldsC, Ob.Holds, Atom.Holds]
      rw [e13, F3.1]; simpa using hpool 2 (by simp)
    · simp only [IOb.HoldsC, Ob.Holds, Atom.Holds]; rw [e14, e1893]; exact hcpl 2 (by omega)
  · rw [h]
    exact ⟨e25, F1.1, F2.1, F3.1, F3.2⟩

/-! ## The pull side -/

set_option maxHeartbeats 1000000 in
/-- **The push side's padding and the pull side complete over a completeness model**
(`vt_glue4`), the two final counters' absorbs answered. -/
theorem vt_glue4C {CM : CompModel} (κ : ℕ) (hκ : 6 ≤ κ) (rd : Reader) (hlow : LowDef κ rd)
    (σ : Val) (cur bk fpw pool cplen bim mF bF : E) (ks : ℕ → ℕ) (cv : Digest)
    (h2 : σ (.n 2) = cur) (h9 : σ (.n 9) = bk) (h11 : σ (.n 11) = fpw) (h13 : σ (.n 13) = pool)
    (h14 : σ (.n 14) = cplen) (h1852 : σ (.n 1852) = bim)
    (hcv : (σ (.n 1986), σ (.n 1987)) = digestScalars cv)
    (hbk : ∀ b < 102, LoadHolds rd bk b (gen ^ ks b)) (hks : ∀ b < 102, ks b < 34)
    (hfpw : ∀ i < 16, ∃ v, LoadHolds rd fpw i v) (hmF : LoadHolds rd cur 3 mF)
    (hbF : LoadHolds rd cur 4 bF) (hpool : ∀ j < 3, ∃ v, LoadHolds rd pool j v)
    (hpm : LoadHolds rd pool 3 mF) (hpb : LoadHolds rd pool 4 bF)
    (hc3 : LoadHolds rd cplen 3 (gen ^ ks 38)) (hc4 : LoadHolds rd cplen 4 (gen ^ ks 39))
    (hb1 : ∃ v, LoadHolds rd bim 1 v) (hb2 : ∃ v, LoadHolds rd bim 2 v)
    (hA : ObsAns CM.hm cv [mF, bF]) :
    CompletesB CM.sem (coreProgram.RelB CM.sem rd) rd 3061 3706 ((vtPre.drop 2826).take 571) σ
      (fun σ' => σ' (.n 3359) = mF ∧ σ' (.n 3409) = bF ∧
        (σ' (.n 3422), σ' (.n 3423)) = digestScalars (obsCvT CM.hm (obsCvT CM.hm cv mF) bF)) := by
  rw [← vtcG4_eq]
  have Cm := completes_itemsC (CM := CM) (C := coreProgram.RelB CM.sem rd) (rd := rd) (fun _ => 0) vtcG4 vtcG4_ok σ
  generalize hσf : fRunIC CM.hm rd 3061 (fun _ => 0) [] σ vtcG4 = σf at Cm
  have hf : ∀ u, fRunIC CM.hm rd 3061 (fun _ => 0) [] σ vtcG4 u = σf u := fun u => by rw [hσf]
  have E := fRunIC_eqs rd (fun _ => 0) σf vtcG4 [] σ vtcG4_ok hf
  have FR : ∀ k < 3061, σf (.n k) = σ (.n k) := fun k hk =>
    fRunIC_eq_of_def rd _ vtcG4_ok hf (by simp [fDef, vNum, hk])
  have h2k : 64 ≤ 2 ^ κ := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hκ)
  have e9 : σf (.n 9) = bk := by rw [FR 9 (by omega), h9]
  have RC : ∀ p ∈ vtcG4Rc, p.2 < 102 ∧ σf (.n p.1) = gen ^ ks p.2 ∧
      σf (.n (p.1 + 2)) = gen ^ (33 - ks p.2) := by
    intro p hp
    have h := List.all_eq_true.mp vtcG4_rcB p hp
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
    obtain ⟨hb, he⟩ := h
    have Ep := fun e (h' : e ∈ vtcG4RcEq p) => E e (mem_of_any feqEqb_sound (he e h'))
    simp only [vtcG4RcEq, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at Ep
    obtain ⟨l, c, r⟩ := Ep
    have ex : σf (.n p.1) = gen ^ ks p.2 := by
      rw [show σf (.n p.1) = memAt rd (σf (.n 9)) p.2 from l, e9, memAt_of_loadHolds (hbk p.2 hb)]
    refine ⟨hb, ex, ?_⟩
    rw [r.1, show σf (.n (p.1 + 1)) = word 8589934592 0 0 from c, ex,
      show (8589934592 : ℕ) = 2 ^ 33 by norm_num, word_two_pow (by norm_num)]
    exact gen_pow_div (by have := hks p.2 hb; omega)
  have hFS := vtcG4_fsB
  simp only [Bool.and_eq_true] at hFS
  have f1 := E _ (mem_of_any feqEqb_sound hFS.1)
  have f2 := E _ (mem_of_any feqEqb_sound hFS.2)
  have e2 : σf (.n 2) = cur := by rw [FR 2 (by omega), h2]
  have hcv' : (σf (.n 1986), σf (.n 1987)) = digestScalars cv := by
    rw [FR 1986 (by omega), FR 1987 (by omega)]; exact hcv
  have cF : LoadHolds rd (σf (.n 2)) 3 mF := by rw [e2]; exact hmF
  have cB : LoadHolds rd (σf (.n 2)) 4 bF := by rw [e2]; exact hbF
  have F1 := vtc_fs_valsC f1 hcv' cF
  have F2 := vtc_fs_valsC f2 F1.2 cB
  have e13 : σf (.n 13) = pool := by rw [FR 13 (by omega), h13]
  have e14 : σf (.n 14) = cplen := by rw [FR 14 (by omega), h14]
  have r38 := RC (3345, 38) (by simp [vtcG4Rc])
  have r39 := RC (3395, 39) (by simp [vtcG4Rc])
  refine (Cm (IOblsC_of_obs _ _ ?_)).mono le_rfl le_rfl fun σ' h => ?_
  · intro o ho
    have h := List.all_eq_true.mp vtcG4_obs o ho
    simp only [vtcG4Ok, Bool.or_eq_true, List.any_eq_true, List.mem_range] at h
    rcases h with ⟨i, hi, he⟩ | ⟨b, hb, he⟩ | ⟨p, hp, he⟩ | ⟨j, hj, he⟩ | he | he | he | he | he | he | he | he <;>
      obtain rfl := iobEqb_sound he
    · exact vtc_fpw_obC (by rw [FR 11 (by omega), h11]) hfpw hi
    · exact vtc_ld_obC (by rw [e9]; exact hbk b hb)
    · obtain ⟨hb, ex, ey⟩ := RC p hp
      simp only [IOb.HoldsC, Ob.Holds]
      rw [ex, ey]
      have a := low_gen_pow hlow (i := ks p.2) (by have := hks p.2 hb; omega)
      have c := low_gen_pow hlow (i := 33 - ks p.2) (by omega)
      exact ⟨gen_pow_ne_zero _, a.1, a.2, c.1, c.2⟩
    · obtain ⟨w, hw⟩ := hpool j hj
      exact vtc_ld_obC (by rw [e13]; exact hw)
    · obtain ⟨w, hw⟩ := hb1
      exact vtc_ld_obC (by rw [FR 1852 (by omega), h1852]; exact hw)
    · obtain ⟨w, hw⟩ := hb2
      exact vtc_ld_obC (by rw [FR 1852 (by omega), h1852]; exact hw)
    · exact vtc_fs_obC hcv' cF (hA 0 (by simp))
    · exact vtc_fs_obC F1.2 cB (hA 1 (by simp))
    · simp only [IOb.HoldsC, Ob.Holds, Atom.Holds]; rw [e13, F1.1]; exact hpm
    · simp only [IOb.HoldsC, Ob.Holds, Atom.Holds]; rw [e14, r38.2.1]; exact hc3
    · simp only [IOb.HoldsC, Ob.Holds, Atom.Holds]; rw [e13, F2.1]; exact hpb
    · simp only [IOb.HoldsC, Ob.Holds, Atom.Holds]; rw [e14, r39.2.1]; exact hc4
  · rw [h]
    exact ⟨F1.1, F2.1, F2.2⟩


/-! ## A column evaluation -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- **A column evaluation completes over a completeness model** (`vt_ev_complete`), its absorb
answered. -/
theorem vt_ev_completeC {CM : CompModel} (j : ℕ) (hj : j < 104) (rd : Reader) (σ : Val)
    (cur pool cplen w g : E) (cv : Digest) (h4651 : σ (.n 4651) = cur) (h13 : σ (.n 13) = pool)
    (h14 : σ (.n 14) = cplen) (hτ : σ (.n (evTau.getD j 0)) = g)
    (hcv : (σ (.n (if j = 0 then 4649 else evVal.getD (j - 1) 0 + 13)),
      σ (.n ((if j = 0 then 4649 else evVal.getD (j - 1) 0 + 13) + 1))) = digestScalars cv)
    (hw : LoadHolds rd cur j w) (hpool : LoadHolds rd pool (5 + j) w)
    (hcplen : LoadHolds rd cplen (5 + j) g) (hans : obsCvM CM.hm cv w = some (obsCvT CM.hm cv w)) :
    CompletesB CM.sem (coreProgram.RelB CM.sem rd) rd (evVal.getD j 0) (evVal.getD j 0 + 16)
      ((vtPre.drop (evStmt.getD j 0)).take 16) σ (fun σ' =>
        σ' (.n (evVal.getD j 0)) = w ∧ σ' (.n (evVal.getD j 0 + 15)) = w ∧
          (σ' (.n (evVal.getD j 0 + 13)), σ' (.n (evVal.getD j 0 + 14))) =
            digestScalars (obsCvT CM.hm cv w)) := by
  have hst := stmtsEqb_sound (ev_blocks j hj)
  have hok := vtEv_ok j hj
  have hobs := listEqb_sound iobEqb_sound (vtEv_obsB j hj)
  have heqs := vtEv_eqsB j hj
  obtain ⟨l1, l2, l3⟩ := vtEv_lt j hj
  rw [← hst, ← vtEvI_stmts]
  change (σ (.n (evS j)), σ (.n (evS j + 1))) = digestScalars cv at hcv
  generalize evVal.getD j 0 = v at *
  generalize evS j = s at *
  generalize evTau.getD j 0 = τv at *
  have Cm := completes_itemsC (CM := CM) (C := coreProgram.RelB CM.sem rd) (rd := rd) (fun _ => 0) (vtEvI j v s τv) hok σ
  generalize hσf : fRunIC CM.hm rd v (fun _ => 0) [] σ (vtEvI j v s τv) = σf at Cm
  have hf : ∀ u, fRunIC CM.hm rd v (fun _ => 0) [] σ (vtEvI j v s τv) u = σf u := fun u => by rw [hσf]
  have E := fRunIC_eqs rd (fun _ => 0) σf (vtEvI j v s τv) [] σ hok hf
  have FR : ∀ n < v, σf (.n n) = σ (.n n) := fun n hn =>
    fRunIC_eq_of_def rd _ hok hf (by simp [fDef, vNum, hn])
  have hB := heqs
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hB
  have dfs := E _ (mem_of_any feqEqb_sound hB.1)
  have dcp : σf (.n (v + 15)) = σf (.n v) := E _ (mem_of_any feqEqb_sound hB.2)
  have hdec : decodeCv (σf (.n s)) (σf (.n (s + 1))) = cv := by
    rw [FR s (by omega), FR (s + 1) (by omega)]
    exact digestScalars_injective ((decodeCv_spec ⟨cv, hcv⟩).symm.trans hcv)
  have e0 : σf (.n v) = w := by
    have := dfs 0 (by simp [FItem.sets]) (by simp [FItem.valsC])
    simp only [FItem.sets, FItem.valsC, List.getElem_map, List.getElem_range, List.getElem_cons_zero,
      Nat.add_zero] at this
    rw [this, FR 4651 (by omega), h4651, memAt_of_loadHolds hw]
  have ek : ∀ k < 14, σf (.n (v + (k + 1))) = fsValsD w (obsCvT CM.hm cv w) 1 k := fun k hk => by
    have := dfs (k + 1) (by simp [FItem.sets]; omega) (by simp [FItem.valsC]; omega)
    simp only [FItem.sets, FItem.valsC, List.getElem_map, List.getElem_range, List.getElem_cons_succ] at this
    rw [this, hdec, FR 4651 (by omega), h4651, memAt_of_loadHolds hw]
  refine (Cm (IOblsC_of_obs _ _ ?_)).mono le_rfl le_rfl ?_
  · rw [hobs]
    intro o ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl
    · simp only [IOb.HoldsC]
      rw [FR 4651 (by omega), h4651, FR s (by omega), FR (s + 1) (by omega)]
      exact ⟨hw.1, isSome_of_loadHolds hw, cv, hcv, by rw [memAt_of_loadHolds hw]; exact hans⟩
    · simp only [IOb.HoldsC, Ob.Holds, Atom.Holds]
      rw [FR 13 (by omega), h13, e0]; exact hpool
    · simp only [IOb.HoldsC, Ob.Holds, Atom.Holds]
      rw [FR 14 (by omega), h14, FR τv (by omega), hτ]; exact hcplen
  · intro σ' h
    rw [h]
    refine ⟨e0, by rw [dcp, e0], ?_⟩
    rw [show v + 13 = v + (12 + 1) by ring, show v + 14 = v + (13 + 1) by ring, ek 12 (by omega),
      ek 13 (by omega)]
    rfl


/-! ## The table sumcheck -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **The table sumcheck's window completes over a completeness model** (`vt_zc_complete`):
its squeeze and its rounds' runs answered, `__loop79`'s rounds the model's. -/
theorem vt_zc_completeC {CM : CompModel} (κ : ℕ) (hκ : 6 ≤ κ) (rd : Reader) (hlow : LowDef κ rd)
    (σ : Val) (dims chiP zeta cur pR pC pP T0 T1 T2 : E) (point chis : List E) (τs : ℕ → ℕ) (n : ℕ)
    (cvB : Digest) (cl : ℕ → E) (cvr : ℕ → Digest) (wsr : ℕ → List E) (ch : ℕ → E)
    (h7 : σ (.n 7) = dims) (h6 : σ (.n 6) = gen ^ point.length) (h2 : σ (.n 2) = cur)
    (h15 : σ (.n 15) = chiP) (h5 : σ (.n 5) = zeta) (hcv : (σ (.n 3422), σ (.n 3423)) = digestScalars cvB)
    (h3326 : σ (.n 3326) = T0) (h3705 : σ (.n 3705) = T1) (h4553 : σ (.n 4553) = T2)
    (hdims : ∀ t < 6, LoadHolds rd dims (t + 1) (gen ^ τs t)) (hτn : ∀ t < 6, τs t ≤ n)
    (hτmax : ∃ t < 6, τs t = n) (hnμ : n ≤ point.length) (hμ33 : point.length < 33)
    (hzeta : ReadsAt rd zeta point) (hchiP : ReadsAt rd chiP chis)
    (hchis : chis = ((List.range n).map ch).reverse)
    (hcl0 : cl 0 = challengeOf (sqCvT CM.hm cvB) ^ 2 * T0 + challengeOf (sqCvT CM.hm cvB) ^ 3 * T1 +
      challengeOf (sqCvT CM.hm cvB) ^ 4 * T2)
    (hcvr0 : cvr 0 = sqCvT CM.hm cvB)
    (hruns : ∀ r < n, RunsToM CM.hm (roundPoly 4 (cl r) none) (cvr r) (wsr r) (cl (r + 1), ch r)
      (cvr (r + 1)))
    (hws : ReadsAt rd (cur * gen ^ 5) ((List.range n).flatMap wsr))
    (hR : ReadsAt rd pR (zcRoundsW cvr cur cl n)) (hC : ReadsAt rd pC (zcCprodW ch n))
    (hP : ReadsAt rd pP (zcPeqW point chis n)) (hq : sqCvM CM.hm cvB = some (sqCvT CM.hm cvB)) :
    CompletesB CM.sem (coreProgram.RelB CM.sem rd) rd 4554 4660 ((vtPre.drop 4273).take 101) σ
      (fun σ' => σ' (.n 4554) = gen ^ n ∧ σ' (.n 4621) = challengeOf (sqCvT CM.hm cvB) ∧
        (∀ k < 5, σ' (.n (4622 + k)) = challengeOf (sqCvT CM.hm cvB) ^ k) ∧
        σ' (.n 4636) = pR ∧ σ' (.n 4639) = pC ∧ σ' (.n 4655) = pP ∧
        (σ' (.n 4649), σ' (.n 4650)) = digestScalars (cvr n) ∧ σ' (.n 4651) = cur * gen ^ (5 + 3 * n) ∧
        σ' (.n 4652) = cl n) := by
  rw [← vtItZc_eq]
  have Cm := completes_itemsC (CM := CM) (C := coreProgram.RelB CM.sem rd) (rd := rd) (vtHvZc n pR pC pP) vtItZc
    vtItZc_ok σ
  generalize hσf : fRunIC CM.hm rd 4554 (vtHvZc n pR pC pP) [] σ vtItZc = σf at Cm
  have hf : ∀ v, fRunIC CM.hm rd 4554 (vtHvZc n pR pC pP) [] σ vtItZc v = σf v := fun v => by rw [hσf]
  have E := fRunIC_eqs rd (vtHvZc n pR pC pP) σf vtItZc [] σ vtItZc_ok hf
  have FR : ∀ k < 4554, σf (.n k) = σ (.n k) := fun k hk =>
    fRunIC_eq_of_def rd (vtHvZc n pR pC pP) vtItZc_ok hf (by simp [fDef, vNum, hk])
  have hB := vtItZc_eqsB
  have Ed := fun e (he : e ∈ vtItZcEq) => E e (mem_of_any feqEqb_sound (List.all_eq_true.mp hB e he))
  simp only [vtItZcEq, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at Ed
  obtain ⟨i4554, l4555, d4556, s4557, r4557, d4561, l4562, d4563, s4564, r4564, d4568, d4569, l4570,
    d4571, s4572, r4572, d4576, d4577, l4578, d4579, s4580, r4580, d4584, d4585, l4586, d4587, s4588,
    r4588, d4592, d4593, l4594, d4595, s4596, r4596, d4600, d4601, d4602, d4603, s4604, r4604, isq,
    d4622, d4623, d4624, d4625, d4626, d4627, d4628, d4629, d4630, d4631, d4632, d4633, d4634, d4635,
    i4636, d4637, d4638, i4639, d4640, d4641, d4642, d4643, d4644, d4645, -, d4646, d4647, d4648,
    l4649, l4650, l4651, l4652, d4653, d4654, i4655, d4656, d4657, d4658, d4659, -⟩ := Ed
  have ptr := fun (it : FItem) (hit : FEq.HoldsC CM.hm rd (vtHvZc n pR pC pP) σf (.item it)) (v : ℕ)
      (hs : it.sets = [.n v]) => hit 0 (by rw [hs]; simp) (by rw [FItem.valsC_length, hs]; simp)
  have v4554 : σf (.n 4554) = gen ^ n := by
    have := ptr _ i4554 4554 rfl
    simp only [FItem.sets, FItem.valsC, hintCells, List.getElem_cons_zero, List.map_cons,
      List.map_nil] at this
    rw [this]; simp [vtHvZc]
  have v4636 : σf (.n 4636) = pR := by
    have := ptr _ i4636 4636 rfl
    simp only [FItem.sets, FItem.valsC, hintCells, List.getElem_cons_zero, List.map_cons,
      List.map_nil] at this
    rw [this]; simp [vtHvZc]
  have v4639 : σf (.n 4639) = pC := by
    have := ptr _ i4639 4639 rfl
    simp only [FItem.sets, FItem.valsC, hintCells, List.getElem_cons_zero, List.map_cons,
      List.map_nil] at this
    rw [this]; simp [vtHvZc]
  have v4655 : σf (.n 4655) = pP := by
    have := ptr _ i4655 4655 rfl
    simp only [FItem.sets, FItem.valsC, hintCells, List.getElem_cons_zero, List.map_cons,
      List.map_nil] at this
    rw [this]; simp [vtHvZc]
  have f7 : σf (.n 7) = dims := by rw [FR 7 (by omega), h7]
  have hn32 : n ≤ 32 := by omega
  -- the six log-heights
  have blk : ∀ {L S C A : ℕ} (t : ℕ), t < 6 → σf (.n L) = memAt rd (σf (.n 7)) (t + 1) →
      σf (.n S) = σf (.n 4554) * (σf (.n L))⁻¹ →
      σf (.n (S + 1)) = σf (.n C) * (σf (.n S))⁻¹ → σf (.n C) = word 4294967296 0 0 →
      σf (.n A) = σf (.n 4554) + σf (.n L) →
      σf (.n L) = gen ^ τs t ∧ σf (.n S) = gen ^ (n - τs t) ∧
        σf (.n (S + 1)) = gen ^ (32 - (n - τs t)) ∧ σf (.n A) = gen ^ n + gen ^ τs t := by
    intro L S C A t ht hl hs hr hc ha
    have eL : σf (.n L) = gen ^ τs t := by rw [hl, f7, memAt_of_loadHolds (hdims t ht)]
    have eS : σf (.n S) = gen ^ (n - τs t) := by rw [hs, v4554, eL, gen_pow_div (hτn t ht)]
    refine ⟨eL, eS, ?_, by rw [ha, v4554, eL]⟩
    rw [hr, hc, word_g32, eS, gen_pow_div (by omega)]
  have B0 := blk 0 (by omega) l4555 s4557 r4557.1 d4556 d4561
  have B1 := blk 1 (by omega) l4562 s4564 r4564.1 d4563 d4568
  have B2 := blk 2 (by omega) l4570 s4572 r4572.1 d4571 d4576
  have B3 := blk 3 (by omega) l4578 s4580 r4580.1 d4579 d4584
  have B4 := blk 4 (by omega) l4586 s4588 r4588.1 d4587 d4592
  have B5 := blk 5 (by omega) l4594 s4596 r4596.1 d4595 d4600
  have v4601 : σf (.n 4601) = 0 := by
    have e : σf (.n 4601) = (gen ^ n + gen ^ τs 0) * (gen ^ n + gen ^ τs 1) * (gen ^ n + gen ^ τs 2) *
        (gen ^ n + gen ^ τs 3) * (gen ^ n + gen ^ τs 4) * (gen ^ n + gen ^ τs 5) := by
      have m69 : σf (.n 4569) = σf (.n 4561) * σf (.n 4568) := d4569
      have m77 : σf (.n 4577) = σf (.n 4569) * σf (.n 4576) := d4577
      have m85 : σf (.n 4585) = σf (.n 4577) * σf (.n 4584) := d4585
      have m93 : σf (.n 4593) = σf (.n 4585) * σf (.n 4592) := d4593
      have m01 : σf (.n 4601) = σf (.n 4593) * σf (.n 4600) := d4601
      rw [m01, m93, m85, m77, m69, B0.2.2.2, B1.2.2.2, B2.2.2.2, B3.2.2.2, B4.2.2.2, B5.2.2.2]
    obtain ⟨t, ht, htn⟩ := hτmax
    rw [e]
    interval_cases t <;> simp [htn, e_add_self]
  have v4602 : σf (.n 4602) = 0 := by rw [show σf (.n 4602) = word 0 0 0 from d4602, word_zero]
  have v4604 : σf (.n 4604) = gen ^ (point.length - n) := by
    rw [show σf (.n 4604) = σf (.n 6) * (σf (.n 4554))⁻¹ from s4604, FR 6 (by omega), h6, v4554,
      gen_pow_div hnμ]
  have v4605 : σf (.n 4605) = gen ^ (32 - (point.length - n)) := by
    rw [r4604.1, show σf (.n 4603) = word 4294967296 0 0 from d4603, word_g32, v4604,
      gen_pow_div (by omega)]
  -- the squeeze
  have hcvf : (σf (.n 3422), σf (.n 3423)) = digestScalars cvB := by
    rw [FR 3422 (by omega), FR 3423 (by omega)]; exact hcv
  have hdec : decodeCv (σf (.n 3422)) (σf (.n 3423)) = cvB :=
    digestScalars_injective ((decodeCv_spec ⟨cvB, hcvf⟩).symm.trans hcvf)
  have sq : ∀ k < 14, σf (.n (4608 + k)) = sqValsD (sqCvT CM.hm cvB) k := fun k hk => by
    have := isq k (by simp [FItem.sets]; exact hk) (by rw [FItem.valsC_length]; simp [FItem.sets]; exact hk)
    simp only [FItem.sets, FItem.valsC, List.getElem_map, List.getElem_range, hdec] at this
    exact this
  set ξ := challengeOf (sqCvT CM.hm cvB) with hξ
  have v4613 : σf (.n 4613) = (digestScalars (sqCvT CM.hm cvB)).1 := sq 5 (by omega)
  have v4614 : σf (.n 4614) = (digestScalars (sqCvT CM.hm cvB)).2 := sq 6 (by omega)
  have v4621 : σf (.n 4621) = ξ := sq 13 (by omega)
  have hpw : ∀ k < 5, σf (.n (4622 + k)) = ξ ^ k := by
    have p0 : σf (.n 4622) = 1 := by rw [show σf (.n 4622) = word 1 0 0 from d4622, word_one]
    have p1 : σf (.n 4623) = ξ := by
      rw [show σf (.n 4623) = σf (.n 4622) * σf (.n 4621) from d4623, p0, v4621, one_mul]
    have p2 : σf (.n 4624) = ξ ^ 2 := by
      rw [show σf (.n 4624) = σf (.n 4623) * σf (.n 4621) from d4624, p1, v4621]; ring
    have p3 : σf (.n 4625) = ξ ^ 3 := by
      rw [show σf (.n 4625) = σf (.n 4624) * σf (.n 4621) from d4625, p2, v4621]; ring
    have p4 : σf (.n 4626) = ξ ^ 4 := by
      rw [show σf (.n 4626) = σf (.n 4625) * σf (.n 4621) from d4626, p3, v4621]; ring
    intro k hk
    interval_cases k
    · simpa using p0
    · simpa using p1
    · exact p2
    · exact p3
    · exact p4
  have v4631 : σf (.n 4631) = cl 0 := by
    rw [show σf (.n 4631) = σf (.n 4629) + σf (.n 4630) from d4631,
      show σf (.n 4629) = σf (.n 4627) + σf (.n 4628) from d4629,
      show σf (.n 4627) = σf (.n 4624) * σf (.n 3326) from d4627,
      show σf (.n 4628) = σf (.n 4625) * σf (.n 3705) from d4628,
      show σf (.n 4630) = σf (.n 4626) * σf (.n 4553) from d4630, hpw 2 (by omega), hpw 3 (by omega),
      hpw 4 (by omega), FR 3326 (by omega), FR 3705 (by omega), FR 4553 (by omega), h3326, h3705,
      h4553, hcl0]
  have v4641 : σf (.n 4641) = cur * gen ^ 5 := by
    rw [show σf (.n 4641) = σf (.n 2) * σf (.n 4640) from d4641,
      show σf (.n 4640) = word 32 0 0 from d4640, word_g5, FR 2 (by omega), h2]
  have v4642 : σf (.n 4642) = 1 := by rw [show σf (.n 4642) = word 1 0 0 from d4642, word_one]
  have v4644 : σf (.n 4644) = 1 + gen ^ n := by
    rw [show σf (.n 4644) = σf (.n 4643) + σf (.n 4554) from d4644,
      show σf (.n 4643) = word 1 0 0 from d4643, word_one, v4554]
  have v4645 : σf (.n 4645) = 1 := by rw [show σf (.n 4645) = word 1 0 0 from d4645, word_one]
  have v4648 : σf (.n 4648) = pR * gen ^ (4 * n) := by
    rw [show σf (.n 4648) = σf (.n 4636) * σf (.n 4647) from d4648,
      show σf (.n 4647) = σf (.n 4646) * σf (.n 4646) from d4647,
      show σf (.n 4646) = σf (.n 4554) * σf (.n 4554) from d4646, v4636, v4554, ← pow_add, ← pow_add, show n + n + (n + n) = 4 * n by ring]
  have v4656 : σf (.n 4656) = 1 := by rw [show σf (.n 4656) = word 1 0 0 from d4656, word_one]
  have v4658 : σf (.n 4658) = 1 + gen ^ n := by
    rw [show σf (.n 4658) = σf (.n 4657) + σf (.n 4554) from d4658,
      show σf (.n 4657) = word 1 0 0 from d4657, word_one, v4554]
  have v4659 : σf (.n 4659) = 1 := by rw [show σf (.n 4659) = word 1 0 0 from d4659, word_one]
  have f15 : σf (.n 15) = chiP := by rw [FR 15 (by omega), h15]
  have f5 : σf (.n 5) = zeta := by rw [FR 5 (by omega), h5]
  -- the rounds' slots
  have hchl : chis.length = n := by rw [hchis]; simp
  have hwl : ∀ r < n, (wsr r).length = 3 := fun r hr => RunsToM.roundPoly4_len (hruns r hr)
  have slotN := zcRoundsW_get hR (r := n) le_rfl
  have hround : ∀ j < n, ZcRoundM CM.hm rd pR chiP (gen ^ n) pC (gen ^ j) := by
    intro j hj
    obtain ⟨o0, o1, o2, o3⟩ := zcRoundsW_get hR (r := j) (by omega)
    obtain ⟨o4, o5, o6, o7⟩ := zcRoundsW_get hR (r := j + 1) (by omega)
    obtain ⟨c0, c2, c3, hw⟩ : ∃ c0 c2 c3, wsr j = [c0, c2, c3] := by
      match h : wsr j, hwl j hj with
      | [a, b, c], _ => exact ⟨a, b, c, rfl⟩
    have hx4 : ∀ k w, LoadHolds rd pR (4 * j + k) w → LoadHolds rd (pR * (gen ^ j) ^ 4) k w := by
      intro k w h; rw [← pow_mul, loadHolds_mul_gen_pow, show j * 4 = 4 * j by ring]; exact h
    have hcur : ReadsAt rd (cur * gen ^ (5 + 3 * j)) [c0, c2, c3] := by
      intro k hk
      simp only [List.length_cons, List.length_nil] at hk
      have g := flatMapK_get 3 wsr n hwl j k hj (by omega)
      rw [hw, List.getElem?_eq_getElem (l := [c0, c2, c3]) (by simp; omega)] at g
      have := readsAt_get? hws g
      rw [pow_add, ← mul_assoc, loadHolds_mul_gen_pow]
      exact this
    have hq : gen ^ n * wInvG = gen ^ (n - 1 - j) * gen ^ j := by
      rw [← pow_add, show n - 1 - j + j = n - 1 by omega, show n = n - 1 + 1 by omega, pow_succ,
        mul_assoc, show gen * wInvG = 1 by rw [mul_comm]; exact wInvG_mul_gen, mul_one,
        Nat.add_sub_cancel]
    have hrk : LoadHolds rd (chiP * gen ^ (n - 1 - j)) 0 (ch j) := by
      apply ld_mul
      refine readsAt_get? hchiP ?_
      rw [hchis, List.getElem?_reverse (by simp; omega)]
      simp only [List.length_map, List.length_range, show n - 1 - (n - 1 - j) = j by omega,
        List.getElem?_map, List.getElem?_range hj, Option.map_some]
    have hc0 : LoadHolds rd (pC * gen ^ j) 0 (∏ i ∈ Finset.range j, ch i) :=
      ld_mul (readsAt_map_get hC (by omega))
    have hc1 : LoadHolds rd (pC * gen ^ j) 1 ((∏ i ∈ Finset.range j, ch i) * ch j) := by
      rw [loadHolds_mul_gen_pow, ← Finset.prod_range_succ]
      exact readsAt_map_get hC (by omega)
    refine ⟨cvr j, cur * gen ^ (5 + 3 * j), cl j, c0, c2, c3, cl (j + 1), ch j, cvr (j + 1),
      gen ^ (n - 1 - j), ∏ i ∈ Finset.range j, ch i, hx4 0 _ (by simpa using o0), hx4 1 _ o1,
      hx4 2 _ o2, hx4 3 _ o3, hcur, by rw [← hw]; exact hruns j hj, hq, hrk, hx4 4 _ ?_, hx4 5 _ ?_,
      hx4 6 _ ?_, hx4 7 _ ?_, hc0, hc1⟩
    · rw [show 4 * j + 4 = 4 * (j + 1) by ring]; exact o4
    · rw [show 4 * j + 5 = 4 * (j + 1) + 1 by ring]; exact o5
    · rw [show 4 * j + 6 = 4 * (j + 1) + 2 by ring, mul_assoc, ← pow_add,
        show 5 + 3 * j + 3 = 5 + 3 * (j + 1) by ring]; exact o6
    · rw [show 4 * j + 7 = 4 * (j + 1) + 3 by ring]; exact o7
  have hpeq : ∀ j < n, PeqBody rd pP zeta chiP (gen ^ j) := by
    intro j hj
    refine ⟨∏ i ∈ Finset.range j, (1 + point.getD i 0 + chis.getD i 0), point.getD j 0,
      chis.getD j 0, ld_mul (readsAt_map_get hP (by omega)),
      ld_mul (readsAt_getD0 hzeta (by omega)), ld_mul (readsAt_getD0 hchiP (by omega)), ?_⟩
    rw [loadHolds_mul_gen_pow, ← Finset.prod_range_succ]
    exact readsAt_map_get hP (by omega)
  refine (Cm (IOblsC_of_obs _ _ ?_)).mono le_rfl le_rfl ?_
  · rw [vtItZc_obs]
    have hdl : ∀ t < 6, Ob.Holds rd σf (.ld (.n 7) (t + 1)) := fun t ht => ob_ld_of f7 (hdims t ht)
    have hτ32 : ∀ t < 6, n - τs t < 2 ^ κ ∧ 32 - (n - τs t) < 2 ^ κ := fun t _ => by
      have : 64 ≤ 2 ^ κ := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hκ)
      omega
    have h64 : 64 ≤ 2 ^ κ := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hκ)
    intro o ho
    simp only [vtItZcOb, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
    · exact hdl 0 (by omega)
    · show σf _ ≠ 0; rw [B0.1]; exact gen_pow_ne_zero _
    · exact ob_rc_gen hlow B0.2.1 B0.2.2.1 (hτ32 0 (by omega)).1 (hτ32 0 (by omega)).2
    · exact hdl 1 (by omega)
    · show σf _ ≠ 0; rw [B1.1]; exact gen_pow_ne_zero _
    · exact ob_rc_gen hlow B1.2.1 B1.2.2.1 (hτ32 1 (by omega)).1 (hτ32 1 (by omega)).2
    · exact hdl 2 (by omega)
    · show σf _ ≠ 0; rw [B2.1]; exact gen_pow_ne_zero _
    · exact ob_rc_gen hlow B2.2.1 B2.2.2.1 (hτ32 2 (by omega)).1 (hτ32 2 (by omega)).2
    · exact hdl 3 (by omega)
    · show σf _ ≠ 0; rw [B3.1]; exact gen_pow_ne_zero _
    · exact ob_rc_gen hlow B3.2.1 B3.2.2.1 (hτ32 3 (by omega)).1 (hτ32 3 (by omega)).2
    · exact hdl 4 (by omega)
    · show σf _ ≠ 0; rw [B4.1]; exact gen_pow_ne_zero _
    · exact ob_rc_gen hlow B4.2.1 B4.2.2.1 (hτ32 4 (by omega)).1 (hτ32 4 (by omega)).2
    · exact hdl 5 (by omega)
    · show σf _ ≠ 0; rw [B5.1]; exact gen_pow_ne_zero _
    · exact ob_rc_gen hlow B5.2.1 B5.2.2.1 (hτ32 5 (by omega)).1 (hτ32 5 (by omega)).2
    · show σf (.n 4601) + σf (.n 4602) = 0; rw [v4601, v4602, add_zero]
    · show σf _ ≠ 0; rw [v4554]; exact gen_pow_ne_zero _
    · exact ob_rc_gen hlow v4604 v4605 (by omega) (by omega)
    · exact ⟨cvB, hcvf, hq⟩
    · show LoadHolds rd (σf (.n 4636)) 0 (σf (.n 4613))
      rw [v4636, v4613, ← hcvr0]; simpa using (zcRoundsW_get hR (r := 0) (by omega)).1
    · show LoadHolds rd (σf (.n 4636)) 1 (σf (.n 4614))
      rw [v4636, v4614, ← hcvr0]; simpa using (zcRoundsW_get hR (r := 0) (by omega)).2.1
    · show LoadHolds rd (σf (.n 4636)) 2 (σf (.n 4641))
      rw [v4636, v4641]; simpa using (zcRoundsW_get hR (r := 0) (by omega)).2.2.1
    · show LoadHolds rd (σf (.n 4636)) 3 (σf (.n 4631))
      rw [v4636, v4631]; simpa using (zcRoundsW_get hR (r := 0) (by omega)).2.2.2
    · show LoadHolds rd (σf (.n 4639)) 0 (σf (.n 4642))
      rw [v4639, v4642]
      simpa using readsAt_map_get hC (j := 0) (by omega)
    · refine ⟨by rw [v4644]; exact isInK_one_add_gen_pow n, fun hz => ?_⟩
      rw [v4644] at hz
      simp only [List.map_cons, List.map_nil]
      rw [v4645, v4554, v4636, f15, v4639]
      exact loop79_completeC (one_add_gen_pow hz) hround
    · exact ob_ld_of v4648 (ld_mul slotN.1)
    · exact ob_ld_of v4648 ((loadHolds_mul_gen_pow _ _ _ _ _).mpr slotN.2.1)
    · exact ob_ld_of v4648 ((loadHolds_mul_gen_pow _ _ _ _ _).mpr slotN.2.2.1)
    · exact ob_ld_of v4648 ((loadHolds_mul_gen_pow _ _ _ _ _).mpr slotN.2.2.2)
    · show LoadHolds rd (σf (.n 4655)) 0 (σf (.n 4656))
      rw [v4655, v4656]
      simpa using readsAt_map_get hP (j := 0) (by omega)
    · refine ⟨by rw [v4658]; exact isInK_one_add_gen_pow n, fun hz => ?_⟩
      rw [v4658] at hz
      simp only [List.map_cons, List.map_nil]
      rw [v4659, v4554, v4655, f5, f15]
      exact (relB_vtFree (by decide) _ _).mpr (loop80_complete (one_add_gen_pow hz) hpeq)
  · intro σ' h
    rw [h]
    have m49 : σf (.n 4649) = (digestScalars (cvr n)).1 := by
      rw [show σf (.n 4649) = memAt rd (σf (.n 4648)) 0 from l4649, v4648, memAt_of_loadHolds (ld_mul slotN.1)]
    have m50 : σf (.n 4650) = (digestScalars (cvr n)).2 := by
      rw [show σf (.n 4650) = memAt rd (σf (.n 4648)) 1 from l4650, v4648,
        memAt_of_loadHolds ((loadHolds_mul_gen_pow _ _ _ _ _).mpr slotN.2.1)]
    have m51 : σf (.n 4651) = cur * gen ^ (5 + 3 * n) := by
      rw [show σf (.n 4651) = memAt rd (σf (.n 4648)) 2 from l4651, v4648,
        memAt_of_loadHolds ((loadHolds_mul_gen_pow _ _ _ _ _).mpr slotN.2.2.1)]
    have m52 : σf (.n 4652) = cl n := by
      rw [show σf (.n 4652) = memAt rd (σf (.n 4648)) 3 from l4652, v4648,
        memAt_of_loadHolds ((loadHolds_mul_gen_pow _ _ _ _ _).mpr slotN.2.2.2)]
    exact ⟨v4554, v4621, hpw, v4636, v4639, v4655, by rw [m49, m50], m51, m52⟩


/-! ## The tail -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- **The tail completes over a completeness model** (`vt_c_tail`), its squeeze answered. -/
theorem vt_c_tailC {CM : CompModel} {rd : Reader} {σ : Val} {cvR : Digest}
    (hcv : (σ (.n 7569), σ (.n 7570)) = digestScalars cvR) (heq : σ (.n 8139) = σ (.n 4652))
    (hc3 : IsCanonical128 (σ (.n 3))) (hc4 : IsCanonical128 (σ (.n 4)))
    (h109 : LoadHolds rd (σ (.n 13)) 109 (ofK ((σ (.n 3)).limb 0) +
      challengeOf (sqCvT CM.hm cvR) * (ofK ((σ (.n 3)).limb 0) + ofK ((σ (.n 4)).limb 0))))
    (h110 : LoadHolds rd (σ (.n 13)) 110 (ofK ((σ (.n 3)).limb 1) +
      challengeOf (sqCvT CM.hm cvR) * (ofK ((σ (.n 3)).limb 1) + ofK ((σ (.n 4)).limb 1))))
    (h111 : LoadHolds rd (σ (.n 13)) 111 0) (hq : sqCvM CM.hm cvR = some (sqCvT CM.hm cvR)) :
    CompletesB CM.sem (coreProgram.RelB CM.sem rd) rd 8140 8179 ((vtPre.drop 7854).take 45) σ (fun σ' =>
      σ' (.n 8171) = (digestScalars (sqCvT CM.hm cvR)).1 ∧ σ' (.n 8172) = (digestScalars (sqCvT CM.hm cvR)).2 ∧
        σ' (.n 8175) = σ (.n 4651) * gen ^ 104 ∧ σ' (.n 8176) = σ (.n 4554) ∧
        σ' (.n 8177) = σ (.n 1732) ∧ σ' (.n 8178) = challengeOf (sqCvT CM.hm cvR)) := by
  rw [← vtItTail_eq]
  set hv := vtHvTail (σ (.n 3)) (σ (.n 4))
  have Cm := completes_itemsC (CM := CM) (C := coreProgram.RelB CM.sem rd) (rd := rd) hv vtItTail vtItTail_ok σ
  generalize hσf : fRunIC CM.hm rd 8140 hv [] σ vtItTail = σf at Cm
  have hf : ∀ v, fRunIC CM.hm rd 8140 hv [] σ vtItTail v = σf v := fun v => by rw [hσf]
  have E := fRunIC_eqs rd hv σf vtItTail [] σ vtItTail_ok hf
  have FR : ∀ k < 8140, σf (.n k) = σ (.n k) := fun k hk =>
    fRunIC_eq_of_def rd hv vtItTail_ok hf (by simp [fDef, vNum, hk])
  have hB := vtItTail_eqsB
  simp only [List.all_eq_true] at hB
  have F := fun e (he : e ∈ vtItTailEq) => E e (mem_of_any feqEqb_sound (hB e he))
  simp only [vtItTailEq, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at F
  obtain ⟨i7855, i7869, d8155, d8156, d8157, d8158, i7875, d8160, d8161, d8162, d8163, d8164, d8165,
    d8166, d8167, d8168, d8169, d8170, d8171, d8172, d8173, d8174, d8175, d8176, d8177, d8178⟩ := F
  simp only [FEq.HoldsC, FEq.Holds, Atom.Holds] at d8155 d8156 d8157 d8158 d8160 d8161 d8162 d8163 d8164 d8165
  simp only [FEq.HoldsC, FEq.Holds, Atom.Holds] at d8166 d8167 d8168 d8169 d8170 d8171 d8172 d8173 d8174 d8175
  simp only [FEq.HoldsC, FEq.Holds, Atom.Holds] at d8176 d8177 d8178
  have hdc : decodeCv (σf (.n 7569)) (σf (.n 7570)) = cvR := by
    rw [FR 7569 (by omega), FR 7570 (by omega)]
    have := decodeCv_spec ⟨cvR, hcv⟩
    rw [hcv] at this
    exact (digestScalars_injective this).symm
  have sq := fun k (hk : k < 14) => i7855 k (by simp [FItem.sets]; omega)
    (by simp [FItem.valsC]; omega)
  simp only [FItem.sets, FItem.valsC, List.getElem_map, List.getElem_range, hdc] at sq
  have s5 := sq 5 (by omega)
  have s6 := sq 6 (by omega)
  have s13 := sq 13 (by omega)
  simp only [sqValsD, sqStateValsD] at s5 s6 s13
  have l54 := i7869 0 (by show 0 < 1; omega) (by show 0 < 1; omega)
  have l59 := i7875 0 (by show 0 < 1; omega) (by show 0 < 1; omega)
  simp only [FItem.sets, FItem.valsC, hintCells, List.getElem_cons_zero, List.map_cons, List.map_nil] at l54 l59
  have e54 : σf (.n 8154) = ofK ((σ (.n 3)).limb 0) := by rw [l54]; simp [hv, vtHvTail]
  have e59 : σf (.n 8159) = ofK ((σ (.n 4)).limb 0) := by rw [l59]; simp [hv, vtHvTail]
  have e57 : σf (.n 8157) = ofK ((σ (.n 3)).limb 1) := by
    rw [d8157, d8155, d8156, FR 3 (by omega), e54, word_y_inv, split_hi hc3]
  have e62 : σf (.n 8162) = ofK ((σ (.n 4)).limb 1) := by
    rw [d8162, d8160, d8161, FR 4 (by omega), e59, word_y_inv, split_hi hc4]
  refine (Cm (IOblsC_of_obs _ _ ?_)).mono le_rfl le_rfl ?_
  · rw [vtItTail_obs]
    intro o ho
    simp only [vtItTailOb, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · show σf (.n 8139) + σf (.n 4652) = 0
      rw [FR 8139 (by omega), FR 4652 (by omega), heq]; exact e_add_self _
    · exact ⟨cvR, by rw [FR 7569 (by omega), FR 7570 (by omega)]; exact hcv, hq⟩
    · show IsInK (σf (.n 8154)) ∧ IsInK (σf (.n 8157))
      rw [e54, e57]; exact ⟨ofK_isInK _, ofK_isInK _⟩
    · show IsInK (σf (.n 8159)) ∧ IsInK (σf (.n 8162))
      rw [e59, e62]; exact ⟨ofK_isInK _, ofK_isInK _⟩
    · show LoadHolds rd (σf (.n 13)) 109 (σf (.n 8166))
      rw [d8166, d8165, d8164, d8158, d8163, e54, e59, s13, FR 13 (by omega)]; exact h109
    · show LoadHolds rd (σf (.n 13)) 110 (σf (.n 8169))
      rw [d8169, d8168, d8167, e57, e62, s13, FR 13 (by omega)]; exact h110
    · show LoadHolds rd (σf (.n 13)) 111 (σf (.n 8170))
      rw [d8170, word_zero, FR 13 (by omega)]; exact h111
  · intro σ' h; rw [h]
    refine ⟨by rw [d8171, s5], by rw [d8172, s6], ?_, by rw [d8176, FR 4554 (by omega)],
      by rw [d8177, FR 1732 (by omega)], by rw [d8178, s13]⟩
    rw [d8175, d8174, d8173, word_g104, FR 4651 (by omega)]


end
end LeanVM.Guest.B1.VerifySub
