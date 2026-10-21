/-
  LeanVM.Guest.B1.Comp.Da.Verify

  `da_verify` over a completeness model, from what its relation says of memory.
-/

module

public import LeanVM.Guest.B1.Comp.Da.Column
public import LeanVM.Guest.B1.Comp.Da.RowHash

/-!
# `da_verify` over a completeness model, from its facts

The backward half of `da_verify_facts` over a `CompModel` (`da_verify_of_facts`): `DaFactsC CM`
lists what `da_verify`'s body needs of memory, the columns over the model
(`Meaning_da_verify_columnComp CM`), the row digests and the trees over its answers
(`L93StepM CM.hm`, `Meaning_da_levelsWith CM.hm`), the root's row under its semantics; the
helpers free of `BLAKE2S` carry over (`relB_dv`'s converse). `dv_holdsC`, `da_verify_of_factsC`;
at `CompModel.deployed` the deployed backward direction (`da_verify_of_facts_of_comp`).
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.E2E.Complete

@[expose] public section

/-- `da_verify`'s helpers free of `BLAKE2S` have their deployed relation under any semantics,
backward. -/
theorem relB_dv_of {S : BlakeSem} {rd : Reader} {f : String}
    (hf : f ∈ ["da_row_shape", "__loop88", "__loop89", "__loop92", "__loop94"]) {args rets : List E}
    (h : coreProgram.Rel rd f args rets) : coreProgram.RelB S rd f args rets :=
  (relB_iff_rel_of_freeOn freeOn_dv hf args rets).mpr h

/-- One frame of a column loop under any semantics, backward (`colLoop_step`'s backward half). -/
theorem colLoop_step_bwdB {S : BlakeSem} (store : Bool) (rd : Reader) (ps : List E)
    (hps : ps.length = 9) (x : E) (hcall : coreProgram.RelB S rd (colName store) (x :: ps) [])
    (hk : IsInK (x * gen + colLoopEnd store))
    (hnext : x * gen + colLoopEnd store ≠ 0 →
      coreProgram.RelB S rd (colLoopName store) (x * gen :: ps) []) :
    ∃ fn, coreProgram.find? (colLoopName store) = some fn ∧
      fn.SemB S (coreProgram.RelB S rd) rd (x :: ps) [] := by
  match ps, hps with
  | [nb, np, gap, glp, pb, ct, rb, hs, ctr], _ =>
  refine ⟨_, find_colLoop store, ?_⟩
  simp only [Fn.SemB, colLoopBody, Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, List.map_cons,
    List.map_nil, word_gen]
  refine ⟨listVal [x, nb, np, gap, glp, pb, ct, rb, hs, ctr, gen, x * gen, colLoopEnd store,
    x * gen + colLoopEnd store, gen, x * gen], rfl, ?_⟩
  simp only [listVal, List.getD_cons_succ, List.getD_cons_zero, true_and]
  exact ⟨hcall, hk, hnext, trivial⟩

/-- **What `da_verify` needs of memory, over a completeness model** (`DaFacts`): the columns over
the model, the row digests and the trees over its answers, the root's row under its semantics. -/
def DaFactsC (CM : CompModel) (rd : Reader) (r0 r1 v0 v1 : E) : Prop :=
  ∃ (r : ℕ) (pb pd hs ctr acc rb ct rt rc0 rc1 rr0 rr1 : E),
    1 ≤ r ∧ r ≤ LeanDa.maxRows ∧
    (∀ i < r, L88Step rd pb pd (gen ^ i)) ∧
    LoadHolds rd hs 0 (digestScalars paramIv).1 ∧ LoadHolds rd hs 1 (digestScalars paramIv).2 ∧
    IsInK ctr ∧
    (∀ k < 385, ∀ w, rd (ctr.limb 0 * Parameters.gpow k) = some w → w = word (k * 2048) 0 0) ∧
    (∀ i < r, L89Step rd acc rb (gen ^ i)) ∧
    (∀ b < 128, Meaning_da_verify_columnComp CM (decide (b < 64)) rd
      [gen ^ b, gen ^ r, gen ^ LeanDa.nPad r, gen ^ (LeanDa.nPad r - r), gen ^ LeanDa.logPad r,
        pb, ct, rb, hs, ctr] []) ∧
    (∀ i < r, L92Step rd rb (gen ^ i)) ∧
    Meaning_da_levelsWith CM.hm 7 rd [ct] [rc0, rc1] ∧
    (∀ i < r, L93StepM CM.hm rd pb rt (gen ^ i)) ∧
    (∀ d < LeanDa.nPad r - r, L94Step rd rt (gen ^ r) (gen ^ d)) ∧
    Meaning_da_levelsWith CM.hm (LeanDa.logPad r) rd [rt] [rr0, rr1] ∧
    CM.sem.check ![rr0, rr1, rc0, rc1] (digestScalars paramIv).1 (digestScalars paramIv).2 r0 r1
      (metadataCell 64 true) ∧
    LoadHolds rd hs 256 v0 ∧ LoadHolds rd hs 257 v1

/-- **`da_verify`'s body holds over a completeness model** under its honest values, the pointers
given (`dv_holds`). -/
theorem dv_holdsC {CM : CompModel} {rd : Reader} (hl : Low16 rd) {gsq : E} (hT : SquaresAt rd gsq)
    {r0 r1 v0 v1 : E} {r : ℕ} {pb pd hs ctr acc rb ct rt rc0 rc1 rr0 rr1 : E}
    (hr1 : 1 ≤ r) (hr2 : r ≤ LeanDa.maxRows)
    (h88 : ∀ i < r, L88Step rd pb pd (gen ^ i))
    (hiv0 : LoadHolds rd hs 0 (digestScalars paramIv).1)
    (hiv1 : LoadHolds rd hs 1 (digestScalars paramIv).2) (hkc : IsInK ctr)
    (hctr : ∀ k < 385, ∀ w, rd (ctr.limb 0 * Parameters.gpow k) = some w → w = word (k * 2048) 0 0)
    (h89 : ∀ i < r, L89Step rd acc rb (gen ^ i))
    (hcol : ∀ b < 128, Meaning_da_verify_columnComp CM (decide (b < 64)) rd
      [gen ^ b, gen ^ r, gen ^ LeanDa.nPad r, gen ^ (LeanDa.nPad r - r), gen ^ LeanDa.logPad r,
        pb, ct, rb, hs, ctr] [])
    (h92 : ∀ i < r, L92Step rd rb (gen ^ i))
    (hlv7 : Meaning_da_levelsWith CM.hm 7 rd [ct] [rc0, rc1])
    (h93 : ∀ i < r, L93StepM CM.hm rd pb rt (gen ^ i))
    (h94 : ∀ d < LeanDa.nPad r - r, L94Step rd rt (gen ^ r) (gen ^ d))
    (hlvr : Meaning_da_levelsWith CM.hm (LeanDa.logPad r) rd [rt] [rr0, rr1])
    (hfin : CM.sem.check ![rr0, rr1, rc0, rc1] (digestScalars paramIv).1 (digestScalars paramIv).2
      r0 r1 (metadataCell 64 true))
    (hv0 : LoadHolds rd hs 256 v0) (hv1 : LoadHolds rd hs 257 v1) :
    Stmt.HoldsListB CM.sem (coreProgram.RelB CM.sem rd) rd (fun v => dvVals gsq (gen ^ r)
      (gen ^ LeanDa.logPad r) (gen ^ LeanDa.nPad r) (gen ^ (LeanDa.nPad r - r)) pd pb hs ctr acc rb
      ct rt rc0 rc1 rr0 rr1 r0 r1 v0 v1 v.idx) dvBody False (fun rs => rs = [r0, r1, v0, v1]) := by
  have hr33 : r < 2 ^ 33 := by unfold LeanDa.maxRows at hr2; omega
  have hlp := logPad_le hr2
  have hN := nPad_le hr2
  rw [dvBody, holdsListB_append, holdsListB_append, holdsListB_atoms']
  simp only [dvA, dvB, Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, List.map_cons, List.map_nil,
    true_and, word_one, word_g64]
  have hk1 : IsInK (1 + gen ^ r) := isInK_one_add.mpr (isInK_gen_pow r)
  have hcolRel : ∀ b < 128, coreProgram.RelB CM.sem rd (colName (decide (b < 64))) [gen ^ b,
      gen ^ r, gen ^ LeanDa.nPad r, gen ^ (LeanDa.nPad r - r), gen ^ LeanDa.logPad r, pb, ct, rb,
      hs, ctr] [] := fun b hb => da_verify_column_comp _ rd _ _ (hcol b hb)
  refine ⟨relB_dv_of (by simp) (da_row_shape_complete hl hT _ _ _
      ⟨_, _, _, _, _, rfl, rfl, r, hr1, hr2, rfl, rfl, rfl, rfl⟩),
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hk1,
    fun _ => relB_dv_of (by simp) (one_rel ((l88_iff rd _ _ _ 0).mpr (loop_of_all hr1 hr33 h88))),
    rfl, by rw [← iv0_word] at hiv0; exact hiv0, rfl, by rw [← iv1_word] at hiv1; exact hiv1,
    fun a ha => ?_, ⟨hkc, fun k hk w hw => ?_⟩,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hk1,
    fun _ => relB_dv_of (by simp) (one_rel ((l89_iff rd _ _ _ 0).mpr (loop_of_all hr1 hr33 h89))),
    rfl, ?_, rfl, ?_, rfl, rfl, rfl, hk1,
    fun _ => relB_dv_of (by simp) (one_rel ((l92_iff rd _ _ 0).mpr (loop_of_all hr1 hr33 h92))),
    da_levels_comp 7 (by norm_num) _ _ hlv7, rfl, rfl, rfl, rfl, rfl, hk1,
    fun _ => ?_, rfl, rfl, rfl, isInK_one_add.mpr (isInK_gen_pow _), fun hne => ?_,
    dl_dispatch_comp ⟨_, by omega, rfl, hlvr⟩, rfl, rfl, rfl, ?_, rfl, rfl, hv0, hv1, rfl⟩
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp ha
    exact dvVals_K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (List.mem_range.mp hw)
  · simp only [List.length_map, List.length_range] at hk
    simp only [List.getElem_map, List.getElem_range]
    rw [hctr k hk w hw]
    exact (dvVals_K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hk).symm
  · -- the prefix columns
    have := Digest.loopB_bwd (k := 0) (m := 64) (S := CM.sem) (rd := rd) (f := "__loop90")
      (ps := [gen ^ r, gen ^ LeanDa.nPad r, gen ^ (LeanDa.nPad r - r), gen ^ LeanDa.logPad r,
        pb, ct, rb, hs, ctr]) (N := colLoopEnd true)
      (B := fun x => coreProgram.RelB CM.sem rd (colName true) (x :: [gen ^ r,
        gen ^ LeanDa.nPad r, gen ^ (LeanDa.nPad r - r), gen ^ LeanDa.logPad r, pb, ct, rb, hs,
        ctr]) [])
      (fun x hB hK hn => colLoop_step_bwdB true rd _ rfl x hB hK hn) (by norm_num)
      (by rw [colLoopEnd_eq, ite_pos' rfl])
      (fun b _ hb => by
        have := hcolRel b (by omega)
        rwa [decide_eq_true hb] at this)
    rwa [pow_zero] at this
  · -- the other columns
    have := Digest.loopB_bwd (k := 64) (m := 128) (S := CM.sem) (rd := rd) (f := "__loop91")
      (ps := [gen ^ r, gen ^ LeanDa.nPad r, gen ^ (LeanDa.nPad r - r), gen ^ LeanDa.logPad r,
        pb, ct, rb, hs, ctr]) (N := colLoopEnd false)
      (B := fun x => coreProgram.RelB CM.sem rd (colName false) (x :: [gen ^ r,
        gen ^ LeanDa.nPad r, gen ^ (LeanDa.nPad r - r), gen ^ LeanDa.logPad r, pb, ct, rb, hs,
        ctr]) [])
      (fun x hB hK hn => colLoop_step_bwdB false rd _ rfl x hB hK hn) (by norm_num)
      (by rw [colLoopEnd_eq, ite_neg' (by decide)])
      (fun b hb hb' => by
        have := hcolRel b hb'
        rwa [decide_eq_false (by omega)] at this)
    exact this
  · have := l93_rel_bwdC (CM := CM) (k := 0) rd (gen ^ r) pb rt hr1 rfl (fun j _ hj => h93 j hj)
    rwa [pow_zero] at this
  · have hpos : 0 < LeanDa.nPad r - r := by
      by_contra h0
      apply hne
      rw [show LeanDa.nPad r - r = 0 by omega, pow_zero]
      exact e_add_eq_zero_iff.mpr rfl
    exact relB_dv_of (by simp) (one_rel ((l94_iff rd _ _ _ 0).mpr (loop_of_all hpos (by omega) h94)))
  · rw [← iv0_word, ← iv1_word, ← md64_word] at hfin
    exact hfin

/-- **`da_verify` is complete over a completeness model, from its facts** (`da_verify_of_facts`). -/
theorem da_verify_of_factsC {CM : CompModel} {rd : Reader} (hm : MemOk rd) {gsq : E}
    (hT : SquaresAt rd gsq) {r0 r1 v0 v1 : E} (h : DaFactsC CM rd r0 r1 v0 v1) :
    coreProgram.RelB CM.sem rd "da_verify" [gsq] [r0, r1, v0, v1] := by
  obtain ⟨r, pb, pd, hs, ctr, acc, rb, ct, rt, rc0, rc1, rr0, rr1, hr1, hr2, h88, hiv0, hiv1, hkc,
    hctr, h89, hcol, h92, hlv7, h93, h94, hlvr, hfin, hv0, hv1⟩ := h
  rw [relB_of_find find_dv]
  exact ⟨_, rfl, dv_holdsC hm.low16 hT hr1 hr2 h88 hiv0 hiv1 hkc hctr h89 hcol h92 hlv7 h93 h94
    hlvr hfin hv0 hv1⟩

/-! ## At the deployed model -/

theorem l93StepM_of_deployed {rd : Reader} {pb rt x : E} (h : L93Step rd pb rt x) :
    L93StepM CompModel.deployed.hm rd pb rt x := by
  obtain ⟨P, cs, hP, hlen, hcells, hcan, hout⟩ := h
  exact ⟨P, cs, hP, hlen, hcells, hcan, _, _, hout, _, rfl, rfl⟩

theorem daFactsC_of_deployed {rd : Reader} {r0 r1 v0 v1 : E} (h : DaFacts rd r0 r1 v0 v1) :
    DaFactsC CompModel.deployed rd r0 r1 v0 v1 := by
  obtain ⟨r, pb, pd, hs, ctr, acc, rb, ct, rt, rc0, rc1, rr0, rr1, hr1, hr2, h88, hiv0, hiv1, hkc,
    hctr, h89, hcol, h92, hlv7, h93, h94, hlvr, hfin, hv0, hv1⟩ := h
  exact ⟨r, pb, pd, hs, ctr, acc, rb, ct, rt, rc0, rc1, rr0, rr1, hr1, hr2, h88, hiv0, hiv1, hkc,
    hctr, h89, fun b hb => meaning_da_verify_columnComp_of_deployed (hcol b hb), h92,
    meaning_da_levelsWith_of_deployed hlv7, fun i hi => l93StepM_of_deployed (h93 i hi), h94,
    meaning_da_levelsWith_of_deployed hlvr, hfin, hv0, hv1⟩

theorem da_verify_of_facts_of_comp {rd : Reader} (hm : MemOk rd) {gsq : E} (hT : SquaresAt rd gsq)
    {r0 r1 v0 v1 : E} (h : DaFacts rd r0 r1 v0 v1) :
    coreProgram.Rel rd "da_verify" [gsq] [r0, r1, v0, v1] := by
  rw [← relB_deployed]
  exact da_verify_of_factsC (CM := CompModel.deployed) hm hT (daFactsC_of_deployed h)

end
end LeanVM.Guest.B1.Digest
