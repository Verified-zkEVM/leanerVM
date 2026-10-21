/-
  LeanVM.Guest.B1.Comp.Da.VerifyAtC

  `da_verify` placed by the bump allocator, loading from a region (`B1/Da/VerifyAt`), over a
  completeness model: on a memory holding the honest words of its run over the model.
-/

module

public import LeanVM.Guest.B1.Comp.Da.ColumnAtC
public import LeanVM.Guest.B1.Comp.Da.Complete
public import LeanVM.Guest.B1.Da.VerifyAt

/-!
# `da_verify`, placed, over a completeness model

`daMem_partsC`: what the honest memory over a model (`DaMemC`) holds, a witness opening
`(root, vd)` over the model's answers: every column's memory (`ColMemC`) and its vector hash's
rows under the model's semantics, and `dv_holdsC`'s other facts. `dv_relAtInC`: `dv_relAtIn`
over the model, at `dvPtrs`, by a tree of `dvTot` words weighing at most `dvTot θ` at every frame
weight `θ`; its callees free of `BLAKE2S` placed by the deployed lemmas (`relAtInWS_of_freeOn`),
the hashing ones by `…S`/`…C` lemmas.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.Value LeanVM.E2E.Complete
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.B1.Main (RelAtInWS relAtInWS_of_walk KidsFromInWS)

@[expose] public section

/-- The column tree's root of `w`'s run over a model. -/
def daColRootC (CM : CompModel) (w : Da.Witness) : Digest :=
  nodeM CM.hm (fun b => nodeM CM.hm (colLeafM w.rows.length (daCD CM w) b)
    (LeanDa.logPad w.rows.length) 0) 7 0

/-- The row tree's root of `w`'s run over a model. -/
def daRowRootC (CM : CompModel) (w : Da.Witness) : Digest :=
  nodeM CM.hm (rowLeafM w.rows.length (daRD CM w)) (LeanDa.logPad w.rows.length) 0

/-- **What the honest memory over a model holds**, a witness opening `(root, vd)` over the
model's answers (`daMem_parts`). -/
theorem daMem_partsC {CM : CompModel} {rd : Reader} {root vd : Digest} {w : Da.Witness}
    (hw : w.OpensWith CM.H (Da.toBytes padCellD) (Da.toBytes padRowD) root vd) (P : DaPtrs)
    (hP : DaMemC CM rd P w) :
    (∀ b < 128, ColMemC CM (decide (b < 64)) rd b w.rows.length (LeanDa.nPad w.rows.length)
        (LeanDa.logPad w.rows.length) P.pb P.ct P.rb P.hs P.ctr (P.node b) (P.lv b)
        (daSC CM w b).1 (daSC CM w b).2 (daSC CM w (b + 1)).1 (daSC CM w (b + 1)).2
        (digestScalars (nodeM CM.hm (colLeafM w.rows.length (daCD CM w) b)
          (LeanDa.logPad w.rows.length) 0)).1
        (digestScalars (nodeM CM.hm (colLeafM w.rows.length (daCD CM w) b)
          (LeanDa.logPad w.rows.length) 0)).2
        (daWs w b) ((List.range 4).map (cvOf b)) ∧
      ChainSteps CM.sem ((daSC CM w b).1, (daSC CM w b).2) (vxBlocks ((daWs w b).getD · 0))
        (vxMd (decide (b = 127)) (((List.range 4).map (cvOf b)).getD · 0)) 96
        ((daSC CM w (b + 1)).1, (daSC CM w (b + 1)).2)) ∧
    1 ≤ w.rows.length ∧ w.rows.length ≤ LeanDa.maxRows ∧
    (∀ i < w.rows.length, L88Step rd P.pb P.pd (gen ^ i)) ∧
    LoadHolds rd P.hs 0 (digestScalars paramIv).1 ∧ LoadHolds rd P.hs 1 (digestScalars paramIv).2 ∧
    IsInK P.ctr ∧
    (∀ k < 385, ∀ v, rd (P.ctr.limb 0 * Parameters.gpow k) = some v → v = word (k * 2048) 0 0) ∧
    (∀ i < w.rows.length, L89Step rd P.acc P.rb (gen ^ i)) ∧
    (∀ i < w.rows.length, L92Step rd P.rb (gen ^ i)) ∧
    Meaning_da_levelsWith CM.hm 7 rd [P.ct] [(digestScalars (daColRootC CM w)).1,
      (digestScalars (daColRootC CM w)).2] ∧
    (∀ i < w.rows.length, L93StepM CM.hm rd P.pb P.rt (gen ^ i)) ∧
    (∀ d < LeanDa.nPad w.rows.length - w.rows.length,
      L94Step rd P.rt (gen ^ w.rows.length) (gen ^ d)) ∧
    Meaning_da_levelsWith CM.hm (LeanDa.logPad w.rows.length) rd [P.rt]
      [(digestScalars (daRowRootC CM w)).1, (digestScalars (daRowRootC CM w)).2] ∧
    CM.sem.check ![(digestScalars (daRowRootC CM w)).1, (digestScalars (daRowRootC CM w)).2,
      (digestScalars (daColRootC CM w)).1, (digestScalars (daColRootC CM w)).2]
      (digestScalars paramIv).1 (digestScalars paramIv).2 (digestScalars root).1
      (digestScalars root).2 (metadataCell 64 true) ∧
    LoadHolds rd P.hs 256 (digestScalars vd).1 ∧ LoadHolds rd P.hs 257 (digestScalars vd).2 := by
  obtain ⟨hr1, hr2, hrl, hcom, hvl, hvd, hdot⟩ := hw
  obtain ⟨m88, mpd, mhs, mctr, m89, macc, mct, mrt, mnode, mlv⟩ := hP
  set r := w.rows.length with hr
  set lp := LeanDa.logPad r
  have hr33 : r < 2 ^ 33 := by unfold LeanDa.maxRows at hr2; omega
  have hN := nPad_le hr2
  obtain ⟨hrN, -⟩ := (logPad_iff (lp := lp) hr1).mp rfl
  have hNdef : LeanDa.nPad r = 2 ^ lp := rfl
  -- what the opening answers
  obtain ⟨hcD, hrD, hRT, hCT, hTop, hRoot⟩ := commitCodewordsWith_inv (M := CM.hm) hr1 hcom
  have hVX : CM.H (daVX w) = some vd := by
    rw [daVX_eq hvl]; exact vectorDigestWith_inv (M := CM.hm) hvd
  have hvdA : ansD CM.hm (daVX w) = vd := by
    show (CM.H (daVX w)).getD default = vd
    rw [hVX]; rfl
  -- the witness in chunks
  have hws : ∀ b < 128, (daWs w b).length = 256 := fun b hb => length_chunk (n := 128) hvl hb
  have hvec : w.vector = (List.range 128).flatMap (daWs w) := (flatMap_chunks _ 256 128 hvl).symm
  have hrowi : ∀ i < r, (w.rows.getD i []).length = 256 * 128 := fun i hi => by
    rw [List.getD_eq_getElem _ _ hi]; exact hrl _ (List.getElem_mem _)
  have hsyl : ∀ b < 128, ∀ i < r, (daSym w b i).length = 256 := fun b hb i hi => by
    rw [daSym, listCell_chunk]; exact length_chunk (hrowi i hi) hb
  have hrow : ∀ i < r, w.rows.getD i [] = (List.range 128).flatMap fun b => daSym w b i :=
    fun i hi => by
      show _ = (List.range 128).flatMap fun b => LeanDa.listCell (w.rows.getD i []) b
      simp only [listCell_chunk]
      exact (flatMap_chunks _ 256 128 (hrowi i hi)).symm
  -- the rows' sums end at zero
  have hA0 : ∀ i < r, daA w i 128 = 0 := fun i hi => by
    have := hdot _ (List.getElem_mem (show i < w.rows.length from hi))
    rw [← List.getD_eq_getElem _ [] hi,
      dot_eq hvec (hrow i hi) hws (fun b hb => hsyl b hb i hi)] at this
    exact this
  -- every column
  have hcolR : ∀ b < 128, ColMemC CM (decide (b < 64)) rd b r (LeanDa.nPad r) lp P.pb P.ct P.rb P.hs
        P.ctr (P.node b) (P.lv b) (daSC CM w b).1 (daSC CM w b).2 (daSC CM w (b + 1)).1
        (daSC CM w (b + 1)).2 (digestScalars (nodeM CM.hm (colLeafM r (daCD CM w) b) lp 0)).1
        (digestScalars (nodeM CM.hm (colLeafM r (daCD CM w) b) lp 0)).2
        (daWs w b) ((List.range 4).map (cvOf b)) ∧
      ChainSteps CM.sem ((daSC CM w b).1, (daSC CM w b).2) (vxBlocks ((daWs w b).getD · 0))
        (vxMd (decide (b = 127)) (((List.range 4).map (cvOf b)).getD · 0)) 96
        ((daSC CM w (b + 1)).1, (daSC CM w (b + 1)).2) := by
    intro b hb
    refine ⟨⟨?_, ?_, fun k hk => ?_, fun k hk => (frameRun_of_cells (by rw [hws b hb]; norm_num)
      (mlv b hb)).2 k (by rw [hws b hb]; exact hk),
      fun i hi => ?_, fun d hd => ?_, levelsWith_of_treeAtM (mnode b hb) (hCT b hb), ?_⟩,
      daSC_col CM w (by rw [hvdA]; exact hVX) hb⟩
    · rw [gen_sq]; exact mhs b (by omega)
    · rw [show gen ^ b * gen * (gen ^ b * gen) = gen ^ (2 * (b + 1)) by
        rw [← pow_succ, ← pow_add]; congr 1; ring]
      exact mhs (b + 1) (by omega)
    · have hk' : k < 4 := by simpa using hk
      rw [show gen ^ b * gen ^ b * gen ^ b = gen ^ (3 * b) by
          rw [← pow_add, ← pow_add]; congr 1; ring,
        loadHolds_mul_gen_pow]
      simp only [List.getElem_map, List.getElem_range, cvOf, Nat.add_mul]
      have := ctr_load mctr (k := 3 * b + k) (by omega)
      rwa [Nat.add_mul] at this
    · have hleaf := treeAtM_leaf (mnode b hb) (j := i) (by rw [← hNdef]; omega)
      simp only [colLeafM, hi, ↓reduceIte] at hleaf
      have hsucc : daA w i (b + 1) = daA w i b + daCellS w b i := Finset.sum_range_succ _ _
      refine ⟨(digestScalars (daCD CM w b i)).1, (digestScalars (daCD CM w b i)).2, daCellS w b i,
        P.acc * gen ^ (129 * i), daA w i b, ⟨P.lv b, _, _, _, rfl, rfl, daSym w b i, daWs w b,
        hsyl b hb i hi, hws b hb, mlv b hb, ⟨_, hcD b hb i hi, rfl⟩, rfl⟩, m89 i hi,
        (loadHolds_mul_gen_pow _ b 0 _).mpr (macc i hi b (by omega)),
        (loadHolds_mul_gen_pow _ b 1 _).mpr (by rw [← hsucc]; exact macc i hi (b + 1) (by omega)),
        by rw [gen_sq]; exact hleaf, fun h64 => ⟨P.pd * gen ^ (128 * i), m88 i hi, ?_⟩⟩
      rw [gen_sq, mul_assoc, ← pow_add]
      exact mpd i hi b (of_decide_eq_true h64)
    · unfold GapStep
      rw [pad_ptr]
      have := treeAtM_leaf (mnode b hb) (j := r + d) (by rw [← hNdef]; omega)
      simp only [colLeafM, show ¬(r + d < r) by omega, ↓reduceIte, padCell_cells] at this
      exact this
    · rw [gen_sq]; exact treeAtM_leaf mct (j := b) (by norm_num; omega)
  -- the rows' digests
  let cs : ℕ → List E := fun i => (List.range 128).map fun k =>
    if k % 2 = 0 then (digestScalars (daCD CM w (k / 2) i)).1
    else (digestScalars (daCD CM w (k / 2) i)).2
  have hcsl : ∀ i, (cs i).length = 128 := fun i => by simp [cs]
  have hcsb : ∀ i, (cs i).flatMap cellBytes =
      (List.range 64).flatMap fun b => digestBytes (daCD CM w b i) := by
    intro i
    rw [List.flatMap_map, show 128 = 2 * 64 by rfl, flatMap_range_mul 2]
    refine List.flatMap_congr fun b _ => ?_
    rw [show List.range 2 = [0, 1] from rfl, digestBytes_eq]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, Nat.add_zero,
      show 2 * b % 2 = 0 by omega, show (2 * b + 1) % 2 = 1 by omega, show 2 * b / 2 = b by omega,
      show (2 * b + 1) / 2 = b by omega, ↓reduceIte, one_ne_zero]
  have h93 : ∀ i < r, L93StepM CM.hm rd P.pb P.rt (gen ^ i) := by
    intro i hi
    refine ⟨P.pd * gen ^ (128 * i), cs i, m88 i hi, hcsl i, fun k hk => ?_, fun c hc => ?_,
      (digestScalars (daRD CM w i)).1, (digestScalars (daRD CM w i)).2, ?_,
      ⟨daRD CM w i, by rw [hcsb i]; exact hrD i hi, rfl⟩⟩
    · have hk' : k < 128 := by rw [hcsl] at hk; exact hk
      have hl := mpd i hi (k / 2) (by omega)
      rw [pow_add, ← mul_assoc] at hl
      have hl2 := hl (k % 2) (by simp; omega)
      rw [loadHolds_mul_gen_pow, show 2 * (k / 2) + k % 2 = k by omega] at hl2
      simp only [cs, List.getElem_map, List.getElem_range]
      by_cases h2 : k % 2 = 0
      · simp only [h2, ↓reduceIte]
        simpa [h2] using hl2
      · have h1 : k % 2 = 1 := by omega
        simp only [h2, ↓reduceIte]
        simpa [h1] using hl2
    · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hc
      split_ifs
      exacts [(isCanonical128_digestScalars _).1, (isCanonical128_digestScalars _).2]
    · rw [gen_sq]
      have := treeAtM_leaf mrt (j := i) (by rw [← hNdef]; omega)
      simp only [rowLeafM, hi, ↓reduceIte] at this
      exact this
  have hs0 := mhs 0 (by norm_num)
  rw [Nat.mul_zero, pow_zero, mul_one, daSC_zero] at hs0
  have hsl := mhs 128 le_rfl
  rw [daSC_last, hvdA] at hsl
  obtain ⟨x0, x1⟩ := cellsAt_two.mp hsl
  rw [loadHolds_mul_gen_pow] at x0 x1
  refine ⟨hcolR, hr1, hr2, fun i hi => ?_, (cellsAt_two.mp hs0).1, (cellsAt_two.mp hs0).2,
    (mctr 0 (by simp)).1, fun k hk v hv => ?_, fun i hi => ⟨?_, ?_⟩,
    fun i hi => ⟨P.acc * gen ^ (129 * i), ?_, ?_⟩, levelsWith_of_treeAtM mct hTop, h93,
    fun d hd => ?_, levelsWith_of_treeAtM mrt hRT, pair_comp CM hRoot, x0, x1⟩
  · show LoadHolds rd (P.pb * gen ^ i) 0 (P.pd * (gen ^ i) ^ 128)
    rw [← pow_mul, Nat.mul_comm i 128]; exact m88 i hi
  · have := (ctr_load mctr hk).2
    rw [hv] at this
    exact Option.some.inj this
  · rw [← pow_mul, Nat.mul_comm i 129]; exact m89 i hi
  · rw [← pow_mul, Nat.mul_comm i 129]
    have := macc i hi 0 (by norm_num)
    rwa [show daA w i 0 = 0 from Finset.sum_range_zero _] at this
  · exact m89 i hi
  · have := macc i hi 128 le_rfl
    rwa [hA0 i hi] at this
  · unfold L94Step
    rw [pad_ptr]
    have := treeAtM_leaf mrt (j := r + d) (by rw [← hNdef]; omega)
    simp only [rowLeafM, show ¬(r + d < r) by omega, ↓reduceIte, padRow_cells] at this
    exact this

/-- A column's meaning over a model from its memory (`colMeaning_of_mem`). -/
theorem colMeaningC_of_mem {CM : CompModel} {store : Bool} {rd : Reader} {b r N lp : ℕ} (hb : b < 128)
    (hr1 : 1 ≤ r) (hr33 : r < 2 ^ 33) (hN : N < 2 ^ 33) (hlp : lp < 11)
    {pb ct rb hs ctr node lv h0 h1 o0 o1 c0 c1 : E} {ws cv : List E} (hwl : ws.length = 256)
    (hcl : cv.length = 4)
    (hm : ColMemC CM store rd b r N lp pb ct rb hs ctr node lv h0 h1 o0 o1 c0 c1 ws cv)
    (hch : ChainSteps CM.sem (h0, h1) (vxBlocks (ws.getD · 0)) (vxMd (decide (b = 127)) (cv.getD · 0))
      96 (o0, o1))
    (hlvK : IsInK lv) :
    Meaning_da_verify_columnComp CM store rd
      [gen ^ b, gen ^ r, gen ^ N, gen ^ (N - r), gen ^ lp, pb, ct, rb, hs, ctr] [] := by
  obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8⟩ := hm
  refine ⟨_, _, _, _, _, _, _, _, _, _, rfl, rfl, h0, h1, o0, o1, lv, node, c0, c1, m1, ?_,
    m2, isInK_gen_pow r, fun _ => loopTo_of_all hr1 hr33 m5, isInK_gen_pow _, fun hne => ?_,
    ⟨lp, hlp, rfl, m7⟩, m8⟩
  · refine ⟨gen ^ b, _, rfl, isInK_gen_pow b, ?_⟩
    rw [decide_gen127 hb]
    exact ⟨_, _, _, _, _, _, _, rfl, rfl, ws, cv, hwl, hcl, m3, hch, hlvK,
      fun k hk v hv => m4 k (by omega) v hv⟩
  · have hpos : 0 < N - r := by
      by_contra h0
      exact hne (by rw [show N - r = 0 by omega, pow_zero])
    exact loopTo_of_all hpos (by omega) m6

/-- **`da_verify` at `fp` over a completeness model** (`dv_relAtIn`): a witness opening
`(root, vd)` over the model's answers, on a memory holding the honest words of its run over the
model at `dvPtrs` and the squares table at `gsq`, holds under the model's semantics placed by a
tree of `dvTot` words weighing at most `dvTot θ` at every `θ`, loading only `g_squares[logPad r]`
outside its own data, at a word of `R`. -/
theorem dv_relAtInC (fs : String → ℕ) (cert : String → V → ℕ) {CM : CompModel} {rd : Reader}
    (hl : Low16 rd) {gsq : E} (hT : SquaresAt rd gsq) {root vd : Digest} {w : Da.Witness}
    (hw : w.OpensWith CM.H (Da.toBytes padCellD) (Da.toBytes padRowD) root vd) {R : ℕ → Prop}
    (hR : ∃ i, (gsq * gen ^ LeanDa.logPad w.rows.length).limb 0 * gpow 0 = gpow i ∧ R i) (fp : ℕ)
    (hP : DaMemC CM rd (dvPtrs fs cert w.rows.length fp) w) :
    RelAtInWS CM.sem fs cert wId rd R (fun _ => False) fp (dvTot fs w.rows.length) "da_verify" [gsq]
      [(digestScalars root).1, (digestScalars root).2, (digestScalars vd).1, (digestScalars vd).2]
      fun θ => dvTot θ w.rows.length := by
  obtain ⟨hcol, hr1, hr2, h88, hiv0, hiv1, hkc, hctr, h89, h92, hlv7, h93, h94, hlvr, hfin, hv0, hv1⟩ :=
    daMem_partsC hw _ hP
  set r := w.rows.length with hr
  set N := LeanDa.nPad r with hNd
  set lp := LeanDa.logPad r with hlpd
  have hr33 : r < 2 ^ 33 := by unfold LeanDa.maxRows at hr2; omega
  have hN := nPad_le hr2
  have hlp : lp ≤ 10 := logPad_le hr2
  have hrN : r ≤ N := ((logPad_iff (lp := lp) hr1).mp rfl).1
  have hNp : N = 2 ^ lp := rfl
  have hvl := hw.2.2.2.2.1
  set P := dvPtrs fs cert r fp with hPd
  -- the columns
  have hcolM : ∀ b < 128, Meaning_da_verify_columnComp CM (decide (b < 64)) rd
      [gen ^ b, gen ^ r, gen ^ N, gen ^ (N - r), gen ^ lp, P.pb, P.ct, P.rb, P.hs, P.ctr] [] :=
    fun b hb => by
      obtain ⟨hcm, hch⟩ := hcol b hb
      have hwl : (daWs w b).length = 256 := length_chunk (n := 128) hvl hb
      exact colMeaningC_of_mem hb hr1 hr33 (by omega) (by omega) hwl (by simp) hcm hch
        (isInK_gen_pow _)
  have hholds := dv_holdsC hl hT hr1 hr2 h88 hiv0 hiv1 hkc hctr h89 hcolM h92 hlv7 h93 h94 hlvr hfin
    hv0 hv1 (pd := P.pd) (acc := P.acc)
  set σ : Val := fun v => dvVals (gsq) (gen ^ r) (gen ^ lp) (gen ^ N) (gen ^ (N - r)) P.pd P.pb P.hs
    P.ctr P.acc P.rb P.ct P.rt (digestScalars (daColRootC CM w)).1 (digestScalars (daColRootC CM w)).2
    (digestScalars (daRowRootC CM w)).1 (digestScalars (daRowRootC CM w)).2 (digestScalars root).1
    (digestScalars root).2 (digestScalars vd).1 (digestScalars vd).2 v.idx with hσ
  have hx : σ (.n 2) = ofK (gpow lp) := by rw [← gen_pow_eq_ofK]; rfl
  have hw' := walk_dispatch σ dvPre dvPost dvPre_straight dvPost_straight (.n 2) dlNames [.n 429]
    [.n 436, .n 437] [.n 443, .n 444, .n 445, .n 446] (i := lp) (by simp [dlNames]; omega)
    (by simp [dlNames]) hx
  rw [← dvBody_split] at hw'
  set es := dvPre.flatMap (Main.slEvs σ) ++
    .call dlNames[lp]! [.n 429] [.n 436, .n 437] :: dvPost.flatMap (Main.slEvs σ) with hes
  have hev := holdsB_of_holdsList find_dv hholds hw'
  obtain ⟨hpd, hpa, hpad, hpc⟩ := Main.straight_parts σ _ dvPre_straight
  obtain ⟨hqd, hqa, hqad, hqc⟩ := Main.straight_parts σ _ dvPost_straight
  have hpaS : dvPre.filterMap Main.Stmt.allocSz = [(.n 12, .inr (.n 11)), (.n 13, .inr (.n 1)),
      (.n 17, .inl 258), (.n 414, .inr (.n 413)), (.n 415, .inr (.n 1)), (.n 419, .inl 512),
      (.n 429, .inr (.n 428))] := by
    decide +kernel
  have hqaS : dvPost.filterMap Main.Stmt.allocSz = [] := by decide +kernel
  have hlg : ∀ {e : ℕ}, e < 2 ^ 64 - 1 → logG (gen ^ e) = e := fun he => logG_gen_pow he
  have h11 : σ (.n 11) = gen ^ (128 * N) := by
    show sqIter (gen ^ N) 7 = _; rw [sqIter_gen, show 2 ^ 7 * N = 128 * N by norm_num]
  have h413 : σ (.n 413) = gen ^ (129 * r) := by
    show sqIter (gen ^ r) 7 * gen ^ r = _
    rw [sqIter_gen, ← pow_add, show 2 ^ 7 * r + r = 129 * r by norm_num; ring]
  have h428 : σ (.n 428) = gen ^ (4 * N) := by
    show gen ^ N * gen ^ N * (gen ^ N * gen ^ N) = _; ring
  have hal : allocs σ es = dvSizes r N := by
    rw [hes, allocs_append, show allocs σ (.call dlNames[lp]! [.n 429] [.n 436, .n 437] ::
      dvPost.flatMap (Main.slEvs σ)) = allocs σ (dvPost.flatMap (Main.slEvs σ)) from rfl, hpa, hqa,
      hpaS, hqaS]
    simp only [List.map_cons, List.map_nil, Sum.elim_inr, Sum.elim_inl, id, h11, h413, h428,
      List.append_nil]
    rw [show σ (.n 1) = gen ^ r from rfl, hlg (show r < 2 ^ 64 - 1 by omega),
      hlg (show 128 * N < 2 ^ 64 - 1 by omega), hlg (show 129 * r < 2 ^ 64 - 1 by omega),
      hlg (show 4 * N < 2 ^ 64 - 1 by omega)]
    rfl
  -- the data
  set b0 := fp + fs "da_verify" with hb0
  have hzip : (dvSizes r N).zip (bases b0 (dvSizes r N)) = [(128 * N, b0), (r, b0 + 128 * N),
      (258, b0 + 128 * N + r), (129 * r, b0 + 128 * N + r + 258),
      (r, b0 + 128 * N + r + 258 + 129 * r), (512, b0 + 128 * N + r + 258 + 129 * r + r),
      (4 * N, b0 + 128 * N + r + 258 + 129 * r + r + 512)] := rfl
  have hruns : runs es = [(.n 20, 385)] := by
    rw [hes, runs_append, show runs (.call dlNames[lp]! [.n 429] [.n 436, .n 437] ::
      dvPost.flatMap (Main.slEvs σ)) = runs (dvPost.flatMap (Main.slEvs σ)) from rfl,
      runs_straight σ _ dvPre_straight, runs_straight σ _ dvPost_straight,
      show dvPre.filterMap stmtRun? = [(.n 20, 385)] by decide +kernel,
      show dvPost.filterMap stmtRun? = [] by decide +kernel]
    rfl
  have hO : ∀ {k i : ℕ}, ∀ q ∈ (dvSizes r N).zip (bases b0 (dvSizes r N)), q.2 + k = i → k < q.1 →
      ownData cert fp b0 "da_verify" (dvSizes r N) es i :=
    fun q hq h1 h2 => Or.inl ⟨q, hq, by omega, by omega⟩
  have hC : ∀ {i : ℕ}, fp + cert "da_verify" (.n 20) ≤ i → i < fp + cert "da_verify" (.n 20) + 385 →
      ownData cert fp b0 "da_verify" (dvSizes r N) es i := fun h1 h2 =>
    Or.inr ⟨(.n 20, 385), by rw [hruns]; exact List.Mem.head _, h1, h2⟩
  -- the frames
  have hpcS : dvPre.filterMap Main.Stmt.callS =
      [(none, "da_row_shape", [.n 1, .n 2, .n 0], [.n 3, .n 4]),
      (some (.n 15), "__loop88", [.n 16, .n 1, .n 13, .n 12], []),
      (some (.n 417), "__loop89", [.n 418, .n 1, .n 414, .n 415], []),
      (none, "__loop90", [.n 420, .n 1, .n 3, .n 4, .n 2, .n 13, .n 419, .n 415, .n 17, .n 405], []),
      (none, "__loop91", [.n 421, .n 1, .n 3, .n 4, .n 2, .n 13, .n 419, .n 415, .n 17, .n 405], []),
      (some (.n 423), "__loop92", [.n 424, .n 1, .n 415], []),
      (none, "da_levels__L128_L7", [.n 419], [.n 425, .n 426]),
      (some (.n 431), "__loop93", [.n 432, .n 1, .n 13, .n 429], []),
      (some (.n 434), "__loop94", [.n 435, .n 4, .n 429, .n 1], [])] := by decide +kernel
  have hk1 : decide (1 + gen ^ r ≠ (0 : E)) = true :=
    decide_eq_true (one_add_ne_zero.mpr fun he => by
      have := (gen_pow_eq_one_iff (by omega)).mp he; omega)
  have hgapd : decide (1 + gen ^ (N - r) ≠ (0 : E)) = decide (N - r ≠ 0) := by
    refine decide_eq_decide.mpr ⟨fun h he => h (by rw [he, pow_zero]; exact e_add_eq_zero_iff.mpr rfl),
      fun h he => h ((gen_pow_eq_one_iff (show N - r < 2 ^ 64 - 1 by omega)).mp
        (e_add_eq_zero_iff.mp he).symm)⟩
  have hcalls : calls es = [⟨"da_row_shape", [.n 1, .n 2, .n 0], [.n 3, .n 4], true⟩,
      ⟨"__loop88", [.n 16, .n 1, .n 13, .n 12], [], true⟩,
      ⟨"__loop89", [.n 418, .n 1, .n 414, .n 415], [], true⟩,
      ⟨"__loop90", [.n 420, .n 1, .n 3, .n 4, .n 2, .n 13, .n 419, .n 415, .n 17, .n 405], [], true⟩,
      ⟨"__loop91", [.n 421, .n 1, .n 3, .n 4, .n 2, .n 13, .n 419, .n 415, .n 17, .n 405], [], true⟩,
      ⟨"__loop92", [.n 424, .n 1, .n 415], [], true⟩,
      ⟨"da_levels__L128_L7", [.n 419], [.n 425, .n 426], true⟩,
      ⟨"__loop93", [.n 432, .n 1, .n 13, .n 429], [], true⟩,
      ⟨"__loop94", [.n 435, .n 4, .n 429, .n 1], [], decide (N - r ≠ 0)⟩,
      ⟨dlNames[lp]!, [.n 429], [.n 436, .n 437], true⟩] := by
    rw [hes, calls_append, show calls (.call dlNames[lp]! [.n 429] [.n 436, .n 437] ::
      dvPost.flatMap (Main.slEvs σ)) = ⟨dlNames[lp]!, [.n 429], [.n 436, .n 437], true⟩ ::
        calls (dvPost.flatMap (Main.slEvs σ)) from rfl, hpc, hqc, hpcS,
      show dvPost.filterMap Main.Stmt.callS = [] by decide +kernel]
    simp only [List.map_cons, List.map_nil, Main.mkCall, List.cons_append, List.nil_append]
    rw [show σ (.n 15) = 1 + gen ^ r from rfl, show σ (.n 417) = 1 + gen ^ r from rfl,
      show σ (.n 423) = 1 + gen ^ r from rfl, show σ (.n 431) = 1 + gen ^ r from rfl,
      show σ (.n 434) = 1 + gen ^ (N - r) from rfl, hk1, hgapd]
  -- the pointers' exponents
  set Dx := b0
  set Px := b0 + 128 * N
  set Hx := Px + r
  set Ax := Hx + 258
  set Bx := Ax + 129 * r
  set Tx := Bx + r
  set Wx := Tx + 512
  set Cx := fp + cert "da_verify" (.n 20)
  have hmemZ : ∀ {q : ℕ × ℕ}, q ∈ [(128 * N, Dx), (r, Px), (258, Hx), (129 * r, Ax), (r, Bx),
      (512, Tx), (4 * N, Wx)] → q ∈ (dvSizes r N).zip (bases b0 (dvSizes r N)) := fun h => by
    rw [hzip]; exact h
  have oD : ∀ {k : ℕ}, k < 128 * N → ownData cert fp b0 "da_verify" (dvSizes r N) es (Dx + k) :=
    fun hk => hO (128 * N, Dx) (hmemZ (by simp)) rfl hk
  have oP : ∀ {k : ℕ}, k < r → ownData cert fp b0 "da_verify" (dvSizes r N) es (Px + k) :=
    fun hk => hO (r, Px) (hmemZ (by simp)) rfl hk
  have oH : ∀ {k : ℕ}, k < 258 → ownData cert fp b0 "da_verify" (dvSizes r N) es (Hx + k) :=
    fun hk => hO (258, Hx) (hmemZ (by simp)) rfl hk
  have oA : ∀ {k : ℕ}, k < 129 * r → ownData cert fp b0 "da_verify" (dvSizes r N) es (Ax + k) :=
    fun hk => hO (129 * r, Ax) (hmemZ (by simp)) rfl hk
  have oB : ∀ {k : ℕ}, k < r → ownData cert fp b0 "da_verify" (dvSizes r N) es (Bx + k) :=
    fun hk => hO (r, Bx) (hmemZ (by simp)) rfl hk
  have oT : ∀ {k : ℕ}, k < 512 → ownData cert fp b0 "da_verify" (dvSizes r N) es (Tx + k) :=
    fun hk => hO (512, Tx) (hmemZ (by simp)) rfl hk
  have oW : ∀ {k : ℕ}, k < 4 * N → ownData cert fp b0 "da_verify" (dvSizes r N) es (Wx + k) :=
    fun hk => hO (4 * N, Wx) (hmemZ (by simp)) rfl hk
  have oC : ∀ {k : ℕ}, k < 385 → ownData cert fp b0 "da_verify" (dvSizes r N) es (Cx + k) :=
    fun hk => hC (by omega) (by omega)
  -- the memory's pointers
  have hrb : ∀ j < r, rd (gpow (Bx + j)) = some (gen ^ (Ax + 129 * j)) := fun j hj => by
    have := load_rd (h89 j hj).1
    rw [show P.rb * gen ^ j = gen ^ (Bx + j) by show gen ^ Bx * gen ^ j = _; rw [← pow_add],
      addr_gen, Nat.add_zero] at this
    rwa [show P.acc * (gen ^ j) ^ 129 = gen ^ (Ax + 129 * j) by
      show gen ^ Ax * (gen ^ j) ^ 129 = _; rw [← pow_mul, ← pow_add, Nat.mul_comm j]] at this
  have hpb : ∀ j < r, rd (gpow (Px + j)) = some (gen ^ (Dx + 128 * j)) := fun j hj => by
    have := load_rd (h88 j hj)
    rw [show P.pb * gen ^ j = gen ^ (Px + j) by show gen ^ Px * gen ^ j = _; rw [← pow_add],
      addr_gen, Nat.add_zero] at this
    rwa [show P.pd * (gen ^ j) ^ 128 = gen ^ (Dx + 128 * j) by
      show gen ^ Dx * (gen ^ j) ^ 128 = _; rw [← pow_mul, ← pow_add, Nat.mul_comm j]] at this
  -- the callees
  have hfree : ∀ {f : String}, f ∈ ["da_row_shape", "__loop88", "__loop89", "__loop92", "__loop94"] →
      ∀ {Rk : ℕ → Prop} {fp' n : ℕ} {args rets : List E} {Bw : (String → ℕ) → ℕ},
      Main.RelAtInW fs cert wId rd Rk (fun _ => False) fp' n f args rets Bw →
      RelAtInWS CM.sem fs cert wId rd Rk (fun _ => False) fp' n f args rets Bw :=
    fun hf _ _ _ _ _ _ h => relAtInWS_of_freeOn fs freeOn_dv hf cert h
  have hdrs : coreProgram.Rel rd "da_row_shape" [gen ^ r, gen ^ lp, gsq] [gen ^ N, gen ^ (N - r)] :=
    da_row_shape_complete hl hT _ _ _ ⟨_, _, _, _, _, rfl, rfl, r, hr1, hr2, rfl, rfl, rfl, rfl⟩
  have k1 := fun fp' => hfree (by simp) (relAtInW_of_relInTW_pure fs cert drs_pure
    (List.mem_singleton_self _) (drs_relInT fs (R := R) hR hdrs) fp')
  have k2 := fun fp' => hfree (by simp) (relAtInW_of_relInTW_pure fs cert l88_pure
    (List.mem_singleton_self _) (l88_relInT fs (R := R88 r Px) hr33 (fun _ h => h) hr1
      ((l88_iff rd _ _ _ 0).mpr (loop_of_all hr1 hr33 h88))) fp')
  have k3 := fun fp' => hfree (by simp) (relAtInW_of_relInTW_pure fs cert l89_pure
    (List.mem_singleton_self _) (l89_relInT fs (R := R89 r Ax Bx) hr33 (fun _ h => h) hr1
      ((l89_iff rd _ _ _ 0).mpr (loop_of_all hr1 hr33 h89))) fp')
  have k6 := fun fp' => hfree (by simp) (relAtInW_of_relInTW_pure fs cert l92_pure
    (List.mem_singleton_self _) (l92_relInT fs (R := R92 r Ax Bx) hr33 hrb (fun _ h => h) hr1
      ((l92_iff rd _ _ 0).mpr (loop_of_all hr1 hr33 h92))) fp')
  have k7 := relAtInWS_of_relInTWS_pure fs cert (lv_pure (k := 7) (by norm_num)) (by simp [lvSet])
    (levels_relInTS fs (k := 7) (by norm_num) (R := TreeR Tx 7) (fun _ h => h)
      (da_levels_comp 7 (by norm_num) _ _ hlv7))
  have h93R : coreProgram.RelB CM.sem rd "__loop93" [gen ^ 0, gen ^ r, P.pb, P.rt] [] :=
    l93_rel_bwdC (CM := CM) (k := 0) rd (gen ^ r) P.pb P.rt hr1 rfl (fun j _ hj => h93 j hj)
  have k8 := relAtInWS_of_relInTWS_pure fs cert l93_pure (List.mem_singleton_self _)
    (l93_relInTS fs (R := R93 r Px Dx Wx) hr33 hpb (fun _ h => h) hr1 h93R)
  have k10 := relAtInWS_of_relInTWS_pure fs cert (lv_pure hlp) (by simp [lvSet])
    (levels_relInTS fs hlp (R := TreeR Wx lp) (fun _ h => h) (da_levels_comp lp hlp _ _ hlvr))
  rw [pow_zero] at k2 k3 k6 k8
  rw [← dlNames_getElem! (by omega)] at k10
  -- the column loops
  set Rcol : ℕ → Prop := fun i => R i ∨ ownData cert fp b0 "da_verify" (dvSizes r N) es i with hRcol
  have hRc : ∀ b < 128, ∀ k < 4, Rcol (Cx + 3 * b + k) := fun b hb k hk => Or.inr (by
    rw [show Cx + 3 * b + k = Cx + (3 * b + k) by ring]; exact oC (by omega))
  have hRh : ∀ b < 128, ∀ k < 4, Rcol (Hx + 2 * b + k) := fun b hb k hk => Or.inr (by
    rw [show Hx + 2 * b + k = Hx + (2 * b + k) by ring]; exact oH (by omega))
  have hRt : ∀ b < 128, ∀ k < 2, Rcol (Tx + 2 * b + k) := fun b hb k hk => Or.inr (by
    rw [show Tx + 2 * b + k = Tx + (2 * b + k) by ring]; exact oT (by omega))
  have hRrow : ∀ (store : Bool), ∀ b < clHi store, ∀ j < r, Rcol (Bx + j) ∧ Rcol (Ax + 129 * j + b) ∧
      Rcol (Ax + 129 * j + b + 1) ∧ (store = true → Rcol (Px + j) ∧ Rcol (Dx + 128 * j + 2 * b) ∧
        Rcol (Dx + 128 * j + 2 * b + 1)) := fun store b hb j hj =>
    have hb' : b < 128 := by cases store <;> simp [clHi] at hb <;> omega
    ⟨Or.inr (oB hj), Or.inr (by rw [Nat.add_assoc]; exact oA (by nlinarith)),
      Or.inr (by rw [Nat.add_assoc, Nat.add_assoc]; exact oA (by nlinarith)),
      fun hs => have h64 : b < 64 := by subst hs; simpa [clHi] using hb
        ⟨Or.inr (oP hj), Or.inr (by rw [Nat.add_assoc]; exact oD (by nlinarith)),
        Or.inr (by rw [Nat.add_assoc, Nat.add_assoc]; exact oD (by nlinarith))⟩⟩
  have hmemC : ∀ (store : Bool) (fp0 : ℕ), (∀ b, clLo store ≤ b → b < clHi store →
      (decide (b < 64) = store ∧ (if b < 64 then dvPos90 fs fp r N else dvPos91 fs fp r N lp) = fp0)) →
      ∀ b, clLo store ≤ b → b < clHi store → ColAtC CM fs cert store rd b r N lp Px Tx Bx Hx Cx
        (daSC CM w b).1 (daSC CM w b).2 (daSC CM w (b + 1)).1 (daSC CM w (b + 1)).2
        (digestScalars (nodeM CM.hm (colLeafM r (daCD CM w) b) lp 0)).1
        (digestScalars (nodeM CM.hm (colLeafM r (daCD CM w) b) lp 0)).2
        (daWs w b) ((List.range 4).map (cvOf b))
        (colPos fs store r N lp fp0 b) := fun store fp0 hst b h1 h2 => by
    have hb : b < 128 := by cases store <;> simp [clHi] at h2 <;> omega
    obtain ⟨e1, e2⟩ := hst b h1 h2
    have := (hcol b hb).1
    simp only [hPd, dvPtrs, dvColPos, e1] at this
    rw [e2] at this
    exact this
  have k4 := colLoop_relAtInC fs cert true (R := Rcol) hr1 hrN hNp hlp (WS := daWs w)
    (CV := fun b => (List.range 4).map (cvOf b)) (fun b => by simp) (fun b hb => (hcol b hb).2) hRc hRh
    hRt (hRrow true) (dvPos90 fs fp r N) rd (hmemC true _ fun b h1 h2 => by
      have : b < 64 := by simpa [clHi] using h2
      exact ⟨decide_eq_true this, ite_pos' this _ _⟩) hrb (fun _ => hpb) 0 (by decide) (by decide)
  have k5 := colLoop_relAtInC fs cert false (R := Rcol) hr1 hrN hNp hlp (WS := daWs w)
    (CV := fun b => (List.range 4).map (cvOf b)) (fun b => by simp) (fun b hb => (hcol b hb).2) hRc hRh
    hRt (hRrow false) (dvPos91 fs fp r N lp) rd (hmemC false _ fun b h1 h2 => by
      have : ¬ b < 64 := by simp [clLo] at h1; omega
      exact ⟨decide_eq_false this, ite_neg' this _ _⟩) hrb (fun h => absurd h (by decide)) 64
    (by decide) (by decide)
  rw [show (0 : ℕ) - clLo true = 0 from rfl, Nat.zero_mul, Nat.add_zero, pow_zero] at k4
  rw [show (64 : ℕ) - clLo false = 0 from rfl, Nat.zero_mul, Nat.add_zero] at k5
  have h := relAtInWS_of_walk (S := CM.sem) (fs := fs) (cert := cert) (w := wId) (σ := σ) (rd := rd)
    (R := R) (D := fun _ => False) (Dk := fun _ => False) (fp := fp)
    (N := (dvKids fs r N lp).foldr (· + ·) 0)
    (bws := [fun θ => θ "da_row_shape", fun θ => (r - 0) * θ "__loop88" + θ "__loop88",
      fun θ => (r - 0) * θ "__loop89" + θ "__loop89", fun θ => clTot θ true r N lp 0,
      fun θ => clTot θ false r N lp 64, fun θ => (r - 0) * θ "__loop92" + θ "__loop92",
      fun θ => dlTot θ 7, fun θ => (r - 0) * θ "__loop93" + θ "__loop93",
      fun θ => (N - r - 0) * θ "__loop94" + θ "__loop94", fun θ => dlTot θ lp])
    find_dv (Or.inl (by decide +kernel)) rfl hw' rfl hev
    (by
      rw [hal, hes, allocDsts_append, show allocDsts (.call dlNames[lp]! [.n 429] [.n 436, .n 437] ::
        dvPost.flatMap (Main.slEvs σ)) = allocDsts (dvPost.flatMap (Main.slEvs σ)) from rfl, hpd, hqd,
        hpaS, hqaS]
      simp only [List.map_cons, List.map_nil, List.append_nil, ← gen_pow_eq_ofK]
      rfl)
    (fun q hq => by
      rw [hes, addrs_append, show addrs (.call dlNames[lp]! [.n 429] [.n 436, .n 437] ::
        dvPost.flatMap (Main.slEvs σ)) = addrs (dvPost.flatMap (Main.slEvs σ)) from rfl, hpad, hqad,
        show dvPre.filterMap Main.Stmt.addrS = [(.n 405, .n 20)] by decide +kernel,
        show dvPost.filterMap Main.Stmt.addrS = [] by decide +kernel] at hq
      simp only [List.append_nil, List.mem_singleton] at hq
      subst hq
      rw [← gen_pow_eq_ofK]; rfl)
    ?_ ?_ (fun _ h => h.elim)
  · rw [hal] at h
    refine h.wmono fun θ => ?_
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, dvTot, dvKids, List.foldr,
      wId, Nat.sub_zero, ← hNd, ← hlpd]
    split_ifs with h0
    · rw [h0, Nat.zero_mul, Nat.zero_add]; omega
    · omega
  · rw [hcalls, hal]
    refine ⟨_, _, R, fun _ => False, rfl, fun i hi => Or.inl (Or.inl hi), k1 _, ?_⟩
    refine ⟨_, _, R88 r Px, fun _ => False, rfl, fun i hi => ?_, k2 _, ?_⟩
    · obtain ⟨j, hj, rfl⟩ := hi; exact Or.inl (Or.inr (oP hj))
    refine ⟨_, _, R89 r Ax Bx, fun _ => False, rfl, fun i hi => ?_, k3 _, ?_⟩
    · obtain ⟨j, hj, rfl | rfl⟩ := hi
      · exact Or.inl (Or.inr (oB hj))
      · exact Or.inl (Or.inr (oA (by omega)))
    refine ⟨_, _, Rcol, fun _ => False, rfl, fun i hi => Or.inl hi, k4, ?_⟩
    refine ⟨_, _, Rcol, fun _ => False, rfl, fun i hi => Or.inl hi, k5, ?_⟩
    refine ⟨_, _, R92 r Ax Bx, fun _ => False, rfl, fun i hi => ?_, k6 _, ?_⟩
    · obtain ⟨j, hj, rfl | rfl⟩ := hi
      · exact Or.inl (Or.inr (oB hj))
      · exact Or.inl (Or.inr (by rw [Nat.add_assoc]; exact oA (by omega)))
    refine ⟨_, _, TreeR Tx 7, fun _ => False, rfl, fun i hi => ?_, k7 _, ?_⟩
    · obtain ⟨h1, h2⟩ := hi
      have := oT (k := i - Tx) (by norm_num at h2; omega)
      rw [Nat.add_sub_cancel' h1] at this
      exact Or.inl (Or.inr this)
    refine ⟨_, _, R93 r Px Dx Wx, fun _ => False, rfl, fun i hi => ?_, k8 _, ?_⟩
    · obtain ⟨j, hj, rfl | ⟨h1, h2⟩ | rfl | rfl⟩ := hi
      · exact Or.inl (Or.inr (oP hj))
      · have := oD (k := i - Dx) (by omega)
        rw [Nat.add_sub_cancel' (by omega)] at this
        exact Or.inl (Or.inr this)
      · exact Or.inl (Or.inr (oW (by omega)))
      · exact Or.inl (Or.inr (by rw [Nat.add_assoc]; exact oW (by omega)))
    have hlast : ∀ {Dacc : ℕ → Prop} {b : ℕ}, KidsFromInWS CM.sem fs cert wId rd σ
        (fun i => R i ∨ ownData cert fp b0 "da_verify" (dvSizes r N) es i) Dacc
        [⟨dlNames[lp]!, [.n 429], [.n 436, .n 437], true⟩] [fun θ => dlTot θ lp] b (dlTot fs lp + 0)
        (fun _ => False) :=
      ⟨_, _, TreeR Wx lp, fun _ => False, rfl, fun i hi => ?_, k10 _, rfl, fun i hi => hi.elim⟩
    · by_cases hG : N - r = 0
      · refine ⟨_, _, fun _ => False, fun _ => False, rfl, fun i hi => hi.elim, ?_, ?_⟩
        · simp only [hG, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
        · simp only [hG, ↓reduceIte]
          exact hlast
      · have hGp : 0 < N - r := by omega
        have k9 := fun fp' => hfree (by simp) (relAtInW_of_relInTW_pure fs cert l94_pure
          (List.mem_singleton_self _) (l94_relInT fs (G := N - r) (T := Wx) (r := r)
            (R := R94 (N - r) Wx r) (by omega) (fun _ h => h) hGp
            ((l94_iff rd _ _ _ 0).mpr (loop_of_all hGp (by omega) h94))) fp')
        rw [pow_zero] at k9
        refine ⟨_, _, R94 (N - r) Wx r, fun _ => False, rfl, fun i hi => ?_, ?_, ?_⟩
        · obtain ⟨d, hd, rfl | rfl⟩ := hi
          · exact Or.inl (Or.inr (oW (by omega)))
          · exact Or.inl (Or.inr (by rw [Nat.add_assoc]; exact oW (by omega)))
        · simp only [ne_eq, hG, not_false_eq_true, decide_true, ↓reduceIte]
          exact k9 _
        · simp only [hG, ↓reduceIte]
          exact hlast
    · obtain ⟨h1, h2⟩ := hi
      have := oW (k := i - Wx) (by rw [← hNp] at h2; omega)
      rw [Nat.add_sub_cancel' h1] at this
      exact Or.inl (Or.inr this)
  · intro A hA
    rw [hes, loadAddrs_append, show loadAddrs σ (.call dlNames[lp]! [.n 429] [.n 436, .n 437] ::
      dvPost.flatMap (Main.slEvs σ)) = loadAddrs σ (dvPost.flatMap (Main.slEvs σ)) from rfl,
      loadAddrs_straight σ _ dvPre_straight, loadAddrs_straight σ _ dvPost_straight,
      show dvPre.filterMap stmtLoad? = [(.n 17, 0), (.n 17, 1)] by decide +kernel,
      show dvPost.filterMap stmtLoad? = [(.n 17, 256), (.n 17, 257)] by decide +kernel] at hA
    have g17 : σ (.n 17) = gen ^ Hx := rfl
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hA
    rw [hal]
    rcases hA with rfl | rfl | rfl | rfl
    · exact ⟨_, by rw [g17, addr_gen], Or.inl (oH (by norm_num))⟩
    · exact ⟨_, by rw [g17, addr_gen], Or.inl (oH (by norm_num))⟩
    · exact ⟨_, by rw [g17, addr_gen], Or.inl (oH (by norm_num))⟩
    · exact ⟨_, by rw [g17, addr_gen], Or.inl (oH (by norm_num))⟩

end
end LeanVM.Guest.B1.Digest
