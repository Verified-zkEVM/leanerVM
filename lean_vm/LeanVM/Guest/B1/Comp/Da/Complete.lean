/-
  LeanVM.Guest.B1.Comp.Da.Complete

  `da_verify` over a completeness model, completely: a LeanDA witness opening a root and a vector
  digest over the model's answers, and a memory holding the honest words of its run over the
  model, give `da_verify`'s relation under the model's semantics.
-/

module

public import LeanVM.Guest.B1.Comp.Da.Witness
public import LeanVM.Guest.B1.Comp.Da.Verify
public import LeanVM.Guest.B1.Da.Complete

/-!
# `da_verify` over a completeness model, completely

`da_verify_complete`'s analog over a `CompModel`. The honest run of a witness `w` over the model
(`daCD`: its cells' answered digests, `daRD`: its rows', `daSC`: the vector hash's states, the
model's cells of the prefixes of the vector's bytes `daVX`) and the memory it leaves
(`DaMemC`): `DaMem` with the model's digests and trees (`TreeAtM`, over `nodeM CM.hm`).
`da_verify_completeC`: on such a memory, a witness opening `(root, vd)` over the model
(`Witness.OpensWith CM.H` with the guest's padding digests) makes `da_verify` return the root's
and the vector digest's cells under `CM.sem`; every hash it computes is one the opening answers
(`commitCodewordsWith_inv`, `vectorDigestWith_inv`). At `CompModel.deployed` the honest memory is
the deployed one (`daMemC_of_deployed`) and the deployed completeness follows
(`da_verify_complete_of_comp`).
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.E2E.Complete

@[expose] public section

/-! ## The honest run over a model -/

/-- Cell `b` of row `i`'s digest, the model's answer. -/
def daCD (CM : CompModel) (w : Da.Witness) (b i : ℕ) : Digest :=
  ansD CM.hm ((daSym w b i).flatMap kBytes)

/-- Row `i`'s digest, the model's answer for its prefix cells' digests. -/
def daRD (CM : CompModel) (w : Da.Witness) (i : ℕ) : Digest :=
  ansD CM.hm ((List.range 64).flatMap fun b => digestBytes (daCD CM w b i))

/-- The vector's bytes, as the guest's `12288` blocks. -/
def daVX (w : Da.Witness) : List UInt8 :=
  (List.range (12287 + 1)).flatMap fun j => blockBytes (vecBlocks (daWs w) j)

/-- The vector hash's state before column `b`, over the model. -/
def daSC (CM : CompModel) (w : Da.Witness) (b : ℕ) : E × E :=
  CM.chainSt (daVX w) (ansD CM.hm (daVX w)) (96 * b)

/-- A tree of depth `k` over `leaf` and a model's pairs, every level as `da_levels` lays it out. -/
def TreeAtM (M : HashModel) (rd : Reader) (tree : E) (k : ℕ) (leaf : ℕ → Digest) : Prop :=
  ∀ l ≤ k, ∀ j < 2 ^ (k - l), CellsAt rd (tree * gen ^ (lvOff k l + 2 * j))
    [(digestScalars (nodeM M leaf l j)).1, (digestScalars (nodeM M leaf l j)).2]

/-- **The honest memory of `w`'s run over a completeness model** at the pointers `P` (`DaMem`). -/
def DaMemC (CM : CompModel) (rd : Reader) (P : DaPtrs) (w : Da.Witness) : Prop :=
  (∀ i < w.rows.length, LoadHolds rd (P.pb * gen ^ i) 0 (P.pd * gen ^ (128 * i))) ∧
  (∀ i < w.rows.length, ∀ b < 64, CellsAt rd (P.pd * gen ^ (128 * i + 2 * b))
    [(digestScalars (daCD CM w b i)).1, (digestScalars (daCD CM w b i)).2]) ∧
  (∀ b ≤ 128, CellsAt rd (P.hs * gen ^ (2 * b)) [(daSC CM w b).1, (daSC CM w b).2]) ∧
  CellsAt rd P.ctr ((List.range 385).map fun k => word (k * 2048) 0 0) ∧
  (∀ i < w.rows.length, LoadHolds rd (P.rb * gen ^ i) 0 (P.acc * gen ^ (129 * i))) ∧
  (∀ i < w.rows.length, ∀ b ≤ 128, LoadHolds rd (P.acc * gen ^ (129 * i)) b (daA w i b)) ∧
  TreeAtM CM.hm rd P.ct 7
    (fun b => nodeM CM.hm (colLeafM w.rows.length (daCD CM w) b) (LeanDa.logPad w.rows.length) 0) ∧
  TreeAtM CM.hm rd P.rt (LeanDa.logPad w.rows.length) (rowLeafM w.rows.length (daRD CM w)) ∧
  (∀ b < 128, TreeAtM CM.hm rd (P.node b) (LeanDa.logPad w.rows.length)
    (colLeafM w.rows.length (daCD CM w) b)) ∧
  (∀ b < 128, CellsAt rd (P.lv b) (daWs w b))

/-! ## Helpers -/

/-- An answered tree laid out in memory is `da_levels`' meaning over the model. -/
theorem levelsWith_of_treeAtM {M : HashModel} {rd : Reader} {tree : E} {k : ℕ} {leaf : ℕ → Digest}
    (h : TreeAtM M rd tree k leaf) (hA : TreeAns M leaf k) :
    Meaning_da_levelsWith M k rd [tree]
      [(digestScalars (nodeM M leaf k 0)).1, (digestScalars (nodeM M leaf k 0)).2] := by
  refine ⟨tree, _, _, rfl, rfl, ?_⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have := h 0 le_rfl 0 (by norm_num)
    rw [show lvOff 0 0 + 2 * 0 = 0 by rfl, pow_zero, mul_one] at this
    exact Or.inl ⟨rfl, this⟩
  · exact Or.inr ⟨hk, leaf, h, hA, rfl⟩

/-- A tree's leaf `j` over a model, as the cells at `tree·g^(2j)`. -/
theorem treeAtM_leaf {M : HashModel} {rd : Reader} {tree : E} {k : ℕ} {leaf : ℕ → Digest}
    (h : TreeAtM M rd tree k leaf) {j : ℕ} (hj : j < 2 ^ k) :
    CellsAt rd (tree * gen ^ (2 * j)) [(digestScalars (leaf j)).1, (digestScalars (leaf j)).2] := by
  have := h 0 (Nat.zero_le _) j (by simpa using hj)
  rw [lvOff, Nat.sub_zero, Nat.sub_self, Nat.zero_add] at this
  exact this

/-- The vector's blocks are its bytes. -/
theorem daVX_eq {w : Da.Witness} (hvl : w.vector.length = 2 ^ LeanDa.logM) :
    daVX w = w.vector.flatMap LeanVM.Node.eBytes := by
  have hws : ∀ b < 128, (daWs w b).length = 256 := fun b hb => length_chunk (n := 128) hvl hb
  have hvec : w.vector = (List.range 128).flatMap (daWs w) := (flatMap_chunks _ 256 128 hvl).symm
  rw [daVX, hvec, show 12287 + 1 = 96 * 128 by rfl, flatMap_range_mul 96, List.flatMap_assoc]
  refine List.flatMap_congr fun b hb => ?_
  have hb' := List.mem_range.mp hb
  rw [← vx_bytes _ (hws b hb')]
  refine List.flatMap_congr fun j hj => ?_
  have hj' := List.mem_range.mp hj
  show blockBytes (vxBlocks ((daWs w ((96 * b + j) / 96)).getD · 0) ((96 * b + j) % 96)) = _
  rw [show (96 * b + j) / 96 = b by omega, show (96 * b + j) % 96 = j by omega]

theorem nBlocks_daVX (w : Da.Witness) : ((daVX w).length - 1) / 64 = 12287 := by
  rw [daVX, CompModel.length_flatMap_blocks]

/-- The vector hash starts at the IV. -/
theorem daSC_zero (CM : CompModel) (w : Da.Witness) : daSC CM w 0 = digestScalars paramIv :=
  CM.chainSt_zero _ _

/-- The vector hash ends at the model's answer for the vector's bytes. -/
theorem daSC_last (CM : CompModel) (w : Da.Witness) :
    daSC CM w 128 = digestScalars (ansD CM.hm (daVX w)) :=
  CM.chainSt_succ_of _ (nBlocks_daVX w)

/-- The vector hash's state after row `j` of column `b`, over the model. -/
def daSt (CM : CompModel) (w : Da.Witness) (b j : ℕ) : E × E :=
  CM.chainSt (daVX w) (ansD CM.hm (daVX w)) (96 * b + j)

/-- Row `96b + j` of the vector hash over a model, as row `j` of column `b`'s. -/
theorem daSt_step (CM : CompModel) (w : Da.Witness)
    (hH : CM.H (daVX w) = some (ansD CM.hm (daVX w))) {b j : ℕ} (hb : b < 128) (hj : j < 96) :
    CM.sem.check (vxBlocks ((daWs w b).getD · 0) j) (daSt CM w b j).1 (daSt CM w b j).2
      (daSt CM w b (j + 1)).1 (daSt CM w b (j + 1)).2
      (vxMd (decide (b = 127)) (((List.range 4).map (cvOf b)).getD · 0) j) := by
  have hchk := CM.chain_checks_blocks (n := 12287) (blocks := vecBlocks (daWs w)) (md := vecMd) hH
    (fun j _ r => vxBlocks_canonical _ _ r)
    (fun j hj => by simp only [vecMd]; congr 1; simp only [decide_eq_false_iff_not]; omega)
    (by unfold vecMd; congr 1)
  have hcv : ∀ k < 4, ((List.range 4).map (cvOf b)).getD k 0 = cvOf b k := fun k hk => by
    rw [List.getD_eq_getElem _ _ (by simpa using hk)]; simp
  have hblk : vecBlocks (daWs w) (96 * b + j) = vxBlocks ((daWs w b).getD · 0) j := by
    show vxBlocks ((daWs w ((96 * b + j) / 96)).getD · 0) ((96 * b + j) % 96) = _
    rw [show (96 * b + j) / 96 = b by omega, show (96 * b + j) % 96 = j by omega]
  have hmd : vecMd (96 * b + j) =
      vxMd (decide (b = 127)) (((List.range 4).map (cvOf b)).getD · 0) j := by
    rw [vxMd_congr hcv hj, vxMd_counters hb hj]
    show metadataCell (64 * (96 * b + j + 1)) (decide (96 * b + j + 1 = 12288)) = _
    rw [decide_eq_decide.mpr (show 96 * b + j + 1 = 12288 ↔ (b = 127 ∧ j = 95) by omega)]
  have := hchk (96 * b + j) (by omega)
  rw [hblk, hmd] at this
  unfold daSt
  rw [← Nat.add_assoc]
  exact this

/-- **Column `b`'s part of the vector hash over a model**: its `96` rows, from the state after
`96b`, check under the model's semantics. -/
theorem daSC_col (CM : CompModel) (w : Da.Witness)
    (hH : CM.H (daVX w) = some (ansD CM.hm (daVX w))) {b : ℕ} (hb : b < 128) :
    ChainSteps CM.sem ((daSC CM w b).1, (daSC CM w b).2) (vxBlocks ((daWs w b).getD · 0))
      (vxMd (decide (b = 127)) (((List.range 4).map (cvOf b)).getD · 0)) 96
      ((daSC CM w (b + 1)).1, (daSC CM w (b + 1)).2) := by
  rw [Prod.mk.eta, Prod.mk.eta]
  have e0 : daSt CM w b 0 = daSC CM w b := rfl
  have e1 : daSt CM w b 96 = daSC CM w (b + 1) := by
    unfold daSt daSC
    rw [Nat.mul_succ]
  rw [← e0, ← e1]
  exact chainSteps_of_steps fun j hj => daSt_step CM w hH hb hj

/-! ## Completeness -/

/-- **`da_verify` is complete over a completeness model**: a witness opening `(root, vd)` over the
model's answers and, for any choice of the pointers, a memory holding the honest words of its run
over the model give `da_verify`'s relation under `CM.sem`, returning their cells
(`da_verify_complete`). -/
theorem da_verify_completeC {CM : CompModel} {rd : Reader} (hm : MemOk rd) {gsq : E}
    (hT : SquaresAt rd gsq) {root vd : Digest} {w : Da.Witness}
    (hw : w.OpensWith CM.H (Da.toBytes padCellD) (Da.toBytes padRowD) root vd) (P : DaPtrs)
    (hP : DaMemC CM rd P w) :
    coreProgram.RelB CM.sem rd "da_verify" [gsq]
      [(digestScalars root).1, (digestScalars root).2, (digestScalars vd).1, (digestScalars vd).2] := by
  obtain ⟨hr1, hr2, hrl, hcom, hvl, hvd, hdot⟩ := hw
  obtain ⟨m88, mpd, mhs, mctr, m89, macc, mct, mrt, mnode, mlv⟩ := hP
  set r := w.rows.length with hr
  set lp := LeanDa.logPad r
  have hr33 : r < 2 ^ 33 := by unfold LeanDa.maxRows at hr2; omega
  have hlp : lp ≤ 10 := logPad_le hr2
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
  have hcol : ∀ b < 128, Meaning_da_verify_columnComp CM (decide (b < 64)) rd
      [gen ^ b, gen ^ r, gen ^ LeanDa.nPad r, gen ^ (LeanDa.nPad r - r), gen ^ lp,
        P.pb, P.ct, P.rb, P.hs, P.ctr] [] := by
    intro b hb
    have hcvl : ((List.range 4).map (cvOf b)).length = 4 := by simp
    refine ⟨_, _, _, _, _, _, _, _, _, _, rfl, rfl, (daSC CM w b).1, (daSC CM w b).2,
      (daSC CM w (b + 1)).1, (daSC CM w (b + 1)).2, P.lv b, P.node b,
      (digestScalars (nodeM CM.hm (colLeafM r (daCD CM w) b) lp 0)).1,
      (digestScalars (nodeM CM.hm (colLeafM r (daCD CM w) b) lp 0)).2, ?_, ?_, ?_,
      isInK_gen_pow r, fun _ => loopTo_of_all hr1 hr33 fun i hi => ?_, isInK_gen_pow _,
      fun hne => ?_, ⟨lp, by omega, rfl, levelsWith_of_treeAtM (mnode b hb) (hCT b hb)⟩, ?_⟩
    · rw [gen_sq]; exact mhs b (by omega)
    · refine ⟨gen ^ b, _, rfl, isInK_gen_pow b, ?_⟩
      rw [decide_gen127 hb]
      refine ⟨_, _, _, _, _, _, _, rfl, rfl, daWs w b, (List.range 4).map (cvOf b), hws b hb, hcvl,
        fun k hk => ?_, daSC_col CM w (by rw [hvdA]; exact hVX) hb,
        frameRun_of_cells (by rw [hws b hb]; norm_num) (mlv b hb)⟩
      have hk' : k < 4 := by simpa using hk
      rw [show gen ^ b * gen ^ b * gen ^ b = gen ^ (3 * b) by
          rw [← pow_add, ← pow_add]; congr 1; ring,
        loadHolds_mul_gen_pow]
      simp only [List.getElem_map, List.getElem_range, cvOf, Nat.add_mul]
      have := ctr_load mctr (k := 3 * b + k) (by omega)
      rwa [Nat.add_mul] at this
    · rw [show gen ^ b * gen * (gen ^ b * gen) = gen ^ (2 * (b + 1)) by
        rw [← pow_succ, ← pow_add]; congr 1; ring]
      exact mhs (b + 1) (by omega)
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
    · have hpos : 0 < LeanDa.nPad r - r := by
        by_contra h0
        exact hne (by rw [show LeanDa.nPad r - r = 0 by omega, pow_zero])
      refine loopTo_of_all hpos (by omega) fun d hd => ?_
      unfold GapStep
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
  refine da_verify_of_factsC hm hT ⟨r, P.pb, P.pd, P.hs, P.ctr, P.acc, P.rb, P.ct, P.rt, _, _, _, _,
    hr1, hr2, fun i hi => ?_, (cellsAt_two.mp hs0).1, (cellsAt_two.mp hs0).2, (mctr 0 (by simp)).1,
    fun k hk v hv => ?_, fun i hi => ⟨?_, ?_⟩, hcol, fun i hi => ⟨P.acc * gen ^ (129 * i), ?_, ?_⟩,
    levelsWith_of_treeAtM mct hTop, h93, fun d hd => ?_, levelsWith_of_treeAtM mrt hRT,
    pair_comp CM hRoot, x0, x1⟩
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

/-! ## At the deployed model -/

/-- At the deployed model the vector hash's states are the deployed ones. -/
theorem daSC_deployed (w : Da.Witness) {b : ℕ} (hb : b ≤ 128) :
    daSC CompModel.deployed w b = digestScalars (daS w b) := by
  rcases Nat.lt_or_eq_of_le hb with hb | rfl
  · have hle : 96 * b ≤ nBlocks (daVX w) := by
      show 96 * b ≤ ((daVX w).length - 1) / 64
      rw [nBlocks_daVX]; omega
    have hpre : prefixAt (daVX w) (96 * b) =
        (List.range (96 * b)).map fun j => blockBytes (vecBlocks (daWs w) j) :=
      List.map_congr_left fun j hj =>
        CompModel.blockAt_blocks _ (by have := List.mem_range.mp hj; omega)
    rw [daSC, CompModel.chainSt_of_le _ _ hle, hpre, daS, chainRun_nonfinal (t := 0) (96 * b)
      (fun j hj => by
        simp only [vecMd, Nat.zero_add]; congr 1; simp only [decide_eq_false_iff_not]; omega)]
    rfl
  · have hd : CompModel.deployed.hm.H (daVX w) = some (blake2sBytes (daVX w)) := rfl
    rw [daSC_last, ansD_of hd, daS, show 96 * 128 = 12287 + 1 by rfl,
      chainRun_blocks (blocks := vecBlocks (daWs w)) (md := vecMd) (n := 12287)
        (fun j _ r => vxBlocks_canonical _ _ r)
        (fun j hj => by simp only [vecMd]; congr 1; simp only [decide_eq_false_iff_not]; omega)
        (by unfold vecMd; congr 1)]
    rfl

/-- At the deployed model the honest memory is the deployed one. -/
theorem daMemC_of_deployed {rd : Reader} {P : DaPtrs} {w : Da.Witness} (h : DaMem rd P w) :
    DaMemC CompModel.deployed rd P w := by
  obtain ⟨m88, mpd, mhs, mctr, m89, macc, mct, mrt, mnode, mlv⟩ := h
  have ecD : daCD CompModel.deployed w = cellDOf (daSym w) := rfl
  have erD : daRD CompModel.deployed w = rowDOf (daSym w) := rfl
  have ecol : ∀ b, colLeafM w.rows.length (daCD CompModel.deployed w) b =
      colLeafOf w.rows.length (daSym w) b := fun b => rfl
  have erow : rowLeafM w.rows.length (daRD CompModel.deployed w) =
      rowLeafOf w.rows.length (daSym w) := rfl
  have etree : ∀ {tree k leaf}, TreeAtM CompModel.deployed.hm rd tree k leaf ↔ TreeAt rd tree k leaf :=
    fun {tree k leaf} => by simp only [TreeAtM, TreeAt, nodeM_deployed]
  refine ⟨m88, mpd, fun b hb => ?_, mctr, m89, macc, ?_, ?_, fun b hb => ?_, mlv⟩
  · rw [daSC_deployed w hb]; exact mhs b hb
  · rw [etree]
    simp only [ecol, nodeM_deployed]
    exact mct
  · rw [etree, erow]; exact mrt
  · rw [etree, show colLeafM w.rows.length (daCD CompModel.deployed w) b =
      colLeafOf w.rows.length (daSym w) b from funext fun _ => rfl]
    exact mnode b hb

/-- The deployed completeness of `da_verify` (`da_verify_complete`), from the model's at
`CompModel.deployed`. -/
theorem da_verify_complete_of_comp {rd : Reader} (hm : MemOk rd) {gsq : E} (hT : SquaresAt rd gsq)
    {root vd : Digest} {w : Da.Witness} (hw : w.Opens root vd) (P : DaPtrs) (hP : DaMem rd P w) :
    coreProgram.Rel rd "da_verify" [gsq]
      [(digestScalars root).1, (digestScalars root).2, (digestScalars vd).1, (digestScalars vd).2] := by
  rw [← relB_deployed]
  exact da_verify_completeC (CM := CompModel.deployed) hm hT ((opensWith_deployed_iff root vd w).mpr hw)
    P (daMemC_of_deployed hP)

end
end LeanVM.Guest.B1.Digest
