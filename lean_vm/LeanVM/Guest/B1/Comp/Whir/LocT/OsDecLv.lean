/-
  LeanVM.Guest.B1.Comp.Whir.LocT.OsDecLv

  A level's openings decoded from its `opening_queries` tree, the cap's siblings from its
  `verify_merkle_cap` tree's loads.
-/

module

public import LeanVM.Guest.B1.Comp.Whir.LocT.OsLvT
public import LeanVM.Guest.B1.Comp.Whir.LocT.CapSibs

/-!
# A level's openings, decoded

`lvDecC`: at a level of an honest run, on a reader satisfying the load equations of the level's
`opening_queries` tree and of its `verify_merkle_cap` tree, with frame valuations linked to the
former, the decoder `wqV` gives the level's openings: the queries' tree decodes them with the cap's
siblings the reader holds (`OsLvQ`), which are the honest cap's (`capSibs_agree`), the openings'
paths above the cap (`capSibs_honestW`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub
open LeanVM.Guest.B1.Main (MemL RegionL)
open LeanVM.E2E.Complete
open LeanVM.Guest.Located (oqLookup)
open LeanVM.Protocol.Compile (Bytes)
open LeanVM.Protocol (Digest)

@[expose] public section

variable {Ht : Bytes → Digest} {CM : CompModel}

theorem take_eq_map_getD {α : Type} (l : List α) (d0 : α) {n : ℕ} (h : n ≤ l.length) :
    l.take n = (List.range n).map fun j => l.getD j d0 := by
  apply List.ext_getElem (by simp; omega)
  intro i h1 h2
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < l.length by simp at h1; omega)]

namespace OsData

variable {fs : String → ℕ} {cert : String → V → ℕ} {κ : ℕ} {cfg : OsCfg} {d : OsData} {bd : String → ℕ}

/-- **A level's openings, decoded.** -/
theorem lvDecC {μ r : ℕ} {Lall : List Whir.Level} (hok : OsCfgOk cfg μ r Lall) (hlay : OsLayoutOk cfg)
    (hkT : OsKidsAtBCT CM Ht fs cert κ cfg bd) {Lin : Main.Layout} {b : ℕ}
    (hbuf : ∀ rd, MemL rd (osLkW Ht cfg d Lin b) → OsBufReadsW Ht rd cfg d b []) {Q : List (ℕ × List (ℕ × Opening))}
    (hQ : ∀ x ∈ Q, BatchAgreesW Ht x.1 x.2) {l : ℕ} (hl : l < cfg.levels.length)
    (hF : OsLvFactsW CM.hm Ht cfg μ d.xs Lall Q (d.lvW Ht cfg l)) (hlv : (d.lvW Ht cfg l).lvl = l)
    {rd rd' : Reader} (hm : MemL rd (osLkW Ht cfg d Lin b)) {V : FrameVals} {k tc : Tree}
    {qa qr : List E} (hqa : qa.getD 0 0 = (osPtrsOf cfg b).caps * gen ^ (4 * (cfg.lv l).capOff))
    (hk : OsLvQ Ht cfg d l qa k) (hks : Sat rd' (k.loadEqns coreProgram)) (hkl : KidsLink V k)
    (hka : B2C.NodeAgree k (V (cfg.lv l).queriesFn qa qr))
    (htl : CapLoadsQ (cfg.lv l).capDepth rd (osCapArgs cfg b l) tc) (htr : Sat rd (tc.loadEqns coreProgram))
    (hts : Sat rd' (tc.loadEqns coreProgram)) :
    wqV rd' V cfg l qa qr = (d.lvW Ht cfg l).osp.take (cfg.lv l).queries := by
  have hspec := hok.spec l (by rw [hok.len]; exact hl)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hcd1, hcd2, -, -, -, -, -, -, -, -, -⟩ := hspec
  set L := d.lvW Ht cfg l with hL'
  have hst := hF.step
  rw [hlv] at hst
  have hoa := lv_openC (Ht := Ht) (CM := CM) hF hlv
  have hcap := os_capOk_ofW hoa (hQ _ hst) rfl (hlay.queries l hl) hcd1 hcd2
  obtain ⟨os1, hosp, hl1, -, -⟩ := os_openAll_invW _ _ _ _ hoa
  have hqsl : (osHQsW Ht cfg l d.xs L.p L.H.cv1).length = (cfg.lv l).queries := by simp [osHQsW]
  rw [hqsl] at hl1
  obtain ⟨Bq, ⟨loopq, blocksq, hlk, -⟩, -⟩ := hkT l hl
  have hb := hbuf rd hm
  have hcells := os_seg_readsAt (off := fun l => 4 * (cfg.lv l).capOff)
    (c := fun l => osCapCellsW Ht (cfg.lv l).depth (cfg.lv l).capDepth (d.qsW Ht cfg l)) hb.caps
    (fun a c hac hc => by rw [os_capCells_lengthW]; exact hlay.caps a c hac hc)
    (fun a ha => by rw [os_capCells_lengthW]; exact hlay.capsFit a ha) hl
  have hflags := os_seg_readsAt (off := fun l => (cfg.lv l).capOff)
    (c := fun l => osCapFlags (cfg.lv l).depth (cfg.lv l).capDepth (d.qsW Ht cfg l)) hb.flags
    (fun a c hac hc => by simp only [osCapFlags, List.length_map, List.length_range]; exact hlay.flags a c hac hc)
    (fun a ha => by simp only [osCapFlags, List.length_map, List.length_range]; exact hlay.flagsFit a ha) hl
  simp only [OsLvQ, hlk] at hk
  have hdec := hk rd' V _ hks hkl hka
  simp only [wqV, hlk, wqDecV, frameDecV]
  rw [hdec, take_eq_map_getD L.osp ⟨[], []⟩ (by rw [hosp, List.length_append]; omega)]
  refine List.map_congr_left fun j hj => ?_
  have hj' := List.mem_range.mp hj
  have hgj : L.osp.getD j ⟨[], []⟩ = os1.getD j ⟨[], []⟩ := by
    rw [hosp, List.getD_append _ _ _ _ (by omega)]
  have hmem : ((osHQsW Ht cfg l d.xs L.p L.H.cv1).getD j 0, L.osp.getD j ⟨[], []⟩) ∈
      (osHQsW Ht cfg l d.xs L.p L.H.cv1).zip L.osp := by
    rw [hgj, hosp]
    refine List.mem_iff_getElem.mpr ⟨j, by rw [List.length_zip, List.length_append, hqsl]; omega, ?_⟩
    simp only [List.getElem_zip, List.getElem_append_left (show j < os1.length by omega)]
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
  have hpos := hcap.pos _ hmem
  have hplen := hcap.len _ hmem
  simp only at hpos hplen
  have e1 : 2 ^ (cfg.lv l).capDepth + (osHQsW Ht cfg l d.xs L.p L.H.cv1).getD j 0 /
      2 ^ ((cfg.lv l).depth - (cfg.lv l).capDepth) =
      heapNode (cfg.lv l).depth ((osHQsW Ht cfg l d.xs L.p L.H.cv1).getD j 0) ((cfg.lv l).depth - (cfg.lv l).capDepth) := by
    unfold heapNode; rw [show (cfg.lv l).depth - ((cfg.lv l).depth - (cfg.lv l).capDepth) = (cfg.lv l).capDepth by omega]
  have hh : capSibs rd ((osPtrsOf cfg b).caps * gen ^ (4 * (cfg.lv l).capOff)) (cfg.lv l).capDepth
      (heapNode (cfg.lv l).depth ((osHQsW Ht cfg l d.xs L.p L.H.cv1).getD j 0) ((cfg.lv l).depth - (cfg.lv l).capDepth)) =
      (L.osp.getD j ⟨[], []⟩).path.drop ((cfg.lv l).depth - (cfg.lv l).capDepth) :=
    capSibs_honestW hcap hcells hmem (cfg.lv l).capDepth ((cfg.lv l).depth - (cfg.lv l).capDepth) (by omega) le_rfl
  simp only [oqHonest]
  rw [hqa, e1, capSibs_agree (cap := (osPtrsOf cfg b).caps * gen ^ (4 * (cfg.lv l).capOff))
    (flags := (osPtrsOf cfg b).flags * gen ^ (cfg.lv l).capOff) htl htr hts hpos hcd2 (fun l' h1 h2 => ?_), hh,
    List.take_append_drop]
  have := os_onClimb_flag hflags (os_heapNode_cap hpos h1 h2.le) ⟨_, hmem, l', h1, h2.le, rfl⟩
  have e : memAt rd ((osPtrsOf cfg b).flags * gen ^ (cfg.lv l).capOff)
      (heapNode (cfg.lv l).depth ((osHQsW Ht cfg l d.xs L.p L.H.cv1).getD j 0) l') = 1 := memAt_of_load this
  rw [e]
  exact one_ne_zero

end OsData

end
end LeanVM.Guest.B1
