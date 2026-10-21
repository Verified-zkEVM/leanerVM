/-
  LeanVM.Guest.B1.Comp.Whir.LocT.OsDecRoot

  `open_stacked`'s openings decoded at its node, from its callees' trees.
-/

module

public import LeanVM.Guest.B1.Comp.Whir.LocT.OsRootDec
public import LeanVM.Guest.B1.Comp.Whir.LocT.OsFinal2T

/-!
# The root's openings, decoded

`os_decQC`: at an honest run, `open_stacked`'s node whose callees are valid and satisfy the
predicates `kids_atBCT` gives them (`osLvsQs` of `osQB`), on every reader satisfying the node's
load equations, every frame valuation linked to it and every valuation agreeing with it on its named
cells, the decoder `osOsOf` gives the run's openings: level by level the queries' trees decode them
(`lvDecC`), chained (`osp_flatten`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub
open LeanVM.Guest.B1.Main (MemL RegionL)
open LeanVM.E2E.Complete
open LeanVM.Protocol.Compile (Bytes)
open LeanVM.Protocol (Digest)

@[expose] public section

variable {Ht : Bytes → Digest} {CM : CompModel}

namespace OsData

variable {fs : String → ℕ} {cert : String → V → ℕ} {κ : ℕ} {cfg : OsCfg} {d : OsData} {bd : String → ℕ}

set_option maxHeartbeats 1000000 in
/-- **`open_stacked`'s openings, decoded at its node.** -/
theorem os_decQC {μ r : ℕ} {Lall : List Whir.Level} (hok : OsCfgOk cfg μ r Lall) (hbf : OsBodyFacts cfg)
    (hkT : OsKidsAtBCT CM Ht fs cert κ cfg bd) {w : WhirEnd} (hkit : OsRunKitC CM Ht cfg μ Lall d w)
    (hlast : ((d.lvsW Ht cfg).getLastD default).H.osq = []) {Lin : Main.Layout} {b0 : ℕ} {name : String}
    (hcells : CellsOk name (osLvsReads cfg 0 cfg.levels (osHead cfg).2)) {fn : Fn}
    (hfind : coreProgram.find? name = some fn) {σ : Val} {es : List Memory.Ev} {vs : List V}
    (hw : walk σ fn.body = .ret es vs)
    (hcalls : calls es = (osLvsKOf cfg σ 0 (osHead cfg).2 cfg.levels.length).flatMap OsLvK.calls ++
      ((((osTail cfg.yrLog (OsRun.sL cfg)).1.filterMap Main.Stmt.callS).map (Main.mkCall σ)) ++
        ((osFinPre cfg).filterMap Main.Stmt.callS).map (Main.mkCall σ)))
    {rd : Reader} (hmk : MemL rd (osLkW Ht cfg d Lin b0)) {bufs bs : List ℕ} {ks : List Tree}
    (hkv : Tree.KidsValidB CM.sem coreProgram rd σ ((osLvsKOf cfg σ 0 (osHead cfg).2 cfg.levels.length).flatMap OsLvK.calls ++
      ((((osTail cfg.yrLog (OsRun.sL cfg)).1.filterMap Main.Stmt.callS).map (Main.mkCall σ)) ++
        ((osFinPre cfg).filterMap Main.Stmt.callS).map (Main.mkCall σ))) ks)
    (hks : KidsSat ((osLvsKOf cfg σ 0 (osHead cfg).2 cfg.levels.length).flatMap OsLvK.calls ++
      ((((osTail cfg.yrLog (OsRun.sL cfg)).1.filterMap Main.Stmt.callS).map (Main.mkCall σ)) ++
        ((osFinPre cfg).filterMap Main.Stmt.callS).map (Main.mkCall σ)))
      (osLvsQs (fun l f a b t => osQB Ht cfg d b0 l f a b rd t) σ 0 (osLvsKOf cfg σ 0 (osHead cfg).2 cfg.levels.length) ++
        ((((osTail cfg.yrLog (OsRun.sL cfg)).1.filterMap Main.Stmt.callS).map (Main.mkCall σ)).map (fun _ _ _ => True) ++
          (((osFinPre cfg).filterMap Main.Stmt.callS).map (Main.mkCall σ)).map (fun _ _ _ => True)))
      bs ks)
    (hbl : bs.length = ks.length) :
    ∀ (rd' : Reader) (V : FrameVals) (σ' : Val), Sat rd' ((Memory.Tree.node name σ bufs ks).loadEqns coreProgram) →
      KidsLink V (Memory.Tree.node name σ bufs ks) → B2C.NodeAgree (Memory.Tree.node name σ bufs ks) σ' →
      osOsOf cfg σ' (wqV rd' V cfg) = d.os := by
  intro rd' V σ' hsat hlink hag
  rw [← hcalls] at hkv hks
  set n := cfg.levels.length with hn
  have hlinkc : KidsLinkCalls V σ (calls es) ks := by
    have := hlink.1
    rwa [events_node hfind hw] at this
  have hkl : KidsLinkKids V ks := hlink.2
  -- a level's queries call, and its cap call
  have hqB : ∀ l (hl : l < n), (⟨(cfg.lv l).queriesFn, (osQCall cfg (cfg.lv l) l (osLevelQState cfg l (cfg.lv l)
      (osStAt cfg 0 (osHead cfg).2 l))).1, [.n (osQCall cfg (cfg.lv l) l (osLevelQState cfg l (cfg.lv l)
      (osStAt cfg 0 (osHead cfg).2 l))).2], true⟩ : Call) ∈ ((osLvsKOf cfg σ 0 (osHead cfg).2 n)[l]'(by rw [osLvsKOf_length]; omega)).B := fun l hl => by
    rw [osLvsKOf_getElem cfg σ n 0 _ l (by rw [osLvsKOf_length]; omega), Nat.zero_add]
    exact osLvKOf_qcall cfg σ l _
  have hcB : ∀ l (hl : l < n), (⟨(cfg.lv l).verifyCap, (osCapCallV (cfg.lv l) (osLevelQState cfg l (cfg.lv l)
      (osStAt cfg 0 (osHead cfg).2 l))).1, (osCapCallV (cfg.lv l) (osLevelQState cfg l (cfg.lv l)
      (osStAt cfg 0 (osHead cfg).2 l))).2, true⟩ : Call) ∈ ((osLvsKOf cfg σ 0 (osHead cfg).2 n)[l]'(by rw [osLvsKOf_length]; omega)).B := fun l hl => by
    rw [osLvsKOf_getElem cfg σ n 0 _ l (by rw [osLvsKOf_length]; omega), Nat.zero_add]
    exact osLvKOf_capcall cfg σ l _
  have hinCalls : ∀ l (hl : l < n), ∀ c ∈ ((osLvsKOf cfg σ 0 (osHead cfg).2 n)[l]'(by rw [osLvsKOf_length]; omega)).B, c ∈ calls es := fun l hl c hc => by
    rw [hcalls]
    exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨_, List.getElem_mem _,
      List.mem_append_right _ (List.mem_cons_of_mem _ hc)⟩)
  have hinZip : ∀ l (hl : l < n), ∀ c ∈ ((osLvsKOf cfg σ 0 (osHead cfg).2 n)[l]'(by rw [osLvsKOf_length]; omega)).B,
      (c, fun b t => osQB Ht cfg d b0 l c.f (c.args.map σ) b rd t) ∈ (calls es).zip
        (osLvsQs (fun l f a b t => osQB Ht cfg d b0 l f a b rd t) σ 0 (osLvsKOf cfg σ 0 (osHead cfg).2 n) ++
          ((((osTail cfg.yrLog (OsRun.sL cfg)).1.filterMap Main.Stmt.callS).map (Main.mkCall σ)).map (fun _ _ _ => True) ++
            (((osFinPre cfg).filterMap Main.Stmt.callS).map (Main.mkCall σ)).map (fun _ _ _ => True))) := by
    intro l hl c hc
    rw [hcalls, List.zip_append (by rw [length_osLvsQs])]
    have := osLvsQs_zip_mem (fun l f a b t => osQB Ht cfg d b0 l f a b rd t) σ (osLvsKOf cfg σ 0 (osHead cfg).2 n) 0 l
      (by rw [osLvsKOf_length]; omega) c hc
    rw [Nat.zero_add] at this
    exact List.mem_append_left _ this
  -- the root reads only the queries calls' values
  have hreads : ∀ v ∈ osLvsReads cfg 0 cfg.levels (osHead cfg).2, σ' v = σ v := fun v hv => by
    obtain ⟨i, hi, hv'⟩ := osLvsReads_mem cfg n 0 _ (by omega) v (by simpa using hv)
    rw [Nat.zero_add] at hv'
    exact nodeAgree_read hfind hw hag hcells hv (mem_named_call (hinCalls i hi _ (hqB i hi)) rfl hv')
  -- the run's levels
  obtain ⟨sp', Q', hQ, hch⟩ := hkit.chain
  have hrun := d.runOk_ofC (Ht := Ht) (CM := CM) hok hkit.len hch hkit.chst
  have hlay := hbf.layout
  have hbuf : ∀ rd, MemL rd (osLkW Ht cfg d Lin b0) → OsBufReadsW Ht rd cfg d b0 [] :=
    fun rd hm => os_bufReadsC (Ht := Ht) (Main.memL_append.mp hm).2
  have hLl : (d.lvsW Ht cfg).length = n := by
    simp only [lvsW]; rw [os_lvsList_lengthC (Ht := Ht), hkit.len]
  have hlvF : ∀ l < n, OsLvFactsW CM.hm Ht cfg μ d.xs Lall Q' (d.lvW Ht cfg l) ∧ (d.lvW Ht cfg l).lvl = l := by
    intro l hl
    have hmem : d.lvW Ht cfg l ∈ d.lvsW Ht cfg := by
      simp only [lvW]; rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
    refine ⟨os_chain_memC (Ht := Ht) (CM := CM) d.Hs 0 _ _ _ _ _ hch _ hmem, ?_⟩
    simp only [lvW]
    rw [List.getD_eq_getElem _ _ (by omega)]
    have := os_lvsList_lvlC (Ht := Ht) cfg d.xs d.Hs 0 (d.cv0W Ht) 2 (osW0 d.target d.xs) d.os (d.roots0 cfg) l
      (by simp only [lvsW] at hLl; omega)
    rw [Nat.zero_add] at this
    exact this
  -- level by level
  rw [osOsOf, osLevelsOs_congr cfg 0 _ _ hreads, show cfg.levels = cfg.levels.drop 0 from rfl,
    osLevelsOs_range cfg σ _ n 0 _ (by omega)]
  have hsplit : ∀ i < n, ((d.lvsW Ht cfg).getD i default).osp =
      ((d.lvsW Ht cfg).getD i default).osp.take (cfg.lv i).queries ++ ((d.lvsW Ht cfg).getD i default).H.osq := by
    intro i hi
    obtain ⟨hF, hlv⟩ := hlvF i hi
    obtain ⟨os1, hosp, hl1, -, -⟩ := os_openAll_invW _ _ _ _ (lv_openC (Ht := Ht) (CM := CM) hF hlv)
    have hqsl : (osHQsW Ht cfg i d.xs (d.lvW Ht cfg i).p (d.lvW Ht cfg i).H.cv1).length = (cfg.lv i).queries := by
      simp [osHQsW]
    rw [hqsl] at hl1
    show (d.lvW Ht cfg i).osp = (d.lvW Ht cfg i).osp.take _ ++ (d.lvW Ht cfg i).H.osq
    rw [hosp, List.take_left' hl1]
  have hflat := osp_flatten (d.lvsW Ht cfg) (fun i => (cfg.lv i).queries) n hsplit
    (fun i hi => osLvsListW_getD_succ Ht cfg d.xs d.Hs 0 (d.cv0W Ht) 2 (osW0 d.target d.xs) d.os (d.roots0 cfg) i
      (by rw [hkit.len]; omega))
    (by rw [← hlast, List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, hLl, List.getD_eq_getElem?_getD])
    (by have := hok.len2; omega)
  have h0 : ((d.lvsW Ht cfg).getD 0 default).osp = d.os :=
    osLvsListW_getD_osp Ht cfg d.xs d.Hs 0 (d.cv0W Ht) 2 (osW0 d.target d.xs) d.os (d.roots0 cfg)
      (by intro h; simp only [lvsW] at hLl; rw [h] at hLl; have := hok.len2; simp [osLvsListW] at hLl; omega)
  rw [h0] at hflat
  rw [hflat]
  refine List.flatMap_congr fun l hl' => ?_
  have hl := List.mem_range.mp hl'
  obtain ⟨hF, hlv⟩ := hlvF l hl
  simp only [Nat.zero_add]
  unfold osLevelOs osQueriesOs
  -- the queries' tree
  obtain ⟨k, hkm, bq, hq, -, -, hka⟩ := kidsSat_zip hkv hks hlinkc hbl _ (hinZip l hl _ (hqB l hl)) rfl
  obtain ⟨hqa, hk⟩ := hq.1 (by simp [osQCall])
  -- the cap's tree
  obtain ⟨tc, htm, bc, hc, htv, -, -⟩ := kidsSat_zip hkv hks hlinkc hbl _ (hinZip l hl _ (hcB l hl)) rfl
  obtain ⟨hca, hcl⟩ := hc.2 rfl (by simp [osCapCallV])
  rw [hca] at hcl
  obtain ⟨Bq, ⟨loopq, blocksq, hlk, -⟩, -⟩ := hkT l hl
  have hdecl := lvDecC (Ht := Ht) (CM := CM) hok hlay hkT hbuf hQ hl hF hlv hmk (k := k) (tc := tc)
    (qr := [σ (.n (osQCall cfg (cfg.lv l) l (osLevelQState cfg l (cfg.lv l) (osStAt cfg 0 (osHead cfg).2 l))).2)])
    (by rw [hqa]; rfl) hk (fun q hq' => hsat q (mem_loadEqns_kid hkm hq')) (kidsLinkKids_mem hkm hkl)
    (hka (mem_osDecNames_name hlk)) hcl (validB_loadEqns tc htv) (fun q hq' => hsat q (mem_loadEqns_kid htm hq'))
  exact hdecl

end OsData

end
end LeanVM.Guest.B1
