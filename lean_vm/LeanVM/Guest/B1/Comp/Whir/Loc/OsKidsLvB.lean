/-
  LeanVM.Guest.B1.Comp.Whir.Loc.OsKidsLvB

  A level's kids of `open_stacked`, bounded, over a completeness model (`Whir/OsKidsLvB.lean`)
-/

module

public import LeanVM.Guest.B1.Whir.OsKidsLvB
public import LeanVM.Guest.B1.Comp.Whir.Loc.OsKidsAB
public import LeanVM.Guest.B1.Comp.Whir.Loc.OsFinal1
public import LeanVM.Guest.B1.Comp.Whir.Loc.LvAns

/-!
# A level's kids of `open_stacked`, bounded, over a completeness model (`Whir/OsKidsLvB.lean`)
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

/-- **A level's callees before its positions, bounded.** -/
theorem lvCallABC {μ r : ℕ} {Lall : List Whir.Level} (hok : OsCfgOk cfg μ r Lall) (hlay : OsLayoutOk cfg)
    (hk : OsKidsAtBC CM Ht fs cert κ cfg bd) {Lin : Main.Layout} {b : ℕ} {cur : E}
    (hLin : ∀ rd, LowDef κ rd → MemL rd Lin → ReadsAt rd cur d.xs)
    (hbuf : ∀ rd, MemL rd (osLkW Ht cfg d Lin b) → OsBufReadsW Ht rd cfg d b [])
    {Q : List (ℕ × List (ℕ × Opening))} {l : ℕ} (hl : l < cfg.levels.length)
    (hF : OsLvFactsW CM.hm Ht cfg μ d.xs Lall Q (d.lvW Ht cfg l)) (hlv : (d.lvW Ht cfg l).lvl = l) :
    (∀ (cv' : Digest) (p' : ℕ) (q' : List E), q'.length = 3 → p' + 2 ≤ d.xs.length →
      RunsToM CM.hm (foldStep q') cv' [d.xs.getD p' 0, d.xs.getD (p' + 1) 0]
        (challengeOf (sqCvW Ht cv'), polyEval q' (challengeOf (sqCvW Ht cv')),
          [d.xs.getD p' 0, polyEval q' (challengeOf (sqCvW Ht cv')) + d.xs.getD (p' + 1) 0, d.xs.getD (p' + 1) 0])
        (obsAllW Ht (sqCvW Ht cv') [d.xs.getD p' 0, d.xs.getD (p' + 1) 0]) →
      osKCBC CM fs cert κ bd (osLkW Ht cfg d Lin b) "opening_fold" [(digestScalars cv').1, (digestScalars cv').2,
        cur * gen ^ p', q'.getD 0 0, q'.getD 1 0, q'.getD 2 0] (osFoldRetsW Ht d.xs cv' p' q' (cur * gen ^ p'))) ∧
    (l = cfg.yrLevel → osKCBC CM fs cert κ bd (osLkW Ht cfg d Lin b) cfg.finalMsg
      [(digestScalars (d.lvW Ht cfg l).H.cv1).1, (digestScalars (d.lvW Ht cfg l).H.cv1).2,
        cur * gen ^ osHP1 cfg l (d.lvW Ht cfg l).p, (osPtrsOf cfg b).fmsg]
      [(digestScalars (osHCv2W Ht cfg l d.xs (d.lvW Ht cfg l).p (d.lvW Ht cfg l).H.cv1)).1,
        (digestScalars (osHCv2W Ht cfg l d.xs (d.lvW Ht cfg l).p (d.lvW Ht cfg l).H.cv1)).2,
        cur * gen ^ osHP2 cfg l (d.lvW Ht cfg l).p]) ∧
    (l ≠ cfg.yrLevel → osKCBC CM fs cert κ bd (osLkW Ht cfg d Lin b) "assert_canonical" [osHW cfg l d.xs (d.lvW Ht cfg l).p 0] [0] ∧
      osKCBC CM fs cert κ bd (osLkW Ht cfg d Lin b) "assert_canonical" [osHW cfg l d.xs (d.lvW Ht cfg l).p 1] [0] ∧
      osKCBC CM fs cert κ bd (osLkW Ht cfg d Lin b) "opening_ood_point"
        [(digestScalars (osHCv12W Ht cfg l d.xs (d.lvW Ht cfg l).p (d.lvW Ht cfg l).H.cv1)).1,
          (digestScalars (osHCv12W Ht cfg l d.xs (d.lvW Ht cfg l).p (d.lvW Ht cfg l).H.cv1)).2,
          (osPtrsOf cfg b).oodz * osGw ((l + 1 + 0) * 22), osGw (cfg.lv l).logCols]
        [(digestScalars (sqAllW Ht (cfg.lv l).logCols (osHCv12W Ht cfg l d.xs (d.lvW Ht cfg l).p (d.lvW Ht cfg l).H.cv1)).2).1,
          (digestScalars (sqAllW Ht (cfg.lv l).logCols (osHCv12W Ht cfg l d.xs (d.lvW Ht cfg l).p (d.lvW Ht cfg l).H.cv1)).2).2]) ∧
    osKCBC CM fs cert κ bd (osLkW Ht cfg d Lin b) "grind_check"
      [(digestScalars (osHCv2W Ht cfg l d.xs (d.lvW Ht cfg l).p (d.lvW Ht cfg l).H.cv1)).1,
        (digestScalars (osHCv2W Ht cfg l d.xs (d.lvW Ht cfg l).p (d.lvW Ht cfg l).H.cv1)).2, osHNonce cfg l d.xs (d.lvW Ht cfg l).p,
        osGw (cfg.lv l).grindBits] [] := by
  have hspec := hok.spec l (by rw [hok.len]; exact hl)
  obtain ⟨-, -, -, hml0, hml1, hlc, -, hgr, -, -, -, -, -, -, -, -, -, -, -, -, -, h22, -, -, -⟩ := hspec
  have hokL := hF.ok
  rw [hlv] at hokL
  have hLinN : ∀ rd, MemL rd (osLkW Ht cfg d Lin b) → ReadsAt rd cur d.xs := fun rd hm =>
    os_reads_noLow hLin (Main.memL_append.mp hm).1
  have hans := hF.ans
  rw [hlv] at hans
  refine ⟨fun cv' p' q' hq hp hrun => os_kid_foldBC (Ht := Ht) (CM := CM) hk.fold
    (fun rd hlw hm => hLin rd hlw (Main.memL_append.mp hm).1) cv' p' q' hq hp hrun, fun hy => ?_, fun hy => ⟨?_, ?_, ?_⟩, ?_⟩
  · have hlen := hokL.len
    unfold osHPEnd osHP2 at hlen
    rw [ite_pos' hy] at hlen
    have h := os_kid_finalBC (Ht := Ht) (CM := CM) (fs := fs) (cert := cert) (κ := κ) hk.finalMsg (Lk := osLkW Ht cfg d Lin b) (xs := d.xs)
      (cur := cur) (out := (osPtrsOf cfg b).fmsg) (P1 := osHP1 cfg l (d.lvW Ht cfg l).p) (by omega) (fun rd hm => by
        refine ⟨hLinN rd hm, ?_⟩
        have := (hbuf rd hm).fmsg
        rw [fmsgCW, ← hy] at this
        exact this) (d.lvW Ht cfg l).H.cv1 (hans.last hy)
    unfold osHCv2W osHP2
    rw [ite_pos' hy, ite_pos' hy]
    exact h
  · exact os_kid_canonicalBC (CM := CM) hk.canonical _ (os_canonical_of_digest (hokL.root hy)).1
  · exact os_kid_canonicalBC (CM := CM) hk.canonical _ (os_canonical_of_digest (hokL.root hy)).2
  · have hl1 : l + 1 < cfg.levels.length := by have := hok.yrLevel; omega
    rw [Nat.add_zero, os_gw_eq (by omega), os_gw_eq (by omega)]
    exact os_kid_oodBC (Ht := Ht) (CM := CM) hk.ood (by omega) (hlay.cols l hl) (by simp only [ordG]; omega) (fun rd _ hm =>
      oodz_readsAtC (Ht := Ht) hlay (hbuf rd hm).oodz hl1) (hans.ood hy)
  · rw [hgr, os_gw_eq (by decide)]
    exact os_kid_grindBC (Ht := Ht) (CM := CM) hk.grind _ _ _ hokL.pow hans.base hans.gc

/-- **A level's query-position loop, placed, bounded.** -/
theorem lvCallSqBC {μ r : ℕ} {Lall : List Whir.Level} (hok : OsCfgOk cfg μ r Lall) (hlay : OsLayoutOk cfg)
    (hk : OsKidsAtBC CM Ht fs cert κ cfg bd) {Lin : Main.Layout} {b : ℕ}
    (hbuf : ∀ rd, MemL rd (osLkW Ht cfg d Lin b) → OsBufReadsW Ht rd cfg d b []) {l : ℕ} (hl : l < cfg.levels.length)
    (hHt : ∀ x dg, CM.H x = some dg → dg = Ht x)
    (hsqA : sqAllM CM.hm (cfg.lv l).squeezes (d.cv3W Ht cfg l) = some (sqAllW Ht (cfg.lv l).squeezes (d.cv3W Ht cfg l))) :
    1 + osGw (cfg.lv l).squeezes ≠ 0 →
    osCsqBC CM fs cert κ bd (osLkW Ht cfg d Lin b) (osW fs cert cfg b l) (osSW Ht fs cert cfg d l) (cfg.lv l).sqLoop
      [1, osGw (cfg.lv l).squeezes, osPtrAt cfg b (11 + 2 * l), (osPtrsOf cfg b).qpos, (osPtrsOf cfg b).qbp] [] := by
  intro _
  have hspec := hok.spec l (by rw [hok.len]; exact hl)
  obtain ⟨-, -, -, -, -, -, -, -, hper, hqs, -, -, hsq62, hdig, -, -, -, -, -, hpo, -, -, -, -, -⟩ := hspec
  have hq0 := hlay.queries l hl
  have hn : 0 < (cfg.lv l).squeezes := by
    rcases Nat.eq_zero_or_pos (cfg.lv l).squeezes with h | h
    · rw [h, Nat.zero_mul] at hqs; omega
    · exact h
  obtain ⟨fn, hfind, hp, hb⟩ := (hk.lv l hl).sqFn
  rw [os_gw_eq (by omega)]
  refine os_kid_sqBC (Ht := Ht) (CM := CM) (hk.lv l hl).sqPlace hfind hp hb (hk.lv l hl).sqLoop hpo hdig (hk.lv l hl).decode hn
    (by simp only [ordG]; omega) (cv := d.cv3W Ht cfg l) (fun rd _ hm j hj => ?_) (fun p rd _ hm j hj i hi => ?_)
    (fun j hj t ht => ?_) (fun j hj => sqAllM_steps hHt hsqA j hj) (hk.lv l hl).sqLe
  · have h1 := sqz_atC (Ht := Ht) ((hbuf rd hm).sqz l hl) (j := j) (by omega)
    have h2 := sqz_atC (Ht := Ht) ((hbuf rd hm).sqz l hl) (j := j + 1) (by omega)
    rw [sqAll_succ_sndW] at h2
    exact ⟨h1.1, h1.2, by simpa [Nat.mul_add] using h2.1, by simpa [Nat.mul_add, Nat.add_assoc] using h2.2⟩
  · obtain ⟨hm1, hm2⟩ := Main.memL_append.mp hm
    have hqp := os_seg_readsAt (n := cfg.levels.length) (off := fun l => (cfg.lv l).posOff)
      (c := fun l => (List.range ((cfg.lv l).squeezes * (192 / (cfg.lv l).depth))).map fun i =>
        eOfNat (osPosOfW Ht (cfg.lv l).depth (d.cv3W Ht cfg l) i)) (hbuf rd hm1).qpos
      (fun a c hac hc => by simp only [List.length_map, List.length_range]; exact hlay.pos a c hac hc)
      (fun a ha => by simp only [List.length_map, List.length_range]; exact hlay.posFit a ha) hl
    have hidx : j * (192 / (cfg.lv l).depth) + i < (cfg.lv l).squeezes * (192 / (cfg.lv l).depth) := by
      have : (j + 1) * (192 / (cfg.lv l).depth) ≤ (cfg.lv l).squeezes * (192 / (cfg.lv l).depth) :=
        Nat.mul_le_mul_right _ hj
      rw [Nat.succ_mul] at this; omega
    have hw := hm2 _ (List.mem_singleton.mpr rfl)
    refine ⟨?_, ?_⟩
    · have := hqp (j * (192 / (cfg.lv l).depth) + i) (by simpa using hidx)
      rw [loadHolds_mul_gen_pow] at this ⊢
      simp only [List.getElem_map, List.getElem_range] at this
      rw [osPosOf_splitC (Ht := Ht) hper _ hi] at this
      rw [Nat.add_assoc]; exact this
    · have e1 : (osPtrsOf cfg b).qbp * gen ^ ((cfg.lv l).posOff + j * (192 / (cfg.lv l).depth)) =
          ofK (Parameters.gpow ((bases b (osSizes cfg)).getD 8 0 + (cfg.lv l).posOff)) *
            gen ^ (j * (192 / (cfg.lv l).depth)) := by
        show osPtrAt cfg b 8 * _ = _
        unfold osPtrAt; rw [ofK_gpow_mul, ofK_gpow_mul, Nat.add_assoc]
      rw [e1, loadHolds_mul_gen_pow]
      have := hw (j * (192 / (cfg.lv l).depth) + i) (by simpa [qbpSeg] using hidx)
      simp only [qbpSeg, List.getElem_map, List.getElem_range] at this
      rw [show (j * (192 / (cfg.lv l).depth) + i) / (192 / (cfg.lv l).depth) = j by
          rw [Nat.add_comm, Nat.add_mul_div_right _ _ hper, Nat.div_eq_of_lt hi, Nat.zero_add],
        show (j * (192 / (cfg.lv l).depth) + i) % (192 / (cfg.lv l).depth) = i by
          rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]] at this
      exact this
  · refine ⟨(bases b (osSizes cfg)).getD (11 + 2 * l) 0 + (2 * j + t), ?_, _,
      List.mem_append_right _ (os_bufL_mem (ownQ_lengthC (Ht := Ht) []) (j := 11 + 2 * l)
        (by rw [os_length_osSizes]; omega)), ?_, ?_⟩
    · unfold osPtrAt; rw [Main.addr_ofK]
    · simp
    · rw [os_ownQ_getD_sqzC (Ht := Ht) hl]
      simp only [sqzCW, List.length_flatMap, List.length_cons, List.length_nil, List.map_const', List.length_range,
        List.sum_replicate, smul_eq_mul]
      omega

/-- **A level's row weights, placed, bounded.** -/
theorem lvCallRwBC (hlay : OsLayoutOk cfg) (hrun : RunOkW Ht cfg d) (hk : OsKidsAtBC CM Ht fs cert κ cfg bd) {Lin : Main.Layout} {b : ℕ}
    (hbuf : ∀ rd, MemL rd (osLkW Ht cfg d Lin b) → OsBufReadsW Ht rd cfg d b []) {l : ℕ} (hl : l < cfg.levels.length) :
    osCBBC CM fs cert κ bd (osLkW Ht cfg d Lin b) (osW fs cert cfg b l) (osSW Ht fs cert cfg d l) (cfg.lv l).rowWeights
      [(osPtrsOf cfg b).fch * gen ^ (cfg.lv l).foldsOff, osPtrAt cfg b (11 + 2 * l + 1)] [] := fun _ =>
  os_kid_rwBC (CM := CM) (hk.lv l hl).rw (hrun.chs l hl) fun rd hm =>
    ⟨fch_readsAtC (Ht := Ht) hlay hrun (hbuf rd (memL_lkC (Ht := Ht) hm)).fch hl, (hbuf rd (memL_lkC (Ht := Ht) hm)).rew l hl⟩

/-- **A level's cap, placed, bounded.** -/
theorem lvCallCapBC {μ r : ℕ} {Lall : List Whir.Level} (hok : OsCfgOk cfg μ r Lall) (hlay : OsLayoutOk cfg)
    (hHt : ∀ x dg, CM.H x = some dg → dg = Ht x)
    (hk : OsKidsAtBC CM Ht fs cert κ cfg bd) {Lin : Main.Layout} {b : ℕ}
    (hbuf : ∀ rd, MemL rd (osLkW Ht cfg d Lin b) → OsBufReadsW Ht rd cfg d b []) {Q : List (ℕ × List (ℕ × Opening))}
    (hQ : ∀ x ∈ Q, BatchAgreesW Ht x.1 x.2) {l : ℕ} (hl : l < cfg.levels.length)
    (hF : OsLvFactsW CM.hm Ht cfg μ d.xs Lall Q (d.lvW Ht cfg l)) (hlv : (d.lvW Ht cfg l).lvl = l) :
    osCBBC CM fs cert κ bd (osLkW Ht cfg d Lin b) (osW fs cert cfg b l) (osSW Ht fs cert cfg d l) (cfg.lv l).verifyCap
      [(osPtrsOf cfg b).caps * gen ^ (4 * (cfg.lv l).capOff), (osPtrsOf cfg b).flags * gen ^ (cfg.lv l).capOff]
      [(digestScalars (d.rtW Ht cfg l)).1, (digestScalars (d.rtW Ht cfg l)).2] := by
  have hspec := hok.spec l (by rw [hok.len]; exact hl)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hcd1, hcd2, -, -, -, -, -, -, -, -, -⟩ := hspec
  have hst := hF.step
  rw [hlv] at hst
  have hcap := os_capOk_ofW (lv_openC (Ht := Ht) (CM := CM) hF hlv) (hQ _ hst) rfl (hlay.queries l hl) hcd1 hcd2
  intro p
  refine os_kid_capBC (Ht := Ht) (CM := CM) (hk.lv l hl).cap hcap (osCapAns_of (lv_ansC hHt hF hlv)) fun rd hm => ⟨?_, ?_⟩
  · exact os_seg_readsAt (off := fun l => 4 * (cfg.lv l).capOff)
      (c := fun l => osCapCellsW Ht (cfg.lv l).depth (cfg.lv l).capDepth (d.qsW Ht cfg l)) (hbuf rd (memL_lkC (Ht := Ht) hm)).caps
      (fun a c hac hc => by rw [os_capCells_lengthW]; exact hlay.caps a c hac hc)
      (fun a ha => by rw [os_capCells_lengthW]; exact hlay.capsFit a ha) hl
  · exact os_seg_readsAt (off := fun l => (cfg.lv l).capOff)
      (c := fun l => osCapFlags (cfg.lv l).depth (cfg.lv l).capDepth (d.qsW Ht cfg l)) (hbuf rd (memL_lkC (Ht := Ht) hm)).flags
      (fun a c hac hc => by simp only [osCapFlags, List.length_map, List.length_range]; exact hlay.flags a c hac hc)
      (fun a ha => by simp only [osCapFlags, List.length_map, List.length_range]; exact hlay.flagsFit a ha) hl

/-- **A level's queries, placed, bounded.** -/
theorem lvCallQBC {μ r : ℕ} {Lall : List Whir.Level} (hok : OsCfgOk cfg μ r Lall) (hlay : OsLayoutOk cfg)
    (hHt : ∀ x dg, CM.H x = some dg → dg = Ht x)
    (hrun : RunOkW Ht cfg d) (hk : OsKidsAtBC CM Ht fs cert κ cfg bd) {Lin : Main.Layout} {b : ℕ}
    (hbuf : ∀ rd, MemL rd (osLkW Ht cfg d Lin b) → OsBufReadsW Ht rd cfg d b []) {Q : List (ℕ × List (ℕ × Opening))}
    (hQ : ∀ x ∈ Q, BatchAgreesW Ht x.1 x.2) {l : ℕ} (hl : l < cfg.levels.length)
    (hF : OsLvFactsW CM.hm Ht cfg μ d.xs Lall Q (d.lvW Ht cfg l)) (hlv : (d.lvW Ht cfg l).lvl = l) :
    osCBBC CM fs cert κ bd (osLkW Ht cfg d Lin b) (osW fs cert cfg b l) (osSW Ht fs cert cfg d l) (cfg.lv l).queriesFn
      [(osPtrsOf cfg b).caps * gen ^ (4 * (cfg.lv l).capOff), (osPtrsOf cfg b).flags * gen ^ (cfg.lv l).capOff,
        (osPtrsOf cfg b).qw * gen ^ (l * cfg.maxQ), (osPtrsOf cfg b).qbp * gen ^ (cfg.lv l).posOff,
        osPtrAt cfg b (11 + 2 * l + 1), osGw (cfg.lv l).queries]
      [osHEnfW Ht cfg l d.xs (d.lvW Ht cfg l).p (d.lvW Ht cfg l).H] := by
  have hspec := hok.spec l (by rw [hok.len]; exact hl)
  obtain ⟨-, -, -, -, -, -, -, -, hper, hqs, -, -, -, -, hcd1, hcd2, -, -, -, -, hq62, -, -, -, -⟩ := hspec
  set L := d.lvW Ht cfg l with hL
  set rev : ℕ := if l = 0 then 1 else 0
  have hst := hF.step
  rw [hlv] at hst
  have hoa := lv_openC (Ht := Ht) (CM := CM) hF hlv
  have hcap := os_capOk_ofW hoa (hQ _ hst) rfl (hlay.queries l hl) hcd1 hcd2
  obtain ⟨os1, hosp, hl1, hrows, hj⟩ := os_openAll_invW _ _ _ _ hoa
  have hqsl : (osHQsW Ht cfg l d.xs L.p L.H.cv1).length = (cfg.lv l).queries := by simp [osHQsW]
  rw [hqsl] at hl1
  set leaf : ℕ → List K := fun j => (os1.getD j ⟨[], []⟩).leaf
  set wts : ℕ → E := fun jw => (eqKernel L.H.chs).getD (orwSlot (cfg.lv l).folds rev jw) 0
  set qwV : ℕ → E := fun j => d.lamW Ht cfg l ^ j
  have hE : osHEnfW Ht cfg l d.xs L.p L.H = oqSum rev (2 ^ (cfg.lv l).folds) wts qwV leaf (cfg.lv l).queries := by
    have h := os_oqSum_eq (l := l) (hrun.chs l hl) (d.lamW Ht cfg l) (os1 := os1) (fun j hj' => by
      rw [(hj j hj').1])
    rw [hl1] at h
    rw [h]
    unfold osHEnfW
    rw [hqsl, hrows]
    rfl
  intro p
  rw [hE, os_gw_eq (by omega)]
  have hmemq : ∀ j < (cfg.lv l).queries, ((osHQsW Ht cfg l d.xs L.p L.H.cv1).getD j 0, os1.getD j ⟨[], []⟩) ∈
      (osHQsW Ht cfg l d.xs L.p L.H.cv1).zip L.osp := by
    intro j hj'
    rw [hosp]
    refine List.mem_iff_getElem.mpr ⟨j, by rw [List.length_zip, List.length_append, hqsl]; omega, ?_⟩
    simp only [List.getElem_zip, List.getElem_append_left (show j < os1.length by omega)]
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
  obtain ⟨Bq, hqB, hqle⟩ := (hk.lv l hl).queries
  refine CompleteAtBS.mono (os_kid_queriesBC (Ht := Ht) (CM := CM) hqB (n := (cfg.lv l).queries) (by simp only [ordG]; omega) (leaf := leaf)
    (pos := fun j => (osHQsW Ht cfg l d.xs L.p L.H.cv1).getD j 0)
    (sibs := fun j => (os1.getD j ⟨[], []⟩).path.take ((cfg.lv l).depth - (cfg.lv l).capDepth)) (wts := wts) (qwV := qwV)
    (dbpV := fun j => (qbpSeg cfg fs cert l p).getD j 0)
    (fun j hj' => by simp only [leaf]; rw [List.getD_eq_getElem _ _ (by omega)]; exact (hj j (by omega)).1)
    (fun j hj' => (hcap.pos _ (hmemq j hj')))
    (fun j hj' => by
      simp only [List.length_take]
      rw [List.getD_eq_getElem _ _ (by omega), (hj j (by omega)).2.1]; omega)
    (fun j hj' => oqAns_of_opening (lv_ansC hHt hF hlv _ (hmemq j hj')) (by omega))
    (fun rd _ hm => ?_)) le_rfl hqle
  obtain ⟨hm12, hmS⟩ := Main.memL_append.mp hm
  obtain ⟨hmk, hmW⟩ := Main.memL_append.mp hm12
  have hb := hbuf rd hmk
  have hcells := os_seg_readsAt (off := fun l => 4 * (cfg.lv l).capOff)
    (c := fun l => osCapCellsW Ht (cfg.lv l).depth (cfg.lv l).capDepth (d.qsW Ht cfg l)) hb.caps
    (fun a c hac hc => by rw [os_capCells_lengthW]; exact hlay.caps a c hac hc)
    (fun a ha => by rw [os_capCells_lengthW]; exact hlay.capsFit a ha) hl
  have hflags := os_seg_readsAt (off := fun l => (cfg.lv l).capOff)
    (c := fun l => osCapFlags (cfg.lv l).depth (cfg.lv l).capDepth (d.qsW Ht cfg l)) hb.flags
    (fun a c hac hc => by simp only [osCapFlags, List.length_map, List.length_range]; exact hlay.flags a c hac hc)
    (fun a ha => by simp only [osCapFlags, List.length_map, List.length_range]; exact hlay.flagsFit a ha) hl
  have hW := hmW _ (List.mem_singleton.mpr rfl)
  refine ⟨fun jw hjw => ?_, fun j hj' => ?_, fun j hj' => ?_, fun j hj' l' hl' => ?_, fun j hj' => ?_,
    fun j hj' => ?_⟩
  · have := os_readsAt_getD (hb.rew l hl) (k := jw) (by simpa [rewCW] using hjw)
    rw [rewCW, os_getD_map_range _ hjw] at this
    exact this
  · rw [loadHolds_mul_gen_pow]; exact qw_atC (Ht := Ht) hlay hb.qw hl j hj'
  · have e1 : (osPtrsOf cfg b).qbp * gen ^ (cfg.lv l).posOff =
        ofK (Parameters.gpow ((bases b (osSizes cfg)).getD 8 0 + (cfg.lv l).posOff)) := by
      show osPtrAt cfg b 8 * _ = _
      unfold osPtrAt; rw [ofK_gpow_mul]
    rw [e1]
    have hsq1 : 1 ≤ (cfg.lv l).squeezes := by
      rcases Nat.eq_zero_or_pos (cfg.lv l).squeezes with h | h
      · rw [h, Nat.zero_mul] at hqs; omega
      · exact h
    have := Nat.mul_le_mul_right (192 / (cfg.lv l).depth) hsq1
    exact os_readsAt_getD hW (by simp only [qbpSeg, List.length_map, List.length_range]; omega)
  · have hjs : j < (cfg.lv l).squeezes * (192 / (cfg.lv l).depth) := by omega
    have hdiv : j / (192 / (cfg.lv l).depth) < (cfg.lv l).squeezes := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hjs)
    have hmod : j % (192 / (cfg.lv l).depth) < (192 / (cfg.lv l).depth) := Nat.mod_lt _ hper
    have hpd : (192 / (cfg.lv l).depth) * (cfg.lv l).depth ≤ 192 := Nat.div_mul_le_self 192 (cfg.lv l).depth
    have hl'd : l' < (cfg.lv l).depth := by omega
    have hc : j % (192 / (cfg.lv l).depth) * (cfg.lv l).depth + l' < 192 := by
      have : (j % (192 / (cfg.lv l).depth) + 1) * (cfg.lv l).depth ≤ (192 / (cfg.lv l).depth) * (cfg.lv l).depth := Nat.mul_le_mul_right _ hmod
      rw [Nat.succ_mul] at this; omega
    simp only
    rw [List.getD_eq_getElem _ _ (by simp [qbpSeg]; exact hjs)]
    simp only [qbpSeg, List.getElem_map, List.getElem_range]
    rw [loadHolds_mul_gen_pow]
    have hpos : (osHQsW Ht cfg l d.xs L.p L.H.cv1).getD j 0 = osPosOfW Ht (cfg.lv l).depth (d.cv3W Ht cfg l) j := by
      unfold osHQsW; rw [os_getD_map_range _ hj']; rfl
    rw [hpos, osPosOf_testBitC (Ht := Ht) _ _ hl'd]
    exact sqRuns_bitC hmS hdiv hc
  · have := osCap_parentW hcap hflags (hmemq j hj')
    exact this
  · have := osCap_leafW hcap hcells (hmemq j hj')
    exact this

/-- **Every level's callees, placed, bounded.** -/
theorem lvsCallHBC {μ r : ℕ} {Lall : List Whir.Level} (hok : OsCfgOk cfg μ r Lall) (hlay : OsLayoutOk cfg)
    (hHt : ∀ x dg, CM.H x = some dg → dg = Ht x)
    (hrun : RunOkW Ht cfg d) (hk : OsKidsAtBC CM Ht fs cert κ cfg bd) {Lin : Main.Layout} {b : ℕ} {cur : E}
    (hLin : ∀ rd, LowDef κ rd → MemL rd Lin → ReadsAt rd cur d.xs)
    (hbuf : ∀ rd, MemL rd (osLkW Ht cfg d Lin b) → OsBufReadsW Ht rd cfg d b []) {e : WhirEnd} {sp' : St}
    {Q : List (ℕ × List (ℕ × Opening))} (hQ : ∀ x ∈ Q, BatchAgreesW Ht x.1 x.2)
    (hch : OsChainC CM.hm Ht cfg μ (cfg.lv 0).folds d.xs Lall e sp' Q 0 (d.cv0W Ht) 2 (osW0 d.target d.xs) d.os (d.roots0 cfg) d.Hs) :
    OsLvsCallHC CM Ht (fun _ => osKCBC CM fs cert κ bd (osLkW Ht cfg d Lin b))
      (fun l => osCBBC CM fs cert κ bd (osLkW Ht cfg d Lin b) (osW fs cert cfg b l) (osSW Ht fs cert cfg d l))
      (fun l => osCsqBC CM fs cert κ bd (osLkW Ht cfg d Lin b) (osW fs cert cfg b l) (osSW Ht fs cert cfg d l)) cfg d.xs cur
      (osPtrsOf cfg b) (fun l => osPtrAt cfg b (11 + 2 * l)) (fun l => osPtrAt cfg b (11 + 2 * l + 1)) 0 2
      (osW0 d.target d.xs) (d.roots0 cfg) d.Hs := by
  refine os_lvsCallH_memC (Ht := Ht) (CM := CM) d.Hs 0 (d.cv0W Ht) 2 (osW0 d.target d.xs) d.os (d.roots0 cfg) fun L hL => ?_
  obtain ⟨hg, hlt⟩ := os_lvs_getC (Ht := Ht) cfg d.xs d.Hs _ _ _ _ _ L hL
  have hl : L.lvl < cfg.levels.length := by rw [os_lvsList_lengthC (Ht := Ht), hrun.len] at hlt; exact hlt
  have hF := os_chain_memC (Ht := Ht) (CM := CM) d.Hs 0 _ _ _ _ _ hch L hL
  have e : d.lvW Ht cfg L.lvl = L := hg
  have hF' : OsLvFactsW CM.hm Ht cfg μ d.xs Lall Q (d.lvW Ht cfg L.lvl) := by rw [e]; exact hF
  have hlv : (d.lvW Ht cfg L.lvl).lvl = L.lvl := by rw [e]
  obtain ⟨hA1, hA2, hA3, hA4⟩ := lvCallABC (Ht := Ht) (CM := CM) (fs := fs) (cert := cert) (κ := κ) hok hlay hk hLin hbuf hl hF' hlv
  have hSq := lvCallSqBC (Ht := Ht) (CM := CM) (fs := fs) (cert := cert) (κ := κ) (d := d) hok hlay hk hbuf hl hHt
    (by have h := hF'.ans.sq; rw [hlv] at h; exact h)
  have hRw := lvCallRwBC (Ht := Ht) (CM := CM) (fs := fs) (cert := cert) (κ := κ) hlay hrun hk hbuf hl
  have hCap := lvCallCapBC (Ht := Ht) (CM := CM) (fs := fs) (cert := cert) (κ := κ) hok hlay hHt hk hbuf hQ hl hF' hlv
  have hQr := lvCallQBC (Ht := Ht) (CM := CM) (fs := fs) (cert := cert) (κ := κ) hok hlay hHt hrun hk hbuf hQ hl hF' hlv
  have ert : d.rtW Ht cfg L.lvl = (L.roots.getD L.lvl default).1 := by unfold rtW; rw [e]
  rw [e] at hA2 hA3 hA4 hQr
  rw [ert] at hCap
  exact ⟨hA1, hA2, hA3, hA4, hSq, hRw, hCap, hQr⟩

end OsData

end
end LeanVM.Guest.B1
