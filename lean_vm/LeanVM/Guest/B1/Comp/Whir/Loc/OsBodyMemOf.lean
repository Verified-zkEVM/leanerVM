/-
  LeanVM.Guest.B1.Comp.Whir.Loc.OsBodyMemOf

  The body's memory facts from the buffers over a total hash (`Whir/OsBodyMemOf.lean`)
-/

module

public import LeanVM.Guest.B1.Whir.OsBodyMemOf
public import LeanVM.Guest.B1.Comp.Whir.Loc.OsGlue

/-!
# The body's memory facts from the buffers over a total hash (`Whir/OsBodyMemOf.lean`)
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub
open LeanVM.E2E.Complete
open LeanVM.Protocol.Compile (Bytes)
open LeanVM.Protocol (Digest)

@[expose] public section

variable {Ht : Bytes → Digest} {CM : CompModel}

namespace OsData

variable {cfg : OsCfg} {d : OsData}

/-- The run facts the memory facts use. -/
structure RunOkW (Ht : Bytes → Digest) (cfg : OsCfg) (d : OsData) : Prop where
  len : d.Hs.length = cfg.levels.length
  chs : ∀ l < cfg.levels.length, (d.lvW Ht cfg l).H.chs.length = (cfg.lv l).folds
  rt0 : d.rtW Ht cfg 0 = d.root
  rt : ∀ l, l + 1 < cfg.levels.length →
    digestScalars (d.rtW Ht cfg (l + 1)) = (osHW cfg l d.xs (d.lvW Ht cfg l).p 0, osHW cfg l d.xs (d.lvW Ht cfg l).p 1)
  chst : d.chst.length = cfg.yrLog - 1
  fchLen : (d.fchCW Ht cfg).length = cfg.nFolds
  fch : ∀ l < cfg.levels.length, ∀ j < (cfg.lv l).folds,
    (d.fchCW Ht cfg).getD ((cfg.lv l).foldsOff + j) 0 = (d.lvW Ht cfg l).H.chs.getD j 0

theorem fch_atC (hlay : OsLayoutOk cfg) (hrun : RunOkW Ht cfg d) {rd : Reader} {ptr : E}
    (hr : ReadsAt rd ptr (d.fchCW Ht cfg)) {l : ℕ} (hl : l < cfg.levels.length) :
    ∀ j < (cfg.lv l).folds, LoadHolds rd ptr ((cfg.lv l).foldsOff + j) ((d.lvW Ht cfg l).H.chs.getD j 0) := by
  intro j hj
  rw [← hrun.fch l hl j hj]
  exact os_readsAt_getD hr (by rw [hrun.fchLen]; have := hlay.fchFit l hl; omega)

theorem fch_readsAtC (hlay : OsLayoutOk cfg) (hrun : RunOkW Ht cfg d) {rd : Reader} {ptr : E}
    (hr : ReadsAt rd ptr (d.fchCW Ht cfg)) {l : ℕ} (hl : l < cfg.levels.length) :
    ReadsAt rd (ptr * gen ^ (cfg.lv l).foldsOff) (d.lvW Ht cfg l).H.chs := by
  intro j hj
  rw [loadHolds_mul_gen_pow]
  have := fch_atC (Ht := Ht) hlay hrun hr hl j (by rw [← hrun.chs l hl]; exact hj)
  rwa [List.getD_eq_getElem _ _ hj] at this

theorem roots_atC {rd : Reader} {ptr : E} (hr : ReadsAt rd ptr (d.rootsCW Ht cfg)) {l : ℕ} (hl : l < cfg.levels.length) :
    LoadHolds rd ptr (2 * l) (digestScalars (d.rtW Ht cfg l)).1 ∧
      LoadHolds rd ptr (2 * l + 1) (digestScalars (d.rtW Ht cfg l)).2 := by
  have h := os_seg_at (off := fun l => 2 * l) (c := fun l => [(digestScalars (d.rtW Ht cfg l)).1,
    (digestScalars (d.rtW Ht cfg l)).2]) hr (fun i k hik _ => by simp only [List.length_cons, List.length_nil]; omega)
    (fun l hl => by simp only [List.length_cons, List.length_nil]; omega) hl
  exact ⟨by simpa using h 0 (by simp), by simpa using h 1 (by simp)⟩

theorem qw_atC (hlay : OsLayoutOk cfg) {rd : Reader} {ptr : E} (hr : ReadsAt rd ptr (d.qwCW Ht cfg)) {l : ℕ}
    (hl : l < cfg.levels.length) : ∀ i < (cfg.lv l).queries, LoadHolds rd ptr (l * cfg.maxQ + i) (d.lamW Ht cfg l ^ i) := by
  intro i hi
  have h := os_seg_at (off := fun l => l * cfg.maxQ) (c := fun l => (List.range (cfg.lv l).queries).map
    fun i => d.lamW Ht cfg l ^ i) hr (fun a k hak hk => by
      simp only [List.length_map, List.length_range]
      have := hlay.qw a (by omega)
      have : a * cfg.maxQ + cfg.maxQ ≤ k * cfg.maxQ := by
        rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hak
      omega)
    (fun l hl => by
      simp only [List.length_map, List.length_range]
      have := hlay.qw l hl
      have : l * cfg.maxQ + cfg.maxQ ≤ cfg.levels.length * cfg.maxQ := by
        rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hl
      omega) hl i (by simpa using hi)
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range] at h
  exact h

theorem ood_atC {rd : Reader} {ptr : E} (hr : ReadsAt rd ptr (d.oodCW Ht cfg)) {l : ℕ} (hl : l + 1 < cfg.levels.length) :
    LoadHolds rd ptr ((l + 1) * 4) (d.lamW Ht cfg l) ∧
      LoadHolds rd ptr ((l + 1) * 4 + 1) (osHW cfg l d.xs (d.lvW Ht cfg l).p 2) ∧
      LoadHolds rd ptr ((l + 1) * 4 + 2) (osHW cfg l d.xs (d.lvW Ht cfg l).p 3) ∧
      LoadHolds rd ptr ((l + 1) * 4 + 3) (osHW cfg l d.xs (d.lvW Ht cfg l).p 4) := by
  have h := os_seg_at (n := cfg.levels.length - 1) (off := fun l => (l + 1) * 4)
    (c := fun l => [d.lamW Ht cfg l, osHW cfg l d.xs (d.lvW Ht cfg l).p 2, osHW cfg l d.xs (d.lvW Ht cfg l).p 3,
      osHW cfg l d.xs (d.lvW Ht cfg l).p 4]) hr
    (fun i k hik _ => by simp only [List.length_cons, List.length_nil]; omega)
    (fun l hl => by simp only [List.length_cons, List.length_nil]; omega) (l := l) (by omega)
  exact ⟨by simpa using h 0 (by simp), by simpa using h 1 (by simp), by simpa using h 2 (by simp),
    by simpa using h 3 (by simp)⟩

theorem sqz_atC {rd : Reader} {ptr : E} {l : ℕ} (hr : ReadsAt rd ptr (d.sqzCW Ht cfg l)) {j : ℕ}
    (hj : j ≤ (cfg.lv l).squeezes) :
    LoadHolds rd ptr (2 * j) (digestScalars (sqAllW Ht j (d.cv3W Ht cfg l)).2).1 ∧
      LoadHolds rd ptr (2 * j + 1) (digestScalars (sqAllW Ht j (d.cv3W Ht cfg l)).2).2 := by
  have hlen : (d.sqzCW Ht cfg l).length = 2 * ((cfg.lv l).squeezes + 1) := by
    simp only [sqzCW, List.length_flatMap, List.length_cons, List.length_nil, List.map_const', List.length_range,
      List.sum_replicate, smul_eq_mul]; ring
  have e := os_flatMap_pair_getD (fun j => (digestScalars (sqAllW Ht j (d.cv3W Ht cfg l)).2).1)
    (fun j => (digestScalars (sqAllW Ht j (d.cv3W Ht cfg l)).2).2) 0 ((cfg.lv l).squeezes + 1) j (by omega)
  have h1 := os_readsAt_getD hr (k := 2 * j) (by omega)
  have h2 := os_readsAt_getD hr (k := 2 * j + 1) (by omega)
  unfold sqzCW at h1 h2
  rw [e.1] at h1; rw [e.2] at h2
  exact ⟨h1, h2⟩

/-- **A level's reads.** -/
theorem lvMemC (hlay : OsLayoutOk cfg) (hrun : RunOkW Ht cfg d) (hyr : cfg.yrLevel = cfg.levels.length - 1)
    {rd : Reader} {b : ℕ} {Q : List E} {cur : E} (hbr : OsBufReadsW Ht rd cfg d b Q) (hxs : ReadsAt rd cur d.xs)
    {l : ℕ} (hl : l < cfg.levels.length) :
    OsLvMemW Ht rd cfg l d.xs (d.lvW Ht cfg l).p (d.lvW Ht cfg l).H (d.rtW Ht cfg l) (osPtrsOf cfg b) (osPtrAt cfg b (11 + 2 * l))
      cur := by
  have hs0 := sqz_atC (Ht := Ht) (hbr.sqz l hl) (j := 0) (by omega)
  have hsN := sqz_atC (Ht := Ht) (hbr.sqz l hl) (j := (cfg.lv l).squeezes) le_rfl
  refine ⟨fun j hj => os_readsAt_getD hxs hj, fch_atC (Ht := Ht) hlay hrun hbr.fch hl, fun hne => ?_, fun hne => ?_,
    hs0.1, hs0.2, hsN.1, hsN.2, qw_atC (Ht := Ht) hlay hbr.qw hl, (roots_atC (Ht := Ht) hbr.roots hl).1, (roots_atC (Ht := Ht) hbr.roots hl).2, ?_⟩
  · have h := roots_atC (Ht := Ht) hbr.roots (d := d) (l := l + 1) (by omega)
    rw [hrun.rt l (by omega)] at h
    rw [show 2 * (l + 1) = 2 * l + 2 by ring] at h
    exact ⟨h.1, h.2⟩
  · exact ood_atC (Ht := Ht) hbr.ood (by omega)
  · have h := os_readsAt_getD hbr.betas (k := l) (by simp [betasCW, hl])
    simp only [betasCW, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hl, Option.map_some,
      Option.getD_some, betaW] at h
    exact h

theorem tch_lenC (hrun : RunOkW Ht cfg d) (h1 : 1 ≤ cfg.yrLog) (h5 : cfg.yrLog ≤ 5) : (d.tchCW Ht cfg).length = 5 := by
  simp only [tchCW, tfW, List.length_append, List.length_cons, List.length_nil, List.length_replicate, hrun.chst]
  omega

/-- **A source's word at its pointer.** -/
theorem src_loadC (hrun : RunOkW Ht cfg d) (h1 : 1 ≤ cfg.yrLog) (h5 : cfg.yrLog ≤ 5) {rd : Reader} {b : ℕ} {Q : List E}
    {cur : E} (hbr : OsBufReadsW Ht rd cfg d b Q) {q : ℕ × ℕ} (hf : q.1 = osFch → q.2 < cfg.nFolds)
    (ht : q.1 ≠ osFch → q.2 < 5) : LoadHolds rd (osSrcPtr (d.runOfW Ht cfg cur b) q.1) q.2 (d.srcValW Ht cfg q) := by
  unfold osSrcPtr srcValW
  by_cases h : q.1 = osFch
  · rw [ite_pos' h, ite_pos' h]
    exact os_readsAt_getD hbr.fch (by rw [hrun.fchLen]; exact hf h)
  · rw [ite_neg' h, ite_neg' h]
    exact os_readsAt_getD hbr.tch (by rw [tch_lenC (Ht := Ht) hrun h1 h5]; exact ht h)

/-- **What the body reads**, on a memory holding the buffers' honest words. -/
theorem bodyMemC {μ r : ℕ} {Lall : List Whir.Level} (hok : OsCfgOk cfg μ r Lall) (htne : OsRun.tch cfg ≠ osFch)
    (hlay : OsLayoutOk cfg) (hrun : RunOkW Ht cfg d) {rd : Reader} {b : ℕ} {Q : List E} {cur : E}
    (hbr : OsBufReadsW Ht rd cfg d b Q) (hxs : ReadsAt rd cur d.xs) (σ : Val) :
    OsBodyMemW Ht rd σ cfg (d.runOfW Ht cfg cur b) := by
  have hn2 := hok.len2
  have hyr2 := hok.yr2
  have hyr5 := hok.yr5
  have hlane := hok.laneLe
  have hhd : (cfg.levels.headD default) = cfg.lv 0 := by
    cases h' : cfg.levels with
    | nil => simp [h'] at hn2
    | cons a b => simp [OsCfg.lv, h']
  have htl : ∀ i, cfg.levels.tail.getD i default = cfg.lv (i + 1) := by
    intro i; simp [OsCfg.lv, List.getD_eq_getElem?_getD]
  have hsrcL : ∀ q : ℕ × ℕ, (q.1 = osFch → q.2 < cfg.nFolds) → (q.1 ≠ osFch → q.2 < 5) →
      LoadHolds rd (osSrcPtr (d.runOfW Ht cfg cur b) q.1) q.2 (d.srcValW Ht cfg q) := fun q hf ht =>
    src_loadC (Ht := Ht) hrun (by omega) hyr5 hbr hf ht
  have hchst := hrun.chst
  have htch : ∀ j < (d.tchCW Ht cfg).length, LoadHolds rd (osPtrAt cfg b (11 + 2 * cfg.levels.length)) j
      ((d.tchCW Ht cfg).getD j 0) := fun j hj => os_readsAt_getD hbr.tch hj
  have hlen5 := tch_lenC (Ht := Ht) hrun (by omega) hyr5
  refine ⟨fun j hj => os_readsAt_getD hxs hj, ?_, ?_, ?_, fun j hj => ?_, ?_, fun j hj => ?_, ?_,
    fun i hi => ?_, ?_, ?_, fun l hl => ?_, fun i hi => ?_, ?_⟩
  · have h := (roots_atC (Ht := Ht) hbr.roots (d := d) (l := 0) (by omega)).1
    rw [hrun.rt0] at h; exact h
  · have h := (roots_atC (Ht := Ht) hbr.roots (d := d) (l := 0) (by omega)).2
    rw [hrun.rt0] at h; exact h
  · refine os_lvsMem_memC (Ht := Ht) d.Hs 0 (d.cv0W Ht) 2 (osW0 d.target d.xs) d.os (d.roots0 cfg) fun L hL => ?_
    obtain ⟨hg, hlt⟩ := os_lvs_getC (Ht := Ht) cfg d.xs d.Hs _ _ _ _ _ L hL
    have hlt' : L.lvl < cfg.levels.length := by
      rw [os_lvsList_lengthC (Ht := Ht), hrun.len] at hlt; exact hlt
    have h := lvMemC (Ht := Ht) hlay hrun hok.yrLevel hbr hxs hlt'
    have e : d.lvW Ht cfg L.lvl = L := hg
    unfold rtW at h
    rw [e] at h
    exact h
  · have := htch j (by omega)
    simp only [tchCW, tfW, List.append_assoc] at this
    rwa [oq_getD_app_lt (by omega)] at this
  · have := htch (cfg.yrLog - 1) (by omega)
    simp only [tchCW, tfW, List.append_assoc] at this
    rw [oq_getD_app_ge (by omega), show cfg.yrLog - 1 - d.chst.length = 0 by omega] at this
    exact this
  · have := htch (cfg.yrLog + j) (by omega)
    simp only [tchCW, tfW, List.append_assoc] at this
    rw [oq_getD_app_ge (by omega), show cfg.yrLog + j - d.chst.length = j + 1 by omega] at this
    simp only [List.singleton_append, List.getD_eq_getElem?_getD, List.getElem?_cons_succ, List.getElem?_replicate,
      show j < 5 - cfg.yrLog by omega, ite_true, Option.getD_some] at this
    exact this
  · intro i hi b' o hs
    obtain ⟨hb1, hb2⟩ := os_ptSrc_bound htne (by rw [hhd]; exact hlane) hs
    have e : (d.runOfW Ht cfg cur b).D.ent i = d.srcValW Ht cfg (b', o) := by
      show d.entW Ht cfg i = _; unfold entW; rw [hs]
    rw [e]
    exact hsrcL (b', o) hb1 (fun h => by have := hb2 h; omega)
  · have := os_readsAt_getD hbr.pt (k := i) (by simp [ptCW, hi])
    simp only [ptCW, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi, Option.map_some,
      Option.getD_some] at this
    exact this
  · intro i hi it hit
    simp only [Nat.zero_add] at hit
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hit
    rw [List.mem_range] at ht
    obtain ⟨hpre, hrfo, -, hF, -⟩ := hok.lvs i hi
    simp only [OsCfg.lv] at hpre hrfo hF
    refine ⟨hsrcL _ (fun h => ?_) (fun h => ?_), ?_, ?_⟩
    · by_cases htp : t < (cfg.levels.getD i default).prefixLen
      · simp only [htp, ite_true] at h ⊢; omega
      · simp only [htp, ite_false] at h ⊢; exact absurd h htne
    · by_cases htp : t < (cfg.levels.getD i default).prefixLen
      · simp only [htp, ite_true] at h ⊢; exact absurd rfl h
      · simp only [htp, ite_false] at h ⊢; omega
    · exact basis_at (g := fun it => 1 + d.cfW Ht cfg it) hlay hbr.ba hi ht
    · exact basis_at (g := fun it => d.cfW Ht cfg it * eOfNat it.2.2) hlay hbr.bb hi ht
  · have := os_readsAt_getD hbr.ich (k := 0) (by simp [ichCW])
    rw [ichCW, os_getD_map_range _ (by omega), show d.innerW Ht cfg 0 = 0 by simp [innerW]] at this
    exact this
  · have c0 := os_readsAt_getD (hbr.chv l hl) (k := 0) (by simp [chvCW])
    have cN := os_readsAt_getD (hbr.chv l hl) (k := (cfg.lv l).queries) (by simp [chvCW])
    have i0 := os_readsAt_getD hbr.ich (k := l) (by simp [ichCW]; omega)
    have i1 := os_readsAt_getD hbr.ich (k := l + 1) (by simp [ichCW]; omega)
    have b0 := os_readsAt_getD hbr.betas (k := l) (by simp [betasCW, hl])
    rw [chvCW, os_getD_map_range _ (by omega)] at c0 cN
    rw [ichCW, os_getD_map_range _ (by omega)] at i0 i1
    rw [betasCW, os_getD_map_range _ hl] at b0
    rw [show d.chainW Ht cfg l 0 = 0 by simp [chainW]] at c0
    refine ⟨c0, i0, b0, cN, ?_⟩
    show LoadHolds rd _ (l + 1) (d.innerW Ht cfg l + d.betaW Ht cfg l * d.chainW Ht cfg l (cfg.lv l).queries)
    rw [show d.innerW Ht cfg l + d.betaW Ht cfg l * d.chainW Ht cfg l (cfg.lv l).queries = d.innerW Ht cfg (l + 1) by
      simp only [innerW, Finset.sum_range_succ]]
    exact i1
  · have htl' : cfg.levels.tail.length = cfg.levels.length - 1 := by simp
    rw [htl'] at hi
    have hpc := prevCols_eq (cfg := cfg) (by omega) i
    obtain ⟨hpre, -, hml, hF, -⟩ := hok.lvs i (by omega)
    have hcols := hlay.cols i (by omega)
    rw [hpc]
    have hnx := (hok.spec i (by rw [hok.len]; omega))
    rw [List.drop_eq_getElem_cons (by rw [hok.len]; omega)] at hnx
    have hfo := hnx.nextFolds
    refine ⟨by omega, ?_, fun t ht => ?_, fun t ht => ?_⟩
    · have := (ood_atC (Ht := Ht) hbr.ood (d := d) (l := i) (by omega)).1
      rw [show (1 + i) * 4 = (i + 1) * 4 by ring]
      show LoadHolds rd _ _ (d.lamW Ht cfg (1 + i - 1))
      rw [show 1 + i - 1 = i by omega]; exact this
    · have := os_readsAt_getD hbr.oodz (k := (1 + i) * 22 + t) (by
        rw [oodzCW, os_length_segC]
        have : (1 + i) * 22 + 22 ≤ cfg.levels.length * 22 := by
          rw [show (1 + i) * 22 + 22 = (i + 2) * 22 by ring]; exact Nat.mul_le_mul_right _ (by omega)
        omega)
      exact this
    · show LoadHolds rd _ _ (d.srcValW Ht cfg (osOodSrc (OsRun.tch cfg)
        (osPrevColsAt cfg.levels.tail (cfg.levels.headD default).logCols (1 + i - 1) - cfg.yrLog)
        (cfg.levels.tail.getD (1 + i - 1) default).foldsOff t))
      rw [show 1 + i - 1 = i by omega, hpc, htl i, hfo]
      refine hsrcL _ (fun h => ?_) (fun h => ?_)
      · unfold osOodSrc at h ⊢
        by_cases htz : t < (cfg.lv i).logCols - cfg.yrLog
        · simp only [htz, ite_true] at h ⊢; omega
        · simp only [htz, ite_false] at h ⊢; exact absurd h htne
      · unfold osOodSrc at h ⊢
        by_cases htz : t < (cfg.lv i).logCols - cfg.yrLog
        · simp only [htz, ite_true] at h ⊢; exact absurd rfl h
        · simp only [htz, ite_false] at h ⊢; omega
  · have := os_readsAt_getD hbr.ich (k := cfg.levels.length) (by simp [ichCW])
    rw [ichCW, os_getD_map_range _ (by omega)] at this
    exact this

end OsData

end
end LeanVM.Guest.B1
