/-
  LeanVM.Guest.B1.Comp.Whir.Loc.OsAsm2

  The levels' records over a completeness model (`Whir/OsAsm2.lean`)
-/

module

public import LeanVM.Guest.B1.Whir.OsAsm2
public import LeanVM.Guest.B1.Comp.Whir.Loc.OsAsm1

/-!
# The levels' records over a completeness model (`Whir/OsAsm2.lean`)
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Main (MemL RegionL)
open LeanVM.Guest.B1.VerifySub
open LeanVM.E2E.Complete
open LeanVM.Protocol.Compile (Bytes)
open LeanVM.Protocol (Digest)

@[expose] public section

variable {Ht : Bytes → Digest} {CM : CompModel}

namespace OsData

variable {cfg : OsCfg} {d : OsData}

theorem qpos_atC (hlay : OsLayoutOk cfg) {rd : Reader} {ptr : E} (hr : ReadsAt rd ptr (d.qposCW Ht cfg)) {l : ℕ}
    (hl : l < cfg.levels.length) {j : ℕ} (hj : j < (cfg.lv l).squeezes * (192 / (cfg.lv l).depth)) :
    LoadHolds rd ptr ((cfg.lv l).posOff + j) (eOfNat (osPosOfW Ht (cfg.lv l).depth (d.cv3W Ht cfg l) j)) := by
  have h := os_seg_readsAt (n := cfg.levels.length) (off := fun l => (cfg.lv l).posOff)
    (c := fun l => (List.range ((cfg.lv l).squeezes * (192 / (cfg.lv l).depth))).map fun i =>
      eOfNat (osPosOfW Ht (cfg.lv l).depth (d.cv3W Ht cfg l) i)) hr
    (fun a c hac hc => by simp only [List.length_map, List.length_range]; exact hlay.pos a c hac hc)
    (fun a ha => by simp only [List.length_map, List.length_range]; exact hlay.posFit a ha) hl
  have := h j (by simpa using hj)
  rw [loadHolds_mul_gen_pow] at this
  simpa using this

/-- **A level's record**, on a memory holding the buffers. -/
theorem recOkC {μ r : ℕ} {Lall : List Whir.Level} (hok : OsCfgOk cfg μ r Lall) (hlay : OsLayoutOk cfg)
    {rd : Reader} {σ : Val} {b : ℕ} {Q : List E} (hbr : OsBufReadsW Ht rd cfg d b Q) (hP : OsPtrsAt σ (osPtrsOf cfg b))
    {l : ℕ} (hl : l < cfg.levels.length) (hlv : (d.lvW Ht cfg l).lvl = l) :
    OsRecOk rd σ cfg l (osRecOfW Ht cfg d.xs (d.lvW Ht cfg l)) := by
  have hspec := hok.spec l (by rw [hok.len]; exact hl)
  obtain ⟨-, -, -, -, -, -, -, -, -, hqs, -⟩ := hspec
  unfold osRecOfW
  rw [hlv]
  refine ⟨by simp [osHQsW], fun j hj => ?_, fun j hj => ?_, by simp, fun h => ?_, fun z hz => ?_⟩
  · rw [hP.qpos]
    have := qpos_atC (Ht := Ht) hlay hbr.qpos hl (j := j) (by omega)
    unfold osHQsW; rw [os_getD_map_range _ hj]; exact this
  · rw [hP.qw]; exact qw_atC (Ht := Ht) hlay hbr.qw hl j hj
  · have hy : l = cfg.yrLevel := by by_contra hy; simp [hy] at h
    rw [hP.betas]
    have := os_readsAt_getD hbr.betas (k := l) (by simp [betasCW, hl])
    rw [betasCW, os_getD_map_range _ hl, betaW, ite_pos' hy] at this
    exact this
  · have hy : l ≠ cfg.yrLevel := by intro hy; simp [hy] at hz
    simp only [hy, ↓reduceIte, Option.some.injEq] at hz
    subst hz
    have hl1 : l + 1 < cfg.levels.length := by have := hok.yrLevel; omega
    refine ⟨?_, length_sqAllW Ht _ _, ?_, ?_⟩
    · rw [hP.betas]
      have := os_readsAt_getD hbr.betas (k := l) (by simp [betasCW, hl])
      rw [betasCW, os_getD_map_range _ hl, betaW, ite_neg' hy] at this
      exact this
    · rw [hP.oodz]; exact oodz_readsAtC (Ht := Ht) hlay hbr.oodz hl1
    · rw [hP.ood]; exact (ood_atC (Ht := Ht) hbr.ood hl1).1

/-- **What a residual (chainW Ht) loop's iterations read.** -/
theorem resFactsC {μ r : ℕ} {Lall : List Whir.Level} (hok : OsCfgOk cfg μ r Lall) (hlay : OsLayoutOk cfg) {rd : Reader} {b : ℕ} {Q : List E} (hbr : OsBufReadsW Ht rd cfg d b Q) {l : ℕ}
    (hl : l < cfg.levels.length) :
    (∀ x < (cfg.lv l).queries, LoadHolds rd ((osPtrsOf cfg b).qpos * gen ^ x) (cfg.lv l).posOff
      ((d.qposCW Ht cfg).getD ((cfg.lv l).posOff + x) 0)) ∧
    (∀ t < (cfg.lv l).logCols, LoadHolds rd (osPtrAt cfg b (11 + 2 * cfg.levels.length + 2)) (l * 22 + t)
      (d.rowAW Ht cfg l t)) ∧
    (∀ t < (cfg.lv l).logCols, LoadHolds rd (osPtrAt cfg b (11 + 2 * cfg.levels.length + 3)) (l * 22 + t)
      (d.rowBW Ht cfg l t)) ∧
    (∀ x < (cfg.lv l).queries, LoadHolds rd (osPtrAt cfg b (11 + 2 * cfg.levels.length + 5 + l) * gen ^ x) 0
      (d.chainW Ht cfg l x)) ∧
    (∀ x < (cfg.lv l).queries, LoadHolds rd ((osPtrsOf cfg b).qw * gen ^ x) (l * cfg.maxQ) (d.lamW Ht cfg l ^ x)) ∧
    (∀ x < (cfg.lv l).queries, LoadHolds rd (osPtrAt cfg b (11 + 2 * cfg.levels.length + 5 + l) * gen ^ x) 1
      (d.chainW Ht cfg l x + d.lamW Ht cfg l ^ x * resProd (d.rowAW Ht cfg l) (d.rowBW Ht cfg l) (cfg.lv l).vals
        ((d.qposCW Ht cfg).getD ((cfg.lv l).posOff + x) 0) (cfg.lv l).logCols)) := by
  have hc22 := hlay.cols l hl
  have hqm := hlay.qw l hl
  have hrow : ∀ t < (cfg.lv l).logCols, l * 22 + t < cfg.levels.length * 22 := fun t ht => by
    have : l * 22 + 22 ≤ cfg.levels.length * 22 := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hl
    omega
  have hposlen : ∀ x < (cfg.lv l).queries, (cfg.lv l).posOff + x < (d.qposCW Ht cfg).length := fun x hx => by
    rw [qposCW, os_length_segC]
    have := hlay.posFit l hl
    obtain ⟨-, -, -, -, -, -, -, -, -, hqs, -⟩ := hok.spec l (by rw [hok.len]; exact hl)
    omega
  refine ⟨fun x hx => ?_, fun t ht => ?_, fun t ht => ?_, fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · rw [loadHolds_mul_gen_pow, Nat.add_comm x]
    exact os_readsAt_getD hbr.qpos (hposlen x hx)
  · exact os_readsAt_getD hbr.ba (by rw [baCW, os_length_segC]; exact hrow t ht)
  · exact os_readsAt_getD hbr.bb (by rw [bbCW, os_length_segC]; exact hrow t ht)
  · rw [loadHolds_mul_gen_pow, Nat.add_zero]
    have := os_readsAt_getD (hbr.chv l hl) (k := x) (by simp only [chvCW, List.length_map, List.length_range]; omega)
    rwa [chvCW, os_getD_map_range _ (by omega)] at this
  · rw [loadHolds_mul_gen_pow, Nat.add_comm x]; exact qw_atC (Ht := Ht) hlay hbr.qw hl x hx
  · rw [loadHolds_mul_gen_pow]
    have := os_readsAt_getD (hbr.chv l hl) (k := x + 1) (by simp only [chvCW, List.length_map, List.length_range]; omega)
    rw [chvCW, os_getD_map_range _ (by omega)] at this
    rw [show d.chainW Ht cfg l (x + 1) = _ from Finset.sum_range_succ _ x] at this
    exact this

/-- **The glued claims after the levels, one record per level.** -/
theorem glued_eqC {μ r lane : ℕ} {Lall : List Whir.Level} (hok : OsCfgOk cfg μ r Lall) {e : WhirEnd} {sp' : St}
    {Q : List (ℕ × List (ℕ × Opening))} (hlen : d.Hs.length = cfg.levels.length)
    (hch : OsChainC CM.hm Ht cfg μ lane d.xs Lall e sp' Q 0 (d.cv0W Ht) 2 (osW0 d.target d.xs) d.os (d.roots0 cfg) d.Hs) :
    (osLvsEndW Ht cfg d.xs 0 (d.cv0W Ht) 2 (osW0 d.target d.xs) (d.roots0 cfg) d.Hs).2.2.glued =
      osGluedOf μ cfg ((d.lvsW Ht cfg).map (osRecOfW Ht cfg d.xs)) := by
  rw [os_chain_gluedC (Ht := Ht) (CM := CM) hok.spec hok.len d.Hs 0 _ _ _ _ _ (by omega) hch]
  rw [show (osW0 d.target d.xs).glued = [] from rfl, List.nil_append, osGluedOf]
  congr 1
  apply List.ext_getElem (by simp [lvsW])
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_zipIdx, Nat.zero_add]
  have := os_lvsList_lvlC (Ht := Ht) cfg d.xs d.Hs 0 (d.cv0W Ht) 2 (osW0 d.target d.xs) d.os (d.roots0 cfg) i (by simpa [lvsW] using h2)
  simp only [Nat.zero_add] at this
  unfold lvsW
  rw [this]

end OsData

end
end LeanVM.Guest.B1
