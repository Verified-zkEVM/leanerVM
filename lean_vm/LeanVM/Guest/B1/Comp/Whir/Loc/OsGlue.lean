/-
  LeanVM.Guest.B1.Comp.Whir.Loc.OsGlue

  The levels' data glued over a total hash (`Whir/OsGlue.lean`)
-/

module

public import LeanVM.Guest.B1.Whir.OsGlue
public import LeanVM.Guest.B1.Comp.Whir.Loc.OsMem

/-!
# The levels' data glued over a total hash (`Whir/OsGlue.lean`)
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

/-- **A level is the list's entry at its index.** -/
theorem os_lvs_getC (cfg : OsCfg) (xs : List E) (Hs : List OsLvH) (cv : Digest) (p : ℕ) (w : WhirState)
    (osp : List Opening) (roots : List (Digest × ℕ × ℕ)) :
    ∀ L ∈ osLvsListW Ht cfg xs 0 cv p w osp roots Hs,
      (osLvsListW Ht cfg xs 0 cv p w osp roots Hs).getD L.lvl default = L ∧
        L.lvl < (osLvsListW Ht cfg xs 0 cv p w osp roots Hs).length := by
  intro L hL
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hL
  have e := os_lvsList_lvlC (Ht := Ht) cfg xs Hs 0 cv p w osp roots i hi
  rw [e, Nat.zero_add, List.getD_eq_getElem _ _ hi]
  exact ⟨rfl, hi⟩

/-- **The next level along a run.** -/
theorem os_chain_nextC {cfg : OsCfg} {μ lane : ℕ} {xs : List E} {Lall : List Whir.Level} {e : WhirEnd}
    {sp' : St} {Q : List (ℕ × List (ℕ × Opening))} : ∀ (Hs : List OsLvH) lvl cv p w osp roots,
      OsChainC CM.hm Ht cfg μ lane xs Lall e sp' Q lvl cv p w osp roots Hs → roots.length = lvl + 1 →
      ∀ L ∈ osLvsListW Ht cfg xs lvl cv p w osp roots Hs, L.roots.length = L.lvl + 1 ∧
        (L.lvl ≠ cfg.yrLevel → ∃ L' ∈ osLvsListW Ht cfg xs lvl cv p w osp roots Hs, L'.lvl = L.lvl + 1 ∧
          L'.roots = L.roots ++ [(L.H.root, (cfg.lv (L.lvl + 1)).depth, 3 * 2 ^ (cfg.lv (L.lvl + 1)).folds)])
  | [], _, _, _, _, _, _, h, _ => h.elim
  | H :: Hs, lvl, cv, p, w, osp, roots, h, hr => by
    obtain ⟨-, -, -, hl, hn⟩ := h
    intro L hL
    simp only [osLvsListW, List.mem_cons] at hL
    rcases hL with rfl | hL
    · refine ⟨hr, fun hy => ?_⟩
      have hch := hn hy
      cases Hs with
      | nil => exact hch.elim
      | cons H' Hs' =>
        refine ⟨⟨lvl + 1, osHCvEndW Ht cfg lvl xs p H.cv1, osHPEnd cfg lvl p, osHWEndW Ht cfg lvl xs p H, H.osq,
          osHRootsEnd cfg lvl roots H, H'⟩, List.mem_cons_of_mem _ (by simp [osLvsListW]), rfl, ?_⟩
        show osHRootsEnd cfg lvl roots H = _
        rw [osHRootsEnd, ite_neg' hy]
    · by_cases hy : lvl = cfg.yrLevel
      · obtain ⟨rfl, -⟩ := hl hy
        simp [osLvsListW] at hL
      · have ih := os_chain_nextC Hs _ _ _ _ _ _ (hn hy) (by rw [osHRootsEnd, ite_neg' hy]; simp [hr]) L hL
        refine ⟨ih.1, fun hy' => ?_⟩
        obtain ⟨L', hL', h1, h2⟩ := ih.2 hy'
        exact ⟨L', List.mem_cons_of_mem _ hL', h1, h2⟩

/-- **The fold challenges along a run**: each level's after its folds a prefix of the end's, the
end's the last level's. -/
theorem os_chain_foldsC {cfg : OsCfg} {μ lane : ℕ} {xs : List E} {Lall : List Whir.Level} {e : WhirEnd}
    {sp' : St} {Q : List (ℕ × List (ℕ × Opening))} : ∀ (Hs : List OsLvH) lvl cv p w osp roots,
      OsChainC CM.hm Ht cfg μ lane xs Lall e sp' Q lvl cv p w osp roots Hs →
      w.folds <+: (osLvsEndW Ht cfg xs lvl cv p w roots Hs).2.2.folds ∧
        (∀ L ∈ osLvsListW Ht cfg xs lvl cv p w osp roots Hs, L.H.w1.folds <+: (osLvsEndW Ht cfg xs lvl cv p w roots Hs).2.2.folds) ∧
        ∃ L ∈ osLvsListW Ht cfg xs lvl cv p w osp roots Hs, L.lvl = cfg.yrLevel ∧
          (osLvsEndW Ht cfg xs lvl cv p w roots Hs).2.2.folds = L.H.w1.folds
  | [], _, _, _, _, _, _, h => h.elim
  | H :: Hs, lvl, cv, p, w, osp, roots, h => by
    obtain ⟨hok, -, -, hl, hn⟩ := h
    have hw1 : w.folds <+: H.w1.folds := by rw [hok.chs.1]; exact List.prefix_append _ _
    have hend : (osHWEndW Ht cfg lvl xs p H).folds = H.w1.folds := os_glue_folds _ _ _
    by_cases hy : lvl = cfg.yrLevel
    · obtain ⟨rfl, -⟩ := hl hy
      have e : (osLvsEndW Ht cfg xs lvl cv p w roots [H]).2.2.folds = H.w1.folds := hend
      refine ⟨by rw [e]; exact hw1, fun L hL => ?_, ⟨_, List.mem_cons_self, hy, e⟩⟩
      simp only [osLvsListW, List.mem_cons, List.not_mem_nil, or_false] at hL
      subst hL; rw [e]
    · obtain ⟨h1, h2, L', hL', hy', he'⟩ := os_chain_foldsC Hs _ _ _ _ _ _ (hn hy)
      have e : osLvsEndW Ht cfg xs lvl cv p w roots (H :: Hs) = osLvsEndW Ht cfg xs (lvl + 1) (osHCvEndW Ht cfg lvl xs p H.cv1)
          (osHPEnd cfg lvl p) (osHWEndW Ht cfg lvl xs p H) (osHRootsEnd cfg lvl roots H) Hs := rfl
      rw [e]
      rw [hend] at h1
      refine ⟨hw1.trans h1, fun L hL => ?_, ⟨L', List.mem_cons_of_mem _ hL', hy', he'⟩⟩
      simp only [osLvsListW, List.mem_cons] at hL
      rcases hL with rfl | hL
      · exact h1
      · exact h2 L hL

namespace OsData

variable {cfg : OsCfg} {d : OsData}

theorem lv_memC {l : ℕ} (hl : l < d.Hs.length) : d.lvW Ht cfg l ∈ d.lvsW Ht cfg ∧ (d.lvW Ht cfg l).lvl = l := by
  have hlen : (d.lvsW Ht cfg).length = d.Hs.length := os_lvsList_lengthC (Ht := Ht) cfg d.xs d.Hs 0 _ _ _ _ _
  unfold lvW
  rw [List.getD_eq_getElem _ _ (by omega)]
  refine ⟨List.getElem_mem _, ?_⟩
  have := os_lvsList_lvlC (Ht := Ht) cfg d.xs d.Hs 0 (d.cv0W Ht) 2 (osW0 d.target d.xs) d.os (d.roots0 cfg) l (by unfold lvsW at hlen; omega)
  simp only [Nat.zero_add] at this
  exact this

/-- **Level `0`'s root is the commitment's.** -/
theorem rt_zeroC (hn : d.Hs ≠ []) : d.rtW Ht cfg 0 = d.root := by
  cases h : d.Hs with
  | nil => exact absurd h hn
  | cons H Hs => simp [rtW, lvW, lvsW, h, osLvsListW, roots0]

/-- **The next level's root has the scalars the level reads.** -/
theorem rt_succC {μ lane : ℕ} {Lall : List Whir.Level} {e : WhirEnd} {sp' : St}
    {Q : List (ℕ × List (ℕ × Opening))}
    (hch : OsChainC CM.hm Ht cfg μ lane d.xs Lall e sp' Q 0 (d.cv0W Ht) 2 (osW0 d.target d.xs) d.os (d.roots0 cfg) d.Hs)
    (hyr : cfg.yrLevel = d.Hs.length - 1) {l : ℕ} (hl : l + 1 < d.Hs.length) :
    digestScalars (d.rtW Ht cfg (l + 1)) = (osHW cfg l d.xs (d.lvW Ht cfg l).p 0, osHW cfg l d.xs (d.lvW Ht cfg l).p 1) := by
  obtain ⟨hm, hlv⟩ := lv_memC (Ht := Ht) (cfg := cfg) (d := d) (l := l) (by omega)
  have hy : (d.lvW Ht cfg l).lvl ≠ cfg.yrLevel := by rw [hlv]; omega
  obtain ⟨hlen, hnx⟩ := os_chain_nextC (Ht := Ht) (CM := CM) d.Hs 0 _ _ _ _ _ hch rfl _ hm
  obtain ⟨L', hL', h1, h2⟩ := hnx hy
  obtain ⟨hg, -⟩ := os_lvs_getC (Ht := Ht) cfg d.xs d.Hs _ _ _ _ _ L' hL'
  have hL'e : d.lvW Ht cfg (l + 1) = L' := by
    unfold lvW lvsW; rw [← hlv, ← h1]; exact hg
  have hok := (os_chain_memC (Ht := Ht) (CM := CM) d.Hs 0 _ _ _ _ _ hch _ hm).ok
  have hr := hok.root hy
  rw [hlv] at hr
  unfold rtW
  rw [hL'e, h2, hlv, List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_right (by omega)]
  simp only [hlen, hlv, Nat.sub_self, List.getElem_cons_zero]
  exact digestScalars_digestOfScalars hr

/-- **The fold challenges' window of a level.** -/
theorem fch_eqC {μ lane : ℕ} {Lall : List Whir.Level} {e : WhirEnd} {sp' : St} {Q : List (ℕ × List (ℕ × Opening))}
    (hch : OsChainC CM.hm Ht cfg μ lane d.xs Lall e sp' Q 0 (d.cv0W Ht) 2 (osW0 d.target d.xs) d.os (d.roots0 cfg) d.Hs)
    {l : ℕ} (hl : l < d.Hs.length) {j : ℕ} (hj : j < (cfg.lv l).folds) :
    (d.fchCW Ht cfg).getD ((cfg.lv l).foldsOff + j) 0 = (d.lvW Ht cfg l).H.chs.getD j 0 := by
  obtain ⟨hm, hlv⟩ := lv_memC (Ht := Ht) (cfg := cfg) (d := d) hl
  obtain ⟨-, hpre, -⟩ := os_chain_foldsC (Ht := Ht) (CM := CM) d.Hs 0 _ _ _ _ _ hch
  have hp := hpre _ hm
  have hok := (os_chain_memC (Ht := Ht) (CM := CM) d.Hs 0 _ _ _ _ _ hch _ hm).ok
  rw [hlv] at hok
  have hw1 := hok.w1len
  obtain ⟨hc1, hc2⟩ := hok.chs
  unfold osLevelF at hw1
  have hwl : (d.lvW Ht cfg l).w.folds.length = (cfg.lv l).foldsOff := by
    rw [hc1, List.length_append, hc2] at hw1; omega
  have hidx : (cfg.lv l).foldsOff + j < (d.lvW Ht cfg l).H.w1.folds.length := by omega
  unfold fchCW
  rw [List.getD_eq_getElem _ _ (by have := hp.length_le; omega), ← hp.getElem hidx]
  simp only [hc1, List.getElem_append_right (show (d.lvW Ht cfg l).w.folds.length ≤ (cfg.lv l).foldsOff + j by omega),
    hwl, Nat.add_sub_cancel_left]
  rw [List.getD_eq_getElem _ _ (by omega)]

/-- **The fold challenges' length.** -/
theorem fch_lenC {μ r lane : ℕ} {Lall : List Whir.Level} (hok : OsCfgOk cfg μ r Lall) {e : WhirEnd} {sp' : St}
    {Q : List (ℕ × List (ℕ × Opening))}
    (hch : OsChainC CM.hm Ht cfg μ lane d.xs Lall e sp' Q 0 (d.cv0W Ht) 2 (osW0 d.target d.xs) d.os (d.roots0 cfg) d.Hs) :
    (d.fchCW Ht cfg).length = cfg.nFolds := by
  obtain ⟨-, -, L, hL, hy, he⟩ := os_chain_foldsC (Ht := Ht) (CM := CM) d.Hs 0 _ _ _ _ _ hch
  have hokL := (os_chain_memC (Ht := Ht) (CM := CM) d.Hs 0 _ _ _ _ _ hch _ hL).ok
  unfold fchCW
  rw [he, hokL.w1len, hy, hok.yrLevel, hok.nFolds]

end OsData

end
end LeanVM.Guest.B1
