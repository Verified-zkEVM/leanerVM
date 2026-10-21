/-
  LeanVM.Guest.B1.Comp.Whir.Loc.OsKidsLv

  A level's kids of `open_stacked` over a completeness model (`Whir/OsKidsLv.lean`)
-/

module

public import LeanVM.Guest.B1.Whir.OsKidsLv
public import LeanVM.Guest.B1.Comp.Whir.Loc.OsKidsB
public import LeanVM.Guest.B1.Comp.Whir.Loc.SqAt
public import LeanVM.Guest.B1.Comp.Whir.Loc.OsBodyMemOf

/-!
# A level's kids of `open_stacked` over a completeness model (`Whir/OsKidsLv.lean`)
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub
open LeanVM.Guest.B1.Main (MemL RegionL)
open LeanVM.E2E.Complete
open LeanVM.Protocol.Compile (Bytes)
open LeanVM.Protocol (Digest)

@[expose] public noncomputable section

variable {Ht : Bytes → Digest} {CM : CompModel}

/-- The caller's words: its own and its buffers', the decoders' pointers left out. -/
def osLkW (Ht : Bytes → Digest) (cfg : OsCfg) (d : OsData) (Lin : Main.Layout) (b : ℕ) : Main.Layout :=
  Lin ++ bufL b (osSizes cfg) (d.ownQW Ht cfg [])

/-- Level `l`'s decoders' frame runs, its loop entered at `p`. -/
def osSW (Ht : Bytes → Digest) (fs : String → ℕ) (cert : String → V → ℕ) (cfg : OsCfg) (d : OsData) (l p : ℕ) : Main.Layout :=
  sqRuns fs cert (cfg.lv l) (cfg.lv l).squeezes p (sqWW Ht (d.cv3W Ht cfg l)) 0

namespace OsData

variable {fs : String → ℕ} {cert : String → V → ℕ} {κ : ℕ} {cfg : OsCfg} {d : OsData}

theorem oodz_readsAtC (hlay : OsLayoutOk cfg) {rd : Reader} {ptr : E} (hr : ReadsAt rd ptr (d.oodzCW Ht cfg)) {l : ℕ}
    (hl : l + 1 < cfg.levels.length) : ReadsAt rd (ptr * gen ^ ((l + 1) * 22)) (d.oodPtW Ht cfg l) := by
  have hlen : ∀ i, (d.oodPtW Ht cfg i).length = (cfg.lv i).logCols := fun i => length_sqAllW Ht _ _
  refine os_seg_readsAt (n := cfg.levels.length - 1) (off := fun l => (l + 1) * 22) (c := fun l => d.oodPtW Ht cfg l) hr
    (fun i j hij hj => ?_) (fun i hi => ?_) (by omega)
  · rw [hlen]; have := hlay.cols i (by omega)
    have : (i + 1) * 22 + 22 ≤ (j + 1) * 22 := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
    omega
  · rw [hlen]; have := hlay.cols i (by omega)
    have : (i + 1) * 22 + 22 ≤ cfg.levels.length * 22 := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
    omega

theorem ownQ_lengthC (Q : List E) : (d.ownQW Ht cfg Q).length = (osSizes cfg).length := by
  simp [ownQW, osSizes, osHeadSizes, List.length_flatMap, List.map_const']

theorem osPosOf_splitC {depth : ℕ} (hper : 0 < 192 / depth) (cv : Digest) {j i : ℕ} (hi : i < 192 / depth) :
    osPosOfW Ht depth cv (j * (192 / depth) + i) = (eToNat (sqWW Ht cv j) >>> (i * depth)) % 2 ^ depth := by
  unfold osPosOfW sqWW
  rw [show (j * (192 / depth) + i) / (192 / depth) = j by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hper, Nat.div_eq_of_lt hi, Nat.zero_add],
    show (j * (192 / depth) + i) % (192 / depth) = i by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]]

theorem memL_lkC {Lin : Main.Layout} {b l p : ℕ} {rd : Reader}
    (hm : MemL rd (osLkW Ht cfg d Lin b ++ osW fs cert cfg b l p ++ osSW Ht fs cert cfg d l p)) : MemL rd (osLkW Ht cfg d Lin b) :=
  (Main.memL_append.mp (Main.memL_append.mp hm).1).1

/-- A level's root slot and its openings' check, from the run. -/
theorem lv_openC {μ : ℕ} {Lall : List Whir.Level} {Q : List (ℕ × List (ℕ × Opening))} {l : ℕ}
    (hF : OsLvFactsW CM.hm Ht cfg μ d.xs Lall Q (d.lvW Ht cfg l)) (hlv : (d.lvW Ht cfg l).lvl = l) :
    openAll (m := Id) Ht (d.rtW Ht cfg l) (cfg.lv l).depth (oqR (if l = 0 then 1 else 0) (2 ^ (cfg.lv l).folds))
      (osHQsW Ht cfg l d.xs (d.lvW Ht cfg l).p (d.lvW Ht cfg l).H.cv1) (d.lvW Ht cfg l).osp = some ((d.lvW Ht cfg l).H.rows, (d.lvW Ht cfg l).H.osq) := by
  obtain ⟨rt', hrt'⟩ := hF.root
  obtain ⟨rt, hh, ww, hr, hoa⟩ := hF.ok.open_
  rw [hlv] at hrt' hr hoa
  have hlt : l < (d.lvW Ht cfg l).roots.length := by
    rcases Nat.lt_or_ge l (d.lvW Ht cfg l).roots.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hrt'; cases hrt'
  have e : (osHRootsEnd cfg l (d.lvW Ht cfg l).roots (d.lvW Ht cfg l).H)[l]? = (d.lvW Ht cfg l).roots[l]? := by
    unfold osHRootsEnd; split
    · rfl
    · exact List.getElem?_append_left hlt
  rw [e, hrt'] at hr
  simp only [Option.some.injEq, Prod.mk.injEq] at hr
  obtain ⟨rfl, rfl, rfl⟩ := hr
  have hrt : d.rtW Ht cfg l = rt' := by
    unfold rtW; rw [List.getD_eq_getElem?_getD, hrt']; rfl
  rw [hrt]; exact hoa

theorem osPosOf_testBitC {depth : ℕ} (cv : Digest) (j : ℕ) {l : ℕ} (hl : l < depth) :
    (osPosOfW Ht depth cv j).testBit l =
      (eToNat (sqWW Ht cv (j / (192 / depth)))).testBit (j % (192 / depth) * depth + l) := by
  unfold osPosOfW sqWW
  rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  simp [hl]

/-- A decoder's frame run, on a memory holding the level's runs. -/
theorem sqRuns_bitC {lv : OsLvl} {n p : ℕ} {w : ℕ → E} {rd : Reader} (hm : MemL rd (sqRuns fs cert lv n p w 0))
    {i : ℕ} (hi : i < n) {c : ℕ} (hc : c < 192) :
    LoadHolds rd (ofK (Parameters.gpow (sqDecAt fs lv n p i + cert lv.decode (.n 3)))) c
      (bitE ((eToNat (w i)).testBit c)) := by
  have hmem : (sqDecAt fs lv n p i + cert lv.decode (.n 3), (List.range 192).map fun c => bitE ((eToNat (w i)).testBit c))
      ∈ sqRuns fs cert lv n p w 0 := by
    unfold sqRuns
    refine List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨i, List.mem_range.mpr (by omega), rfl⟩, ?_⟩
    simp [dqRunL]
  have := hm _ hmem c (by simpa using hc)
  simpa using this

end OsData

end
end LeanVM.Guest.B1
