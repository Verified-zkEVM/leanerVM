/-
  LeanVM.Guest.B1.Place.OsKidsSp4

  The squeeze loop's words for the queries: the bit pointers `osW` and the decoders' runs `osS`.
-/

module

public import LeanVM.Guest.B1.Place.OsKidsSp3
public import LeanVM.Guest.B1.Whir.QueryBits

/-!
# The bit pointers and bit runs, read

`osW_reads`, `osW_region`: level `l`'s bit pointers, its squeeze loop at `p`, are the decoders'
frame runs shifted to each position's chunk. `osS_mem`, `osS_reads`: decoder `j`'s run holds the
bits of the challenge it decodes. `readsAt_shift`: a run read from a shifted pointer.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Whir
open LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier hiding Layout
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

theorem readsAt_shift {rd : Reader} {a : ℕ} {xs : List E} (h : ReadsAt rd (ofK (Parameters.gpow a)) xs)
    {k m : ℕ} (hk : k + m < xs.length) :
    LoadHolds rd (ofK (Parameters.gpow (a + k))) m (xs[k + m]'hk) := by
  rw [← ofK_gpow_mul_gen, loadHolds_mul_gen_pow]
  exact h (k + m) hk

theorem regionL_append_left {L L' : Layout} {i : ℕ} (h : RegionL L i) : RegionL (L ++ L') i :=
  let ⟨q, hq, h1, h2⟩ := h; ⟨q, List.mem_append_left _ hq, h1, h2⟩

theorem regionL_append_right {L L' : Layout} {i : ℕ} (h : RegionL L' i) : RegionL (L ++ L') i :=
  let ⟨q, hq, h1, h2⟩ := h; ⟨q, List.mem_append_right _ hq, h1, h2⟩

variable {fs : String → ℕ} {cert : String → V → ℕ} {c : OsCfg}

/-- The exponent of query `k`'s bit run, level `l`'s squeeze loop at `p`. -/
def osEb (fs : String → ℕ) (cert : String → V → ℕ) (c : OsCfg) (l p k : ℕ) : ℕ :=
  sqDecAt fs (lvAt c l) (c.sqLoop l) (osSqN c l) p (k / (192 / (lvAt c l).depth)) +
    cert (sqDecName (lvAt c l)) (.n 3) + (k % (192 / (lvAt c l).depth)) * (lvAt c l).depth

/-- **Level `l`'s bit pointers.** -/
theorem osW_reads {b l p : ℕ} {rd : Reader} (hm : MemL rd (osW fs cert c b l p)) {k : ℕ}
    (hk : k < (lvAt c l).squeezes * (192 / (lvAt c l).depth)) :
    LoadHolds rd (ofK (Parameters.gpow (osBase c b 8 + (lvAt c l).posOff))) k
      (ofK (Parameters.gpow (osEb fs cert c l p k))) := by
  have := hm _ (List.mem_singleton_self _) k (by simpa using hk)
  simp only [List.getElem_map, List.getElem_range, osBp] at this
  rw [ofK_gpow_mul_gen] at this
  exact this

theorem osW_region {b l p : ℕ} {k : ℕ} (hk : k < (lvAt c l).squeezes * (192 / (lvAt c l).depth)) :
    RegionL (osW fs cert c b l p) (osBase c b 8 + (lvAt c l).posOff + k) :=
  ⟨_, List.mem_singleton_self _, by simp, by simpa using hk⟩

/-- Decoder `j`'s run in the loop's buffers. -/
theorem osS_mem {tr : OsTr} {l p j : ℕ} (hj : j < osSqN c l) :
    (sqDecAt fs (lvAt c l) (c.sqLoop l) (osSqN c l) p j + cert (sqDecName (lvAt c l)) (.n 3),
      (List.range 192).map fun i ↦
        bitE ((eToNat (sqWJ ((tr.L l).F2.squeezeN 0).2.cap j)).testBit i)) ∈ osS fs cert c tr l p := by
  unfold osS sqRuns
  refine List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨j, List.mem_range.mpr (by omega), rfl⟩, ?_⟩
  simp [dqRunL]

/-- **Query `k`'s bits** in its decoder's run. -/
theorem osS_bits {tr : OsTr} {l p : ℕ} {rd : Reader} (hm : MemL rd (osS fs cert c tr l p)) {k : ℕ}
    (hk : k < (lvAt c l).squeezes * (192 / (lvAt c l).depth))
    {t : ℕ} (ht : t < (lvAt c l).depth) :
    LoadHolds rd (ofK (Parameters.gpow (osEb fs cert c l p k))) t
      (bitE ((eToNat (sqWJ ((tr.L l).F2.squeezeN 0).2.cap (k / (192 / (lvAt c l).depth)))).testBit
        ((k % (192 / (lvAt c l).depth)) * (lvAt c l).depth + t))) := by
  have hper : 1 ≤ 192 / (lvAt c l).depth := by
    rcases Nat.eq_zero_or_pos (192 / (lvAt c l).depth) with h0 | h0
    · rw [h0] at hk; simp at hk
    · omega
  have hj : k / (192 / (lvAt c l).depth) < osSqN c l := by
    unfold osSqN; exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hk)
  have hr := hm _ (osS_mem (fs := fs) (cert := cert) (tr := tr) (p := p) hj)
  have hm2 : (k % (192 / (lvAt c l).depth)) * (lvAt c l).depth + t < 192 := by
    have h1 := Nat.mod_lt k (show 0 < 192 / (lvAt c l).depth by omega)
    have h2 : (k % (192 / (lvAt c l).depth) + 1) * (lvAt c l).depth ≤ 192 :=
      le_trans (Nat.mul_le_mul_right _ h1) (Nat.div_mul_le_self _ _)
    rw [Nat.add_mul, one_mul] at h2; omega
  have := readsAt_shift hr (k := (k % (192 / (lvAt c l).depth)) * (lvAt c l).depth) (m := t)
    (by simpa using hm2)
  simp only [List.getElem_map, List.getElem_range] at this
  unfold osEb
  exact this

theorem osS_region {tr : OsTr} {l p : ℕ} {k : ℕ}
    (hk : k < (lvAt c l).squeezes * (192 / (lvAt c l).depth)) {t : ℕ} (ht : t < (lvAt c l).depth) :
    RegionL (osS fs cert c tr l p) (osEb fs cert c l p k + t) := by
  have hper : 1 ≤ 192 / (lvAt c l).depth := by
    rcases Nat.eq_zero_or_pos (192 / (lvAt c l).depth) with h0 | h0
    · rw [h0] at hk; simp at hk
    · omega
  have hj : k / (192 / (lvAt c l).depth) < osSqN c l := by
    unfold osSqN; exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hk)
  have hm2 : (k % (192 / (lvAt c l).depth)) * (lvAt c l).depth + t < 192 := by
    have h1 := Nat.mod_lt k (show 0 < 192 / (lvAt c l).depth by omega)
    have h2 : (k % (192 / (lvAt c l).depth) + 1) * (lvAt c l).depth ≤ 192 :=
      le_trans (Nat.mul_le_mul_right _ h1) (Nat.div_mul_le_self _ _)
    rw [Nat.add_mul, one_mul] at h2; omega
  refine ⟨_, osS_mem (fs := fs) (cert := cert) (tr := tr) (p := p) hj, ?_, ?_⟩
  · unfold osEb; simp only; omega
  · unfold osEb; simp only [List.length_map, List.length_range]; omega

end
end LeanVM.Guest.B1
