/-
  LeanVM.Guest.B1.KeccakGkr.VkCE

  `verify_keccak`'s inputs' opening, completely: the slices, then the rest.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.VkCD
public import LeanVM.Guest.B1.KeccakGkr.VkIn
public import LeanVM.Guest.B1.KeccakGkr.VkSlices

/-!
# The inputs' opening, completely

`slices_complete`: on `verify_keccak`'s evaluated valuation, the 64 slices at the cursor and at
`slices`, the capacity canonical, the reads are the slices, the sponge absorbing them squeezes the
ring map's first challenge, and the section holds.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr LeanVM.Guest.B1.Fwd Finset

@[expose] public section

variable {C : CallRel} {rd : Reader} {w : ℕ → E} {σ : Val}

theorem not_mem_of_contains {a : Atom} {S : List Atom} (h : S.contains a = false) : a ∉ S :=
  fun hm ↦ by rw [List.contains_iff_mem.mpr hm] at h; exact absurd h (by decide)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- **The slices, completely.** -/
theorem slices_complete (hσ : ∀ v, σ v = σ (.n v.idx))
    (hg : ∀ st ∈ slicesT (.n 4115) 4117 4122, GoodS rd vkSt w σ st)
    (hcap : AllCanonical ((cap5 4117).map σ)) {slices : List E} (hslL : slices.length = 64)
    (hcur : ReadsAt rd (σ (.n 4115)) slices) (hsl : ReadsAt rd (σ (.n 10)) slices) :
    (∀ z < 64, σ (.n (slB 4122 z)) = slices.getD z 0) ∧
      ((⟨(cap5 4117).map σ, []⟩ : Fs).absorbAll slices dsObserve).squeeze =
        (σ (.n (4122 + 854)), ⟨(cap5 (4122 + 843)).map σ, []⟩) ∧
      ∀ {next : Prop} {kret : List E → Prop}, next →
        Stmt.HoldsList C rd σ (slicesT (.n 4115) 4117 4122) next kret := by
  obtain ⟨k1, k2, k3⟩ := vkSlices_ker
  have mP : ∀ st ∈ slicesPre (.n 4115) 4117 4122, st ∈ slicesT (.n 4115) 4117 4122 :=
    fun st h ↦ by rw [slicesT_pre]; exact List.mem_append_left _ h
  have mC : ∀ st ∈ challengeT (.n (4122 + 835)) (.n (4122 + 836)) (4122 + 848),
      st ∈ slicesT (.n 4115) 4117 4122 :=
    fun st h ↦ by rw [slicesT_pre]; exact List.mem_append_right _ h
  -- each read
  have mR : ∀ z < 64, ∀ st ∈ fsNextT (.n 4115) z (slB 4122 z), st ∈ slicesPre (.n 4115) 4117 4122 := by
    intro z hz st h
    rw [slicesPre]
    refine List.mem_append_left _ (List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨z / 4,
      List.mem_range.mpr (by omega), rfl⟩, List.mem_append_right _ (List.mem_flatten.mpr ⟨_,
        List.mem_map.mpr ⟨z % 4, List.mem_range.mpr (Nat.mod_lt _ (by norm_num)), rfl⟩,
        List.mem_append_left _ ?_⟩)⟩)
    rw [Nat.div_add_mod]; exact h
  have R : ∀ z < 64, σ (.n (slB 4122 z)) = slices.getD z 0 ∧
      IsCanonical128 (σ (.n (slB 4122 z + 7))) ∧ IsCanonical128 (σ (.n (slB 4122 z + 9))) := by
    intro z hz
    have hm := mR z hz _ List.mem_cons_self
    have hns : Atom.load (.n (slB 4122 z)) (.n 4115) z ∉ vkSt := by
      have := List.all_eq_true.mp k3 _ (load_mem_resid hm)
      simp only [slRes, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
        Bool.not_eq_true'] at this
      rcases this with ⟨-, h⟩ | ⟨⟨⟨h, -⟩, -⟩, -⟩
      · exact not_mem_of_contains h
      · exact absurd h (by simp)
    obtain ⟨e, c7, c9, -, -⟩ := fsNext_complete (C := C) (fun st h ↦ hg st (mP st (mR z hz st h)))
      hns (v := slices.getD z 0) (by rw [List.getD_eq_getElem _ _ (by omega)]; exact hcur z (by omega))
    exact ⟨e, c7, c9⟩
  -- the reads and their permutations
  have hA : ∀ i ∈ slA, IsCanonical128 (σ (.n i)) := by
    intro i hi
    simp only [slA, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons,
      List.not_mem_nil, or_false] at hi
    rcases hi with (rfl | rfl | rfl | rfl | rfl) | ⟨z, hz, rfl | rfl⟩
    · exact hcap _ (by simp [cap5])
    · exact hcap _ (by simp [cap5])
    · exact hcap _ (by simp [cap5])
    · exact hcap _ (by simp [cap5])
    · exact hcap _ (by simp [cap5])
    · exact (R z hz).2.1
    · exact (R z hz).2.2
  have SP : ∀ {next : Prop} {kret : List E → Prop}, next →
      Stmt.HoldsList C rd σ (slicesPre (.n 4115) 4117 4122) next kret :=
    fun hn ↦ block_holdsP (S := vkSt) (w := w) (P := []) k1 hσ k2 (by simpa using fun st h ↦ hg st (mP st h)) hA
      (fun a ha ↦ by
        have hs := List.all_eq_true.mp k3 a ha
        cases a with
        | load d p off =>
          simp only [slRes, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
            Bool.not_eq_true'] at hs
          rcases hs with ⟨⟨rfl, hoff⟩, hns⟩ | ⟨⟨⟨rfl, hoff⟩, rfl⟩, -⟩
          · exact Or.inr (side_load (not_mem_of_contains hns) (hcur off (by omega)))
          · left
            show LoadHolds rd (σ (.n 10)) off (σ (.n (slB 4122 off)))
            rw [(R off hoff).1, List.getD_eq_getElem _ _ (by omega)]
            exact hsl off (by omega)
        | _ => simp [slRes] at hs) hn
  -- the last permutation, and the challenge
  have hall := ((holdsList_atoms (C := C) (rd := rd) (σ := σ) (allAtoms_of_all k1) True
    (fun _ ↦ True)).1 (SP trivial)).1
  have kf := hall (.keccak (slCells 4122 15 ++ cap5 (slCap 4117 4122 15))
    ((List.range 13).map fun k ↦ .n (4122 + 835 + k)) false false)
    (by rw [slicesPre]; exact List.mem_append_right _ List.mem_cons_self)
  obtain ⟨-, -, -, hout⟩ := keccak_outs kf
  have c1 : IsCanonical128 (σ (.n (4122 + 836))) := by
    have := hout 1 (by norm_num)
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega : 1 < 13),
      Option.map_some, Option.getD_some] at this
    rw [show 4122 + 836 = 4122 + 835 + 1 from rfl, this]; exact cellsOfState_canonical _ _ _
  obtain ⟨-, CH⟩ := challenge_complete (C := C) (fun st h ↦ hg st (mC st h)) c1
  have H : ∀ {next : Prop} {kret : List E → Prop}, next →
      Stmt.HoldsList C rd σ (slicesT (.n 4115) 4117 4122) next kret := fun hn ↦ by
    rw [slicesT_pre, holdsList_append]; exact SP (CH hn)
  obtain ⟨-, -, hsq, -⟩ := slicesT_holds (H (next := True) (kret := fun _ ↦ True) trivial)
  have hm : (List.range 64).map (fun z ↦ σ (.n (slB 4122 z))) = slices := by
    apply List.ext_getElem (by simp [hslL])
    intro k h1 h2
    simp only [List.getElem_map, List.getElem_range]
    rw [(R k (by simpa using h1)).1, List.getD_eq_getElem _ _ h2]
  rw [hm] at hsq
  exact ⟨fun z hz ↦ (R z hz).1, hsq, H⟩

end
end LeanVM.Guest.B1.VerifySub
