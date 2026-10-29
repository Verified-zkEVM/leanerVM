/-
  LeanVM.Guest.B1.KeccakGkr.VkKidsBW

  `kids_completeB` at the deployed frame sizes (`B2C.fs`): the callees' words from their words
  certificates, the bound in numbers.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.VkKidsB
public import LeanVM.Guest.B1.KeccakGkr.LayerCPlacedBW

/-!
# `verify_keccak`'s callees within their words at `B2C.fs`

The words certificates (`Count.Words`) give, at the deployed frame sizes: the copy loops
`__loop10`, `__loop11`, `__loop12` (cores `253`, `259`, `261`, frame 17) at most `34` words per
iteration; `keccak_plain_rounds__L6_L0` (core `258`, `plainName 0`) at most `325`,
`keccak_plain_rounds__L4_L1` (core `260`, `plainName 1`) at most `229`; the layers' pack loops
`294` per iteration and `keccak_round` `80` (`LayerCPlacedBW`). So `verify_keccak`'s callees are
complete within `D.kidsB B2C.fs 34 294 80 325 229` (`kids_completeB_fs`), whose sum is at most
`3 * ((τ - 4) * 34) + 879 + 12 * (2525 + (τ - 3 + 228) + (147 + (τ - 3) / 2 * 294) + 80)`, at most
`81723` words for `τ ≤ 28` (`kidsB_fs_le`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.Memory LeanVM.Guest.Count
open LeanVM.Protocol LeanVM.Protocol.KeccakGkr

@[expose] public section

/-- A loop helper's words at `B2C.fs` from its certificate: `K` per iteration. -/
theorem loop_totalLeOn_at {j K : ℕ} {f : String} (h : wOkK j f = true) (he : wSKJ j = K)
    (hj : (coreProgram[j]?).map Fn.name = some f) :
    TotalLeOn coreProgram LeanVM.Guest.B2C.fs f LoopPre fun a ↦ logG (a.getD 1 0) * K := by
  have h1 := wSK_totalLeOn h
  rwa [wSK_idx hj, he] at h1

/-- **The copy loops' words at `B2C.fs`**: at most `34` per iteration. -/
theorem copyLoop_totalLeOn_fs : ∀ name ∈ ["__loop10", "__loop11", "__loop12"],
    TotalLeOn coreProgram LeanVM.Guest.B2C.fs name LoopPre fun a ↦ logG (a.getD 1 0) * 34 := by
  intro name hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl
  · exact loop_totalLeOn_at (j := 250) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact loop_totalLeOn_at (j := 256) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact loop_totalLeOn_at (j := 258) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- **`keccak_plain_rounds__L6_L0`'s words at `B2C.fs`**: `325`. -/
theorem plain0_totalLe_fs :
    TotalLe coreProgram LeanVM.Guest.B2C.fs (plainName 0) fun _ ↦ 325 := by
  have h1 := wSB_totalLe (j := 255) (f := "keccak_plain_rounds__L6_L0") (by decide +kernel)
  rwa [wSB_idx (j := 255) (f := "keccak_plain_rounds__L6_L0") (by decide +kernel),
    show wSBJ 258 = 325 by decide +kernel] at h1

/-- **`keccak_plain_rounds__L4_L1`'s words at `B2C.fs`**: `229`. -/
theorem plain1_totalLe_fs :
    TotalLe coreProgram LeanVM.Guest.B2C.fs (plainName 1) fun _ ↦ 229 := by
  have h1 := wSB_totalLe (j := 257) (f := "keccak_plain_rounds__L4_L1") (by decide +kernel)
  rwa [wSB_idx (j := 257) (f := "keccak_plain_rounds__L4_L1") (by decide +kernel),
    show wSBJ 260 = 229 by decide +kernel] at h1

/-- A layer's words at `B2C.fs`, its frame at most `2525`. -/
theorem layerWords_fs_le_y {first odd y : ℕ} (hf : first < 2) (ho : odd < 2) :
    layerWords LeanVM.Guest.B2C.fs first odd y 294 80 ≤
      2525 + (y + 228) + (147 + y / 2 * 294) + 80 := by
  have hp : LeanVM.Guest.B2C.fs (packLoopName first odd) = 147 := by
    interval_cases first <;> interval_cases odd
    · rw [show packLoopName 0 0 = "__loop30" from rfl,
        fs_idx (j := 383) (f := "__loop30") (by decide +kernel)]
      decide +kernel
    · rw [show packLoopName 0 1 = "__loop31" from rfl,
        fs_idx (j := 384) (f := "__loop31") (by decide +kernel)]
      decide +kernel
    · rw [show packLoopName 1 0 = "__loop28" from rfl,
        fs_idx (j := 381) (f := "__loop28") (by decide +kernel)]
      decide +kernel
    · rw [show packLoopName 1 1 = "__loop29" from rfl,
        fs_idx (j := 382) (f := "__loop29") (by decide +kernel)]
      decide +kernel
  have hl : LeanVM.Guest.B2C.fs (layerName first odd) ≤ 2525 := by
    interval_cases first <;> interval_cases odd
    · rw [show layerName 0 0 = "keccak_layer__L0_L0" from rfl,
        fs_idx (j := 253) (f := "keccak_layer__L0_L0") (by decide +kernel)]
      decide +kernel
    · rw [show layerName 0 1 = "keccak_layer__L0_L1" from rfl,
        fs_idx (j := 254) (f := "keccak_layer__L0_L1") (by decide +kernel)]
      decide +kernel
    · rw [show layerName 1 0 = "keccak_layer__L1_L0" from rfl,
        fs_idx (j := 251) (f := "keccak_layer__L1_L0") (by decide +kernel)]
      decide +kernel
    · rw [show layerName 1 1 = "keccak_layer__L1_L1" from rfl,
        fs_idx (j := 252) (f := "keccak_layer__L1_L1") (by decide +kernel)]
      decide +kernel
  have h80 : odd * 80 ≤ 80 := by interval_cases odd <;> norm_num
  simp only [layerWords, hp]
  omega

namespace VkData

variable {D : VkData} {cert : String → V → ℕ}

/-- **`verify_keccak`'s calls, complete where it places them, within their words at `B2C.fs`.** -/
theorem kids_completeB_fs (h : D.Ok) (κ : ℕ) (B curE chiE olE zvE slE : ℕ) :
    KidsGB LeanVM.Guest.B2C.fs cert κ (D.kids LeanVM.Guest.B2C.fs B curE chiE olE zvE slE)
      (D.kidsB LeanVM.Guest.B2C.fs 34 294 80 325 229) :=
  kids_completeB h κ B curE chiE olE zvE slE copyLoop_totalLeOn_fs
    (fun _ hf ↦ packLoop_totalLeOn_fs hf (Nat.mod_lt _ (by norm_num))) round_totalLe_fs
    plain0_totalLe_fs plain1_totalLe_fs

/-- **The callees' words at `B2C.fs`, in numbers**: the copy loops `(τ - 4) * 34` each, the
openings' rounds `325 + 229 + 325`, each layer at most
`2525 + (τ - 3 + 228) + (147 + (τ - 3) / 2 * 294) + 80`; at most `81723` (`τ ≤ 28`). -/
theorem kidsB_fs_le (h : D.Ok) :
    (D.kidsB LeanVM.Guest.B2C.fs 34 294 80 325 229).sum ≤
      3 * ((D.τ - 4) * 34) + 879 +
        12 * (2525 + (D.τ - 3 + 228) + (147 + (D.τ - 3) / 2 * 294) + 80) ∧
    (D.kidsB LeanVM.Guest.B2C.fs 34 294 80 325 229).sum ≤ 81723 := by
  have hτ := h.2.1
  have hL : ((List.range 12).map (fun s ↦ layerWords LeanVM.Guest.B2C.fs (firstOf s) D.odd
      (D.layer s).y 294 80)).sum ≤
      12 * (2525 + (D.τ - 3 + 228) + (147 + (D.τ - 3) / 2 * 294) + 80) := by
    have := List.sum_le_length_nsmul ((List.range 12).map (fun s ↦ layerWords
      LeanVM.Guest.B2C.fs (firstOf s) D.odd (D.layer s).y 294 80))
      (2525 + (D.τ - 3 + 228) + (147 + (D.τ - 3) / 2 * 294) + 80) (fun x hx ↦ ?_)
    · simpa using this
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hx
    have hs' := List.mem_range.mp hs
    rw [D.layer_y h (by omega)]
    exact layerWords_fs_le_y (by unfold firstOf; split <;> omega) (Nat.mod_lt _ (by norm_num))
  have hy : (D.τ - 3) / 2 * 294 ≤ 12 * 294 := Nat.mul_le_mul_right _ (by omega)
  rw [kidsB_sum]
  constructor <;> omega

end VkData

end
end LeanVM.Guest.B1.VerifySub
