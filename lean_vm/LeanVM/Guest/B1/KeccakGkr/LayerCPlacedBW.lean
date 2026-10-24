/-
  LeanVM.Guest.B1.KeccakGkr.LayerCPlacedBW

  `layer_completeAtFB` at the deployed frame sizes (`B2C.fs`): the callees' words from their
  words certificates, the bound in numbers.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.LayerCPlacedB
public import LeanVM.Guest.Count.Words

/-!
# `keccak_layer` within its words at `B2C.fs`

At the deployed frame sizes the words certificates (`Count.Words`) give the callees' words: each
pack loop `__loop30`..`__loop33` (core `402`..`405`, frame 147) at most `294` words per iteration
(its frame and its last, skipped call's), `keccak_round` (core `11`, a leaf) at most its frame,
`80`. So `keccak_layer__L{first}_L{odd}` (core `254`..`257`, frames `2152`, `2158`, `2519`,
`2525`) is complete within `layerWords B2C.fs first odd y 294 80`
`= fs (layerName first odd) + (y + 228) + (147 + ⌊y/2⌋ * 294) + odd * 80`, at most `7420` words for
`y ≤ 30` (`layerWords_fs_le`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.Memory LeanVM.Guest.Count
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Main (MemL RegionL)
open LeanVM.Protocol.KeccakGkr

@[expose] public section

/-- One pack loop's words at `B2C.fs`: `294` per iteration. -/
theorem packLoop_totalLeOn_at {j : ℕ} {f : String} (h : wOkK j f = true) (he : wSKJ j = 294)
    (hj : (coreProgram[j]?).map Fn.name = some f) :
    TotalLeOn coreProgram LeanVM.Guest.B2C.fs f LoopPre fun a ↦ logG (a.getD 1 0) * 294 := by
  have h1 := wSK_totalLeOn h
  rwa [wSK_idx hj, he] at h1

/-- **The pack loops' words at `B2C.fs`**: at most `294` per iteration. -/
theorem packLoop_totalLeOn_fs {first odd : ℕ} (hf : first < 2) (ho : odd < 2) :
    TotalLeOn coreProgram LeanVM.Guest.B2C.fs (packLoopName first odd) LoopPre
      fun a ↦ logG (a.getD 1 0) * 294 := by
  interval_cases first <;> interval_cases odd
  · exact packLoop_totalLeOn_at (j := 404) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact packLoop_totalLeOn_at (j := 405) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact packLoop_totalLeOn_at (j := 402) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact packLoop_totalLeOn_at (j := 403) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- **`keccak_round`'s words at `B2C.fs`**: its frame, `80`. -/
theorem round_totalLe_fs : TotalLe coreProgram LeanVM.Guest.B2C.fs "keccak_round" fun _ ↦ 80 := by
  have h1 := wSB_totalLe (j := 11) (f := "keccak_round") (by decide +kernel)
  rwa [wSB_idx (j := 11) (f := "keccak_round") (by decide +kernel),
    show wSBJ 11 = 80 by decide +kernel] at h1

/-- **`keccak_layer`'s words at `B2C.fs`, in numbers**: its frame (`2152`..`2525`), `y + 228`
for its buffers, `147 + ⌊y/2⌋ * 294` for the pack loop, `80` for an odd `y`'s last round: at most
`7420` for `y ≤ 30`. -/
theorem layerWords_fs_le {first odd y : ℕ} (hf : first < 2) (ho : odd < 2) (hy : y ≤ 30) :
    layerWords LeanVM.Guest.B2C.fs first odd y 294 80 ≤ 7420 := by
  have hp : LeanVM.Guest.B2C.fs (packLoopName first odd) = 147 := by
    interval_cases first <;> interval_cases odd
    · rw [show packLoopName 0 0 = "__loop32" from rfl,
      fs_idx (j := 404) (f := "__loop32") (by decide +kernel)]
      decide +kernel
    · rw [show packLoopName 0 1 = "__loop33" from rfl,
      fs_idx (j := 405) (f := "__loop33") (by decide +kernel)]
      decide +kernel
    · rw [show packLoopName 1 0 = "__loop30" from rfl,
      fs_idx (j := 402) (f := "__loop30") (by decide +kernel)]
      decide +kernel
    · rw [show packLoopName 1 1 = "__loop31" from rfl,
      fs_idx (j := 403) (f := "__loop31") (by decide +kernel)]
      decide +kernel
  have hl : LeanVM.Guest.B2C.fs (layerName first odd) ≤ 2525 := by
    interval_cases first <;> interval_cases odd
    · rw [show layerName 0 0 = "keccak_layer__L0_L0" from rfl,
      fs_idx (j := 256) (f := "keccak_layer__L0_L0") (by decide +kernel)]
      decide +kernel
    · rw [show layerName 0 1 = "keccak_layer__L0_L1" from rfl,
      fs_idx (j := 257) (f := "keccak_layer__L0_L1") (by decide +kernel)]
      decide +kernel
    · rw [show layerName 1 0 = "keccak_layer__L1_L0" from rfl,
      fs_idx (j := 254) (f := "keccak_layer__L1_L0") (by decide +kernel)]
      decide +kernel
    · rw [show layerName 1 1 = "keccak_layer__L1_L1" from rfl,
      fs_idx (j := 255) (f := "keccak_layer__L1_L1") (by decide +kernel)]
      decide +kernel
  have hy2 : y / 2 * 294 ≤ 15 * 294 := Nat.mul_le_mul_right _ (by omega)
  simp only [layerWords, hp]
  omega

variable {cert : String → V → ℕ}

/-- **`keccak_layer` is complete, placed, within its words at `B2C.fs`**:
`layer_completeAtFB` with the callees' words from their certificates, at most `7420` words
(`layerWords_fs_le`). -/
theorem layer_completeAtFB_fs {first odd : ℕ} (hf : first < 2) (ho : odd < 2) (κ : ℕ)
    (D : LayerData) (CL : ClaimLay) (bcur bout : ℕ) {p0 p1 iota : E}
    (hcl : D.cap.length = 5) (hcap : AllCanonical D.cap)
    (hw : first = 1 → (p0, p1) = Keccak.scalarCells D.w0 dsObserve)
    (hy : D.y % 2 = odd) (hy1 : 1 ≤ D.y) (hy30 : D.y ≤ 30) (hpl : D.product.length = 47)
    (hpm : D.packMsgs.length = D.y) (hlm : D.localMsgs.length = 11)
    (hproj : projectedOf D.c D.product + iota * sumE D.c.mu = D.c.value)
    (hfin : LayerFinal D.c (D.s0 first) D.product D.packMsgs D.localMsgs D.t)
    (hCL : CL.Ok first D.c D.y) :
    CompleteAtFB LeanVM.Guest.B2C.fs cert κ (layerName first odd)
      (fun fp ↦ layerLin D first CL bcur bout (fp + LeanVM.Guest.B2C.fs (layerName first odd)))
      (D.cap ++ [p0, p1, ptr bcur, gen ^ D.y, gen ^ (D.y / 2), gen ^ (D.y / 2 + odd), ptr CL.bclaim,
        ptr bout, iota])
      (fun fp rets Lout ↦ rets = D.rets first (ptr bcur) ∧
        Lout = layerBufs D first (ptr bcur) (fp + LeanVM.Guest.B2C.fs (layerName first odd)))
      (layerWords LeanVM.Guest.B2C.fs first odd D.y 294 80) :=
  layer_completeAtFB hf ho κ D CL bcur bout (packLoop_totalLeOn_fs hf ho) round_totalLe_fs hcl hcap
    hw hy hy1 hy30 hpl hpm hlm hproj hfin hCL

end
end LeanVM.Guest.B1.VerifySub
