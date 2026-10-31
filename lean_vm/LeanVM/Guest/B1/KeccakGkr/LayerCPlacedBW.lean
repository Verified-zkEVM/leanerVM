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
pack loop `__loop28`..`__loop31` (core `402`..`405`, frame 147) at most `294` words per iteration
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
  · exact packLoop_totalLeOn_at (j := 383) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact packLoop_totalLeOn_at (j := 384) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact packLoop_totalLeOn_at (j := 381) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact packLoop_totalLeOn_at (j := 382) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- **`keccak_round`'s words at `B2C.fs`**: its frame, `80`. -/
theorem round_totalLe_fs : TotalLe coreProgram LeanVM.Guest.B2C.fs "keccak_round" fun _ ↦ 80 := by
  have h1 := wSB_totalLe (j := 11) (f := "keccak_round") (by decide +kernel)
  rwa [wSB_idx (j := 11) (f := "keccak_round") (by decide +kernel),
    show wSBJ 11 = 80 by decide +kernel] at h1

variable {cert : String → V → ℕ}

end
end LeanVM.Guest.B1.VerifySub
