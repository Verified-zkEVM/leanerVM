/-
  LeanVM.Guest.B1.KeccakGkr.LayerBody255

  `keccak_layer__L1_L1`'s body is the template `layerT 1 1`, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.LayerT

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Guest.Core LeanVM.Guest.B1

@[expose] public section

theorem layer_body255 : Data.core255.body = layerT 1 1 := stmtsEqb_sound (by decide +kernel)

end
end LeanVM.Guest.B1.VerifySub
