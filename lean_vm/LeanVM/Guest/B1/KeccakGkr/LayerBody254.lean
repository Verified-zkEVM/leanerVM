/-
  LeanVM.Guest.B1.KeccakGkr.LayerBody254

  `keccak_layer__L1_L0`'s body is the template `layerT 1 0`, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.LayerT

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Guest.Core LeanVM.Guest.B1

@[expose] public section

theorem layer_body254 : Data.core251.body = layerT 1 0 := stmtsEqb_sound (by decide +kernel)

end
end LeanVM.Guest.B1.VerifySub
