/-
  LeanVM.Guest.B1.VerifySub.Gw

  The constant `g^105` of `verify_sub`'s call of `verify_keccak`, as a word.
-/

module

public import LeanVM.Guest.B1.Common.Basic

/-!
# `g^105`

`word_g105`: the word `59373627899904` is `g^105`, the offset of the output lanes' values in
`col_eval_words` (claims `110 .. 134`, the buffer starting at claim `5`; G:3439).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol.Verifier

@[expose] public section

set_option maxRecDepth 100000 in
theorem word_g105 : word 59373627899904 0 0 = gen ^ 105 := by
  rw [word_eOfNat, gen_pow_eq_ofK, ← gpowK_eq (by unfold u128Bound; omega)]
  show ofK (K.ofBits 59373627899904) = ofK (gpowK 105)
  congr 1

end
end LeanVM.Guest.B1.VerifySub
