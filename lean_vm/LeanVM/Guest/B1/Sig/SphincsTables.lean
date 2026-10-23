/-
  LeanVM.Guest.B1.Sig.SphincsTables

  The guest's codeword table is leanSPHINCS's (`spCode_lut`), and its target word is `g^123`.
-/

module

public import LeanVM.Guest.B1.Sig.SphincsScheme
public import LeanVM.Guest.B1.Sig.Codeword
public import LeanVM.Guest.B1.Sig.SphincsT
public import LeanVM.Guest.Value.Bits

/-!
# The tables

`spCode_lut`: the deficit of chain `i` in codeword entry `t` is `lut t i`. `sTarget_eq`: the
codeword's target is `g^123`.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Guest LeanVM.Guest.Value LeanVM.Protocol.Verifier

@[expose] public section

theorem spCode_lut_all : ∀ t < 256, ∀ i < 6,
    spCodes / 5 ^ (6 * t + i) % 5 = Sphincs.codewordCodes.getD t 0 / 5 ^ (5 - i) % 5 := by
  decide +kernel

theorem spCode_lut (t : Sphincs.LutIdx) (i : Sphincs.FChain) : spCode t.val i.val = (Sphincs.lut t i).val := by
  rw [lut_val]
  exact spCode_lut_all t.val t.isLt i.val i.isLt

theorem sTarget_eq : sTarget = gen ^ 123 := by
  rw [LeanVM.Guest.Value.gen_pow_eq_ofK, sTarget, word, Value.ofBits_zero]
  rw [← ofK_eq_ofLimbs]
  exact congrArg ofK (by decide +kernel)

end
end LeanVM.Guest.B1.Sig
