/-
  LeanVM.Guest.B1.Da.VerifyChain3

  The vector digest's chain, blocks 24 to 30, checked by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Da.VerifyDefs

namespace LeanVM.Guest.B1.Da

open LeanVM.Guest.Core LeanVM.Guest.B1.Digest

@[expose] public section

set_option maxRecDepth 100000 in
theorem vd_chain3_ok : (vdSpec (atomsIn dvP)).partOk (atomsIn dvP) 24 31 = true := by decide +kernel

end
end LeanVM.Guest.B1.Da
