module

public import LeanVM.Guest.Memory.GuestCntX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwxstaticRange_309 : kwxStaticRange 309 7 := by
  unfold kwxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwxstaticRange_316 : kwxStaticRange 316 30 := by
  unfold kwxStaticRange; decide +kernel

end
end LeanVM.Guest
