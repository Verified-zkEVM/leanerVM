module

public import LeanVM.Guest.Memory.GuestCntX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwxstaticRange_291 : kwxStaticRange 291 11 := by
  unfold kwxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwxstaticRange_302 : kwxStaticRange 302 7 := by
  unfold kwxStaticRange; decide +kernel

end
end LeanVM.Guest
