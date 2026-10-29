module

public import LeanVM.Guest.Memory.GuestCntX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwxstaticRange_291 : kwxStaticRange 291 8 := by
  unfold kwxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwxstaticRange_299 : kwxStaticRange 299 7 := by
  unfold kwxStaticRange; decide +kernel

end
end LeanVM.Guest
