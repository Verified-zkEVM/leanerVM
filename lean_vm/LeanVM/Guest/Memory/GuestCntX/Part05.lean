module

public import LeanVM.Guest.Memory.GuestCntX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwxstaticRange_306 : kwxStaticRange 306 7 := by
  unfold kwxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwxstaticRange_313 : kwxStaticRange 313 30 := by
  unfold kwxStaticRange; decide +kernel

end
end LeanVM.Guest
