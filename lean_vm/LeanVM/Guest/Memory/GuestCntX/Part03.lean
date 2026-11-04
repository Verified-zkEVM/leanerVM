module

public import LeanVM.Guest.Memory.GuestCntX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwxstaticRange_310 : kwxStaticRange 310 7 := by
  unfold kwxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwxstaticRange_317 : kwxStaticRange 317 7 := by
  unfold kwxStaticRange; decide +kernel

end
end LeanVM.Guest
