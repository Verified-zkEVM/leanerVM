module

public import LeanVM.Guest.Memory.GuestCntX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwxstaticRange_308 : kwxStaticRange 308 7 := by
  unfold kwxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwxstaticRange_315 : kwxStaticRange 315 30 := by
  unfold kwxStaticRange; decide +kernel

end
end LeanVM.Guest
