module

public import LeanVM.Guest.Memory.GuestCntX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwxstaticRange_894 : kwxStaticRange 894 30 := by
  unfold kwxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwxstaticRange_924 : kwxStaticRange 924 23 := by
  unfold kwxStaticRange; decide +kernel

end
end LeanVM.Guest
