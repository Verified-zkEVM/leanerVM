module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_843 : kvxStaticRange 843 12 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_855 : kvxStaticRange 855 8 := by
  unfold kvxStaticRange; decide +kernel

end
end LeanVM.Guest
