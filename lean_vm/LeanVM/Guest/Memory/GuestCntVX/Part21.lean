module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_875 : kvxStaticRange 875 7 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_882 : kvxStaticRange 882 2 := by
  unfold kvxStaticRange; decide +kernel

end
end LeanVM.Guest
