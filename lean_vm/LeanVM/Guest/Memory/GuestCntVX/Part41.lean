module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_935 : kvxStaticRange 935 1 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_936 : kvxStaticRange 936 2 := by
  unfold kvxStaticRange; decide +kernel

end
end LeanVM.Guest
