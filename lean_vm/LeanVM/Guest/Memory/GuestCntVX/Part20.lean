module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_861 : kvxStaticRange 861 6 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_867 : kvxStaticRange 867 8 := by
  unfold kvxStaticRange; decide +kernel

end
end LeanVM.Guest
