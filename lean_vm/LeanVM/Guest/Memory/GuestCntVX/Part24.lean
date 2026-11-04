module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_688 : kvxStaticRange 688 16 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_704 : kvxStaticRange 704 17 := by
  unfold kvxStaticRange; decide +kernel

end
end LeanVM.Guest
