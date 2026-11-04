module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_933 : kvxStaticRange 933 1 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_934 : kvxStaticRange 934 1 := by
  unfold kvxStaticRange; decide +kernel

end
end LeanVM.Guest
