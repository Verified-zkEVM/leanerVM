module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_891 : kvxStaticRange 891 4 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_895 : kvxStaticRange 895 2 := by
  unfold kvxStaticRange; decide +kernel

end
end LeanVM.Guest
