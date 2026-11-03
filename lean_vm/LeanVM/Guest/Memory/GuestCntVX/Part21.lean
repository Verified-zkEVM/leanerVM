module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_874 : kvxStaticRange 874 7 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_881 : kvxStaticRange 881 2 := by
  unfold kvxStaticRange; decide +kernel

end
end LeanVM.Guest
