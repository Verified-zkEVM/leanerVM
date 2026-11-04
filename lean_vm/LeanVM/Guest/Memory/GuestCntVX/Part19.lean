module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_843 : kvxStaticRange 843 8 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_851 : kvxStaticRange 851 9 := by
  unfold kvxStaticRange; decide +kernel

end
end LeanVM.Guest
