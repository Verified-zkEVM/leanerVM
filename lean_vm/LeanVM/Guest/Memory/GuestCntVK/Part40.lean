module

public import LeanVM.Guest.Memory.GuestCntVK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvkstaticRange_933 : kvkStaticRange 933 1 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_934 : kvkStaticRange 934 1 := by
  unfold kvkStaticRange; decide +kernel

end
end LeanVM.Guest
