module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_887 : kvjStaticRange 887 12 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest
