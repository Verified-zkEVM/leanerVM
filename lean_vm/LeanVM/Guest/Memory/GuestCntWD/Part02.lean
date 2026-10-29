module

public import LeanVM.Guest.Memory.GuestCntWD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kudstaticRange_286 : kudStaticRange 286 13 := by
  unfold kudStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kudstaticRange_299 : kudStaticRange 299 7 := by
  unfold kudStaticRange; decide +kernel

end
end LeanVM.Guest
