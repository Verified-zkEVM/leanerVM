module

public import LeanVM.Guest.Memory.GuestCntWD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kudstaticRange_288 : kudStaticRange 288 14 := by
  unfold kudStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kudstaticRange_302 : kudStaticRange 302 7 := by
  unfold kudStaticRange; decide +kernel

end
end LeanVM.Guest
