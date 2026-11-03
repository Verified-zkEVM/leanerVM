module

public import LeanVM.Guest.Memory.GuestCntWD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kudstaticRange_287 : kudStaticRange 287 14 := by
  unfold kudStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kudstaticRange_301 : kudStaticRange 301 7 := by
  unfold kudStaticRange; decide +kernel

end
end LeanVM.Guest
