module

public import LeanVM.Guest.Memory.GuestCntWD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kudstaticRange_308 : kudStaticRange 308 7 := by
  unfold kudStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kudstaticRange_315 : kudStaticRange 315 30 := by
  unfold kudStaticRange; decide +kernel

end
end LeanVM.Guest
