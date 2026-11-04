module

public import LeanVM.Guest.Memory.GuestWords.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem wstaticRange_580 : wStaticRange 580 19 := by
  unfold wStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wstaticRange_599 : wStaticRange 599 17 := by
  unfold wStaticRange; decide +kernel

end
end LeanVM.Guest
