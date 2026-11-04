module

public import LeanVM.Guest.Memory.GuestWords.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem wstaticRange_546 : wStaticRange 546 16 := by
  unfold wStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wstaticRange_562 : wStaticRange 562 18 := by
  unfold wStaticRange; decide +kernel

end
end LeanVM.Guest
