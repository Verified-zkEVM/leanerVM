module

public import LeanVM.Guest.Memory.GuestWords.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem wstaticRange_680 : wStaticRange 680 13 := by
  unfold wStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wstaticRange_693 : wStaticRange 693 16 := by
  unfold wStaticRange; decide +kernel

end
end LeanVM.Guest
