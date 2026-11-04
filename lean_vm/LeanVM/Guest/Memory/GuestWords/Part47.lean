module

public import LeanVM.Guest.Memory.GuestWords.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem wstaticRange_709 : wStaticRange 709 18 := by
  unfold wStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wstaticRange_727 : wStaticRange 727 18 := by
  unfold wStaticRange; decide +kernel

end
end LeanVM.Guest
