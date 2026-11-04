module

public import LeanVM.Guest.Memory.GuestWords.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem wstaticRange_869 : wStaticRange 869 7 := by
  unfold wStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wstaticRange_876 : wStaticRange 876 8 := by
  unfold wStaticRange; decide +kernel

end
end LeanVM.Guest
