module

public import LeanVM.Guest.Memory.GuestWords.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem wstaticRange_835 : wStaticRange 835 12 := by
  unfold wStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wstaticRange_847 : wStaticRange 847 11 := by
  unfold wStaticRange; decide +kernel

end
end LeanVM.Guest
