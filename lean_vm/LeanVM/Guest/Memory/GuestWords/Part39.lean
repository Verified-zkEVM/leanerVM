module

public import LeanVM.Guest.Memory.GuestWords.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem wstaticRange_858 : wStaticRange 858 7 := by
  unfold wStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wstaticRange_865 : wStaticRange 865 9 := by
  unfold wStaticRange; decide +kernel

end
end LeanVM.Guest
