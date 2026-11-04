module

public import LeanVM.Guest.Memory.GuestWords.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem wstaticRange_745 : wStaticRange 745 17 := by
  unfold wStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wstaticRange_762 : wStaticRange 762 19 := by
  unfold wStaticRange; decide +kernel

end
end LeanVM.Guest
