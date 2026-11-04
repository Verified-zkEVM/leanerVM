module

public import LeanVM.Guest.Memory.GuestWords.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem wstaticRange_922 : wStaticRange 922 1 := by
  unfold wStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wstaticRange_923 : wStaticRange 923 2 := by
  unfold wStaticRange; decide +kernel

end
end LeanVM.Guest
