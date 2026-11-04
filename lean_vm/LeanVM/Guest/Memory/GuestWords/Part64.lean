module

public import LeanVM.Guest.Memory.GuestWords.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem wstaticRange_936 : wStaticRange 936 2 := by
  unfold wStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wstaticRange_938 : wStaticRange 938 2 := by
  unfold wStaticRange; decide +kernel

end
end LeanVM.Guest
