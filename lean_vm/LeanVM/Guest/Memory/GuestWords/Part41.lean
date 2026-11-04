module

public import LeanVM.Guest.Memory.GuestWords.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem wstaticRange_512 : wStaticRange 512 17 := by
  unfold wStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wstaticRange_529 : wStaticRange 529 17 := by
  unfold wStaticRange; decide +kernel

end
end LeanVM.Guest
