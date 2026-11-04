module

public import LeanVM.Guest.Memory.GuestWords.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem wstaticRange_875 : wStaticRange 875 8 := by
  unfold wStaticRange; decide +kernel

end
end LeanVM.Guest
