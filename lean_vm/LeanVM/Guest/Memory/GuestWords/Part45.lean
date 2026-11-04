module

public import LeanVM.Guest.Memory.GuestWords.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem wstaticRange_649 : wStaticRange 649 16 := by
  unfold wStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wstaticRange_665 : wStaticRange 665 15 := by
  unfold wStaticRange; decide +kernel

end
end LeanVM.Guest
