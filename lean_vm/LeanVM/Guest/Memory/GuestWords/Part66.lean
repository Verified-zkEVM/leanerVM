module

public import LeanVM.Guest.Memory.GuestWords.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem wstaticRange_944 : wStaticRange 944 3 := by
  unfold wStaticRange; decide +kernel

end
end LeanVM.Guest
