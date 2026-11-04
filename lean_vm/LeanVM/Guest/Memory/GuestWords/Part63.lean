module

public import LeanVM.Guest.Memory.GuestWords.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem wstaticRange_934 : wStaticRange 934 1 := by
  unfold wStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wstaticRange_935 : wStaticRange 935 1 := by
  unfold wStaticRange; decide +kernel

end
end LeanVM.Guest
