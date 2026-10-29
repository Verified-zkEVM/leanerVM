module

public import LeanVM.Guest.Memory.GuestWords.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem wstaticRange_853 : wStaticRange 853 6 := by
  unfold wStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wstaticRange_859 : wStaticRange 859 7 := by
  unfold wStaticRange; decide +kernel

end
end LeanVM.Guest
