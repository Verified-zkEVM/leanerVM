module

public import LeanVM.Guest.Memory.GuestWords.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem wstaticRange_810 : wStaticRange 810 13 := by
  unfold wStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wstaticRange_823 : wStaticRange 823 12 := by
  unfold wStaticRange; decide +kernel

end
end LeanVM.Guest
