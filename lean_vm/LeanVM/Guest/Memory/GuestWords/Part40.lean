module

public import LeanVM.Guest.Memory.GuestWords.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem wstaticRange_874 : wStaticRange 874 6 := by
  unfold wStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wstaticRange_880 : wStaticRange 880 7 := by
  unfold wStaticRange; decide +kernel

end
end LeanVM.Guest
