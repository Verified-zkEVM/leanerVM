module

public import LeanVM.Guest.Memory.GuestWords.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem wstaticRange_854 : wStaticRange 854 9 := by
  unfold wStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wstaticRange_863 : wStaticRange 863 6 := by
  unfold wStaticRange; decide +kernel

end
end LeanVM.Guest
