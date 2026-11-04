module

public import LeanVM.Guest.Memory.GuestWords.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem wstaticRange_881 : wStaticRange 881 4 := by
  unfold wStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wstaticRange_885 : wStaticRange 885 2 := by
  unfold wStaticRange; decide +kernel

end
end LeanVM.Guest
