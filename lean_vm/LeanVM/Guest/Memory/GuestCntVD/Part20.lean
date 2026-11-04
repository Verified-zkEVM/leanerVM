module

public import LeanVM.Guest.Memory.GuestCntVD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvdstaticRange_861 : kvdStaticRange 861 6 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_867 : kvdStaticRange 867 8 := by
  unfold kvdStaticRange; decide +kernel

end
end LeanVM.Guest
