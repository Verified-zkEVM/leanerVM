module

public import LeanVM.Guest.Memory.GuestCntVD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvdstaticRange_874 : kvdStaticRange 874 6 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_880 : kvdStaticRange 880 7 := by
  unfold kvdStaticRange; decide +kernel

end
end LeanVM.Guest
