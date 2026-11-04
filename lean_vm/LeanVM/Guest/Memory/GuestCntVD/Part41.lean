module

public import LeanVM.Guest.Memory.GuestCntVD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvdstaticRange_935 : kvdStaticRange 935 1 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_936 : kvdStaticRange 936 2 := by
  unfold kvdStaticRange; decide +kernel

end
end LeanVM.Guest
