module

public import LeanVM.Guest.Memory.GuestCntVD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvdstaticRange_299 : kvdStaticRange 299 2 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_301 : kvdStaticRange 301 1 := by
  unfold kvdStaticRange; decide +kernel

end
end LeanVM.Guest
