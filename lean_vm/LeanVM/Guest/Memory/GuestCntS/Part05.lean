module

public import LeanVM.Guest.Memory.GuestCntS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwsstaticRange_308 : kwsStaticRange 308 7 := by
  unfold kwsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwsstaticRange_315 : kwsStaticRange 315 30 := by
  unfold kwsStaticRange; decide +kernel

end
end LeanVM.Guest
