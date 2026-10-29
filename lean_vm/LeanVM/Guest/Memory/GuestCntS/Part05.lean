module

public import LeanVM.Guest.Memory.GuestCntS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwsstaticRange_306 : kwsStaticRange 306 7 := by
  unfold kwsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwsstaticRange_313 : kwsStaticRange 313 30 := by
  unfold kwsStaticRange; decide +kernel

end
end LeanVM.Guest
