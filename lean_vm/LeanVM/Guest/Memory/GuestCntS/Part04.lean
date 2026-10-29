module

public import LeanVM.Guest.Memory.GuestCntS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwsstaticRange_291 : kwsStaticRange 291 8 := by
  unfold kwsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwsstaticRange_299 : kwsStaticRange 299 7 := by
  unfold kwsStaticRange; decide +kernel

end
end LeanVM.Guest
