module

public import LeanVM.Guest.Memory.GuestCntS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwsstaticRange_291 : kwsStaticRange 291 10 := by
  unfold kwsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwsstaticRange_301 : kwsStaticRange 301 7 := by
  unfold kwsStaticRange; decide +kernel

end
end LeanVM.Guest
