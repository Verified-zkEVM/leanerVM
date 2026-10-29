module

public import LeanVM.Guest.Memory.GuestCntWK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kukstaticRange_306 : kukStaticRange 306 7 := by
  unfold kukStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kukstaticRange_313 : kukStaticRange 313 30 := by
  unfold kukStaticRange; decide +kernel

end
end LeanVM.Guest
