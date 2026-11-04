module

public import LeanVM.Guest.Memory.GuestCntWK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kukstaticRange_288 : kukStaticRange 288 14 := by
  unfold kukStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kukstaticRange_302 : kukStaticRange 302 7 := by
  unfold kukStaticRange; decide +kernel

end
end LeanVM.Guest
