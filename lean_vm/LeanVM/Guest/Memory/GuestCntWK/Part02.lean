module

public import LeanVM.Guest.Memory.GuestCntWK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kukstaticRange_286 : kukStaticRange 286 13 := by
  unfold kukStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kukstaticRange_299 : kukStaticRange 299 7 := by
  unfold kukStaticRange; decide +kernel

end
end LeanVM.Guest
