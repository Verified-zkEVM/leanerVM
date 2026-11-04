module

public import LeanVM.Guest.Memory.GuestCntWK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kukstaticRange_287 : kukStaticRange 287 14 := by
  unfold kukStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kukstaticRange_301 : kukStaticRange 301 7 := by
  unfold kukStaticRange; decide +kernel

end
end LeanVM.Guest
