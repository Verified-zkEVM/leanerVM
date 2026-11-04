module

public import LeanVM.Guest.Memory.GuestCntWJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kujstaticRange_74 : kujStaticRange 74 29 := by
  unfold kujStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kujstaticRange_103 : kujStaticRange 103 26 := by
  unfold kujStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kujstaticRange_129 : kujStaticRange 129 27 := by
  unfold kujStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kujstaticRange_156 : kujStaticRange 156 23 := by
  unfold kujStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kujstaticRange_179 : kujStaticRange 179 26 := by
  unfold kujStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kujstaticRange_205 : kujStaticRange 205 26 := by
  unfold kujStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kujstaticRange_231 : kujStaticRange 231 30 := by
  unfold kujStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kujstaticRange_261 : kujStaticRange 261 26 := by
  unfold kujStaticRange; decide +kernel

end
end LeanVM.Guest
