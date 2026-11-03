module

public import LeanVM.Guest.Memory.GuestCntWS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kusstaticRange_74 : kusStaticRange 74 29 := by
  unfold kusStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kusstaticRange_103 : kusStaticRange 103 26 := by
  unfold kusStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kusstaticRange_129 : kusStaticRange 129 27 := by
  unfold kusStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kusstaticRange_156 : kusStaticRange 156 23 := by
  unfold kusStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kusstaticRange_179 : kusStaticRange 179 26 := by
  unfold kusStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kusstaticRange_205 : kusStaticRange 205 26 := by
  unfold kusStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kusstaticRange_231 : kusStaticRange 231 30 := by
  unfold kusStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kusstaticRange_261 : kusStaticRange 261 26 := by
  unfold kusStaticRange; decide +kernel

end
end LeanVM.Guest
