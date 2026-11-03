module

public import LeanVM.Guest.Memory.GuestCntWM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kumstaticRange_74 : kumStaticRange 74 29 := by
  unfold kumStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kumstaticRange_103 : kumStaticRange 103 26 := by
  unfold kumStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kumstaticRange_129 : kumStaticRange 129 27 := by
  unfold kumStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kumstaticRange_156 : kumStaticRange 156 23 := by
  unfold kumStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kumstaticRange_179 : kumStaticRange 179 26 := by
  unfold kumStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kumstaticRange_205 : kumStaticRange 205 26 := by
  unfold kumStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kumstaticRange_231 : kumStaticRange 231 30 := by
  unfold kumStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kumstaticRange_261 : kumStaticRange 261 26 := by
  unfold kumStaticRange; decide +kernel

end
end LeanVM.Guest
