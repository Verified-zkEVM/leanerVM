module

public import LeanVM.Guest.Memory.GuestCntS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwsstaticRange_345 : kwsStaticRange 345 30 := by
  unfold kwsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwsstaticRange_375 : kwsStaticRange 375 30 := by
  unfold kwsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwsstaticRange_405 : kwsStaticRange 405 30 := by
  unfold kwsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwsstaticRange_435 : kwsStaticRange 435 30 := by
  unfold kwsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwsstaticRange_465 : kwsStaticRange 465 30 := by
  unfold kwsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwsstaticRange_495 : kwsStaticRange 495 30 := by
  unfold kwsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwsstaticRange_525 : kwsStaticRange 525 30 := by
  unfold kwsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwsstaticRange_555 : kwsStaticRange 555 30 := by
  unfold kwsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwsstaticRange_585 : kwsStaticRange 585 30 := by
  unfold kwsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwsstaticRange_615 : kwsStaticRange 615 30 := by
  unfold kwsStaticRange; decide +kernel

end
end LeanVM.Guest
