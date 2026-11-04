module

public import LeanVM.Guest.Memory.GuestCntD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwdsplit_19_533 : blockR (kwdlookJ 19) (kwdomLookJ 19) false [] Data.core19.params Data.core19.name (Data.core19.body.drop 533)
    ([], []) = some (⟨0, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kwdsplit_20_0 : noTopRet ((Data.core20.body.drop 0).take 61) = true ∧
    blockR (kwdlookJ 20) (kwdomLookJ 20) false [] Data.core20.params Data.core20.name ((Data.core20.body.drop 0).take 61)
      ([], []) = some (⟨0, []⟩, []) ∧
    blockEnv false [] Data.core20.params ([], []) ((Data.core20.body.drop 0).take 61) = ([], []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kwdsplit_20_61 : blockR (kwdlookJ 20) (kwdomLookJ 20) false [] Data.core20.params Data.core20.name (Data.core20.body.drop 61)
    ([], []) = some (⟨0, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kwdstaticRange_21 : kwdStaticRange 21 30 := by
  unfold kwdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwdstaticRange_51 : kwdStaticRange 51 30 := by
  unfold kwdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwdstaticRange_81 : kwdStaticRange 81 30 := by
  unfold kwdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwdstaticRange_111 : kwdStaticRange 111 30 := by
  unfold kwdStaticRange; decide +kernel

end
end LeanVM.Guest
