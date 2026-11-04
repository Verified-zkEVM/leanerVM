module

public import LeanVM.Guest.Memory.GuestCntM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwmsplit_19_533 : blockR (kwmlookJ 19) (kwmomLookJ 19) false [] Data.core19.params Data.core19.name (Data.core19.body.drop 533)
    ([], []) = some (⟨0, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kwmsplit_20_0 : noTopRet ((Data.core20.body.drop 0).take 61) = true ∧
    blockR (kwmlookJ 20) (kwmomLookJ 20) false [] Data.core20.params Data.core20.name ((Data.core20.body.drop 0).take 61)
      ([], []) = some (⟨0, []⟩, []) ∧
    blockEnv false [] Data.core20.params ([], []) ((Data.core20.body.drop 0).take 61) = ([], []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kwmsplit_20_61 : blockR (kwmlookJ 20) (kwmomLookJ 20) false [] Data.core20.params Data.core20.name (Data.core20.body.drop 61)
    ([], []) = some (⟨0, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kwmstaticRange_21 : kwmStaticRange 21 30 := by
  unfold kwmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwmstaticRange_51 : kwmStaticRange 51 30 := by
  unfold kwmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwmstaticRange_81 : kwmStaticRange 81 30 := by
  unfold kwmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwmstaticRange_111 : kwmStaticRange 111 30 := by
  unfold kwmStaticRange; decide +kernel

end
end LeanVM.Guest
