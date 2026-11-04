module

public import LeanVM.Guest.Memory.GuestCntJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwjsplit_19_533 : blockR (kwjlookJ 19) (kwjomLookJ 19) false [] Data.core19.params Data.core19.name (Data.core19.body.drop 533)
    ([], []) = some (⟨0, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kwjsplit_20_0 : noTopRet ((Data.core20.body.drop 0).take 61) = true ∧
    blockR (kwjlookJ 20) (kwjomLookJ 20) false [] Data.core20.params Data.core20.name ((Data.core20.body.drop 0).take 61)
      ([], []) = some (⟨0, []⟩, []) ∧
    blockEnv false [] Data.core20.params ([], []) ((Data.core20.body.drop 0).take 61) = ([], []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kwjsplit_20_61 : blockR (kwjlookJ 20) (kwjomLookJ 20) false [] Data.core20.params Data.core20.name (Data.core20.body.drop 61)
    ([], []) = some (⟨0, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kwjstaticRange_21 : kwjStaticRange 21 30 := by
  unfold kwjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwjstaticRange_51 : kwjStaticRange 51 30 := by
  unfold kwjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwjstaticRange_81 : kwjStaticRange 81 30 := by
  unfold kwjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwjstaticRange_111 : kwjStaticRange 111 30 := by
  unfold kwjStaticRange; decide +kernel

end
end LeanVM.Guest
