module

public import LeanVM.Guest.Memory.GuestCntK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwksplit_19_533 : blockR (kwklookJ 19) (kwkomLookJ 19) false [] Data.core19.params Data.core19.name (Data.core19.body.drop 533)
    ([], []) = some (⟨0, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kwksplit_20_0 : noTopRet ((Data.core20.body.drop 0).take 61) = true ∧
    blockR (kwklookJ 20) (kwkomLookJ 20) false [] Data.core20.params Data.core20.name ((Data.core20.body.drop 0).take 61)
      ([], []) = some (⟨0, []⟩, []) ∧
    blockEnv false [] Data.core20.params ([], []) ((Data.core20.body.drop 0).take 61) = ([], []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kwksplit_20_61 : blockR (kwklookJ 20) (kwkomLookJ 20) false [] Data.core20.params Data.core20.name (Data.core20.body.drop 61)
    ([], []) = some (⟨0, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kwkstaticRange_21 : kwkStaticRange 21 30 := by
  unfold kwkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwkstaticRange_51 : kwkStaticRange 51 30 := by
  unfold kwkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwkstaticRange_81 : kwkStaticRange 81 30 := by
  unfold kwkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwkstaticRange_111 : kwkStaticRange 111 30 := by
  unfold kwkStaticRange; decide +kernel

end
end LeanVM.Guest
