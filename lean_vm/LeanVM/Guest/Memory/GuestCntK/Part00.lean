module

public import LeanVM.Guest.Memory.GuestCntK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwkstaticRange_0 : kwkStaticRange 0 10 := by
  unfold kwkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwkstaticRange_10 : kwkStaticRange 10 8 := by
  unfold kwkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwkstaticRange_18 : kwkStaticRange 18 1 := by
  unfold kwkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwksplit_19_0 : noTopRet ((Data.core19.body.drop 0).take 533) = true ∧
    blockR (kwklookJ 19) (kwkomLookJ 19) false [] Data.core19.params Data.core19.name ((Data.core19.body.drop 0).take 533)
      ([], []) = some (⟨0, []⟩, []) ∧
    blockEnv false [] Data.core19.params ([], []) ((Data.core19.body.drop 0).take 533) = ([], []) := by
  decide +kernel

end
end LeanVM.Guest
