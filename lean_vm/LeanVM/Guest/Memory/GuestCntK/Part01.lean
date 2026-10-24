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
theorem kwksplit_20_0 : noTopRet ((Data.core20.body.drop 0).take 246) = true ∧
    blockR (kwklookJ 20) (kwkomLookJ 20) false [] Data.core20.params Data.core20.name ((Data.core20.body.drop 0).take 246)
      ([], []) = some (⟨0, []⟩, []) ∧
    blockEnv false [] Data.core20.params ([], []) ((Data.core20.body.drop 0).take 246) = ([], []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kwksplit_20_246 : noTopRet ((Data.core20.body.drop 246).take 63) = true ∧
    blockR (kwklookJ 20) (kwkomLookJ 20) false [] Data.core20.params Data.core20.name ((Data.core20.body.drop 246).take 63)
      ([], []) = some (⟨0, []⟩, []) ∧
    blockEnv false [] Data.core20.params ([], []) ((Data.core20.body.drop 246).take 63) = ([], []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kwksplit_20_309 : noTopRet ((Data.core20.body.drop 309).take 48) = true ∧
    blockR (kwklookJ 20) (kwkomLookJ 20) false [] Data.core20.params Data.core20.name ((Data.core20.body.drop 309).take 48)
      ([], []) = some (⟨0, []⟩, []) ∧
    blockEnv false [] Data.core20.params ([], []) ((Data.core20.body.drop 309).take 48) = ([], []) := by
  decide +kernel

end
end LeanVM.Guest
