module

public import LeanVM.Guest.Memory.GuestCntK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwksplit_20_357 : noTopRet ((Data.core20.body.drop 357).take 63) = true ∧
    blockR (kwklookJ 20) (kwkomLookJ 20) false [] Data.core20.params Data.core20.name ((Data.core20.body.drop 357).take 63)
      ([], []) = some (⟨0, []⟩, []) ∧
    blockEnv false [] Data.core20.params ([], []) ((Data.core20.body.drop 357).take 63) = ([], []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kwksplit_20_420 : noTopRet ((Data.core20.body.drop 420).take 48) = true ∧
    blockR (kwklookJ 20) (kwkomLookJ 20) false [] Data.core20.params Data.core20.name ((Data.core20.body.drop 420).take 48)
      ([], []) = some (⟨0, []⟩, []) ∧
    blockEnv false [] Data.core20.params ([], []) ((Data.core20.body.drop 420).take 48) = ([], []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kwksplit_20_468 : noTopRet ((Data.core20.body.drop 468).take 110) = true ∧
    blockR (kwklookJ 20) (kwkomLookJ 20) false [] Data.core20.params Data.core20.name ((Data.core20.body.drop 468).take 110)
      ([], []) = some (⟨0, []⟩, []) ∧
    blockEnv false [] Data.core20.params ([], []) ((Data.core20.body.drop 468).take 110) = ([], []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kwksplit_20_578 : blockR (kwklookJ 20) (kwkomLookJ 20) false [] Data.core20.params Data.core20.name (Data.core20.body.drop 578)
    ([], []) = some (⟨0, []⟩, []) := by
  decide +kernel

end
end LeanVM.Guest
