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
theorem kwdsplit_20_0 : noTopRet ((Data.core20.body.drop 0).take 246) = true ∧
    blockR (kwdlookJ 20) (kwdomLookJ 20) false [] Data.core20.params Data.core20.name ((Data.core20.body.drop 0).take 246)
      ([], []) = some (⟨0, []⟩, []) ∧
    blockEnv false [] Data.core20.params ([], []) ((Data.core20.body.drop 0).take 246) = ([], []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kwdsplit_20_246 : noTopRet ((Data.core20.body.drop 246).take 63) = true ∧
    blockR (kwdlookJ 20) (kwdomLookJ 20) false [] Data.core20.params Data.core20.name ((Data.core20.body.drop 246).take 63)
      ([], []) = some (⟨0, []⟩, []) ∧
    blockEnv false [] Data.core20.params ([], []) ((Data.core20.body.drop 246).take 63) = ([], []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kwdsplit_20_309 : noTopRet ((Data.core20.body.drop 309).take 48) = true ∧
    blockR (kwdlookJ 20) (kwdomLookJ 20) false [] Data.core20.params Data.core20.name ((Data.core20.body.drop 309).take 48)
      ([], []) = some (⟨0, []⟩, []) ∧
    blockEnv false [] Data.core20.params ([], []) ((Data.core20.body.drop 309).take 48) = ([], []) := by
  decide +kernel

end
end LeanVM.Guest
