module

public import LeanVM.Guest.Memory.GuestWords.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem wsplit_19_533 : blockR (wlookJ 19) (womLookJ 19) true [] Data.core19.params Data.core19.name (Data.core19.body.drop 533)
    ([], []) = some (⟨0, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem wsplit_20_0 : noTopRet ((Data.core20.body.drop 0).take 246) = true ∧
    blockR (wlookJ 20) (womLookJ 20) true [] Data.core20.params Data.core20.name ((Data.core20.body.drop 0).take 246)
      ([], []) = some (⟨0, []⟩, []) ∧
    blockEnv true [] Data.core20.params ([], []) ((Data.core20.body.drop 0).take 246) = ([], []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem wsplit_20_246 : noTopRet ((Data.core20.body.drop 246).take 63) = true ∧
    blockR (wlookJ 20) (womLookJ 20) true [] Data.core20.params Data.core20.name ((Data.core20.body.drop 246).take 63)
      ([], []) = some (⟨0, []⟩, []) ∧
    blockEnv true [] Data.core20.params ([], []) ((Data.core20.body.drop 246).take 63) = ([], []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem wsplit_20_309 : noTopRet ((Data.core20.body.drop 309).take 48) = true ∧
    blockR (wlookJ 20) (womLookJ 20) true [] Data.core20.params Data.core20.name ((Data.core20.body.drop 309).take 48)
      ([], []) = some (⟨0, []⟩, []) ∧
    blockEnv true [] Data.core20.params ([], []) ((Data.core20.body.drop 309).take 48) = ([], []) := by
  decide +kernel

end
end LeanVM.Guest
