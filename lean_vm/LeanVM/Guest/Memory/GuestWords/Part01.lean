module

public import LeanVM.Guest.Memory.GuestWords.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem wsplit_19_558 : blockR (wlookJ 19) (womLookJ 19) true [] Data.core19.params Data.core19.name (Data.core19.body.drop 558)
    ([], []) = some (⟨0, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem wsplit_20_0 : noTopRet ((Data.core20.body.drop 0).take 94) = true ∧
    blockR (wlookJ 20) (womLookJ 20) true [] Data.core20.params Data.core20.name ((Data.core20.body.drop 0).take 94)
      ([], []) = some (⟨0, []⟩, []) ∧
    blockEnv true [] Data.core20.params ([], []) ((Data.core20.body.drop 0).take 94) = ([], []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem wsplit_20_94 : blockR (wlookJ 20) (womLookJ 20) true [] Data.core20.params Data.core20.name (Data.core20.body.drop 94)
    ([], []) = some (⟨0, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem wstaticRange_21 : wStaticRange 21 23 := by
  unfold wStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wstaticRange_44 : wStaticRange 44 27 := by
  unfold wStaticRange; decide +kernel

end
end LeanVM.Guest
