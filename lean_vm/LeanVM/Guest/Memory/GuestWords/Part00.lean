module

public import LeanVM.Guest.Memory.GuestWords.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem wstaticRange_0 : wStaticRange 0 10 := by
  unfold wStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wstaticRange_10 : wStaticRange 10 7 := by
  unfold wStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wstaticRange_17 : wStaticRange 17 2 := by
  unfold wStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wsplit_19_0 : noTopRet ((Data.core19.body.drop 0).take 533) = true ∧
    blockR (wlookJ 19) (womLookJ 19) true [] Data.core19.params Data.core19.name ((Data.core19.body.drop 0).take 533)
      ([], []) = some (⟨0, []⟩, []) ∧
    blockEnv true [] Data.core19.params ([], []) ((Data.core19.body.drop 0).take 533) = ([], []) := by
  decide +kernel

end
end LeanVM.Guest
