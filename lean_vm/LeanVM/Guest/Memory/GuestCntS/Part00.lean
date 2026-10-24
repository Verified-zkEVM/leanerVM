module

public import LeanVM.Guest.Memory.GuestCntS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwsstaticRange_0 : kwsStaticRange 0 10 := by
  unfold kwsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwsstaticRange_10 : kwsStaticRange 10 8 := by
  unfold kwsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwsstaticRange_18 : kwsStaticRange 18 1 := by
  unfold kwsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwssplit_19_0 : noTopRet ((Data.core19.body.drop 0).take 533) = true ∧
    blockR (kwslookJ 19) (kwsomLookJ 19) false [] Data.core19.params Data.core19.name ((Data.core19.body.drop 0).take 533)
      ([], []) = some (⟨0, []⟩, []) ∧
    blockEnv false [] Data.core19.params ([], []) ((Data.core19.body.drop 0).take 533) = ([], []) := by
  decide +kernel

end
end LeanVM.Guest
