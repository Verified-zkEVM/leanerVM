module

public import LeanVM.Guest.Memory.GuestCntX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwxstaticRange_0 : kwxStaticRange 0 10 := by
  unfold kwxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwxstaticRange_10 : kwxStaticRange 10 8 := by
  unfold kwxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwxstaticRange_18 : kwxStaticRange 18 1 := by
  unfold kwxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwxsplit_19_0 : noTopRet ((Data.core19.body.drop 0).take 533) = true ∧
    blockR (kwxlookJ 19) (kwxomLookJ 19) false [] Data.core19.params Data.core19.name ((Data.core19.body.drop 0).take 533)
      ([], []) = some (⟨0, []⟩, []) ∧
    blockEnv false [] Data.core19.params ([], []) ((Data.core19.body.drop 0).take 533) = ([], []) := by
  decide +kernel

end
end LeanVM.Guest
