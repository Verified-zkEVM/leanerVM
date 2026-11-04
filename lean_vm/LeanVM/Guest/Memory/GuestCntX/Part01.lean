module

public import LeanVM.Guest.Memory.GuestCntX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwxsplit_19_558 : blockR (kwxlookJ 19) (kwxomLookJ 19) false [] Data.core19.params Data.core19.name (Data.core19.body.drop 558)
    ([], []) = some (⟨0, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kwxsplit_20_0 : noTopRet ((Data.core20.body.drop 0).take 94) = true ∧
    blockR (kwxlookJ 20) (kwxomLookJ 20) false [] Data.core20.params Data.core20.name ((Data.core20.body.drop 0).take 94)
      ([], []) = some (⟨0, []⟩, []) ∧
    blockEnv false [] Data.core20.params ([], []) ((Data.core20.body.drop 0).take 94) = ([], []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kwxsplit_20_94 : blockR (kwxlookJ 20) (kwxomLookJ 20) false [] Data.core20.params Data.core20.name (Data.core20.body.drop 94)
    ([], []) = some (⟨0, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kwxstaticRange_21 : kwxStaticRange 21 30 := by
  unfold kwxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwxstaticRange_51 : kwxStaticRange 51 30 := by
  unfold kwxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwxstaticRange_81 : kwxStaticRange 81 30 := by
  unfold kwxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwxstaticRange_111 : kwxStaticRange 111 30 := by
  unfold kwxStaticRange; decide +kernel

end
end LeanVM.Guest
