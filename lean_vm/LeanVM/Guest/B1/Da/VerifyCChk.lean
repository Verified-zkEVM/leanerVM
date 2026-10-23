/-
  LeanVM.Guest.B1.Da.VerifyCChk

  `da_verify`'s body, evaluated (by kernel evaluation), for its completeness.
-/

module

public import LeanVM.Guest.B1.Da.VerifyChk
public import LeanVM.Guest.B1.Da.LevelsTab
public import LeanVM.Guest.B1.Fwd.Canon

namespace LeanVM.Guest.B1.Da

open LeanVM.Guest.Core LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Digest

@[expose] public section

/-- A load of the column digests' cell `i < 256` through `.n 17`. -/
def isCdLoad : Atom → Bool
  | .load d p i => decide (p = .n 17) && decide (d = .n (69 + i)) && decide (i < 256)
  | _ => false

/-- **`da_verify`'s body, evaluated.** -/
noncomputable def dvCOk : Bool :=
  (chk 1 (Fn.body Data.core25)).isSome && (storesOf 1 (Fn.body Data.core25)).isEmpty &&
  canonChk ([37, 38, 48, 49] ++ (List.range 256).map (69 + ·)) (atomsIn dvP) &&
  (atomsIn dvP).all (fun a => !needsSide a || isCdLoad a)

set_option maxRecDepth 100000 in
theorem dvc_ok : dvCOk = true := by decide +kernel

end
end LeanVM.Guest.B1.Da
