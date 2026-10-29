/-
  LeanVM.Guest.B1.Da.VerifyL23CChk

  `__loop22`, evaluated (by kernel evaluation), for its completeness.
-/

module

public import LeanVM.Guest.B1.Da.VerifyL23Chk
public import LeanVM.Guest.B1.Fwd.Canon

namespace LeanVM.Guest.B1.Da

open LeanVM.Guest.Core LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Digest

@[expose] public section

/-- A load of a row's cell `i < 128` through its run. -/
def isRowCellLoad : Atom → Bool
  | .load d p i => decide (p = .n 5) && decide (d = .n (6 + i)) && decide (i < 128)
  | _ => false

/-- **`__loop22`, evaluated.** -/
noncomputable def l23COk (fn : Fn) : Bool :=
  let A := atomsIn (loopPre fn)
  let S := storesOf 4 fn.body
  (chk 4 fn.body).isSome && (loopPre fn).all (fun s => match s with | .atom _ => true | _ => false) &&
  decide (S = [.load (.n 464) (.n 478) 0, .load (.n 465) (.n 478) 1]) &&
  canonChk ((List.range 128).map (6 + ·)) (A.filter fun a => decide (a ∉ S)) &&
  A.all (fun a => !needsSide a || decide (a ∈ S) || decide (a = .load (.n 5) (.n 4) 0) ||
    isRowCellLoad a) &&
  decide (Atom.mul (.n 4) (.n 2) (.n 0) ∈ A) && decide (Atom.load (.n 5) (.n 4) 0 ∈ A) &&
  (List.range 128).all (fun i => decide (Atom.load (.n (6 + i)) (.n 5) i ∈ A)) &&
  decide (Atom.mul (.n 477) (.n 0) (.n 0) ∈ A) && decide (Atom.mul (.n 478) (.n 3) (.n 477) ∈ A) &&
  decide ((rowSpec A).outV ((rowSpec A).nb - 1) 0 = .n 464) &&
  decide ((rowSpec A).outV ((rowSpec A).nb - 1) 1 = .n 465)

set_option maxRecDepth 100000 in
theorem l23c_ok : l23COk (coreProgram.getD 362 default) = true := by decide +kernel

end
end LeanVM.Guest.B1.Da
