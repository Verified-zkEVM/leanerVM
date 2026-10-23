/-
  LeanVM.Guest.B1.Da.VectorCChk

  `da_vector_cell`, evaluated (by kernel evaluation): its values defined in order, its stores the
  digest's two cells, the template's side conditions its assertions, the chain's inputs canonical
  from the pairs' cells.
-/

module

public import LeanVM.Guest.B1.Da.Vector
public import LeanVM.Guest.B1.Fwd.Canon

namespace LeanVM.Guest.B1.Da

open LeanVM.Guest.Core LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Digest

@[expose] public section

/-- The weights' hint. -/
def wHint : Atom := .hint (.witness "da_weights" (.stack wRun))

/-- The pairs' cells, known canonical. -/
def vecA : List ℕ :=
  (List.range 128).flatMap fun p => [255 + 25 * p + 8, 255 + 25 * p + 17, 255 + 25 * p + 26]

/-- **`da_vector_cell`, evaluated.** -/
def vecCOk (fn : Fn) : Bool :=
  (chk 1 fn.body).isSome &&
  decide (storesOf 1 fn.body = [.load (.n 4448) (.n 0) 0, .load (.n 4449) (.n 0) 1]) &&
  canonChk [] tmplV && tmplV.all (fun a => !needsSide a || match a with
    | .assertInK .. => true
    | _ => false) &&
  match splitBody fn.body with
  | some (A, _) =>
    canonChk vecA ((A.drop 3329).filter fun a => decide (a ∉ storesOf 1 fn.body)) &&
      (A.drop 3329).all (fun a => !needsSide a || decide (a ∈ storesOf 1 fn.body) ||
        decide (a = .frameAddr (.n 4461) wRun)) && decide (A.take 1 = [wHint])
  | none => false

set_option maxRecDepth 100000 in
theorem vecc_ok : vecCOk Data.core28 = true := by decide +kernel

end
end LeanVM.Guest.B1.Da
