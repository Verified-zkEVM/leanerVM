/-
  LeanVM.Guest.B2C.CplAllB

  B2's completeness for every compiled function (`CplAll.lean`) under any semantics of `BLAKE2S`.
-/

module

public import LeanVM.Guest.B2C.CplAll
public import LeanVM.Guest.B2C.CplCompB

/-!
# Every function's run under any `BLAKE2S` semantics

`CplAll.lean`'s `cplRun_of` over `S : BlakeSem` (`cplRunB_of`): the completeness check of
function `j` gives `CplRunB S j`, and `CplRunKB S j`, its callees entered on its run
(`cplRunKB_of`). `sitesApart_all_of` does not mention the semantics and is
`CplAll.lean`'s.
-/

namespace LeanVM.Guest.B2C

open LeanVM.Guest LeanVM.Guest.Memory
open LeanVM.Semantics (BlakeSem blakeDeployed)

@[expose] public section

variable {S : BlakeSem}

/-- **B2's completeness for function `j` with its callees' entries on the run**, given its
completeness check. -/
theorem cplRunKB_of {j : ℕ} (h1 : 1 ≤ j) (hj : j < nFns) (hok : CplOk j) : CplRunKB S j :=
  cplKB_run h1 hj hok (End.winOk_of h1 hj) (End.certOf_pows_ok j)

/-- **B2's completeness for function `j`**, given its completeness check. -/
theorem cplRunB_of {j : ℕ} (h1 : 1 ≤ j) (hj : j < nFns) (hok : CplOk j) : CplRunB S j :=
  CplRunKB.cplRunB (cplRunKB_of h1 hj hok)

end
end LeanVM.Guest.B2C
