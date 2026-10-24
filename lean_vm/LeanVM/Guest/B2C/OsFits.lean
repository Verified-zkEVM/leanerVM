/-
  LeanVM.Guest.B2C.OsFits

  The deployed certificates fit `open_stacked`'s `opening_queries` frames at every candidate
  (`OsFitsAt`).
-/

module

public import LeanVM.Guest.B2C.RunsFit
public import LeanVM.Guest.Lift.OqFitsAll

namespace LeanVM.Guest.B2C

open LeanVM.Guest.B1 LeanVM.Guest.B1.Whir

@[expose] public section

/-- **The deployed certificates fit every `open_stacked` candidate's `opening_queries` frames.** -/
theorem osFitsAt_deployed (μ r : ℕ) (h1 : 22 ≤ μ) (h2 : μ ≤ 28) (h3 : 1 ≤ r) (h4 : r ≤ 4) :
    OsFitsAt fs cert (osCfg (candidate μ r)) :=
  osFitsAt_all fs cert runsFit runsApart μ r h1 h2 h3 h4

end
end LeanVM.Guest.B2C
