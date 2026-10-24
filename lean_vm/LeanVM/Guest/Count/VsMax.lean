/-
  LeanVM.Guest.Count.VsMax

  `verify_bus_gkr`'s and `verify_tables`' largest bounds over their depths and heights, by the
  kernel, through the search tree's lookups (`Count.Fast`).
-/

module

public import LeanVM.Guest.Count.VsWords
public import LeanVM.Guest.Count.Fast

namespace LeanVM.Guest.Count

@[expose] public section

set_option maxRecDepth 100000 in
theorem vbgMax_eq : B1.VerifySub.vbgMax B2C.fs vsWords.K29 vsWords.R vsWords.K8 = 49403 := by
  dsimp only [vsWords]
  rw [← fsFast_eq, ← wSBFast_eq, ← wSKFast_eq]
  decide +kernel

set_option maxRecDepth 100000 in
theorem vtMax_eq : B1.VerifySub.vtMax B2C.fs vsWords.Kf vsWords.Ksh vsWords.K10 = 59762 := by
  dsimp only [vsWords]
  rw [← fsFast_eq, ← wSBFast_eq, ← wSKFast_eq]
  decide +kernel

end
end LeanVM.Guest.Count
