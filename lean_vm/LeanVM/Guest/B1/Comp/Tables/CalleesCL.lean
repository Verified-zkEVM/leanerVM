/-
  LeanVM.Guest.B1.Comp.Tables.CalleesCL

  `verify_bus_gkr`, `verify_tables` and `verify_flock` placed over a completeness model at the
  deployed frame sizes, certificates and bounds, their trees loading the stream words they read.
-/

module

public import LeanVM.Guest.B1.Comp.Tables.CalleesC
public import LeanVM.Guest.B1.Comp.Tables.FlockAtL
public import LeanVM.Guest.B1.Comp.Tables.GkrAtL
public import LeanVM.Guest.B1.Comp.Tables.VtAtL

/-!
# The tables' placed forms with their loads, at the deployed sizes

`verify_bus_gkr_completeAtWCL`, `verify_tables_completeAtWCL` and `verify_flock_completeAtWCL` at
`B2C.fs`, `B2C.cert`, `κ = 16` and the deployed bytecode, every frame weight `w`, within the
deployed bounds (`gkrCL_b2c`, `tablesCL_b2c`, `flockCL_b2c`): `gkrC_b2c`, `tablesC_b2c`,
`flockC_b2c` with each tree loading the stream words its callee reads (`LoadsWords`).
-/

namespace LeanVM.Guest.B2C

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.E2E.Complete

@[expose] public section

/-- **`verify_bus_gkr`, placed over a completeness model, loading what it reads, at the deployed
sizes.** -/
theorem gkrCL_b2c (CM : CompModel) {Θ : Type} (w : Θ → String → ℕ) :
    VerifySub.CompleteGkrAtWCL CM fs cert 16 w (VerifySub.vtcGkrBound fs)
      fun θ => VerifySub.vtcGkrBoundW (w θ) :=
  VerifySub.verify_bus_gkr_completeAtWCL CM fs cert w (by norm_num)

/-- **`verify_tables`, placed over a completeness model, loading what it reads, at the deployed
sizes.** -/
theorem tablesCL_b2c (CM : CompModel) {Θ : Type} (w : Θ → String → ℕ) :
    VerifySub.CompleteTablesAtWCL CM fs cert 16 End.bytecode VerifySub.TCtx w calleesHyps_b2c.Btab
      fun θ => VerifySub.vtTablesBoundW (w θ) :=
  VerifySub.verify_tables_completeAtWCL CM fs cert w (by norm_num) End.bytecode

/-- **`verify_flock`, placed over a completeness model, loading what it reads, at the deployed
sizes.** -/
theorem flockCL_b2c (CM : CompModel) {Θ : Type} (w : Θ → String → ℕ) :
    VerifySub.CompleteFlockAtWCL CM fs cert 16 w (flockBound fs) fun θ => flockBoundW (w θ) :=
  verify_flock_completeAtWCL CM fs cert w 16

end
end LeanVM.Guest.B2C
