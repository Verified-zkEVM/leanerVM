/-
  LeanVM.Guest.B1.Comp.Tables.CalleesC

  `verify_bus_gkr`, `verify_tables` and `verify_flock` placed over a completeness model at the
  deployed frame sizes, certificates and bounds, in the shapes `main`'s callees over a model take.
-/

module

public import LeanVM.Guest.B2C.CalleesHyps
public import LeanVM.Guest.B1.Comp.Tables.FlockAtC
public import LeanVM.Guest.B1.Comp.Tables.GkrAtC
public import LeanVM.Guest.B1.Comp.Tables.VtPlacedC

/-!
# The tables' placed forms over a model at the deployed sizes

`verify_bus_gkr_completeAtWC`, `verify_tables_completeAtWC` and `verify_flock_completeAtWC` at
`B2C.fs`, `B2C.cert`, `κ = 16` and the deployed bytecode, every frame weight `w`, within the
deployed bounds (`vtcGkrBound`, `calleesHyps_b2c.Btab`, `flockBound`): the `gkr`, `tables` and
`flock` fields of `main`'s callees over a completeness model (`gkrC_b2c`, `tablesC_b2c`,
`flockC_b2c`).
-/

namespace LeanVM.Guest.B2C

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.E2E.Complete

@[expose] public section

/-- **`verify_bus_gkr`, placed over a completeness model, at the deployed sizes.** -/
theorem gkrC_b2c (CM : CompModel) {Θ : Type} (w : Θ → String → ℕ) :
    VerifySub.CompleteGkrAtWC CM fs cert 16 w (VerifySub.vtcGkrBound fs)
      fun θ => VerifySub.vtcGkrBoundW (w θ) :=
  VerifySub.verify_bus_gkr_completeAtWC CM fs cert w (by norm_num)

/-- **`verify_tables`, placed over a completeness model, at the deployed sizes.** -/
theorem tablesC_b2c (CM : CompModel) {Θ : Type} (w : Θ → String → ℕ) :
    VerifySub.CompleteTablesAtWC CM fs cert 16 End.bytecode VerifySub.TCtx w calleesHyps_b2c.Btab
      fun θ => VerifySub.vtTablesBoundW (w θ) :=
  VerifySub.verify_tables_completeAtWC CM fs cert w (by norm_num) End.bytecode

/-- **`verify_flock`, placed over a completeness model, at the deployed sizes.** -/
theorem flockC_b2c (CM : CompModel) {Θ : Type} (w : Θ → String → ℕ) :
    VerifySub.CompleteFlockAtWC CM fs cert 16 w (flockBound fs) fun θ => flockBoundW (w θ) :=
  verify_flock_completeAtWC CM fs cert w 16

end
end LeanVM.Guest.B2C
