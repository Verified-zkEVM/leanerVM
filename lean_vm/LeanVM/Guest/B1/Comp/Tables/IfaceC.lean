/-
  LeanVM.Guest.B1.Comp.Tables.IfaceC

  The tables' placed forms over a completeness model (`Comp/VerifySub/PlacedIface.lean`) at
  `CompModel.deployed`: the deployed placed forms.
-/

module

public import LeanVM.Guest.B1.Comp.VerifySub.PlacedIface
public import LeanVM.Guest.B1.Comp.Tables.ShapesWS

/-!
# The tables' placed forms over the deployed model

`CompleteGkrAtWC`, `CompleteTablesAtWC`, `CompleteFlockAtWC` (`Comp/VerifySub/PlacedIface.lean`)
at `CompModel.deployed` give the deployed `CompleteGkrAtW`, `CompleteTablesAtW`,
`CompleteFlockAtW` (`….toDeployed`), the converse of `PlacedIface.lean`'s `….toC`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.E2E.Complete

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ} {k : ℕ} {bytecode : List K}
  {TCtx : Reader → Layout → BusResult → List ColumnClaim → List E → Prop} {Θ : Type}
  {wt : Θ → String → ℕ} {B : ℕ} {Bw : Θ → ℕ}

/-- **`CompleteGkrAtWC` at the deployed model is the deployed `CompleteGkrAtW`.** -/
theorem CompleteGkrAtWC.toDeployed (h : CompleteGkrAtWC CompModel.deployed fs cert k wt B Bw) :
    CompleteGkrAtW fs cert k wt B Bw := by
  intro cv depth xs r cv' c z Lin hd hr h1 h2 hm
  exact completeAtWS_deployed.mp (h cv depth xs r cv' c z Lin hd (runsToM_hm_deployed.mpr hr) h1 h2 hm)

/-- **`CompleteTablesAtWC` at the deployed model is the deployed `CompleteTablesAtW`.** -/
theorem CompleteTablesAtWC.toDeployed
    (h : CompleteTablesAtWC CompModel.deployed fs cert k bytecode TCtx wt B Bw) :
    CompleteTablesAtW fs cert k bytecode TCtx wt B Bw := by
  intro pi logMem alphas point values cv xs cv' rowsN bus claims beta bv rm gzcn c z lp sq dims rows
    bk fpw pool cplen chi Lin h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 hrun hm
  exact completeAtWS_deployed.mp (h pi logMem alphas point values cv xs cv' rowsN bus claims beta bv
    rm gzcn c z lp sq dims rows bk fpw pool cplen chi Lin h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
    (fun ev hev => runsToM_hm_deployed.mpr (hrun ev (bytecodeAtM_deployed.mp hev))) hm)

/-- **`CompleteFlockAtWC` at the deployed model is the deployed `CompleteFlockAtW`.** -/
theorem CompleteFlockAtWC.toDeployed (h : CompleteFlockAtWC CompModel.deployed fs cert k wt B Bw) :
    CompleteFlockAtW fs cert k wt B Bw := by
  intro τ cv xs cv' zSkip alpha mv chi rcs s c zc lr zp Lin h1 h2 h3 h4 hrun hm
  exact completeAtWS_deployed.mp (h τ cv xs cv' zSkip alpha mv chi rcs s c zc lr zp Lin h1 h2 h3 h4
    (fun ev hev => runsToM_hm_deployed.mpr (hrun ev (matricesAtM_deployed.mp hev))) hm)

end
end LeanVM.Guest.B1.VerifySub
