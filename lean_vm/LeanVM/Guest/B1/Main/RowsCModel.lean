/-
  LeanVM.Guest.B1.Main.RowsCModel

  The inline rows and the batching sumchecks over a completeness model, from B1's hash sites.
-/

module

public import LeanVM.Guest.B1.Main.RowsC
public import LeanVM.Guest.B1.Comp.FsBlocks
public import LeanVM.Guest.B1.Comp.Sumcheck

/-!
# The inline rows over a completeness model

`FsRowsC CM.sem CM.H` and `BsRowsC CM.sem CM.H` for every completeness model `CM`: the fields are
B1's merged hash sites (`holdsB_fsNextT_comp`, `holdsB_fsCompressT_comp`, `holdsB_squeezeT_comp`,
`CompModel.check_one`, `batch_sumcheck_L22_comp`, `batch_sumcheck_L28_comp`), `MeaningBsC CM.H`
being `MeaningBatchSumcheckComp CM` (`meaningBsC_model`).
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1

@[expose] public section

theorem meaningBsC_model (CM : E2E.Complete.CompModel) (n : ℕ) (rd : Reader) (args rets : List E) :
    MeaningBsC CM.H n rd args rets ↔ MeaningBatchSumcheckComp CM n rd args rets := by
  match args with
  | [s0, s1, msgs, running, point] => exact Iff.rfl
  | [] | [_] | [_, _] | [_, _, _] | [_, _, _, _] | _ :: _ :: _ :: _ :: _ :: _ :: _ => exact Iff.rfl

/-- **The inline rows over a completeness model** (B1's hash sites). -/
theorem fsRowsC_model (CM : E2E.Complete.CompModel) : FsRowsC CM.sem CM.H where
  fsNext s0 s1 cur j b := fun h => holdsB_fsNextT_comp s0 s1 cur j b h
  fsCompress s0 s1 x b _ htag := fun h => holdsB_fsCompressT_comp s0 s1 x b htag h
  squeeze s0 s1 b := fun h => holdsB_squeezeT_comp s0 s1 b h
  oneBlock hm hd := CM.check_one hm hd

/-- **The batching sumchecks over a completeness model** (B1's hash sites). -/
theorem bsRowsC_model (CM : E2E.Complete.CompModel) : BsRowsC CM.sem CM.H where
  bs22 rd args rets h := batch_sumcheck_L22_comp rd args rets ((meaningBsC_model CM 22 rd args rets).mp h)
  bs28 rd args rets h := batch_sumcheck_L28_comp rd args rets ((meaningBsC_model CM 28 rd args rets).mp h)

end
end LeanVM.Guest.B1.Main
