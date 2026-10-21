import LeanVM.Guest.B1.Comp.Da.CalleeC
import LeanVM.Guest.B2C.CalleesHyps

/-!
# Tests: `da_verify` placed over a completeness model, its axioms

`da_verify` complete in the uniform placed form within weights over a `CompModel`
(`CompleteAtWS CM.sem`), its hashing callees placed under any semantics (the trees' level loops,
the row loops, `__loop93`, the vector cells, the columns and the column loops), the layout of its
words over the model, and the deployed placed lemmas recovered at `CompModel.deployed`, rest on
Lean's three standard axioms only. At the deployed frame sizes, certificates and callee bounds,
`da_verify_calleeC` is the `da_verify` field `main`'s completeness over a model takes.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.E2E.Complete
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest.B1 (Returns LowDef)

/-- `da_verify_calleeC` at the deployed hypotheses has the shape of `CalleesOpenC`'s `da_verify`
field. -/
example (CM : CompModel) :
    ∀ (wt : Da.Witness) (root vd : Digest), wt.OpensWith CM.H daPadCell daPadRow root vd →
    ∀ (args rets : List E) (Lin : Layout),
    (∀ rd, LowDef 16 rd → MemL rd Lin → DaVerifyPreAt root vd rd args rets) →
    CompleteAtWS CM.sem LeanVM.Guest.B2C.fs LeanVM.Guest.B2C.cert (fun θ : String → ℕ => θ) 16
      "da_verify" Lin args (Returns rets)
      ((calleeBd LeanVM.Guest.B2C.fs LeanVM.Guest.B2C.calleesHyps_b2c).daVerify wt.rows.length)
      fun θ => (calleeBd LeanVM.Guest.B2C.fs LeanVM.Guest.B2C.calleesHyps_b2c).daVerifyW θ
        wt.rows.length :=
  da_verify_calleeC LeanVM.Guest.B2C.calleesHyps_b2c CM

end LeanVM.Guest.B1.Main

/-- info: 'LeanVM.Guest.B1.Digest.relInTWS_of_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.relInTWS_of_inv

/-- info: 'LeanVM.Guest.B1.Digest.relAtInWS_of_relInTWS_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.relAtInWS_of_relInTWS_pure

/-- info: 'LeanVM.Guest.B1.Digest.loop_relInTWS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.loop_relInTWS

/-- info: 'LeanVM.Guest.B1.Digest.relAtInWS_of_freeOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.relAtInWS_of_freeOn

/-- info: 'LeanVM.Guest.B1.Digest.levels_relInTS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.levels_relInTS

/-- info: 'LeanVM.Guest.B1.Digest.da_verify_cell_relInTS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.da_verify_cell_relInTS

/-- info: 'LeanVM.Guest.B1.Digest.rowLoop_relInTS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.rowLoop_relInTS

/-- info: 'LeanVM.Guest.B1.Digest.l93_relInTS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.l93_relInTS

/-- info: 'LeanVM.Guest.B1.Digest.vx_relAtInS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.vx_relAtInS

/-- info: 'LeanVM.Guest.B1.Digest.vd_relAtInS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.vd_relAtInS

/-- info: 'LeanVM.Guest.B1.Digest.col_holdsC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.col_holdsC

/-- info: 'LeanVM.Guest.B1.Digest.col_relAtInC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.col_relAtInC

/-- info: 'LeanVM.Guest.B1.Digest.colLoop_iterS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.colLoop_iterS

/-- info: 'LeanVM.Guest.B1.Digest.colLoop_relAtInC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.colLoop_relAtInC

/-- info: 'LeanVM.Guest.B1.Digest.daMem_partsC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.daMem_partsC

/-- info: 'LeanVM.Guest.B1.Digest.colMeaningC_of_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.colMeaningC_of_mem

/-- info: 'LeanVM.Guest.B1.Digest.dv_relAtInC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.dv_relAtInC

/-- info: 'LeanVM.Guest.B1.Digest.within_of_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.within_of_shape

/-- info: 'LeanVM.Guest.B1.Digest.disjL_of_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.disjL_of_shape

/-- info: 'LeanVM.Guest.B1.Digest.dvLayoutC_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.dvLayoutC_shape

/-- info: 'LeanVM.Guest.B1.Digest.daMemC_of_memL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.daMemC_of_memL

/-- info: 'LeanVM.Guest.B1.Digest.dvLayoutC_within' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.dvLayoutC_within

/-- info: 'LeanVM.Guest.B1.Digest.dvLayoutC_disj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.dvLayoutC_disj

/-- info: 'LeanVM.Guest.B1.Digest.da_verify_completeRelAtWC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.da_verify_completeRelAtWC

/-- info: 'LeanVM.Guest.B1.Digest.da_verify_completeRelAtW_of_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.da_verify_completeRelAtW_of_comp

/-- info: 'LeanVM.Guest.B1.Main.da_verify_calleeC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Main.da_verify_calleeC

/-- info: 'LeanVM.Guest.B1.Main.da_verify_callee_of_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.Main.da_verify_callee_of_comp
