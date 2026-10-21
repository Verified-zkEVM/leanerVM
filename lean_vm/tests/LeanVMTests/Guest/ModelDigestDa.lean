import LeanVM.Guest.B1.Digest.ChildListM
import LeanVM.Guest.B1.Digest.StatementM
import LeanVM.Guest.B1.Da.ListDigestM
import LeanVM.Guest.B1.Da.OpensSome
import LeanVM.Guest.B1.Da.NamedM

/-!
# Tests: the digests, claim lists and LeanDA under a hash model (W2, row 4)

* The generic lemmas of `B1/Digest` and `B1/Da` over a `HashModel` (the prefix layer
  `Digest/CommonM`, `statement_digest_model`, the claim lists', the DA root list's) and the DA
  bridge of package W2-S (`Da.opensWith_some_iff`) rest on Lean's three axioms.
* At the deployed model the generic meanings give the deployed ones: `statement_digest`'s and
  `da_list_digest`'s forward directions are recovered from `statement_digest_model` and
  `da_list_digest_model`, `da_verify_sound`'s conclusion from `da_verify_model`
  (`da_verify_model_deployed`), with the guest's padding digests LeanDA's at BLAKE2s.
-/

namespace LeanVMTests.Guest.ModelDigestDa

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.B1.Digest LeanVM.Protocol LeanVM.Protocol.Blake2sHash

/-! ## Axioms -/

/-- info: 'LeanVM.Guest.B1.Digest.ChainSteps.prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.ChainSteps.prefix

/-- info: 'LeanVM.Guest.B1.Digest.ChainSteps.append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.ChainSteps.append

/-- info: 'LeanVM.Guest.B1.Digest.chainSteps_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.chainSteps_prefix

/-- info: 'LeanVM.Guest.B1.Digest.loopB_fwd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.loopB_fwd

/-- info: 'LeanVM.Guest.B1.Digest.final_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.final_model

/-- info: 'LeanVM.Guest.B1.Digest.statement_digest_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.statement_digest_model

/-- info: 'LeanVM.Guest.B1.Digest.statementDigestWith_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.statementDigestWith_of

/-- info: 'LeanVM.Guest.B1.Digest.meaning_statement_digestWith_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.meaning_statement_digestWith_deployed

/-- info: 'LeanVM.Guest.B1.Digest.scaled_log_11_iffB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.scaled_log_11_iffB

/-- info: 'LeanVM.Guest.B1.Digest.scaled_log_6_iffB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.scaled_log_6_iffB

/-- info: 'LeanVM.Guest.B1.Digest.claims_tail_B' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.claims_tail_B

/-- info: 'LeanVM.Guest.B1.Digest.claims_window_B' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.claims_window_B

/-- info: 'LeanVM.Guest.B1.Digest.claim_list_digest_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.claim_list_digest_model

/-- info: 'LeanVM.Guest.B1.Digest.child_claims_tail_B' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.child_claims_tail_B

/-- info: 'LeanVM.Guest.B1.Digest.child_window_B' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.child_window_B

/-- info: 'LeanVM.Guest.B1.Digest.child_claim_list_digest_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.child_claim_list_digest_model

/-- info: 'LeanVM.Guest.B1.Digest.da_hash_roots_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.da_hash_roots_model

/-- info: 'LeanVM.Guest.B1.Digest.da_list_digest_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.da_list_digest_model

/-- info: 'LeanVM.Guest.B1.Digest.meaning_da_list_digestWith_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.meaning_da_list_digestWith_deployed

/-- info: 'LeanVM.Guest.B1.Digest.cover_da_root_soundB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.cover_da_root_soundB

/-- info: 'LeanVM.Da.commitCodewordsWith_some' depends on axioms: [propext, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms LeanVM.Da.commitCodewordsWith_some

/-- info: 'LeanVM.Da.opensWith_some_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms LeanVM.Da.opensWith_some_iff

/-- info: 'LeanVM.Guest.B1.Digest.da_verify_cell_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.da_verify_cell_model

/-- info: 'LeanVM.Guest.B1.Digest.da_vector_cell_B' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.da_vector_cell_B

/-- info: 'LeanVM.Guest.B1.Digest.da_vector_dispatch_B' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.da_vector_dispatch_B

/-- info: 'LeanVM.Guest.B1.Digest.da_levels_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.da_levels_model

/-- info: 'LeanVM.Guest.B1.Digest.levels_rootM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.levels_rootM

/-- info: 'LeanVM.Guest.B1.Digest.treeRootWith_nodeM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.treeRootWith_nodeM

/-- info: 'LeanVM.Guest.B1.Digest.treeRootWith_blocks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.treeRootWith_blocks

/-- info: 'LeanVM.Guest.B1.Digest.da_verify_column_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.da_verify_column_model

/-- info: 'LeanVM.Guest.B1.Digest.da_verify_restM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.da_verify_restM

/-- info: 'LeanVM.Guest.B1.Digest.da_verify_factsM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.da_verify_factsM

/-- info: 'LeanVM.Guest.B1.Digest.vector_chainM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.vector_chainM

/-- info: 'LeanVM.Guest.B1.Digest.commitCodewordsWith_eqM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.commitCodewordsWith_eqM

/-- info: 'LeanVM.Guest.B1.Digest.opens_ofM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.opens_ofM

/-- info: 'LeanVM.Guest.B1.Digest.da_verify_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.da_verify_model

/-- info: 'LeanVM.Guest.B1.Digest.opensWith_deployed_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.opensWith_deployed_iff

/-- info: 'LeanVM.Guest.B1.Digest.da_verify_model_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.da_verify_model_deployed

/-- info: 'LeanVM.Guest.B1.Digest.col_outB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.col_outB

/-- info: 'LeanVM.Guest.B1.Digest.colLoop_outB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.colLoop_outB

/-- info: 'LeanVM.Guest.B1.Digest.da_verify_sound_wM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.da_verify_sound_wM

/-- info: 'LeanVM.Guest.B1.Digest.daOutM_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms LeanVM.Guest.B1.Digest.daOutM_deployed

/-! ## The deployed model -/

/-- `statement_digest`'s deployed forward direction, from the generic one. -/
example (rd : Reader) (args rets : List E) (h : coreProgram.Rel rd "statement_digest" args rets) :
    Meaning_statement_digest rd args rets := by
  refine (meaning_statement_digestWith_deployed rd args rets).mp
    (statement_digest_model (M := HashModel.deployed) rd args rets ?_)
  show coreProgram.RelB blakeDeployed rd _ _ _
  rw [relB_deployed]
  exact h

/-- `da_list_digest`'s deployed forward direction, from the generic one. -/
example (rd : Reader) (args rets : List E) (h : coreProgram.Rel rd "da_list_digest" args rets) :
    Meaning_da_list_digest rd args rets := by
  refine (meaning_da_list_digestWith_deployed rd args rets).mp
    (da_list_digest_model (M := HashModel.deployed) rd args rets ?_)
  show coreProgram.RelB blakeDeployed rd _ _ _
  rw [relB_deployed]
  exact h

/-- `da_verify`'s deployed soundness, from the generic one at the deployed model. -/
example {rd : Reader} (hm : MemOk rd) {gsq : E} (hT : SquaresAt rd gsq) {r0 r1 v0 v1 : E}
    (h : coreProgram.Rel rd "da_verify" [gsq] [r0, r1, v0, v1]) :
    ∃ (root vd : Digest) (w : LeanVM.Da.Witness),
      (r0, r1) = digestScalars root ∧ (v0, v1) = digestScalars vd ∧ w.Opens root vd :=
  da_verify_model_deployed hm hT h

/-- The claim lists' transfer, by the kernel: `scaled_log` does not hash. -/
example : coreProgram.FreeOn ["scaled_log__L11", "scaled_log__L6"] = true := freeOn_scaled_log

end LeanVMTests.Guest.ModelDigestDa
