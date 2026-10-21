import LeanVM.E2E.Complete.Model
import LeanVM.E2E.Complete.Candidates
import LeanVM.Protocol.EndToEnd.Blind.Complete
import LeanVM.E2E.Complete.Node

/-!
# T6-det's proved pieces, locked

Statement locks of `LeanVM/E2E/Complete/` and `LeanVM/Protocol/EndToEnd/Blind/Complete.lean`
(`docs/roadmap/t6-completeness.md`): the honest table passes V_I's precheck and table check for
every hash, its semantics is functional, the honest execution is the one V_I re-runs, an exact
encoding's candidates are its stack, and V° accepts the honest proof for every hash; with their
foundations pinned.
-/

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.LeanIsa LeanVM.Protocol.EndToEnd
open LeanVM.E2E LeanVM.E2E.Complete

/-! ## The honest table -/

example {D : List Bytes} (I : Intermediates D) (H : Bytes → Digest)
    {rows : List BlakeRow} (h : ∀ r ∈ rows, CanonRow r ∧ ChainRow I H r) :
    tableOKWith (m := Id) (fun x ↦ (pure (H x) : Id Digest)) rows = true :=
  tableOKWith_chainRows h

example {D : List Bytes} (I : Intermediates D) (H : Bytes → Digest)
    {prog : Program} {input : PublicInput} {t : Trace prog}
    (hv : ValidExecutionB (CompModel.chain I H).sem prog input t) :
    haltingRunB blakeFree prog t.image = some t ∧
      tableOKWith (m := Id) (fun x ↦ (pure (H x) : Id Digest))
        (t.blakeRows blakeFree) = true :=
  ⟨haltingRunB_of_validChain hv, tableOKWith_of_validB hv⟩

/-- info: 'LeanVM.E2E.Complete.stdChain_chainRows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stdChain_chainRows

/-- info: 'LeanVM.E2E.Complete.precheck_chainRows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms precheck_chainRows

/-- info: 'LeanVM.E2E.Complete.tableOKWith_chainRows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tableOKWith_chainRows

/-- info: 'LeanVM.E2E.Complete.chainSem_functional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms chainSem_functional

/-- info: 'LeanVM.E2E.Complete.haltingRunB_of_validB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms haltingRunB_of_validB

/-- info: 'LeanVM.E2E.Complete.tableOKWith_of_validB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tableOKWith_of_validB

/-- info: 'LeanVM.E2E.Complete.CompModel.deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompModel.deployed

/-! ## The candidates of an honest word -/

/-- info: 'LeanVM.E2E.Complete.eq_of_mem_candidates_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eq_of_mem_candidates_deployed

/-! ## V° accepts the honest proof -/

/-- info: 'LeanVM.Protocol.EndToEnd.Blind.runI_blindProgram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Protocol.EndToEnd.Blind.runI_blindProgram

/-- info: 'LeanVM.Protocol.EndToEnd.Blind.exists_prove_verifyBlindWith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Protocol.EndToEnd.Blind.exists_prove_verifyBlindWith

/-! ## V_I on honest nodes -/

/-- info: 'LeanVM.E2E.Complete.nodeHead_prove' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms nodeHead_prove

/-- info: 'LeanVM.E2E.Complete.nodeStep_honest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms nodeStep_honest

/-- info: 'LeanVM.E2E.Complete.closure_accepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms closure_accepts

/-- info: 'LeanVM.E2E.Complete.idealVerify_accepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms idealVerify_accepts

/-- info: 'LeanVM.E2E.Complete.outerChecksWith_true' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms outerChecksWith_true
