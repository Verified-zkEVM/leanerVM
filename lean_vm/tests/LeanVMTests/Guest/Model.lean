import LeanVM.Guest.EndFinal
import LeanVM.Guest.SoundB
import LeanVM.Guest.B1.ExpKnownB
import LeanVM.Guest.B1.FiatShamir
import LeanVM.Guest.Value.NodeSome

/-!
# Tests: the guest's proofs under a hash model (the foundation of W2)

* The generic semantics, program logic, executor, checker and B2 (`CoreB`, `LogicB`, `ExecB`,
  `CheckSoundB`, `SoundB`), the chain layer over a hash model (`Value/ModelChain.lean`), the run
  layer (`Value/RunSome.lean`, `Value/NodeSome.lean`, `B1.RunsToM`) and the pilot B1 lemmas rest
  on Lean's three axioms.
* **The generic B2 is the deployed one at the deployed semantics**: `mainBodyLB_of` at
  `blakeDeployed`, its `verify_sub` hypothesis the deployed `VsKnown` and its `exponent_tables`
  hypothesis `expKnownB`, gives `mainBodyL_of`'s conclusion.
* The free-of-`BLAKE2S` transfer applies to `exponent_tables`, by the kernel.
-/

namespace LeanVMTests.Guest.Model

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Check
open LeanVM.Guest.End LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM LeanVM.Protocol.EndToEnd

/-! ## Axioms -/

/-- info: 'LeanVM.Guest.Core.relB_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Core.relB_deployed

/-- info: 'LeanVM.Guest.Core.relB_iff_rel_of_freeOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Core.relB_iff_rel_of_freeOn

/-- info: 'LeanVM.Guest.funSpecB_induction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.funSpecB_induction

/-- info: 'LeanVM.Guest.Exec.execB_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Exec.execB_sound

/-- info: 'LeanVM.Guest.Check.checkWinsB_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Check.checkWinsB_run

/-- info: 'LeanVM.Guest.End.mainBodyLB_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.End.mainBodyLB_of

/-- info: 'LeanVM.Guest.B1.expKnownB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.expKnownB

/-- info: 'LeanVM.Guest.Value.HashModel.one_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Value.HashModel.one_block

/-- info: 'LeanVM.Guest.Value.HashModel.empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Value.HashModel.empty

/-- info: 'LeanVM.Guest.Value.HashModel.chain_blocks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Value.HashModel.chain_blocks

/-- info: 'LeanVM.Guest.Value.HashModel.chain_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Value.HashModel.chain_bytes

/-- info: 'LeanVM.Guest.Value.run_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Value.run_some

/-- info: 'LeanVM.Guest.B1.runsToM_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.runsToM_deployed

/-- info: 'LeanVM.Guest.B1.RunsToM.bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.RunsToM.bind

/-- info: 'LeanVM.Guest.Value.fs_compress_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Value.fs_compress_model

/-- info: 'LeanVM.Guest.Value.grind_check_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Value.grind_check_model

/-- info: 'LeanVM.Guest.B1.holdsB_fsCompressT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.holdsB_fsCompressT

/-- info: 'LeanVM.Guest.B1.holdsB_squeezeT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.holdsB_squeezeT

/-- info: 'LeanVM.Guest.B1.sumcheck_round4_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.sumcheck_round4_model

/-- info: 'LeanVM.Guest.Value.batchWith_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Value.batchWith_some

/-! ## The generic B2 at the deployed semantics -/

/-- The deployed `verify_sub` obligation is the generic one at the deployed semantics. -/
theorem vsKnownB_deployed : VsKnownB blakeDeployed := fun rd hm σ ht h ↦
  vsKnown_proved rd hm σ ht (by rwa [relB_deployed, holdsListB_deployed] at h)

/-- **`mainBodyLB_of` at the deployed semantics is `mainBodyL_of`.** -/
example {input : PublicInput} {t : Trace guest} (hv : ValidExecution guest input t) :
    Stmt.HoldsList (RL coreProgram t.image certByName) t.image.read (valG t.image 1 (certOf 1))
      (coreOf 1).body False (fun rs ↦ rs = []) ∧
    t.image.read 1 = some (digestScalars (publicDigest input)).1 ∧
    t.image.read g = some (digestScalars (publicDigest input)).2 := by
  obtain ⟨h, h1, h2⟩ := mainBodyLB_of vsKnownB_deployed (B1.expKnownB blakeDeployed)
    ((validExecutionB_deployed guest input t).mpr hv)
  have e : RLB blakeDeployed coreProgram t.image certByName = RL coreProgram t.image certByName :=
    relLB_deployed _ _ _ _
  rw [e, holdsListB_deployed] at h
  exact ⟨h, h1, h2⟩

/-! ## The transfer, by the kernel -/

example : coreProgram.FreeOn ["exponent_tables"] = true := B1.freeOn_exponent_tables

/-- A function with a `BLAKE2S` atom is not free: `sumcheck_round4` hashes. -/
example : coreProgram.FreeOn ["sumcheck_round4"] = false := by decide +kernel

end LeanVMTests.Guest.Model
