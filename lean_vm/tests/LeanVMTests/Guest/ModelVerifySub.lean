import LeanVM.Guest.B1.VerifySub.KnownB
import LeanVM.Guest.B1.VerifySub.SoundWM
import LeanVM.Guest.B1.Tables.VerifyTablesSound
import LeanVM.Guest.B1.Tables.Gkr

/-!
# Tests: `verify_sub` over a hash model (W2, VerifySub)

* The generic lemmas of `B1/VerifySub/*B.lean`, `*M.lean` rest on Lean's three axioms.
* **At the deployed model they are the deployed ones**: `vsKnownB_model` at
  `HashModel.deployed`, from the deployed `verify_bus_gkr_sound` and `verify_tables_sound`, gives
  `End.VsKnownB blakeDeployed` and the deployed `VsKnown`; `verify_sub_model` at
  `HashModel.deployed` gives `verify_sub_sound`'s `MeaningVerifySub`.
* The free-of-`BLAKE2S` set `vsFree`, by the kernel.
-/

namespace LeanVMTests.Guest.ModelVerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.B1 LeanVM.Guest.B1.VerifySub LeanVM.Protocol LeanVM.Protocol.Verifier

/-! ## Axioms -/

/-- info: 'LeanVM.Guest.B1.VerifySub.freeOn_vsFree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.freeOn_vsFree

/-- info: 'LeanVM.Guest.B1.VerifySub.VsHoldsB.sliceF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.VsHoldsB.sliceF

/-- info: 'LeanVM.Guest.B1.VerifySub.vs_seedM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.vs_seedM

/-- info: 'LeanVM.Guest.B1.VerifySub.vs_knownB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.vs_knownB

/-- info: 'LeanVM.Guest.B1.VerifySub.vsKnownB_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.vsKnownB_model

/-- info: 'LeanVM.Guest.B1.VerifySub.verifyDeferredWith_true' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.verifyDeferredWith_true

/-- info: 'LeanVM.Guest.B1.VerifySub.verify_sub_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.verify_sub_model

/-- info: 'LeanVM.Guest.B1.VerifySub.verify_sub_sound_wCM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.verify_sub_sound_wCM

/-- info: 'LeanVM.Guest.B1.VerifySub.verify_sub_sound_wM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.verify_sub_sound_wM

/-- info: 'LeanVM.Guest.B1.VerifySub.Reads.runM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.Reads.runM

/-- info: 'LeanVM.Guest.B1.VerifySub.meaningVerifySubWith_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.meaningVerifySubWith_deployed

/-- info: 'LeanVM.Guest.B1.VerifySub.vsOutcomeM_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.vsOutcomeM_deployed

/-- info: 'LeanVM.Guest.B1.VerifySub.soundTablesM_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.soundTablesM_deployed

/-- info: 'LeanVM.Guest.B1.VerifySub.soundOpenM_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.soundOpenM_deployed

/-! ## At the deployed model -/

/-- `verify_bus_gkr`'s deployed soundness is its soundness over the deployed model. -/
theorem soundGkrM_deployed_proved : ∀ rd, Main.MemOk rd → SoundGkrM HashModel.deployed rd :=
  fun rd hm ↦ by
    obtain ⟨κ, -, h32, L, rfl⟩ := hm
    exact soundGkrM_deployed.mpr (verify_bus_gkr_sound h32 L)

/-- `verify_tables`' deployed soundness is its soundness over the deployed model. -/
theorem soundTablesM_deployed_proved :
    ∀ rd, Main.MemOk rd → SoundTablesM HashModel.deployed End.bytecode TCtx rd := fun rd hm ↦ by
  obtain ⟨κ, -, h32, L, rfl⟩ := hm
  exact soundTablesM_deployed.mpr (verify_tables_sound h32 L End.bytecode_length)

/-- **`vsKnownB_model` at the deployed model is `End.VsKnownB blakeDeployed`.** -/
example : End.VsKnownB blakeDeployed :=
  vsKnownB_model (M := HashModel.deployed) soundGkrM_deployed_proved soundTablesM_deployed_proved

/-- **… and the deployed `VsKnown`.** -/
example : VsKnown := fun rd hm σ ht h ↦
  vsKnownB_model (M := HashModel.deployed) soundGkrM_deployed_proved soundTablesM_deployed_proved
    rd hm σ ht (by
      rw [show HashModel.deployed.sem = blakeDeployed from rfl, relB_deployed, holdsListB_deployed]
      exact h)

/-- **`verify_sub_model` at the deployed model is `verify_sub_sound`.** -/
example {κ : ℕ} (hκ : κ ≤ 32) (hκ6 : 6 ≤ κ) (Lm : MemImage κ) {bytecode : List K}
    (hb : bytecode.length = 2 ^ 22)
    {TCtx : Reader → Layout → BusResult → List ColumnClaim → List E → Prop}
    {PCtx : Reader → List ℕ → E → E → Prop}
    (hgkr : SoundGkr Lm.read) (htab : SoundTables bytecode TCtx Lm.read) (hfl : SoundFlock Lm.read)
    (hpl : SoundPlace PCtx Lm.read) (hkap : HypKappa PCtx Lm.read) (hop : SoundOpen Lm.read)
    (hterm : SoundTerm TCtx PCtx Lm.read) {args : List E}
    (ht : ExpTables Lm.read (args.getD 4 0) (args.getD 5 0))
    (h : coreProgram.Rel Lm.read "verify_sub" args []) :
    MeaningVerifySub bytecode Lm.read args [] :=
  meaningVerifySubWith_deployed.mp (verify_sub_model (M := HashModel.deployed) hκ hκ6 Lm hb
    (soundGkrM_deployed.mpr hgkr) (soundTablesM_deployed.mpr htab) (soundFlockM_deployed.mpr hfl)
    hpl hkap (soundOpenM_deployed.mpr hop) hterm ht
    (by rw [show HashModel.deployed.sem = blakeDeployed from rfl, relB_deployed]; exact h))

/-! ## The transfer, by the kernel -/

example : coreProgram.FreeOn vsFree = true := freeOn_vsFree

/-- `verify_bus_gkr` hashes: it is not free. -/
example : coreProgram.FreeOn ("verify_bus_gkr" :: vsFree) = false := by decide +kernel

end LeanVMTests.Guest.ModelVerifySub
