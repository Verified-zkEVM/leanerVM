import LeanVM.Guest.B1.Tables.GkrM
import LeanVM.Guest.B1.Tables.FlockM
import LeanVM.Guest.B1.Tables.VerifyTablesM
import LeanVM.Guest.B1.VerifySub.KnownB
import LeanVM.Guest.B1.Tables.GuestHypsM

/-!
# Tests: `verify_bus_gkr`, `verify_flock`, `verify_tables` over a hash model (W2, Tables)

* The generic lemmas of `B1/Tables/*M.lean`, `*B.lean` rest on Lean's three axioms.
* **They are what `verify_sub`'s proof over a model takes**: `soundGkrM_model` and
  `soundTablesM_model` give `vsKnownB_model`'s hypotheses, hence `End.VsKnownB M.sem` for every
  model; `verify_flock_model` is `verify_sub_model`'s `SoundFlockM`.
* **At the deployed model they are the deployed ones**: `SoundGkr`, `SoundTables`, `SoundFlock`
  by `soundGkrM_deployed`, `soundTablesM_deployed`, `soundFlockM_deployed`.
* The free-of-`BLAKE2S` set `vtFree`, by the kernel.
-/

namespace LeanVMTests.Guest.ModelTables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.B1 LeanVM.Guest.B1.VerifySub LeanVM.Protocol LeanVM.Protocol.Verifier

/-! ## Axioms -/

/-- info: 'LeanVM.Guest.B1.VerifySub.freeOn_vtFree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.freeOn_vtFree

/-- info: 'LeanVM.Guest.B1.VerifySub.runsToM_gkrStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.runsToM_gkrStep

/-- info: 'LeanVM.Guest.B1.VerifySub.loop10_stepM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.loop10_stepM

/-- info: 'LeanVM.Guest.B1.VerifySub.verify_bus_gkr_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.verify_bus_gkr_model

/-- info: 'LeanVM.Guest.B1.VerifySub.soundGkrM_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.soundGkrM_model

/-- info: 'LeanVM.Guest.B1.loop82_stepM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.loop82_stepM

/-- info: 'LeanVM.Guest.B1.runs_verifyFlockM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.runs_verifyFlockM

/-- info: 'LeanVM.Guest.B1.verify_flock_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.verify_flock_model

/-- info: 'LeanVM.Guest.B1.soundFlockM_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.soundFlockM_model

/-- info: 'LeanVM.Guest.B1.VerifySub.window_evalB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.window_evalB

/-- info: 'LeanVM.Guest.B1.VerifySub.vt_valsB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.vt_valsB

/-- info: 'LeanVM.Guest.B1.VerifySub.vt_zcM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.vt_zcM

/-- info: 'LeanVM.Guest.B1.VerifySub.runsToM_tablesSeg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.runsToM_tablesSeg

/-- info: 'LeanVM.Guest.B1.VerifySub.verify_tables_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.verify_tables_model

/-- info: 'LeanVM.Guest.B1.VerifySub.soundTablesM_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.soundTablesM_model

/-- info: 'LeanVM.Guest.B1.VerifySub.guestHypsM_gkr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.guestHypsM_gkr

/-- info: 'LeanVM.Guest.B1.VerifySub.guestHypsM_tables' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.guestHypsM_tables

/-- info: 'LeanVM.Guest.B1.VerifySub.guestHypsM_flock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Guest.B1.VerifySub.guestHypsM_flock

/-! ## What `verify_sub` over a model takes -/

/-- `vsKnownB_model`'s hypotheses hold for every model: `End.VsKnownB M.sem`. -/
example (M : HashModel) {bytecode : List K} (hb : bytecode.length = 2 ^ 22) :
    End.VsKnownB M.sem :=
  vsKnownB_model (soundGkrM_model M) (soundTablesM_model M hb)

/-- `verify_sub_model`'s callees that hash, but the opening, on a memory of `2^κ` words. -/
example (M : HashModel) {κ : ℕ} (hκ : κ ≤ 32) (Lm : MemImage κ) {bytecode : List K}
    (hb : bytecode.length = 2 ^ 22) :
    SoundGkrM M Lm.read ∧ SoundTablesM M bytecode TCtx Lm.read ∧ SoundFlockM M Lm.read :=
  ⟨verify_bus_gkr_model hκ Lm, verify_tables_model hκ Lm hb, verify_flock_model Lm.read⟩

/-- `End.VsKnownB M.sem` at the guest's bytecode, from `guestHypsM_gkr`, `guestHypsM_tables`. -/
example (M : HashModel) : End.VsKnownB M.sem :=
  vsKnownB_model (guestHypsM_gkr M) (guestHypsM_tables M)

/-! ## At the deployed model -/

example {κ : ℕ} (hκ : κ ≤ 32) (Lm : MemImage κ) : SoundGkr Lm.read :=
  soundGkrM_deployed.mp (verify_bus_gkr_model hκ Lm)

example {κ : ℕ} (hκ : κ ≤ 32) (Lm : MemImage κ) {bytecode : List K}
    (hb : bytecode.length = 2 ^ 22) : SoundTables bytecode TCtx Lm.read :=
  soundTablesM_deployed.mp (verify_tables_model hκ Lm hb)

example (rd : Reader) : SoundFlock rd := soundFlockM_deployed.mp (verify_flock_model rd)

end LeanVMTests.Guest.ModelTables
