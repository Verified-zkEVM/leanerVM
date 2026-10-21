import LeanVM.E2E.Sanity

/-!
# Tests: sanity (T7′)

* The sanity theorem `idealVerify_blake2s` and its pieces rest on Lean's three axioms; its
  statement is locked.
* **The table check at BLAKE2s, concretely.** The one-row table of the empty string's chain (a
  row of the compression function) passes the precheck, has finitely many chain inputs, and V_I's
  table check with BLAKE2s accepts it; the empty table too. Two non-final rows with distinct
  inputs and equal outputs fail the precheck, and V_I's table check rejects them.
-/

namespace LeanVMTests.E2E.Sanity

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Guest.Value LeanVM.E2E LeanVM.E2E.Sanity

/-! ## Axioms -/

/-- info: 'LeanVM.E2E.Sanity.idealVerify_blake2s' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms idealVerify_blake2s

/-- info: 'LeanVM.E2E.Sanity.idealVerify_of_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms idealVerify_of_steps

/-- info: 'LeanVM.E2E.Sanity.step_of_reached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms step_of_reached

/-- info: 'LeanVM.E2E.Sanity.head_of_runProof' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms head_of_runProof

/-- info: 'LeanVM.E2E.Sanity.head_of_child' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms head_of_child

/-- info: 'LeanVM.E2E.Sanity.candidateRun_of_m3Holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms candidateRun_of_m3Holds

/-- info: 'LeanVM.E2E.Sanity.tableOKWith_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tableOKWith_run

/-- info: 'LeanVM.E2E.Sanity.chainInputs_finite_of_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms chainInputs_finite_of_card

/-- info: 'LeanVM.E2E.Sanity.nodeStep_eq_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms nodeStep_eq_some

/-! ## The statement -/

/-- T7′: the deployed aggregation's acceptance, the words of the reached roots, the full relation
of the reached candidates, the precheck of their tables and enough fuel make V_I with BLAKE2s
accept. -/
example {s : LeanVM.Node.NodeStatement} {ip : IdealProof} {fuel : ℕ}
    (hagg : LeanVM.Node.verifyAggregate LeanVM.Guest.guest s ip.proof)
    (hcov : WordsCover LeanVM.Guest.guest ip (rootNode LeanVM.Guest.guest s ip))
    (haux : CandidatesAux LeanVM.Guest.guest ip (rootNode LeanVM.Guest.guest s ip))
    (hpre : TablesPrecheck LeanVM.Guest.guest ip (rootNode LeanVM.Guest.guest s ip))
    (hfuel : FuelBounds LeanVM.Guest.guest ip (rootNode LeanVM.Guest.guest s ip) fuel) :
    idealVerify (m := Id) (fun x ↦ (pure (blake2sBytes x) : Id Digest)) LeanVM.Guest.guest ip
      fuel s = true :=
  idealVerify_blake2s hagg hcov haux hpre hfuel

/-! ## The table check at BLAKE2s, concretely -/

/-- The one row of the empty string's chain under BLAKE2s. -/
def emptyRow : BlakeRow :=
  ⟨![0, 0, 0, 0], ivCells.1, ivCells.2, (digestScalars (blake2sBytes [])).1,
    (digestScalars (blake2sBytes [])).2, metadataCell 0 true⟩

/-- It is a row of the compression function. -/
theorem emptyRow_compress : blakeDeployed.row emptyRow := by
  show CompressCells _ _ _ _ _ _
  decide +kernel

/-- A one-row table passes the precheck. -/
theorem precheck_singleton (b : BlakeRow) : Precheck [b] := by
  intro r₁ h₁ r₂ h₂ _ _ _
  rw [List.mem_singleton.mp h₁, List.mem_singleton.mp h₂]

/-- A one-row table has finitely many chain inputs. -/
theorem chainInputs_singleton_finite (b : BlakeRow) : (chainInputs [b]).Finite :=
  chainInputs_finite_of_card (N := 1) (by norm_num) (by simp)

/-- **V_I's table check with BLAKE2s accepts the one-row table of the empty string.** -/
example : tableOKWith (m := Id) (fun x ↦ (pure (blake2sBytes x) : Id Digest)) [emptyRow] = true :=
  tableOKWith_blake2s (fun _ hb ↦ List.mem_singleton.mp hb ▸ emptyRow_compress)
    (precheck_singleton _) (chainInputs_singleton_finite _)

/-- **V_I's table check with BLAKE2s accepts the empty table.** -/
example : tableOKWith (m := Id) (fun x ↦ (pure (blake2sBytes x) : Id Digest)) [] = true :=
  tableOKWith_blake2s (fun _ hb ↦ absurd hb List.not_mem_nil)
    (fun _ h ↦ absurd h List.not_mem_nil) (chainInputs_finite_of_card (N := 0) (by norm_num)
      (by simp))

/-- A non-final row of message `m`, every other cell zero. -/
def zeroRow (m : Fin 4 → E) : BlakeRow := ⟨m, 0, 0, 0, 0, metadataCell 64 false⟩

/-- **The precheck rejects a collision**: two non-final rows with distinct inputs and equal
outputs. -/
theorem not_precheck_collision : ¬ Precheck [zeroRow ![0, 0, 0, 0], zeroRow ![1, 0, 0, 0]] := by
  intro h
  have hnf : ¬ RowFinal (zeroRow ![0, 0, 0, 0]) := by
    show ¬ (unpackMetadata (metadataCell 64 false)).2.1 = lastBlock
    decide +kernel
  have hnf' : ¬ RowFinal (zeroRow ![1, 0, 0, 0]) := by
    show ¬ (unpackMetadata (metadataCell 64 false)).2.1 = lastBlock
    decide +kernel
  have e := h _ (by simp) _ (by simp) hnf hnf' rfl
  have e0 := congrFun (congrArg Prod.fst e) 0
  revert e0
  decide

/-- **V_I's table check rejects the collision.** -/
example : tableOKWith (m := Id) (fun x ↦ (pure (blake2sBytes x) : Id Digest))
    [zeroRow ![0, 0, 0, 0], zeroRow ![1, 0, 0, 0]] = false := by
  unfold tableOKWith
  simp only [not_precheck_collision, ↓reduceIte]
  rfl

end LeanVMTests.E2E.Sanity
