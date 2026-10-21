import LeanVM.Guest.Value.OracleModel

/-!
# Tests: the oracle hash model

* The chain lemma, the oracle model, the execution bridge and the deployed table check rest on
  Lean's three axioms.
* **Inhabitants.** The one-row table of the empty string, its output `blake2sBytes []`, passes the
  table check at BLAKE2s (`tableOK_blake2s`) and at the one-entry log answering `[]`, so
  `HashModel.oracle` is inhabited at a nonempty table and log; so is it at the empty ones.
-/

namespace LeanVMTests.Guest.OracleModel

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Value LeanVM.Protocol
open LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile.Rom

/-- info: 'LeanVM.Guest.Value.stdChain_snoc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms stdChain_snoc

/-- info: 'LeanVM.Guest.Value.HashModel.oracle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HashModel.oracle

/-- info: 'LeanVM.Guest.Value.validExecutionB_tableSem_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms validExecutionB_tableSem_iff

/-- info: 'LeanVM.Guest.Value.validExecutionB_oracle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms validExecutionB_oracle

/-- info: 'LeanVM.Guest.Value.validExecutionB_blakeFree_of_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms validExecutionB_blakeFree_of_valid

/-- info: 'LeanVM.Guest.Value.tableOK_blake2s' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tableOK_blake2s

/-- info: 'LeanVM.Guest.Value.tableOK_blakeRows_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tableOK_blakeRows_deployed

/-- The one row of the empty string's chain under BLAKE2s. -/
def emptyRow : BlakeRow :=
  ⟨![0, 0, 0, 0], ivCells.1, ivCells.2, (digestScalars (blake2sBytes [])).1,
    (digestScalars (blake2sBytes [])).2, metadataCell 0 true⟩

/-- It is a row of the compression function. -/
theorem emptyRow_compress : blakeDeployed.row emptyRow := by
  show CompressCells _ _ _ _ _ _
  decide +kernel

/-- **The one-row table passes the table check at BLAKE2s.** -/
example : TableOK (fun x ↦ some (blake2sBytes x)) [emptyRow] :=
  tableOK_blake2s fun _ hb ↦ List.mem_singleton.mp hb ▸ emptyRow_compress

/-- The log answering the empty string with its BLAKE2s. -/
def emptyLog : Log := [([], blake2sBytes [])]

/-- **The one-row table passes the table check at the one-entry log**: its only standard chain is
the empty string's, one row (a second row would be non-final, but the row has the last-block
flag), which the log answers with the row's output. -/
theorem tableOK_emptyLog : TableOK (look emptyLog) [emptyRow] := by
  intro x c hc hrows hs
  have he : ∀ (i : ℕ) (hi : i < c.length), c[i] = emptyRow := fun i hi ↦
    List.mem_singleton.mp (hrows _ (List.getElem_mem hi))
  have h1 : c.length = 1 := by
    by_contra hne
    have := (hs.2.2.1 0 (by omega)).2
    rw [he 0 hc] at this
    revert this
    decide +kernel
  have hmd := (hs.2.2.2 hc).2
  rw [he _ (by omega)] at hmd
  have hx : x.length ≤ 64 := by have := hs.1; omega
  have hx0 : x = [] := by
    apply List.eq_nil_of_length_eq_zero
    have := congrArg UInt64.toNat (congrArg Prod.fst hmd)
    revert this
    rw [show (unpackMetadata emptyRow.md).1 = 0 by decide +kernel]
    simp only [UInt64.toNat_zero, UInt64.toNat_ofNat']
    omega
  subst hx0
  rw [he _ (by omega)]
  exact congrArg some (cellWords_digestScalars _).symm

/-- `HashModel.oracle` at a nonempty table and log. -/
noncomputable example : HashModel := HashModel.oracle [emptyRow] emptyLog tableOK_emptyLog

/-- `HashModel.oracle` at the empty table and log: no chain lies in the empty table. -/
noncomputable example : HashModel :=
  HashModel.oracle [] [] fun _ _ hc hrows _ ↦ absurd (hrows _ (List.getElem_mem hc)) List.not_mem_nil

/-- The oracle model answers by the log. -/
example (rows : List BlakeRow) (ℓ : Log) (h : TableOK (look ℓ) rows) :
    (HashModel.oracle rows ℓ h).H = look ℓ := rfl

end LeanVMTests.Guest.OracleModel
