import LeanVM.E2E.Sanity

/-!
# Tests: V_I's step before decision E2E-13

Decision E2E-13 removed from `nodeStep`'s trusted definition a finiteness test that always passes:
it walked the candidates only when they were finitely many (`if h : (blindCandidatesS …).Finite`)
and rejected otherwise, but a stack is a `Column`, of a finite type. `nodeStepOld` is the step
before E2E-13, verbatim (`LeanVM/E2E/Statement.lean` at `df6df681`); `nodeStep_eq_old` pins the
two equal at every hash, monad and node, so V_I, and every theorem about it, kept its meaning.

`tableOKWith` keeps its finiteness test: it is no dead branch at every list of rows (a list
of `2^58 + 1` rows can chain cyclically, the counters wrapping modulo `2^64`, giving infinitely
many strings with a chain), only at the tables `nodeStep` checks
(`chainInputs_finite_of_candidateRun`, `tableOKWith_candidateRun`).
-/

namespace LeanVMTests.E2E.StatementOld

open LeanVM.Parameters LeanVM.Semantics LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.Blake2sHash LeanVM.Protocol.LeanIsa
open LeanVM.Protocol.EndToEnd LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.EndToEnd.Sound
open LeanVM.Protocol.Compile.Rom LeanVM.E2E

section Verify

variable {m : Type → Type} [Monad m] (H : Bytes → m Digest) (prog : Program) (seed : Digest)
  (ip : IdealProof)

open Classical in
/-- **`nodeStep` before decision E2E-13**, verbatim: the candidates walked only when finitely
many. -/
noncomputable def nodeStepOld (ν : LeanVM.E2E.Node) : m (Option (List LeanVM.E2E.Node)) := do
  let (pi, π) := ν
  let some (layout, ρ) := Verifier.announced (bytecodeWords prog) π.stream | pure none
  let some s := sizesOf prog layout | pure none
  let some r := stackRoot π | pure none
  let some (ht, w) := stackShape layout ρ | pure none
  let some P := ip.word ν | pure none
  if ¬ WellShaped w P.word then return none
  let root ← pTreeRootM H ht P
  if digestScalars root ≠ r then return none
  if blindCandidatesS prog s ρ ht pi P = ∅ ∧ ¬ P.Full ht then return none
  if h : (blindCandidatesS prog s ρ ht pi P).Finite then
    let mut kids : List LeanVM.E2E.Node := []
    for q in h.toFinset.toList do
      let some t := candidateRun prog s q | return none
      let rows := t.blakeRows blakeFree
      if !(← tableOKWith H rows) then return none
      for c in (LeanVM.Guest.End.decodeAt (LeanVM.Guest.Value.tableSem rows) (ip.frames ν)
          t.image).witness.children do
        let pc ← statementDigestWith H seed c.statement
        kids := kids ++ [(pc, c.proof)]
    return some kids
  else return none

/-- A finiteness test on a set of a finite type passes. -/
theorem dite_finite {β α : Type*} [Finite β] (S : Set β) [Decidable S.Finite]
    (f : S.Finite → α) (g : α) : (if h : S.Finite then f h else g) = f (Set.toFinite S) :=
  dite_eq_left_of_eq_true (eq_true (Set.toFinite S))

/-- **E2E-13 preserves V_I's step**: `nodeStep` is the step before the decision at every hash,
monad and node. -/
theorem nodeStep_eq_old (ν : LeanVM.E2E.Node) :
    nodeStep H prog seed ip ν = nodeStepOld H prog seed ip ν := by
  unfold nodeStep nodeStepOld
  simp only [dite_finite]
  rfl

end Verify

/-- info: 'LeanVMTests.E2E.StatementOld.nodeStep_eq_old' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms nodeStep_eq_old

/-- info: 'LeanVM.E2E.Sanity.chainInputs_finite_of_candidateRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Sanity.chainInputs_finite_of_candidateRun

/-- info: 'LeanVM.E2E.Sanity.tableOKWith_candidateRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Sanity.tableOKWith_candidateRun

end LeanVMTests.E2E.StatementOld
