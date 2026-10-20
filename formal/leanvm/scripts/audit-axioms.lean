import LeanerVM
import LeanerVMTests
import Lean

/-!
# Production and test namespace axiom closure

Run after building production and tests:
`lake env lean -E warning scripts/audit-axioms.lean`.
It checks the recursive axiom dependencies of every declaration defined in a first-party module
(`LeanerVM*` or `LeanerVMTests*`), whatever its namespace: the front page's `LeanVM.*`, the
`@[csimp]` lemmas on CompPoly's `BF64`/`Ext` and every other declaration a first-party module adds.
It complements the lexical source policy and CI's production namespace audit.
-/

open Lean Elab Command

elab "auditValidation" : command => do
  let env ← getEnv
  let mut count : Nat := 0
  let mut unexpected : Array (Name × Name) := #[]
  let modules := env.header.moduleNames
  let firstParty (name : Name) : Bool :=
    match env.getModuleIdxFor? name with
    | some idx =>
      let m := modules[idx.toNat]!
      (`LeanerVM).isPrefixOf m || (`LeanerVMTests).isPrefixOf m
    -- Declarations of the file being elaborated (the audit itself, or an injected probe).
    | none => true
  for (name, _) in env.constants.toList do
    if firstParty name then
      count := count + 1
      for ax in ← collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          unexpected := unexpected.push (name, ax)
  logInfo m!"Audited {count} declarations; unexpected axioms: {unexpected}"
  unless unexpected.isEmpty do throwError "Unexpected axioms"

auditValidation
