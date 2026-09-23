import LeanerVM
import LeanerVMTests
import Lean

/-!
# Production and test namespace axiom closure

Run after building production and tests:
`lake env lean -E warning scripts/audit-axioms.lean`.
This tracks the driver used for the local leanISA acceptance audits. It checks recursive
dependencies of declarations in both project namespaces, including imported dependencies.
It complements the lexical source policy and CI's production namespace audit.
-/

open Lean Elab Command

elab "auditValidation" : command => do
  let env ← getEnv
  let mut count : Nat := 0
  let mut unexpected : Array (Name × Name) := #[]
  for (name, _) in env.constants.toList do
    if (`LeanerVM).isPrefixOf name || (`LeanerVMTests).isPrefixOf name then
      count := count + 1
      for ax in ← collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          unexpected := unexpected.push (name, ax)
  logInfo m!"Audited {count} declarations; unexpected axioms: {unexpected}"
  unless unexpected.isEmpty do throwError "Unexpected axioms"

auditValidation
