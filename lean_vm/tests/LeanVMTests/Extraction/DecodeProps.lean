import Statement.Decode.Words
import Statement.Decode.Bf64Trace
import Statement.Extractor
import LeanVM.Protocol.Extraction.Extract

/-!
# Tests: `Statement/Decode/` holds theorems only; the extractor's axioms

`Statement/Decode/` is the folder of the statement that needs no review: the theorems the
extractor's decoder takes as proof fields (`traceCtx`, `Statement/Extractor.lean`). By proof
irrelevance nothing in it can change what the extractor computes or what a statement says, as long
as every constant it declares is a proof. `#propsOnly` checks that: it fails if a module of
`Statement.Decode` declares a constant whose type is not a proposition.

Then the axioms of the extractor's data (its decoder context carries proofs) and of the theorems
that relate it to the knowledge-soundness proof: Lean's three.
-/

open Lean Elab Command

/-- Fails unless every constant the given modules declare (internal names aside) has a
proposition as its type. -/
elab "#propsOnly " mods:ident* : command => do
  let env ← getEnv
  for m in mods do
    let some idx := env.getModuleIdx? m.getId | throwError "no module {m.getId}"
    let mut bad : Array Name := #[]
    let mut n : Nat := 0
    for (name, ci) in env.constants.toList do
      if env.getModuleIdxFor? name == some idx && !name.isInternal then
        n := n + 1
        unless ← liftTermElabM (Meta.isProp ci.type) do bad := bad.push name
    unless bad.isEmpty do throwError "{m.getId}: not a proof: {bad}"
    if n == 0 then throwError "{m.getId}: no constants"

#propsOnly Statement.Decode.Words Statement.Decode.Bf64Trace

/-- info: 'LeanVM.Extraction.extract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Extraction.extract

/-- info: 'LeanVM.Extraction.gsContext' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Extraction.gsContext

/-- info: 'LeanVM.Extraction.Bf64Trace.tracePowerSum_separates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Extraction.Bf64Trace.tracePowerSum_separates

/-- info: 'LeanVM.Extraction.PruneProofs.candidates_subset_decodeStacks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Extraction.PruneProofs.candidates_subset_decodeStacks

/-- info: 'LeanVM.Extraction.MerkleProofs.committedWordC_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Extraction.MerkleProofs.committedWordC_eq

/-- info: 'LeanVM.Extraction.ExtractProofs.extract_of_candidate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Extraction.ExtractProofs.extract_of_candidate

/-- info: 'LeanVM.Extraction.ExtractProofs.extractorRpm_eq_extract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.Extraction.ExtractProofs.extractorRpm_eq_extract
