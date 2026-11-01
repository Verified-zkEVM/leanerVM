import LeanVM.Guest.EndReplay

/-!
# Tests: the replaying decoder chooses nothing

`LeanVM.Guest.End.decodeReplay` reads its witness off the memory, through the index of its
addresses, and off the frames the replayed run entered. The traversal below follows every
definition `decodeReplay` unfolds to (its value, not the proofs it carries) through this
repository and the schemes it imports (`LeanVM`, `LeanXmss`, `Sphincs`, `LeanDa`), as
`DecodeNoChoice.lean` does for `decode`.

* **Classical constructs.** The definitions that mention `Classical.choose`, `Classical.epsilon`,
  `Exists.choose`, `Classical.indefiniteDescription`, `Classical.propDecidable`,
  `Classical.choice` or `Nat.find` are exactly one: `LeanVM.Semantics.addressIndex?`
  (`Classical.choose`: the index `i` with `a = g^i`, unique by the generator's order), and the
  only definition that mentions it is B1's `B1.Main.gLog` (the exponent of a power of `g` below
  `2^34`, which the witness's decoding reads off the statement's words). The memory is read
  through the index of its addresses (`Located.readIn`), not `MemoryImage.read`, and no frame is
  found by a classical test (`Located.frameOf` is not reached).
* **Positive controls.** The traversal reaches the replay (`Located.statesIn`, the machine's step
  `Semantics.executeWith`, the decided precondition `Located.preTest`) and B1-d's child proof
  `VerifySub.piOfW`.
-/

open Lean Meta Elab Command

/-- The prefixes the traversals follow. -/
def followed : List Name := [`LeanVM, `LeanXmss, `Sphincs, `LeanDa]

/-- The definitions reachable from `root` through values, following `followed`, and the pairs
(definition, constant) for every constant a visited definition's value mentions that `bad`
flags. -/
def traverse (root : Name) (bad : Name → Bool) : MetaM (NameSet × Array (Name × Name)) := do
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut todo : Array Name := #[root]
  let mut hits : Array (Name × Name) := #[]
  while h : todo.size > 0 do
    let n := todo.back
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | continue
    -- follow definitions (and instances), not theorems: a proof is not part of the decoder
    let some v := ci.value? | continue
    if ci matches .thmInfo _ then continue
    if ← isProp ci.type then continue
    for c in v.getUsedConstants do
      if bad c then hits := hits.push (n, c)
      else if followed.any (·.isPrefixOf c) && !seen.contains c then todo := todo.push c
  return (seen, hits)

/-- The classical constructs that could pick a witness. -/
def classical : NameSet :=
  [``Classical.choose, ``Classical.epsilon, ``Exists.choose, ``Classical.indefiniteDescription,
    ``Classical.propDecidable, ``Classical.choice, ``Nat.find].foldl NameSet.insert {}

/-- The hits, sorted, as a string. -/
def showHits (hits : Array (Name × Name)) : String :=
  toString ((hits.map fun p ↦ s!"{p.1} uses {p.2}").qsort (· < ·)).toList

/-- info: [LeanVM.Semantics.addressIndex? uses Classical.choose] -/
#guard_msgs in
run_meta do
  let (_, hits) ← traverse ``LeanVM.Guest.End.decodeReplay classical.contains
  logInfo (showHits hits)

/-- info: [LeanVM.Guest.B1.Main.gLog uses LeanVM.Semantics.addressIndex?] -/
#guard_msgs in
run_meta do
  let reads : List Name := [``LeanVM.Semantics.addressIndex?, ``LeanVM.Semantics.MemoryImage.read,
    ``LeanVM.Semantics.Program.fetch]
  let (_, hits) ← traverse ``LeanVM.Guest.End.decodeReplay (reads.contains ·)
  logInfo (showHits hits)

/-! ## Positive controls -/

/-- info: statesIn: true, executeWith: true, preTest: true, piOfW: true, frameOf: false, addressIndex?: true -/
#guard_msgs in
run_meta do
  let (seen, _) ← traverse ``LeanVM.Guest.End.decodeReplay classical.contains
  logInfo s!"statesIn: {seen.contains ``LeanVM.Guest.Located.statesIn}, executeWith: {seen.contains ``LeanVM.Semantics.executeWith}, preTest: {seen.contains ``LeanVM.Guest.Located.preTest}, piOfW: {seen.contains ``LeanVM.Guest.B1.VerifySub.piOfW}, frameOf: {seen.contains ``LeanVM.Guest.Located.frameOf}, addressIndex?: {seen.contains ``LeanVM.Semantics.addressIndex?}"

/-! ## The end theorem's axioms -/

/-- info: 'LeanVM.Guest.End.guest_knowledge_replay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.End.guest_knowledge_replay
