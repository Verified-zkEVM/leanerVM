import LeanVM.Guest.EndFinal

/-!
# Tests: the decoder chooses nothing, computes no hash and runs no verifier

`LeanVM.Guest.End.decode` reads its witness off the memory. The traversal below follows every
definition `decode` unfolds to (its value, not the proofs it carries) through this repository and
the schemes it imports (`LeanVM`, `LeanXmss`, `Sphincs`, `LeanDa`).

* **Classical constructs.** The definitions that mention `Classical.choose`, `Classical.epsilon`,
  `Exists.choose`, `Classical.indefiniteDescription`, `Classical.propDecidable`,
  `Classical.choice` or `Nat.find` are exactly the reviewed two:
  `LeanVM.Guest.Located.frameOf` (`Classical.propDecidable`: it decides, for each of the memory's
  `2^κ` frames in order, whether the guest's own code for the callee holds there on the call's
  words, and takes the first) and `LeanVM.Semantics.addressIndex?` (`Classical.choose`: the index `i`
  with `a = g^i`, unique by the generator's order, the specification's definition of an address).
  Neither picks a witness.
* **Positive controls.** The traversal reaches `Located.frameOf` and B1-d's child proof
  `VerifySub.piOfW`, and it flags a definition that does choose (`VerifySub.valOf`, the word at
  an address by `Exists.choose`, which `decode` does not use).
* **No hash, no verifier.** No definition `decode` unfolds to mentions Keccak-256, Keccak-f[1600],
  a signature scheme's verifier, the deferring verifier, the DA opening or the batching. This
  traversal stops at the guest's own semantics (`Core.Stmt.HoldsList`, `Core.Program.RelL`,
  `Core.Program.locN`), which `frameOf`'s test evaluates and which includes the guest's
  in-circuit checks (a `KECCAK` atom's `KeccakCellsRelation`): those checks are the guest's, the decoder
  computes no hash and runs no verifier of its own.
-/

open Lean Meta Elab Command

/-- The prefixes the traversals follow. -/
def followed : List Name := [`LeanVM, `LeanXmss, `Sphincs, `LeanDa]

/-- A name ends with one of the suffixes. -/
def endsWithAny (n : Name) (suffixes : List String) : Bool :=
  suffixes.any fun s ↦ n.toString.endsWith s

/-- The definitions reachable from `root` through values, following `followed` and stopping at
the names ending with a `stop` suffix, and the pairs (definition, constant) for every constant a
visited definition's value mentions that `bad` flags. -/
def traverse (root : Name) (stop : List String) (bad : Name → Bool) :
    MetaM (NameSet × Array (Name × Name)) := do
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut todo : Array Name := #[root]
  let mut hits : Array (Name × Name) := #[]
  while h : todo.size > 0 do
    let n := todo.back
    todo := todo.pop
    if seen.contains n || endsWithAny n stop then continue
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

/-- info: [LeanVM.Guest.Located.frameOf uses Classical.propDecidable, LeanVM.Semantics.addressIndex? uses Classical.choose] -/
#guard_msgs in
run_meta do
  let (_, hits) ← traverse ``LeanVM.Guest.End.decode [] classical.contains
  logInfo (showHits hits)

/-! ## Positive controls -/

/-- info: frameOf: true, piOfW: true -/
#guard_msgs in
run_meta do
  let (seen, _) ← traverse ``LeanVM.Guest.End.decode [] classical.contains
  logInfo s!"frameOf: {seen.contains ``LeanVM.Guest.Located.frameOf}, piOfW: {seen.contains ``LeanVM.Guest.B1.VerifySub.piOfW}"

/-- info: [LeanVM.Guest.B1.VerifySub.valOf uses Classical.propDecidable, LeanVM.Guest.B1.VerifySub.valOf uses Exists.choose] -/
#guard_msgs in
run_meta do
  let (_, hits) ← traverse ``LeanVM.Guest.B1.VerifySub.valOf [] classical.contains
  logInfo (showHits hits)

/-! ## No hash, no verifier -/

/-- info: [] -/
#guard_msgs in
run_meta do
  let stop := ["Core.Stmt.HoldsList", "Core.Stmt.Holds", "Core.Stmt.HoldsArms",
    "Core.Program.RelL", "Core.Program.locN", "Semantics.addressIndex?"]
  let forbidden := ["keccak256", "keccakF1600", "Keccak.round", "absorbBlock", "absorbBlockWith", "xmssVerify",
    "sphincsVerify", "LeanXmss.verify", "Sphincs.verify", "verifyDeferred", "verifyDeferredWith",
    "Verifier.verify", "verifyWith", "MatrixWitness.Opens", "Node.batch"]
  let (_, hits) ← traverse ``LeanVM.Guest.End.decode stop (endsWithAny · forbidden)
  logInfo (showHits hits)
