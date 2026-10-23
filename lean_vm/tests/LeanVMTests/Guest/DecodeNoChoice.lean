import LeanVM.Guest.EndKnow

/-!
# Tests: the decoder chooses nothing

Every definition of this repository that the guest's decoder `LeanVM.Guest.End.decodeWith`
unfolds to (its value, not the proofs it carries) is checked not to mention `Classical.choose`,
`Classical.epsilon`, `Exists.choose` or `Classical.indefiniteDescription`: the decoder reads its
witness off the memory, it does not pick one. The one exception is the memory read itself,
`LeanVM.Semantics.gLog?` (the index `i` with `a = g^i`, unique by the generator's order): the
specification's definition of an address, not a witness. Deciding a test
(`Classical.propDecidable`) and the field arithmetic are not choices of a witness, and are
outside the check. `main`'s witness function `W` is a parameter of `decodeWith`; the decoder of
the end theorems instantiates it with B1's, and this test is then run on that decoder too.
-/

open Lean Meta Elab Command

/-- The repository's definitions reachable from `root` through values, and those mentioning a
forbidden constant. -/
def choiceUses (root : Name) (stop : NameSet) (forbidden : NameSet) : MetaM (Array (Name × Name)) := do
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut todo : Array Name := #[root]
  let mut bad : Array (Name × Name) := #[]
  while h : todo.size > 0 do
    let n := todo.back
    todo := todo.pop
    if seen.contains n || stop.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | continue
    -- follow definitions (and instances), not theorems: a proof is not part of the decoder
    let some v := ci.value? | continue
    if ci matches .thmInfo _ then continue
    if ← isProp ci.type then continue
    for c in v.getUsedConstants do
      if forbidden.contains c then bad := bad.push (n, c)
      else if (`LeanVM).isPrefixOf c && !seen.contains c then todo := todo.push c
  return bad

/-- info: [] -/
#guard_msgs in
run_meta do
  let forbidden : NameSet := [``Classical.choose, ``Classical.epsilon, ``Exists.choose,
    ``Classical.indefiniteDescription].foldl NameSet.insert {}
  let stop : NameSet := [``LeanVM.Semantics.gLog?].foldl NameSet.insert {}
  let bad ← choiceUses ``LeanVM.Guest.End.decodeWith stop forbidden
  logInfo m!"{bad.toList}"

/-! ## The decoder verifies nothing

No definition `decodeWith` unfolds to, through this repository and the schemes it imports,
mentions a hash, the permutation or a verification function (Keccak-256, Keccak-f[1600], a
signature scheme's `verify`, the deferring verifier, the DA opening, the batching). The traversal
stops at the guest's own semantics (`Core.Stmt.HoldsList`, `Core.Program.RelL`,
`Core.Program.locN`): the decoder finds a callee's frame as the one at which the guest's code holds
(`Located.frameOf`), and that code's checks are the guest's, not the decoder's. -/

/-- A name ends with one of the suffixes. -/
def endsWithAny (n : Name) (suffixes : List String) : Bool :=
  suffixes.any fun s ↦ n.toString.endsWith s

/-- The definitions reachable from `root` through values, following the given prefixes and
stopping at the names ending with a `stop` suffix, that mention a name ending with a forbidden
suffix. -/
def verifyUses (root : Name) (follow : List Name) (stop forbidden : List String) :
    MetaM (Array (Name × Name)) := do
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut todo : Array Name := #[root]
  let mut bad : Array (Name × Name) := #[]
  while h : todo.size > 0 do
    let n := todo.back
    todo := todo.pop
    if seen.contains n || endsWithAny n stop then continue
    seen := seen.insert n
    let some ci := env.find? n | continue
    let some v := ci.value? | continue
    if ci matches .thmInfo _ then continue
    if ← isProp ci.type then continue
    for c in v.getUsedConstants do
      if endsWithAny c forbidden then bad := bad.push (n, c)
      else if follow.any (·.isPrefixOf c) && !seen.contains c then todo := todo.push c
  return bad

/-- info: [] -/
#guard_msgs in
run_meta do
  let follow := [`LeanVM, `LeanXmss, `Sphincs, `LeanDa]
  let stop := ["Core.Stmt.HoldsList", "Core.Stmt.Holds", "Core.Stmt.HoldsArms",
    "Core.Program.RelL", "Core.Program.locN", "Semantics.gLog?"]
  let forbidden := ["keccak256", "keccakF", "Keccak.round", "absorbBlock", "xmssVerify",
    "sphincsVerify", "LeanXmss.verify", "Sphincs.verify", "verifyDeferred", "verifyDeferredWith",
    "Verifier.verify", "verifyWith", "Witness.Opens", "Node.batch"]
  let bad ← verifyUses ``LeanVM.Guest.End.decodeWith follow stop forbidden
  logInfo m!"{bad.toList}"
