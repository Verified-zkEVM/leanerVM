import LeanVM.Guest.EndKnow

/-!
# Tests: the decoder chooses nothing

Every definition of this repository that `LeanVM.Guest.End.decode` unfolds to (its value, not the
proofs it carries) is checked not to mention `Classical.choose`, `Classical.epsilon`,
`Exists.choose` or `Classical.indefiniteDescription`: the decoder reads its witness off the memory,
it does not pick one. The one exception is the memory read itself, `LeanVM.Semantics.gLog?` (the
index `i` with `a = g^i`, unique by the generator's order): the specification's definition of an
address, not a witness. Deciding a test (`Classical.propDecidable`) and the field arithmetic are
not choices of a witness, and are outside the check.
-/

open Lean Meta Elab Command

/-- The constants a definition's value mentions, skipping proofs. -/
partial def valueConsts (e : Expr) : MetaM NameSet := do
  let mut acc : NameSet := {}
  for c in e.getUsedConstants do
    acc := acc.insert c
  return acc

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
    for c in (← valueConsts v) do
      if forbidden.contains c then bad := bad.push (n, c)
      else if (`LeanVM).isPrefixOf c && !seen.contains c then todo := todo.push c
  return bad

/-- info: [] -/
#guard_msgs in
run_meta do
  let forbidden : NameSet := [``Classical.choose, ``Classical.epsilon, ``Exists.choose,
    ``Classical.indefiniteDescription].foldl NameSet.insert {}
  let stop : NameSet := [``LeanVM.Semantics.gLog?].foldl NameSet.insert {}
  let bad ← choiceUses ``LeanVM.Guest.End.decode stop forbidden
  logInfo m!"{bad.toList}"
