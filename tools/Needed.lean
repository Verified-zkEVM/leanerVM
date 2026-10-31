import Lean
open Lean

/-- The modules whose constants the given roots need: the transitive closure of the constants in
definitions' types and values and in theorems' types (not their proofs). -/
def main (args : List String) : IO Unit := do
  let modName := args[0]!.toName
  let roots := (args.drop 1).map String.toName
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := modName, importAll := true }] {} (loadExts := false)
  let roots := if roots.isEmpty then
      match env.getModuleIdx? modName with
      | some idx => (env.constants.map₁.toList.filterMap fun (c, _) ↦
          if env.getModuleIdxFor? c == some idx then some c else none)
      | none => []
    else roots
  let external := [`Init, `Std, `Lean, `Mathlib, `Batteries, `Aesop, `Qq, `VCVio, `ToMathlib,
    `CompPoly, `ArkLib, `Clean, `PolyFun, `Cslib, `Plausible, `ProofWidgets, `ImportGraph,
    `LeanSearchClient]
  let mut seen : NameSet := {}
  let mut todo := roots
  while !todo.isEmpty do
    let c := todo.head!
    todo := todo.tail!
    if seen.contains c then continue
    seen := seen.insert c
    let some ci := env.find? c | continue
    let mut used := ci.type.getUsedConstants
    match ci with
    | .defnInfo d => used := used ++ d.value.getUsedConstants
    | .thmInfo d =>
      let local? := match env.getModuleIdxFor? c with
        | some idx => !(env.header.moduleNames[idx.toNat]!.getRoot ∈ external)
        | none => true
      if roots.contains c || local? then used := used ++ d.value.getUsedConstants
    | .opaqueInfo d => used := used ++ d.value.getUsedConstants
    | .inductInfo d => used := used ++ d.ctors.toArray ++ #[c]
    | .ctorInfo d => used := used.push d.induct
    | .recInfo d => used := used.push d.getMajorInduct
    | _ => pure ()
    for u in used do
      if !seen.contains u then todo := u :: todo
  let mut mods : Std.HashMap Name Nat := {}
  for c in seen do
    if let some idx := env.getModuleIdxFor? c then
      let m := env.header.moduleNames[idx.toNat]!
      mods := mods.insert m (mods.getD m 0 + 1)
      if (args.getD 0 "").length > 0 && (← IO.getEnv "NEEDED_CONSTS").isSome then
        IO.println s!"CONST {m} {c}" 
  let all := env.header.moduleNames
  IO.println s!"constants: {seen.size}; modules needed: {mods.size}; imported: {all.size}"
  for (m, n) in mods.toList do
    IO.println s!"NEED {m} {n}"
