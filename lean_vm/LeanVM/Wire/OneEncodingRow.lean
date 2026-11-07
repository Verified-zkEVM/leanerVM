/-
  LeanVM.Wire.OneEncodingRow

  One encoding, the header and the rows: for a phase `readPhase` accepted, the paths it unprunes
  to, with any hash, are written back (`Prover.phaseToBytes`) with the header and the rows read.
-/

module

public import LeanVM.Wire.Spec

/-!
# One encoding: the header and the rows of a phase

`Prover.phaseToBytes paths` is the header and the rows (`phaseHeaderAndRows paths`: the queries'
count and positions, the height, the leaf width, the row width and the rows) followed by the
siblings (`phaseSiblingBytes paths`), `phaseToBytes_eq_append`.

The pruning idea and its formalization on leanerVM's main branch are scaraven's
(https://github.com/scaraven).
-/

namespace LeanVM.Wire

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile

public section

/-! ## The split of `Prover.phaseToBytes` -/

/-- The paths of a phase at their distinct positions, ascending, the first at each, as
`Prover.phaseToBytes` takes them. -/
def distinctPaths (paths : List Opening) : List Opening :=
  dedupByKey Opening.leafIndex (paths.mergeSort fun a b ↦ a.leafIndex ≤ b.leafIndex)

/-- The leading zero words every leaf of `leaves` has, as `Prover.phaseToBytes` counts them (`0`
for no leaf). -/
def commonLeadingZeros (leaves : List (List K)) : ℕ :=
  ((leaves.map fun leaf ↦ (leaf.takeWhile fun word ↦ decide (word = 0)).length).min?).getD 0

/-- What `Prover.phaseToBytes paths` writes before the siblings: the queries' count and positions,
the height, the leaf width, the row width, and the rows. -/
def phaseHeaderAndRows (paths : List Opening) : Bytes :=
  let height := (paths.head?.map fun path ↦ path.path.length).getD 0
  let leafWords := (paths.head?.map fun path ↦ path.leaf.length).getD 0
  let distinct := distinctPaths paths
  let zeros := commonLeadingZeros (distinct.map Opening.leaf)
  Prover.u32Bytes paths.length ++ paths.flatMap (fun path ↦ Prover.u32Bytes path.leafIndex) ++
    Prover.u32Bytes height ++ Prover.u32Bytes leafWords ++ Prover.u32Bytes (leafWords - zeros) ++
    distinct.flatMap (fun path ↦ (path.leaf.drop zeros).flatMap K.toBytes)

/-- What `Prover.phaseToBytes paths` writes after the rows: level by level from the leaves, the
sibling of each node the distinct paths climb through (the first path's) whose sibling node is not
one of them, left to right. -/
def phaseSiblingBytes (paths : List Opening) : Bytes :=
  let height := (paths.head?.map fun path ↦ path.path.length).getD 0
  let distinct := distinctPaths paths
  (List.range height).flatMap fun level ↦
    let nodes := dedupByKey Prod.fst (distinct.map fun path ↦
      (path.leafIndex >>> level, path.path.getD level default))
    (nodes.filter fun (node, _) ↦ node ^^^ 1 ∉ nodes.map Prod.fst).flatMap
      fun (_, sibling) ↦ digestBytes sibling

/-- **The split**: a phase's encoding is its header and rows, then its siblings. -/
theorem phaseToBytes_eq_append (paths : List Opening) :
    Prover.phaseToBytes paths = phaseHeaderAndRows paths ++ phaseSiblingBytes paths := by
  unfold Prover.phaseToBytes phaseHeaderAndRows phaseSiblingBytes distinctPaths commonLeadingZeros
  simp only [List.append_assoc, List.map_map]
  rfl

end

end LeanVM.Wire
