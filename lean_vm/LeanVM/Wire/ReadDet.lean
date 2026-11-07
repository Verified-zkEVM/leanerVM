/-
  LeanVM.Wire.ReadDet

  The bytes a pruned proof encodes to (`encodePhase`, `encodePruned`) and the reader's determinism:
  bytes `readPhase` / `readProof` accept are the encoding of what they read.
-/

module

public import LeanVM.Wire.Spec

/-!
# The reader's determinism

`encodePhase ph` is what `Prover.phaseToBytes` writes, computed from the pruned form `ph` instead of
the paths: the queries' count and positions, the height, the leaf width and the row width (the leaf
width less the zero words common to the fronts of the leaves, `zeroPrefix`, as `phaseToBytes`
computes them), each leaf without that prefix, and the carried siblings' digests level by level, in
order. `encodePruned` is `Proof.toBytes` from the pruned form: the stream's length and elements, the
phase count and each phase.

The pruning idea and its formalization on leanerVM's main branch are scaraven's
(https://github.com/scaraven).
-/

@[expose] public section

namespace LeanVM.Wire

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile

/-- The number of zero words common to the fronts of the leaves, as `Prover.phaseToBytes` computes
it: the least, over the leaves, of the length of the leaf's leading run of zeros; `0` for no leaf. -/
def zeroPrefix (leaves : List (List K)) : ℕ :=
  ((leaves.map fun leaf ↦ (leaf.takeWhile fun word ↦ decide (word = 0)).length).min?).getD 0

/-- The bytes of a pruned phase: the queries' count and positions; the height, the leaf width and
the row width `leafWords - zeroPrefix leaves`; each leaf without the common zero prefix; then the
carried siblings' digests, level by level, in order. -/
def encodePhase (ph : PrunedPhase) : Bytes :=
  let zeros := zeroPrefix ph.leaves
  Prover.u32Bytes ph.queries.length ++ ph.queries.flatMap Prover.u32Bytes ++
    Prover.u32Bytes ph.height ++ Prover.u32Bytes ph.leafWords ++
    Prover.u32Bytes (ph.leafWords - zeros) ++
    ph.leaves.flatMap (fun leaf ↦ (leaf.drop zeros).flatMap K.toBytes) ++
    ph.carried.flatMap fun level ↦ level.flatMap fun carried ↦ digestBytes carried.2

/-- The bytes of a pruned proof, as `Proof.toBytes` writes them: the stream's length, then each
element as its three words; the number of phases, then each phase (`encodePhase`). -/
def encodePruned (x : List E × List PrunedPhase) : Bytes :=
  Prover.u32Bytes x.1.length ++ x.1.flatMap E.toBytes ++
    Prover.u32Bytes x.2.length ++ x.2.flatMap encodePhase

end LeanVM.Wire

end
