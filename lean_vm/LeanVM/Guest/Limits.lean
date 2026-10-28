/-
  LeanVM.Guest.Limits

  Where `NodeRel` admits witnesses the deployed guest cannot run: the deployed limits, the
  children's openings agreeing in the guest's Merkle caps, and no zero Fiat-Shamir challenge where
  the guest divides. The hypotheses of the guest's completeness.
-/

module

public import LeanVM.Guest.Hints
public import LeanVM.Protocol.Verifier.DeferredShape
public import Statement.LeanVmGuest
public import LeanVM.Guest.NZProgram

/-!
# The limits of the guest's completeness

`NodeRel bytecode seed s w` (`Statement/LeanVmGuest.lean`) admits witnesses on which the deployed guest
(`crates/rec_aggregation/guests/lean_ethereum.py` at leanVM `4af2cddd`, `G:N` its lines) does
not run to completion. Completeness assumes two hypotheses beside `NodeRel`, each a precise
predicate on the witness:

* **`Limits s w`, the deployed limits** of the node: the guest's fixed capacities and range
  checks, which the Spec does not have (at most `16` children, ...; listed at the structure). An
  honest prover within them is never refused, and `aggregate_with_stats` refuses to aggregate
  outside most of them.
* **`ChildrenOk bytecode seed w`, every child one the guest accepts** (`ChildOk`): besides
  `NodeRel`'s conditions, a child's stack log at least `22` and its proof stream at most `8192`
  scalars; its openings agree in the guest's Merkle caps (the guest writes each level's Merkle
  cap once, so two openings of one query step meeting at a node of the tree must give it one
  digest; one tree's openings agree; two that disagree at a node give a Keccak-256 collision, an
  argument in prose, not proved here); and no zero challenge where the guest divides (the guest
  computes `μ = 1/λ` for each WHIR level's batching challenge `λ`, G:1253, and the basis
  coefficients `(1 + c)/(c·inv)` for the fold and tail challenges `c`, G:1560, G:1565).

The coverage table's size (`coverage`) is `Hints.plan`'s, as an honest run lays it out.
-/

namespace LeanVM.Guest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Node

@[expose] public section

open Limits

/-! ## The children's hypotheses -/

/-- **Every child is one the guest accepts.** -/
abbrev ChildrenOk (bytecode : List K) (seed : Digest) (w : NodeWitness) : Prop :=
  ∀ c ∈ w.children, ChildOk bytecode seed c

/-! ## What `NodeRel` gives of the children's fresh claims -/

/-- **Every child's fresh claim has the bytecode's shape**: the deferring verifier accepts each
child's proof (`NodeRel`), and an accepted proof claims the bytecode at the verifier's own bus
point, `bytecodeLow ++ alphas`, of the bytecode's log-length (`verifyDeferred_shaped`). Not a
hypothesis: `NodeRel` implies it. -/
theorem fresh_shaped_of_nodeRel {bytecode : List K} {seed : Digest} {s : NodeStatement}
    {w : NodeWitness} (h : NodeRel bytecode seed s w) :
    ∀ c ∈ w.children, c.fresh.bytecodePoint.length = Nat.log2 bytecode.length :=
  fun c hc => verifyDeferred_shaped (h.2.1 c hc).2

/-- **At the deployed guest's `2^23` words, every child's fresh point has 23 coordinates**
(B1-f's `FreshShaped w`). -/
theorem fresh_shaped_23 {bytecode : List K} {seed : Digest} {s : NodeStatement}
    {w : NodeWitness} (h : NodeRel bytecode seed s w) (hb : bytecode.length = 2 ^ 23) :
    ∀ c ∈ w.children, c.fresh.bytecodePoint.length = 23 := fun c hc => by
  rw [fresh_shaped_of_nodeRel h c hc, hb, Nat.log2_two_pow]

end
end LeanVM.Guest
