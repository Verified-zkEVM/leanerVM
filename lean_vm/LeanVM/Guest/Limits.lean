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

/-!
# The limits of the guest's completeness

`NodeRel bytecode seed s w` (`Statement/LeanVmGuest.lean`) admits witnesses on which the deployed guest
(`crates/rec_aggregation/guests/lean_ethereum.py` at leanVM `4af2cddd`, `G:N` its lines) does
not run to completion. Completeness assumes three hypotheses beside `NodeRel`, each a precise
predicate on the witness:

* **`Limits s w`, the deployed limits**: the guest's fixed capacities and range checks, which the
  Spec does not have (a child's stack log at least `22`, its proof stream at most `8192` scalars,
  at most `16` children, ...; listed at the structure). They are the triage's findings (the
  README's "The guest's triage"): an honest prover within them is never refused, and
  `aggregate_with_stats` refuses to aggregate outside most of them.
* **`CapsAgree bytecode seed w`, the openings agree in the caps**: the guest writes each level's
  Merkle cap once (write-once memory), so two openings of one query step meeting at a node of the
  tree must give it one digest; the Spec checks each opening alone against the root. One tree's
  openings agree; two that disagree at a node give a Keccak-256 collision (the root's
  preimages; an argument in prose, not proved here). Stated, as `B1.Whir.CapsAgree` is for one opening, at every node of the tree, which
  is stronger than the cap levels alone and fails on the same collisions.
* **`NoZeroChallenge bytecode seed w`, no zero challenge where the guest divides** (new at
  `keccak-gkr`): the guest computes `μ = 1/λ` for each WHIR level's batching challenge `λ`
  (`opening_queries`, G:1253) and the basis coefficients `(1 + c)/(c·inv)` for the fold and tail
  challenges `c` (`open_stacked`, G:1560, G:1565), so a zero challenge there makes it reject a
  child the Spec accepts. Stated as: every child's proof is accepted by the deferring verifier
  whose stacked opening also rejects a zero fold, tail or level batching challenge
  (`verifyDeferredNZ`). Each challenge is a squeeze of Keccak-f[1600] (three lanes, `2^192`
  values), so in the random-permutation model an honest child's proof meets one with probability
  about `(number of those challenges)·2^-192` (an estimate in prose, not proved here).

`NoZeroChallenge` is the node-level form of `B1.Whir.NoZeroChallenge` (the opening's run from a
sponge state, `B1/Whir/CompleteIface.lean`); `verifyDeferredNZ`'s opening is `whirLevelsNZ`, the
Spec's `whirLevels` with exactly that program's three `require`s (`foldRoundsNZ`,
`tailRoundsNZ`, `lam ≠ 0`).

The coverage table's size (`coverage`) is `Hints.plan`'s, as an honest run lays it out.
-/

namespace LeanVM.Guest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Node

@[expose] public section

open Limits

/-! ## The three hypotheses -/

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
