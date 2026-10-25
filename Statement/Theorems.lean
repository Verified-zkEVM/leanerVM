module

public import Statement.LeanVm
public import Statement.LeanVmGuest
public import Statement.LeanXmss
public import Statement.LeanSphincs
public import Statement.LeanDa

/-!
# The theorems

Everything this repository proves, in one place: each field of `Theorems` is one end statement,
defined in the file of `Statement/` named next to it. `lean_vm/LeanVM.lean` proves
`Statement.Theorems LeanVM.Guest.End.decode` (`LeanVM.theorems_hold`), and the build fails if its
axioms are ever more than Lean's three (`propext`, `Classical.choice`, `Quot.sound`).

The guest's two knowledge statements are about a decoder, `decode`, which names the witness of a
valid execution: the proof supplies it (`LeanVM.Guest.End.decode`, in `lean_vm`, which reads the
witness from the execution's memory). They are only as meaningful as that decoder: one that chose
another statement of the same digest would satisfy `aggregateSound` through a Keccak-256 collision.

Every statement involving an adversary is in the random-permutation model: one uniformly random
permutation `π` of Keccak-f[1600]'s state, which the adversary queries forward and inverse.
-/

@[expose] public section

namespace Statement

/-- **The end theorems.** -/
structure Theorems (decode : LeanVM.Node.Decoder) : Prop where
  /-- leanVM is knowledge sound for the straight-line extractor `extractorRpm`: at most
  `(Q + 2^14) · 2^-128 + 7 (Q + 2^14)² · 2^-256` for `Q ≤ 2^128` queries (`LeanVm.lean`). -/
  knowledgeSoundness : LeanVM.KnowledgeSoundness
  /-- leanVM is complete: an honest proof of a valid execution of committed size at most `2^28`,
  at an inverse rate `2^ρ` with `1 ≤ ρ ≤ 4` and `2^25` nonces per proof of work, is rejected with
  probability at most `2^-127` (`LeanVm.lean`). -/
  completeness : LeanVM.Completeness
  /-- Every valid execution of the guest decodes to a statement of its input's digest and a
  witness holding it (`LeanVmGuest.lean`). -/
  guestKnowledge : LeanVM.Node.GuestKnowledge LeanVM.Guest.guest decode
  /-- An accepted guest proof is explained by the extracted execution or by a Keccak-256
  collision, with the bound of `knowledgeSoundness`. A claim held through a child rests only on
  that child's deferred verification; nothing composes across levels (`LeanVmGuest.lean`). -/
  aggregateSound : LeanVM.Node.AggregateSound LeanVM.Guest.guest decode
  /-- The guest is complete on every covered recursion node: at most `2048` declared claims,
  coverage slots and children's claims, and no raw signature and no blob held by the node itself
  (`LeanVmGuest.lean`). -/
  guestCompleteRecursion : LeanVM.Guest.Budget.GuestCompleteRecursion
  /-- The guest is complete on every covered leaf: no child, no blob held directly, at most
  `2048` raw signatures, declared claims and coverage slots (`LeanVmGuest.lean`). -/
  guestCompleteLeaf : LeanVM.Guest.Budget.GuestCompleteLeaf
  /-- The guest is complete on the six families of `Covered`, mixed nodes and nodes checking a
  blob of at most `8` rows among them. The completeness statements assume the children's
  hypotheses (`ChildOk`), which `guestChildComplete` gives honest proofs (`LeanVmGuest.lean`). -/
  guestCompleteCovered : LeanVM.Guest.Budget.GuestCompleteCovered
  /-- The honest proof of a guest execution is a child the guest accepts: rejected with
  probability at most `2^-126` in the random-permutation model, and with the deployed Keccak,
  where accepted, meeting every hypothesis the guest's completeness assumes of a child
  (`LeanVmGuest.lean`). -/
  guestChildComplete : LeanVM.Guest.Budget.GuestChildComplete
  /-- The batching run outside the circuit is sound: at most `(QA + QV + 1) · 2^-191 +
  5 (QA + QV)² · 2^-256` for `QA ≤ 2^128`, `QV ≤ 2^96`; it does not compose with the in-circuit
  statements (`LeanVmGuest.lean`). -/
  batchSound : LeanVM.Guest.Batch.BatchSound
  /-- leanXMSS is strongly unforgeable: at most `(Q + 1) · 2^-127` for `1 ≤ Q ≤ 2^128` permutation
  calls (`LeanXmss.lean`). -/
  leanXmss : LeanXmss.Rpm.LeanXmssRpmSecurityStatement
  /-- leanSPHINCS is strongly unforgeable at every proved lifetime: at most `(Q + 1) · 2^-127` for
  `1 ≤ Q ≤ 2^128` permutation calls (`LeanSphincs.lean`). -/
  leanSphincs : Sphincs.Lifetimes.RequestedSecurityRpm
  /-- LeanDA is perfectly complete, for every `π` (`LeanDa.lean`). -/
  leanDaComplete : LeanDa.PerfectlyCompleteRpm
  /-- LeanDA is position binding: at most `(Q + 1)² · 2^-256` for `Q ≤ 2^128` (`LeanDa.lean`). -/
  leanDaPositionBinding : LeanDa.PositionBindingRpm
  /-- LeanDA is code binding if its argument is knowledge sound in the random-permutation model;
  the argument cannot query `π`, so the hypothesis fails for any useful argument (`LeanDa.lean`). -/
  leanDaCodeBinding : LeanDa.CodeBindingRpm

end Statement

end
