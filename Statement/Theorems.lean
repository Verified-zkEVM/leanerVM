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

Statements that follow from these, in their composed form (what an accepted proof of the leanISA
guest program establishes; the guest program's completeness on recursion nodes and leaves), are in
`Corollaries.lean`, proved from the fields of `Theorems` alone; a reviewer may skip it.

The guest program's knowledge statement takes the decoder that names the witness as a parameter,
`decode` (`LeanVmGuest.lean` says why its content is in that decoder). Every statement with an
adversary is in the random-permutation model (`Statement/README.md`).
-/

@[expose] public section

namespace Statement

/-- **The end theorems.** -/
structure Theorems (decode : LeanVM.Node.Decoder) : Prop where
  /-- leanVM is knowledge sound for the straight-line extractor `transcriptExtractor`: at most
  `(Q + 2^14) · 2^-128 + 5 (Q + 2^14)² · 2^-256` for `Q ≤ 2^128` queries (`LeanVm.lean`). -/
  knowledgeSoundness : LeanVM.KnowledgeSoundness
  /-- leanVM is complete: the honest prover's (`LeanVM.prover`, the executable
  `LeanVM.Prover.prove` of `Prover/Prove.lean`) proof of a valid execution of committed size at
  most `2^28`, at an inverse rate `2^ρ` with `1 ≤ ρ ≤ 4` and `2^25` nonces per proof of work, is
  rejected with probability at most `2^-256` (`LeanVm.lean`). -/
  completeness : LeanVM.Completeness
  
  /-- Every valid execution of the leanISA guest program proves the node statement its public
  input commits to: `decode` reads off its memory a seed, a statement whose digest under that seed
  is the input's digest, and a witness for it: each signature claim of the statement is held, by a
  signature or a child whose proof the deferring verifier accepts, the bytecode's value at the
  child's point taken from the witness and checked only at the root, and its DA digest is that of
  the blob matrix it checks, zeros or a child's (`NodeRelation`, `LeanVmGuest.lean`). -/
  guestKnowledge : LeanVM.Node.GuestKnowledge LeanVM.Guest.guest decode
  /-- A statement's digest binds the seed and the statement, up to a Keccak-256 collision among
  the candidates (`LeanVmGuest.lean`). With the two fields above it gives what an accepted proof
  establishes: an accepted proof of the leanISA guest program on `dig_iv(s)` yields, by
  `knowledgeSoundness`, an extracted execution; by `guestKnowledge`, a decoded statement of the
  same digest with a witness; by `digestBinds`, that it is `s` under `iv` or a Keccak-256
  collision. The composed bound is `Statement.Corollaries`' `aggregateSound`, proved in `lean_vm`
  as `LeanVM.Guest.End.aggregate_sound_outer`. -/
  digestBinds : LeanVM.Node.DigestBinds
  /-- The leanISA guest program is complete on the eight families of `CoveredNode`, mixed nodes and
  nodes checking one DA matrix of at most `32` rows among them. The completeness statements assume
  the children's hypotheses (`AcceptableChild`), which `guestChildComplete` gives honest proofs
  (`LeanVmGuest.lean`). -/
  guestCompleteCovered : LeanVM.Guest.Budget.GuestCompleteCovered
  /-- The same honest prover's proof of an execution of the guest program is a child the guest
  program accepts: rejected with probability at most `2^-126` in the random-permutation model, and
  with the deployed Keccak, where accepted, meeting every hypothesis the guest program's
  completeness assumes of a child (`LeanVmGuest.lean`). -/
  guestChildComplete : LeanVM.Guest.Budget.GuestChildComplete
  /-- The batching run outside the circuit is sound: at most `(QA + QV + 1) · M · 2^-191 +
  5 (QA + QV)² · 2^-256` for fewer than `M` children, `QA ≤ 2^128`, `QV ≤ 2^96`; it does not
  compose with the in-circuit statements (`LeanVmGuest.lean`). -/
  batchSound : LeanVM.Guest.Batch.BatchingSound
  /-- leanXMSS is strongly unforgeable: at most `(Q + 1) · 2^-127` for `Q ≥ 1` permutation
  calls of the whole game (`LeanXmss.lean`), key generation and the honest signer's worst-case
  grinding, about `2^33` calls per signing request, included: about `2^-62` at a full lifetime. -/
  leanXmss : LeanXmss.Rpm.LeanXmssStronglyUnforgeable
  /-- leanSPHINCS is strongly unforgeable at every proved lifetime: at most `(Q + 1) · 2^-127` for
  `Q ≥ 1` permutation calls of the whole game (`LeanSphincs.lean`), key generation and the honest
  signer's worst-case grinding, up to about `2^35` calls per signing request, included. -/
  leanSphincs : Sphincs.Lifetimes.LeanSphincsStronglyUnforgeable

  /-- LeanDA is perfectly complete, for every `π` (`LeanDa.lean`). -/
  leanDaComplete : LeanDa.PerfectlyCompleteRpm
  /-- LeanDA is position binding: at most `(Q + 1)² · 2^-256` for every `Q` (`LeanDa.lean`). -/
  leanDaPositionBinding : LeanDa.PositionBindingRpm
  /-- LeanDA is code binding if its argument, querying the model's oracles, is knowledge sound in
  the random-permutation model with a straight-line extractor (`LeanDa.lean`). -/
  leanDaCodeBinding : LeanDa.CodeBindingRpm

end Statement

end
