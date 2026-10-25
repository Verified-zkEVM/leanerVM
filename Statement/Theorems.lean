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
valid execution: the proof supplies it (`LeanVM.Guest.End.decode`, in `lean_vm`). The statements
hold of any decoder that outputs valid witnesses; a wrong decoder makes them false, not easier.

Every statement involving an adversary is in the random-permutation model: one uniformly random
permutation `π` of Keccak-f[1600]'s state, which the adversary queries forward and inverse.
-/

@[expose] public section

namespace Statement

/-- **The end theorems.** -/
structure Theorems (decode : LeanVM.Node.Decoder) : Prop where
  /-- leanVM is knowledge sound, for the fixed straight-line extractor `extractorRpm`: an
  adversary of `Q ≤ 2^128` queries breaks it with probability at most
  `soundnessError Q + (Q + verifierPermCalls) · 2^-379` (`LeanVm.lean`). -/
  knowledgeSoundness : LeanVM.KnowledgeSoundness
  /-- The same, in bits: at most `(Q + 2^14) · 2^-127` for `Q ≤ 2^120` (`LeanVm.lean`). -/
  knowledgeSoundnessBits : LeanVM.KnowledgeSoundnessBits
  /-- leanVM is complete: an honest proof of a valid execution is rejected with probability at
  most `completenessError fuel + completenessPermCalls fuel · 2^-379` (`LeanVm.lean`). -/
  completeness : LeanVM.Completeness
  /-- The aggregation guest's knowledge soundness: every valid execution of the guest decodes to
  a statement of the input's digest and a witness holding it (`LeanVmGuest.lean`). -/
  guestKnowledge : LeanVM.Node.GuestKnowledge LeanVM.Guest.guest decode
  /-- The outer verifier's acceptance of a guest proof is explained by the extracted execution,
  with the bound of `knowledgeSoundness`, for `Q ≤ 2^128` (`LeanVmGuest.lean`). -/
  aggregateSound : LeanVM.Node.AggregateSound LeanVM.Guest.guest decode
  /-- The guest is complete on every covered recursion node (`LeanVmGuest.lean`). -/
  guestCompleteRecursion : LeanVM.Guest.Budget.GuestCompleteRecursion
  /-- The guest is complete on every covered leaf (`LeanVmGuest.lean`). -/
  guestCompleteLeaf : LeanVM.Guest.Budget.GuestCompleteLeaf
  /-- The batching of the children's deferred claims, run outside the circuit, is sound, for
  `QA ≤ 2^128` adversary queries and a program bound `QV ≤ 2^96`
  (`LeanVmGuest.lean`; it does not compose with the guest's in-circuit statements). -/
  batchSound : LeanVM.Guest.Batch.BatchSoundRpm
  /-- The same, in bits: at most `(QA + QV) · 2^-188` (`LeanVmGuest.lean`). -/
  batchSoundBits : LeanVM.Guest.Batch.BatchSoundRpmBits
  /-- leanXMSS: a single key is strongly unforgeable, at most `Q / 2^127 + Q · 2^-381` for
  `1 ≤ Q ≤ 2^128` permutation calls (`LeanXmss.lean`). -/
  leanXmss : LeanXmss.Rpm.LeanXmssRpmSecurityStatement
  /-- leanSPHINCS: every deployed lifetime is strongly unforgeable, at most
  `Q / 2^127 + Q · 2^-381` for `1 ≤ Q ≤ 2^128` permutation calls (`LeanSphincs.lean`). -/
  leanSphincs : Sphincs.Lifetimes.RequestedSecurityRpm
  /-- LeanDA is perfectly complete, for every `π` (`LeanDa.lean`). -/
  leanDaComplete : LeanDa.PerfectlyCompleteRpm
  /-- LeanDA is position binding: at most `Q² / 2^256 + Q · 2^-380` for `Q ≤ 2^128`
  (`LeanDa.lean`). -/
  leanDaPositionBinding : LeanDa.PositionBindingRpm
  /-- LeanDA is code binding, under the knowledge soundness of its argument (`LeanDa.lean`). -/
  leanDaCodeBinding : LeanDa.CodeBindingRpm

end Statement

end
