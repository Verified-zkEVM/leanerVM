import LeanVM.E2E.Complete.Rom.CompTags

/-!
# Tests: the honest prover's failure tags (T6-prob, §4.4)

The honest prover with an answering hash fails at a proof-of-work search only where V°'s search
fails on the answers (`honestProverM_grind`), and at the matrices' weights only where the
batching's weights vanish on the answers (`honestProverM_weights`, through
`weightsWith_honestBatchM`); the H-oblivious prover's vanishing weights have at least one and at
most `16` children of the bytecode's shapes (`honestOutN_weights_shaped`). Their statements are
pinned, and they rest on Lean's three axioms.
-/

namespace LeanVMTests.E2E.CompleteRomTags

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Compile.Rom
open LeanVM.Protocol.LeanIsa LeanVM.Node LeanVM.Guest LeanVM.E2E LeanVM.E2E.Complete

example {ρ pfuel : ℕ} {L : Bytes → Option Digest} {T : HonestTree} {P : Prog Bool}
    {S : Strategy} {seed : Digest}
    (h : (honestProverM L ρ pfuel T).run = some (.error (.grind P S seed))) :
    (∃ pi, P = progOf pi) ∧ proveFromM L S pfuel P seed [] = some none :=
  honestProverM_grind h

example {ρ pfuel : ℕ} {L : Bytes → Option Digest} {T : HonestTree} {cs : List ChildClaims}
    (h : (honestProverM L ρ pfuel T).run = some (.error (.weights cs))) :
    cs ≠ [] ∧ ∃ rounds : List (E × E), rounds.length = Nat.log2 End.bytecode.length ∧
      weightsWith L B1.Main.aggSeedD cs rounds = some (0, 0) :=
  honestProverM_weights h

example (L : Bytes → Option Digest) {s0 : Digest} {bc : List K} {cs : List ChildClaims}
    {w : E × E} {h : BatchHints} (hb : honestBatchM (m := Option) L s0 bc cs = some (w, h)) :
    weightsWith L s0 cs h.bytecodeRounds = some w ∧
      h.bytecodeRounds.length = Nat.log2 bc.length :=
  weightsWith_honestBatchM L hb

example (H : Bytes → Digest) {ρ pfuel : ℕ} {T : HonestTree} {cs : List ChildClaims}
    (hρ : validRate ρ) (hk : T.AllNodes HonestTree.KidsLe16)
    (h : honestOutN H ρ pfuel T = .error (.weights cs)) :
    cs ≠ [] ∧ (∀ c ∈ cs, LeanVM.Guest.Batch.ChildShaped End.bytecode c) ∧ cs.length ≤ 16 :=
  honestOutN_weights_children H ρ pfuel hρ hk h

/-- `RomPieces.shaped`'s statement, at the shape `AllNodes KidsLe16`. -/
example {ρ pfuel : ℕ} : validRate ρ → ∀ (H : Bytes → Digest) {T : HonestTree}
    {cs : List ChildClaims}, T.AllNodes HonestTree.KidsLe16 →
      honestOutN H ρ pfuel T = .error (.weights cs) →
        (∀ c ∈ cs, LeanVM.Guest.Batch.ChildShaped End.bytecode c) ∧ cs.length ≤ 16 :=
  honestOutN_weights_shaped

/-- info: 'LeanVM.E2E.Complete.honestProverM_grind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.honestProverM_grind

/-- info: 'LeanVM.E2E.Complete.honestProverM_weights' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.honestProverM_weights

/-- info: 'LeanVM.E2E.Complete.weightsWith_honestBatchM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.weightsWith_honestBatchM

/-- info: 'LeanVM.E2E.Complete.honestOutN_weights_children' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.honestOutN_weights_children

/-- info: 'LeanVM.E2E.Complete.honestOutN_weights_shaped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.Complete.honestOutN_weights_shaped

end LeanVMTests.E2E.CompleteRomTags
