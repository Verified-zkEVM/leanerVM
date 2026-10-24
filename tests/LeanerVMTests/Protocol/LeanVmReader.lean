import LeanerVM.Protocol.LeanVmReader
import LeanerVMTests.Protocol.DecodeChain

/-!
# The reader of leanVM's chain histories: tests

On the Rust fixture's history (`LeanerVMTests.Protocol.DecodeChain`):

* the announcement the history opens with is the fixture's sizes, `logMem = 17` and rate `1`, and a
  history shorter than the eight announced scalars announces nothing;
* the roots sit at the reading offsets `[8, 862, 916, 952]`, WHIR starting at reading `844` where
  the walks end the front phases, and the roots there are the roots the walk reads; a history cut
  inside a root carries no root there, so its word is the zero word;
* the levels' positions take `[19, 5, 3, 2]` squeezes, at depths `[15, 14, 13, 12]` and
  `[224, 56, 32, 22]` positions;
* the marked rounds of the compiled schedule, the four levels' query positions, are the rounds after
  the flagged nonce rounds.

A level whose positions take more than `192` bits, or no position, does not fit (`posOk`). The
closed-form error at `2^64` prover queries is below `2^-63`.
-/

namespace LeanerVMTests.Protocol.LeanVmReader

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Protocol LeanerVM.Protocol.Verify
open LeanerVM.Protocol.DecodeChain LeanerVM.Protocol.ProofRoots LeanerVM.Protocol.LeanVmSlots
open LeanerVM.Protocol.LeanVmReader LeanerVM.Protocol.Whir LeanerVM.Protocol.LeanIsa
open LeanerVMTests.Protocol.RustProof LeanerVMTests.Protocol.DecodeChain
open scoped NNReal

/-! ## The window -/

-- Positions of `193` bits, or none, do not fit; `10` positions of `5` bits do.
#guard !posOk (.last (⟨3, 192, 10⟩ : Whir.Shape) 0)
#guard !posOk (.last (⟨3, 1, 0⟩ : Whir.Shape) 3)
#guard posOk (.last (⟨3, 1, 10⟩ : Whir.Shape) 3)

/-! ## The announcement -/

#guard (announcementOf fx.prog hist).map (fun a ↦ (a.1.1.logMem, a.1.2)) == some (17, 1)
#guard (announcementOf fx.prog (hist.take 7)).isNone

/-! ## The roots under the words -/

#guard whirStart readingCounts fx.prog sizes.1 fx.input == 844 && phaseEnds.getLast! == 844
#guard rootOffsets readingCounts fx.prog sizes.1 fx.input shs == [8, 862, 916, 952]
-- The roots at the offsets are the roots the walk reads.
#guard (rootOffsets readingCounts fx.prog sizes.1 fx.input shs).map (rootAt hist) ==
  ((logged.map fun p ↦ p.1.root :: p.1.whir.filterMap (·.root)).getD []).map some
-- A history cut inside level 1's root does not carry it.
#guard (rootAt hist 862).isSome && (rootAt (hist.take 863) 862).isNone

-- The word under a root the history does not carry is the zero word.
example (l : hashSpec.QueryLog) (sh : Whir.Shape) (κ : ℕ) :
    laterWord l sh κ none = ⟨fun _ ↦ Vector.replicate _ 0⟩ := rfl

/-! ## The positions -/

#guard shs.map (fun sh ↦ (sh.msgLog + sh.rate, sh.queries)) ==
  [(15, 224), (14, 56), (13, 32), (12, 22)]
#guard shs.map (fun sh ↦ posSqueezes (sh.msgLog + sh.rate) sh.queries sh.queries) == [19, 5, 3, 2]

/-! ## Marks and nonces -/

/-- The marked rounds of the fixture's compiled schedule, and the rounds after its flagged ones,
with whether the chain's positions fit. -/
def marksAndFlags : List ℕ × List ℕ × Bool :=
  if h : sizes.1.Admissible fx.prog ∧ validRate sizes.2 then
    let I := leanVm fx.prog sizes.1
    let c := leanIsaChain fx.prog sizes.1 h.1 sizes.2 h.2
    ((List.finRange _).filterMap fun k ↦
        if hd : (listBindingSpec I c.sh c.κ c.ladder).dir k = .V_to_P then
          if listBindingMark I c.ladder ⟨k, hd⟩ then some k.val else none
        else none,
      ((List.finRange _).filter fun k ↦ compiledFlags I c k).map (·.val + 1),
      posOk c.ladder)
  else ([], [], false)

-- One marked round per level, each right after a nonce round; the chain's positions fit.
#guard marksAndFlags.1.length == 4 && marksAndFlags.1 == marksAndFlags.2.1 && marksAndFlags.2.2

/-! ## The bound in closed form -/

example : verifierQueriesBound = 13697 := verifierQueriesBound_eq

-- At `2^64` prover queries the error is below `2^-63`: about `2^-64` for the challenges and
-- `2^-126` for collisions and hits.
example : niError εquery 13697 (2 ^ 64) ≤ (2 ^ 63)⁻¹ := by
  rw [← NNReal.coe_le_coe]
  push_cast [niError, hashTerm, εquery]
  norm_num

end LeanerVMTests.Protocol.LeanVmReader
