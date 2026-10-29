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
* the marked rounds of the chain's levels, their query positions, are the rounds after the flagged
  nonce rounds, one a level; in the compiled schedule, after the front and WHIR's first round
  polynomial, level 0's positions are marked and its nonce flagged.

The checks on the history run in one guard. A level whose positions take more than `192` bits, or
no position, does not fit (`posOk`). The closed-form error at `2^64` prover queries is below
`2^-63`.
-/

namespace LeanerVMTests.Protocol.LeanVmReader

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Protocol LeanerVM.Protocol.Verify
open LeanerVM.Protocol.DecodeChain LeanerVM.Protocol.ProofRoots LeanerVM.Protocol.LeanVmSlots
open LeanerVM.Protocol.LeanVmReader LeanerVM.Protocol.Whir LeanerVM.Protocol.LeanIsa
open LeanerVMTests.Protocol.RustProof LeanerVMTests.Protocol.DecodeChain StepSchedule
open scoped NNReal

/-! ## The window -/

-- Positions of `193` bits, or none, do not fit; `10` positions of `5` bits do.
#guard !posOk (.last (⟨3, 192, 10⟩ : Whir.Shape) 0)
#guard !posOk (.last (⟨3, 1, 0⟩ : Whir.Shape) 3)
#guard posOk (.last (⟨3, 1, 10⟩ : Whir.Shape) 3)

/-! ## The history -/

/-- The marked rounds of the fixture's chain of levels, and the rounds after its flagged ones, with
whether its positions fit; and, at rounds `281` and `282` of the compiled schedule, the mark and
the flag. -/
def marksAndFlags : List ℕ × List ℕ × Bool × List (Bool × Bool) :=
  if h : sizes.1.Admissible fx.prog ∧ validRate sizes.2 then
    let I := leanVm fx.prog sizes.1
    let c := leanIsaChain fx.prog sizes.1 h.1 sizes.2 h.2
    ((List.finRange _).filterMap fun k ↦
        if hd : (seqSpec c.ladder.steps).dir k = .V_to_P then
          if c.ladder.mark ⟨k, hd⟩ then some k.val else none
        else none,
      ((List.finRange _).filter fun k ↦ (ladderFlags c.ladder).toFlags k).map (·.val + 1),
      posOk c.ladder,
      ((List.finRange _).filter fun k ↦ k.val == 281 || k.val == 282).map fun k ↦
        ((if hd : (listBindingSpec I c.sh c.κ c.ladder).dir k = .V_to_P then
          listBindingMark I c.ladder ⟨k, hd⟩ else false), compiledFlags I c k))
  else ([], [], false, [])

/-- Every check on the history, named. -/
def results : List (String × Bool) :=
  [("announcement", (announcementOf fx.prog hist).map (fun a ↦ (a.1.1.logMem, a.1.2)) ==
      some (17, 1)),
    ("short announcement", (announcementOf fx.prog (hist.take 7)).isNone),
    ("whir start", whirStart readingCounts fx.prog sizes.1 fx.input == 844 &&
      phaseEnds.getLast! == 844),
    ("root offsets", rootOffsets readingCounts fx.prog sizes.1 fx.input shs == [8, 862, 916, 952]),
    -- The roots at the offsets are the roots the walk reads.
    ("roots", (rootOffsets readingCounts fx.prog sizes.1 fx.input shs).map (rootAt hist) ==
      ((logged.map fun p ↦ p.1.root :: p.1.whir.filterMap (·.root)).getD []).map some),
    -- A history cut inside level 1's root does not carry it.
    ("cut root", (rootAt hist 862).isSome && (rootAt (hist.take 863) 862).isNone),
    ("positions", shs.map (fun sh ↦ (sh.msgLog + sh.rate, sh.queries)) ==
      [(15, 224), (14, 56), (13, 32), (12, 22)]),
    ("squeezes", shs.map (fun sh ↦ posSqueezes (sh.msgLog + sh.rate) sh.queries sh.queries) ==
      [19, 5, 3, 2]),
    -- One marked round per level, each right after a nonce round; the chain's positions fit; in
    -- the compiled schedule, round 281 is level 0's nonce and round 282 its positions.
    ("marks", marksAndFlags.1 == [30, 55, 76, 89] && marksAndFlags.1 == marksAndFlags.2.1 &&
      marksAndFlags.2.2.1 && marksAndFlags.2.2.2 == [(false, true), (true, false)])]

#guard (results.filter (!·.2)).map (·.1) == []

-- The word under a root the history does not carry is the zero word.
example (l : hashSpec.QueryLog) (sh : Whir.Shape) (κ : ℕ) :
    laterWord l sh κ none = ⟨fun _ ↦ Vector.replicate _ 0⟩ := rfl

/-! ## The bound in closed form -/

example : verifierQueriesBound = 13697 := verifierQueriesBound_eq

-- At `2^64` prover queries the error is below `2^-63`: about `2^-64` for the challenges and
-- `2^-126` for collisions and hits.
example : niError εquery 13697 (2 ^ 64) ≤ (2 ^ 63)⁻¹ := by
  rw [← NNReal.coe_le_coe]
  push_cast [niError, hashTerm, εquery]
  norm_num

end LeanerVMTests.Protocol.LeanVmReader
