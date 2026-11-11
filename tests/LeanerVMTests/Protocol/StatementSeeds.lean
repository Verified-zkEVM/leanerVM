import LeanerVM.Protocol.StatementSeeds
import LeanerVMTests.Protocol.Proof

/-!
# The statements a log opens: tests

* **The program-hash slot.** A seed's preimage carries its program hash in its last 32 bytes. A
  preimage asked before its program's bytes makes the answer to the program's bytes a hit, which
  the halves of the inputs alone do not show: the slot is what keeps a later answer from
  completing a statement whose seed was asked out of order, the case `stmtOf_append` needs.
* **A logged seed.** The three seed hashes of the test statement, answered by `d 1`, `d 2` and
  `d 3`, open the statement at `d 3` (`stmtOf_eq_of_seedLogged`), and nothing at the preimage's
  answer `d 2`, which answers no 64-byte input; without the first state's query nothing opens.
-/

namespace LeanerVMTests.Protocol.StatementSeeds

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Protocol LeanerVM.Protocol.Blake2sHash
open LeanerVMTests.Protocol.Proof (program input)

/-- A digest with first word `n`. -/
def d (n : UInt32) : Digest := #v[n, 0, 0, 0, 0, 0, 0, 0]

/-! ## The program-hash slot -/

/-- A seed's preimage of `d 1`, then the program's bytes answered by `d 1`. -/
def slotLog : hashSpec.QueryLog := [⟨seedPreimageOf (d 1), d 2⟩, ⟨programBytes program, d 1⟩]

#guard programHashSlot (seedPreimageOf (d 1)) == [d 1]
#guard programHashSlot (programBytes program) == []
#guard decide (QueryLog.HasHit (inPlay []) slotLog)
#guard !decide (QueryLog.HasHit (fun l ↦ l.flatMap fun e ↦ halves e.1) slotLog)

/-! ## A logged seed -/

/-- The test statement's three seed hashes, answered by `d 1`, `d 2` and `d 3`. -/
def seedLog : hashSpec.QueryLog :=
  [⟨programBytes program, d 1⟩, ⟨seedPreimageOf (d 1), d 2⟩, ⟨seedInput (d 2) input, d 3⟩]

theorem seedLog_noCollision : ¬ QueryLog.HasCollision seedLog := by
  rintro ⟨e₁, h₁, e₂, h₂, hne, heq⟩
  simp only [seedLog, List.mem_cons, List.not_mem_nil, or_false] at h₁ h₂
  rcases h₁ with rfl | rfl | rfl <;> rcases h₂ with rfl | rfl | rfl <;>
    first | exact hne rfl | exact absurd heq (by decide)

/-- The first state's answer opens the test statement. -/
theorem stmtOf_seedLog : stmtOf seedLog (d 3) = some (program, input) :=
  stmtOf_eq_of_seedLogged seedLog_noCollision ⟨d 1, d 2, List.mem_cons_self,
    List.mem_cons_of_mem _ List.mem_cons_self,
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)⟩

/-- The preimage's answer opens nothing: no 64-byte input of the log is answered by it. -/
theorem stmtOf_seedLog_preimage : stmtOf seedLog (d 2) = none :=
  stmtOf_eq_none fun st ⟨_, iv, _, _, h₃⟩ ↦ by
    simp only [seedLog, List.mem_cons, List.not_mem_nil, or_false] at h₃
    rcases h₃ with h | h | h
    · exact absurd (congrArg Sigma.snd h) (show d 2 ≠ d 1 by decide)
    · have := congrArg (fun e ↦ e.1.length) h
      simp only [length_seedInput, length_seedPreimageOf] at this
      omega
    · exact absurd (congrArg Sigma.snd h) (show d 2 ≠ d 3 by decide)

/-- Without the first state's query the log opens nothing at `d 3`. -/
theorem stmtOf_seedLog_take : stmtOf (seedLog.take 2) (d 3) = none :=
  stmtOf_eq_none fun st ⟨_, _, _, _, h₃⟩ ↦ by
    simp only [seedLog, List.take_succ_cons, List.take_zero, List.mem_cons, List.not_mem_nil,
      or_false] at h₃
    rcases h₃ with h | h
    · exact absurd (congrArg Sigma.snd h) (show d 3 ≠ d 1 by decide)
    · exact absurd (congrArg Sigma.snd h) (show d 3 ≠ d 2 by decide)

end LeanerVMTests.Protocol.StatementSeeds
