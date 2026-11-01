module

public import LeanVM.Cost.Decoder.Da
import all LeanVM.Guest.B1.Main.Interface

/-!
# The guest decoder's compiled chain: the children

A child's statement, read off the coverage table (`kidStmt`), and the child itself (`decKid`, its
proof by the reader `wV`); the coverage marks and counts (`markOf`, `countOf`, `slotOf`,
`segCount`) and the child a mark falls in (`kidOf`, staged: `kidOfStaged`, the count of children
passed to `kidOfAt` and its test a function of its own, `kidOf_eq_staged`).
-/

namespace LeanVM.Cost.Decoder

open LeanVM.Cost LeanVM.Parameters LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.B1.Main
open LeanVM.Protocol.Verifier LeanVM.Node

@[expose] public section

cost_compile markOfC := markOf
cost_compile countOfC := countOf
cost_compile nKidsC := nKids

/-- Whether child `c`'s segment of the running counts ends after the mark `e`. -/
noncomputable def endsAfter (rd : Reader) (σ : Val) (e c : ℕ) : Bool :=
  decide (e < countOf rd σ (c + 1))

/-- The first of children `0 … n - 1` whose segment ends after the mark `e`, or `0`. -/
noncomputable def kidOfAt (rd : Reader) (σ : Val) (e n : ℕ) : ℕ :=
  ((List.range n).find? (endsAfter rd σ e)).getD 0

/-- `kidOf`, staged: the number of children (a logarithm) computed by the caller and passed to
`kidOfAt`, whose spec holds at every count (the kernel then never unfolds the logarithm), the test
by partial application. -/
noncomputable def kidOfStaged (rd : Reader) (σ : Val) (e : ℕ) : ℕ := kidOfAt rd σ e (nKids σ)

theorem kidOf_eq_staged (rd : Reader) (σ : Val) (e : ℕ) : kidOf rd σ e = kidOfStaged rd σ e := by
  unfold kidOf kidOfStaged kidOfAt endsAfter; rfl

cost_rewrite kidOf_eq_staged

cost_compile endsAfterC := endsAfter
cost_compile kidOfAtC := kidOfAt
cost_compile kidOfC := kidOfStaged
cost_compile slotOfC := slotOf
cost_compile segCountC := segCount
set_option maxHeartbeats 4000000 in
cost_compile kidStmtC := kidStmt
cost_compile subArgsC := subArgs
cost_compile decKidC := decKid

end

end LeanVM.Cost.Decoder
