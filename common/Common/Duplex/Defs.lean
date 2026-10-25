import Common.Eager
import Common.Lemmas
import Common.Keccak
import Statement.RandomPermutation

/-!
# A duplex challenge derivation: definitions

A protocol derives the challenges of a root (`chalP`) by a duplex over a random function `F` on
states: from the initial state `x₀ = init (H label)`, the answer `y₀ = F x₀`, then
`y₁ = F (first r y₀)` absorbing the root `r`, then `y_{k+1} = F (next y_k)`, the challenges being
`out y₁, …, out y_n`. This is LeanDA's membership challenges over Keccak-f[1600]
(`membership_challenges`), whose `first`, `next`, `out` read and write lanes of the state.

The **simulator** (`simImpl`) answers `F` for an adversary from a random oracle `G` of the roots
(through `ga r j`, the challenge `j` of root `r`): a fresh query at the state `first r y₀`, or at a
state `next y` registered after programming the answer `y` with the challenge `(r, j)`, is
answered `build (G r j, w)` for a fresh `w`, and every other fresh query uniformly. It records a
*collision* (`bad`) when a fresh answer's capacity (`cap`) is one of the capacities seen so far
or that of the query, which is what can make the derived challenges differ from `G`.
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec

namespace Common.Duplex

theorem ite_pos' {α : Sort*} {c : Prop} [Decidable c] {a b : α} (h : c) :
    (if c then a else b) = a := by simp [h]

theorem ite_neg' {α : Sort*} {c : Prop} [Decidable c] {a b : α} (h : ¬c) :
    (if c then a else b) = b := by simp [h]

variable {Msg Dg St Root Z W Cp : Type} {n : ℕ}

namespace DuplexSpec

variable (D : DuplexSpec Msg Dg St Root Z W Cp n)

/-- The challenge an answer carries. -/
def out (y : St) : Z := (D.build.symm y).1

end DuplexSpec

section Programs

variable [DecidableEq Msg] [DecidableEq St]

/-- An `F` query. -/
abbrev fQ (x : St) : OracleComp (Rom2 Msg Dg St) St :=
  liftM ((Rom2 Msg Dg St).query (.inr (.inr x)))

variable (D : DuplexSpec Msg Dg St Root Z W Cp n)

/-- The challenges of the next `k` answers after the answer `y`. -/
def chainP : ℕ → St → OracleComp (Rom2 Msg Dg St) (List Z)
  | 0, _ => pure []
  | k + 1, y => do
    let y' ← fQ (Dg := Dg) (D.next y)
    let zs ← chainP k y'
    pure (D.out y' :: zs)

/-- **The challenges of a root**, by the duplex over `F`. -/
def chalP (r : Root) : OracleComp (Rom2 Msg Dg St) (List Z) := do
  let iv ← hQ (St := St) D.label
  let y₀ ← fQ (Dg := Dg) (D.init iv)
  let y₁ ← fQ (Dg := Dg) (D.first r y₀)
  let zs ← chainP D (n - 1) y₁
  pure (D.out y₁ :: zs)

end Programs

/-! ## The simulator -/

end Common.Duplex
