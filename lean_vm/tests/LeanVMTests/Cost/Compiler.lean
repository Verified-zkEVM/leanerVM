import LeanVM.Cost.Compiler

/-!
# Tests: the compiler on small functions

`cost_compile` compiles a definition, a caller of it, and two recursive functions (on `ℕ` and on
lists); the specs are kernel-checked, with Lean's three axioms, and the assembled program computes
the functions' values.
-/

namespace LeanVMTests.Cost

open LeanVM.Cost

def double (n : ℕ) : ℕ := n + n
cost_compile double at 1

def quad (n : ℕ) : ℕ := double (double n)
cost_compile quad at 2

def sumTo : ℕ → ℕ
  | 0 => 0
  | n + 1 => (n + 1) + sumTo n
cost_compile sumTo at 3 measure fun n ↦ n

def len : List ℕ → ℕ
  | [] => 0
  | _ :: xs => len xs + 1
cost_compile len at 4 measure fun l ↦ l.length

/-- The program: the four bodies at their indices. -/
def toyProgram : Program :=
  #[.val (.nat 0), double.costBody, quad.costBody, sumTo.costBody, len.costBody]

#guard (evalBody toyProgram 10 2 [Enc.enc (5 : ℕ)]).map (·.1) == some (Enc.enc (quad 5))
#guard (evalBody toyProgram 20 3 [Enc.enc (10 : ℕ)]).map (·.1) == some (Enc.enc (sumTo 10))
#guard (evalBody toyProgram 20 4 [Enc.enc [1, 2, 3]]).map (·.1) == some (Enc.enc (3 : ℕ))

-- The program holds the bodies the specs need.
example : Includes toyProgram [(3, sumTo.costBody)] := by
  intro p hp; simp at hp; subst hp; rfl

/-- info: 'LeanVMTests.Cost.sumTo.costSpec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sumTo.costSpec

end LeanVMTests.Cost
