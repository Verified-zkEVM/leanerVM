/-
  LeanVM.Guest.B2C.SemDeployed

  The program logic and the symbolic executor under the deployed semantics of `BLAKE2S` are the
  deployed ones: `LogicB.lean`'s and `ExecB.lean`'s definitions at `blakeDeployed`.
-/

module

public import LeanVM.Guest.ExecB

/-!
# The `B` program logic at the deployed semantics

`LogicB.lean` and `ExecB.lean` restate `Logic.lean` and `Exec.lean` with `S : BlakeSem` a
parameter; at `blakeDeployed` each definition is the deployed one. The B2C layer's `…_deployed`
lemmas rest on these:

* `holdsB_deployed`, `safeB_deployed`, `reachB_deployed` (`LogicB.lean`);
* `Exec.st_holdsB_deployed`, `Exec.atom_holdsB_deployed`, `Exec.followsB_deployed`,
  `Exec.exit_reachedB_deployed`, `Exec.runKB_deployed` (`ExecB.lean`).
-/

namespace LeanVM.Guest

open LeanVM.Parameters LeanVM.Semantics

@[expose] public section

section Logic

variable {κ : ℕ} {prog : Program} {L : MemImage κ}

/-- At the deployed semantics, `HoldsB` is `Logic.lean`'s `Holds`. -/
theorem holdsB_deployed (pc : ℕ) (fp : K) (ins : OInstr) :
    HoldsB blakeDeployed L pc fp ins = Holds L pc fp ins := rfl

/-- At the deployed semantics, `SafeB` is `Logic.lean`'s `Safe`. -/
theorem safeB_deployed (k : ℕ) (r : Regs K) : SafeB blakeDeployed prog L k r = Safe prog L k r := by
  simp only [SafeB, Safe, runB_deployed]

/-- At the deployed semantics, `ReachB` is `Logic.lean`'s `Reach`. -/
theorem reachB_deployed (s t : Regs K) : ReachB blakeDeployed prog L s t = Reach prog L s t := by
  simp only [ReachB, Reach, runB_deployed]

end Logic

namespace Exec

variable {κ : ℕ} {L : MemImage κ} {fp : K}

/-- At the deployed semantics, `St.HoldsB` is `Exec.lean`'s `St.Holds`. -/
theorem st_holdsB_deployed (st : St) : st.HoldsB blakeDeployed L fp = st.Holds L fp := rfl

/-- At the deployed semantics, `Atom.HoldsB` is `Exec.lean`'s `Atom.Holds`. -/
theorem atom_holdsB_deployed (a : Atom) : a.HoldsB blakeDeployed L fp = a.Holds L fp := by
  cases a <;> rfl

/-- At the deployed semantics, `FollowsB` is `Exec.lean`'s `Follows`. -/
theorem followsB_deployed (entry : ℕ) (r : Regs K) (Q : Prop) :
    ∀ its : List Item, FollowsB blakeDeployed L fp entry r Q its = Follows L fp entry r Q its
  | [] => rfl
  | .ins a :: its => by
    simp only [FollowsB, Follows, atom_holdsB_deployed, followsB_deployed entry r Q its]
  | .fact _ :: its => by simp only [FollowsB, Follows, followsB_deployed entry r Q its]
  | .branch oc od of x :: its => by
    simp only [FollowsB, Follows, atom_holdsB_deployed, followsB_deployed entry r Q its]

variable {prog : Program}

/-- At the deployed semantics, `Exit.ReachedB` is `Exec.lean`'s `Exit.Reached`. -/
theorem exit_reachedB_deployed (entry k₀ : ℕ) (x : Exit) (k : ℕ) :
    x.ReachedB blakeDeployed L fp prog entry k₀ k = x.Reached L fp prog entry k₀ k := by
  simp only [Exit.ReachedB, Exit.Reached, safeB_deployed]

/-- At the deployed semantics, `RunKB` is `Exec.lean`'s `RunK`. -/
theorem runKB_deployed (entry k₀ : ℕ) (Q : ℕ → Prop) :
    ∀ (its : List Item) (k : ℕ),
      RunKB blakeDeployed L fp prog entry k₀ Q its k = RunK L fp prog entry k₀ Q its k
  | [], _ => rfl
  | .ins a :: its, k => by
    simp only [RunKB, RunK, atom_holdsB_deployed, runKB_deployed entry k₀ Q its]
  | .fact a :: its, k => by
    simp only [RunKB, RunK, atom_holdsB_deployed, runKB_deployed entry k₀ Q its]
  | .branch oc od of x :: its, k => by
    simp only [RunKB, RunK, atom_holdsB_deployed, exit_reachedB_deployed,
      runKB_deployed entry k₀ Q its]

end Exec

end
end LeanVM.Guest
