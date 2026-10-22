/-
  LeanerVM.Protocol.Whir.Deployed

  The opening of WHIR at leanVM's parameters: the chain of levels of an admissible stack size and
  rate, each level's parameters in the Johnson regime at its deployed slack, and the opening's
  round-by-round soundness there, with no hypothesis.
-/

module

public import LeanerVM.Protocol.Whir.OpenSound
public import LeanerVM.Protocol.Whir.Johnson
public import LeanerVM.Parameters.Whir

/-!
# The opening at leanVM's parameters

Category B: the ladders of `LeanerVM.Parameters.Whir` (the Rust's `derive_config` at leanVM pin
`a386121f84292f6fa663aaa3e570c15bc0240ea2`) with their slacks, and Annex B's `thm:rbr`.

`chainOf` builds, from the levels of a ladder and their slacks, the chain of levels `whirOpen`
runs (`Ladder`: each level's fold count, rate exponent and query count) together with the
parameters of every level (`Ladder.Pars`): `johnsonPar` at the level's slack, the threshold
`⌈(√ρ + η) n⌉₊`, the pairwise Johnson list bound and Annex B's constant. A level whose numbers do
not fit (`Fits`) leaves no chain; `deployed_isSome` decides that every level of every admissible
ladder fits, so `deployedChain` is total on the window and `deployed_rbrSoundness` is
`whirOpen_rbrSoundness` at leanVM's parameters with no hypothesis. `deployed_vars` checks that
the opening's stack has `μ` variables.
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters LeanerVM.Parameters.Whir

@[expose] public section

namespace Whir

/-- A chain of levels with the parameters of every level. -/
structure Chain where
  /-- The shape of the first level. -/
  sh : Shape
  /-- The variables the first level leaves. -/
  κ : ℕ
  /-- The levels. -/
  ladder : Ladder sh κ
  /-- Their parameters. -/
  pars : ladder.Pars

/-- The chain of the levels on `rem` variables, each with its slack, every level's parameters in the
Johnson regime (`johnsonPar`); `none` if the variables run out before the last level or a level
does not fit. -/
noncomputable def chainOf : ℕ → List (Level × ℚ) → Option Chain
  | _, [] => none
  | rem, [(l, η)] =>
    match rem - l.fold with
    | 0 => none
    | nf + 1 =>
      if h : Fits (nf + 1) l.logInvRate η then
        some ⟨Shape.ofFold l.fold l.logInvRate l.queries, nf + 1, .last _ nf,
          johnsonPar (Shape.ofFold l.fold l.logInvRate l.queries) _ η h⟩
      else none
  | rem, (l, η) :: rest =>
    (chainOf (rem - l.fold) rest).bind fun c ↦
      if h : Fits (Kap c.sh c.κ) l.logInvRate η then
        some ⟨Shape.ofFold l.fold l.logInvRate l.queries, Kap c.sh c.κ, .cons _ c.ladder,
          (johnsonPar (Shape.ofFold l.fold l.logInvRate l.queries) _ η h, c.pars)⟩
      else none

/-- The chain of the ladder of a stack size and rate, at the deployed slacks. -/
noncomputable def deployed (μ logInvRate : ℕ) : Option Chain :=
  (ladder μ logInvRate).bind fun ls ↦ (slacks μ logInvRate).bind fun es ↦
    chainOf μ (ls.zip es)

/-- Every admissible ladder's chain exists and has `μ` variables: one decision on the window. -/
private theorem deployed_any {μ logInvRate : ℕ} (h : Admissible μ logInvRate) :
    (deployed μ logInvRate).any (fun c ↦ c.κ + c.sh.ℓ == μ) := by
  have key : ∀ μ < maxLogStack + 1, ∀ r < maxLogInvRate + 1, Admissible μ r →
      (deployed μ r).any (fun c ↦ c.κ + c.sh.ℓ == μ) := by decide +kernel
  exact key μ (Nat.lt_succ_of_le h.2.1) logInvRate (Nat.lt_succ_of_le h.2.2.2) h

/-- **Every level of every admissible ladder fits** the Johnson regime at its slack. -/
theorem deployed_isSome {μ logInvRate : ℕ} (h : Admissible μ logInvRate) :
    (deployed μ logInvRate).isSome :=
  Option.isSome_of_any (deployed_any h)

/-- The opening's stack has `μ` variables: the first level's folds and the variables it leaves. -/
theorem deployed_vars {μ logInvRate : ℕ} (h : Admissible μ logInvRate) :
    (deployed μ logInvRate).all (fun c ↦ c.κ + c.sh.ℓ == μ) := by
  obtain ⟨c, hc, hp⟩ := (Option.any_eq_true _ _).mp (deployed_any h)
  rw [hc]
  exact hp

/-- The chain at leanVM's parameters, for an admissible stack size and rate. -/
noncomputable def deployedChain (μ logInvRate : ℕ) (h : Admissible μ logInvRate) : Chain :=
  (deployed μ logInvRate).get (deployed_isSome h)

/-- **The opening of WHIR at leanVM's parameters is round-by-round sound for the list relation**,
with no hypothesis: `whirOpen_rbrSoundness` at the deployed chain of an admissible stack size and
rate, every level's list bound and bad-fold bound proved in the Johnson regime at its slack. -/
noncomputable def deployed_rbrSoundness (μ logInvRate : ℕ) (h : Admissible μ logInvRate) :
    Component.Security
      (whirOpen (deployedChain μ logInvRate h).sh (deployedChain μ logInvRate h).κ
        (deployedChain μ logInvRate h).ladder)
      (relOpen ((deployedChain μ logInvRate h).ladder.headPar (deployedChain μ logInvRate h).pars))
      Set.univ
      (openErr (deployedChain μ logInvRate h).ladder (deployedChain μ logInvRate h).pars) :=
  whirOpen_rbrSoundness _ _

end Whir

end

end LeanerVM.Protocol
