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
`⌈(√ρ + η) n⌉₊`, the pairwise Johnson list bound and Annex B's constant rounded up
(`mcaCount`), every number computed, so the chain is data. A level whose numbers do not fit
(`Fits`) leaves no chain; `deployed_isSome` decides that every level of every admissible ladder
fits, so `deployedChain` is total on the window and `deployed_rbrSoundness` is
`whirOpen_rbrSoundness` at leanVM's parameters with no hypothesis. `deployed_vars` checks that
the opening's stack has `μ` variables. Level 0 is also computed on its own (`deployedHeadShape`,
`deployedHeadKap`, `deployedHeadThreshold`), and `deployedChain_head` decides that the chain's
level 0 is that one.
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
def chainOf : ℕ → List (Level × ℚ) → Option Chain
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
def deployed (μ logInvRate : ℕ) : Option Chain :=
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
def deployedChain (μ logInvRate : ℕ) (h : Admissible μ logInvRate) : Chain :=
  (deployed μ logInvRate).get (deployed_isSome h)

/-- **The opening of WHIR at leanVM's parameters is round-by-round sound for the list relation**,
with no hypothesis: `whirOpen_rbrSoundness` at the deployed chain of an admissible stack size and
rate, every level's list bound and bad-fold bound proved in the Johnson regime at its slack. -/
def deployed_rbrSoundness (μ logInvRate : ℕ) (h : Admissible μ logInvRate) :
    Component.Security
      (whirOpen (deployedChain μ logInvRate h).sh (deployedChain μ logInvRate h).κ
        (deployedChain μ logInvRate h).ladder)
      (relOpen ((deployedChain μ logInvRate h).ladder.headPar (deployedChain μ logInvRate h).pars))
      Set.univ
      (openErr (deployedChain μ logInvRate h).ladder (deployedChain μ logInvRate h).pars) :=
  whirOpen_rbrSoundness _ _

/-! ## Level 0 of the deployed chain -/

/-- Level 0 of the ladder of a stack size and rate, with its slack. -/
def deployedLevel0 (μ r : ℕ) : Level × ℚ :=
  (((ladder μ r).getD []).zip ((slacks μ r).getD [])).headD (⟨1, 1, 1⟩, 1)

/-- The shape of level 0. -/
def deployedHeadShape (μ r : ℕ) : Shape :=
  Shape.ofFold (deployedLevel0 μ r).1.fold (deployedLevel0 μ r).1.logInvRate
    (deployedLevel0 μ r).1.queries

/-- The variables level 0 leaves. -/
def deployedHeadKap (μ r : ℕ) : ℕ := μ - (deployedLevel0 μ r).1.fold

/-- The threshold of level 0. -/
def deployedHeadThreshold (μ r : ℕ) : ℕ :=
  threshold (deployedHeadKap μ r) (deployedHeadShape μ r).R (deployedLevel0 μ r).2

/-- The chain's level 0 matches the computed one, as a check. -/
private def headMatches (μ r : ℕ) (c : Chain) : Bool :=
  c.sh.lm1 == (deployedHeadShape μ r).lm1 && c.sh.R == (deployedHeadShape μ r).R &&
    c.sh.t == (deployedHeadShape μ r).t && c.κ == deployedHeadKap μ r &&
    (c.ladder.headPar c.pars).a == deployedHeadThreshold μ r

/-- Every admissible chain's level 0 is the computed one: one decision on the window. -/
private theorem deployed_head {μ r : ℕ} (h : Admissible μ r) :
    (deployed μ r).all (headMatches μ r) := by
  have key : ∀ μ < maxLogStack + 1, ∀ r < maxLogInvRate + 1, Admissible μ r →
      (deployed μ r).all (headMatches μ r) := by decide +kernel
  exact key μ (Nat.lt_succ_of_le h.2.1) r (Nat.lt_succ_of_le h.2.2.2) h

/-- A property every member of `deployed` has, the deployed chain has. -/
private theorem deployedChain_of_all {μ r : ℕ} (h : Admissible μ r) {p : Chain → Bool}
    (hp : (deployed μ r).all p) : p (deployedChain μ r h) :=
  (Option.all_eq_true_iff_get p _).mp hp (deployed_isSome h)

/-- Shapes with equal fields are equal. -/
private theorem shape_ext {a b : Shape} (h₁ : a.lm1 = b.lm1) (h₂ : a.R = b.R) (h₃ : a.t = b.t) :
    a = b := by
  cases a
  cases b
  simp_all

/-- **Level 0 of the deployed chain** is the computed one: its shape, the variables it leaves and
its threshold. -/
theorem deployedChain_head {μ r : ℕ} (h : Admissible μ r) :
    (deployedChain μ r h).sh = deployedHeadShape μ r ∧
      (deployedChain μ r h).κ = deployedHeadKap μ r ∧
      ((deployedChain μ r h).ladder.headPar (deployedChain μ r h).pars).a =
        deployedHeadThreshold μ r := by
  have hm := deployedChain_of_all h (deployed_head h)
  simp only [headMatches, Bool.and_eq_true, beq_iff_eq] at hm
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hm
  exact ⟨shape_ext h1 h2 h3, h4, h5⟩

/-- The deployed chain's stack has `μ` variables. -/
theorem deployedChain_height {μ r : ℕ} (h : Admissible μ r) :
    (deployedChain μ r h).κ + (deployedChain μ r h).sh.ℓ = μ := by
  have := deployedChain_of_all h (deployed_vars h)
  simpa using this

/-- Level 0's stack has `μ` variables: the computed fold and the variables it leaves. -/
theorem deployedHead_height {μ r : ℕ} (h : Admissible μ r) :
    deployedHeadKap μ r + (deployedHeadShape μ r).ℓ = μ := by
  rw [← (deployedChain_head h).1, ← (deployedChain_head h).2.1]
  exact deployedChain_height h

end Whir

end

end LeanerVM.Protocol
