/-
  LeanerVM.Protocol.ToArkLib.Typed.Schedule

  The slots of the typed components and their errors, as closed forms: a sumcheck round, a
  sequence of rounds, a sequence of challenges. Candidate for ArkLib.
-/

module

public import LeanerVM.Protocol.ToArkLib.Typed.Append
public import LeanerVM.Protocol.ToArkLib.Typed.PassThrough
public import LeanerVM.Protocol.ToArkLib.Typed.SampleChallenge
public import LeanerVM.Protocol.ToArkLib.Typed.SendChecked

/-!
# Typed slots and their errors

The typed counterparts of `ToArkLib/Schedule.lean`'s schedules, as slots built from the
one-message and one-challenge slots in sequence, each with the errors the legacy schedule
charges:

* `roundSlot C d`: a sumcheck round, the `d + 1` coefficients then one challenge;
* `roundsSlot C d m`: `m` rounds, `roundsErrors C d e m` charging `e` per challenge;
* `drawsSlot C k`: `k` challenges, `drawsErrors C e k` charging `e` each.

A component built by appending components at these slots has the slot in its type by the
definitions alone, as the legacy components have their schedules.
-/

namespace LeanerVM.Protocol.Typed

open Interaction Interaction.Oracle
open scoped NNReal

@[expose] public section

variable (C : Type) [SampleableType C]

/-- A sumcheck round of degree `d`: the coefficients, then the challenge. -/
abbrev roundSlot (d : ℕ) : Slot := (saySlot (Vector C (d + 1))).append (drawSlot C)

/-- The error `e` on a round's challenge. -/
abbrev roundErrors (d : ℕ) (e : ℝ≥0) : Errors (roundSlot C d).tree (roundSlot C d).roles :=
  Errors.append (sayTree (Vector C (d + 1))) (sayRoles _) (sayErrors _) (drawErrors C e)

/-- `m` sumcheck rounds of degree `d`. -/
def roundsSlot (d : ℕ) : ℕ → Slot
  | 0 => doneSlot
  | m + 1 => (roundSlot C d).append (roundsSlot d m)

/-- The error `e` on each round's challenge. -/
def roundsErrors (d : ℕ) (e : ℝ≥0) : (m : ℕ) → Errors (roundsSlot C d m).tree (roundsSlot C d m).roles
  | 0 => doneErrors
  | m + 1 => Errors.append (roundSlot C d).tree (roundSlot C d).roles (roundErrors C d e)
      (roundsErrors d e m)

/-- `k` challenges. -/
def drawsSlot : ℕ → Slot
  | 0 => doneSlot
  | k + 1 => (drawsSlot k).append (drawSlot C)

/-- The error `e` on each challenge. -/
def drawsErrors (e : ℝ≥0) : (k : ℕ) → Errors (drawsSlot C k).tree (drawsSlot C k).roles
  | 0 => doneErrors
  | k + 1 => Errors.append (drawsSlot C k).tree (drawsSlot C k).roles (drawsErrors e k)
      (drawErrors C e)

/-- Each round's error at most another's makes the rounds' errors at most theirs. -/
theorem roundsErrors_le (d : ℕ) {e e' : ℝ≥0} (h : e ≤ e') : (m : ℕ) →
    Errors.Le (roundsSlot C d m).tree (roundsSlot C d m).roles (roundsErrors C d e m)
      (roundsErrors C d e' m)
  | 0 => trivial
  | m + 1 => Errors.Le.append (roundSlot C d).tree (roundSlot C d).roles
      (Errors.Le.append (sayTree _) (sayRoles _) (Errors.Le.refl _ _ _) ⟨h, fun _ ↦ trivial⟩)
      (roundsErrors_le d h m)

/-- Each challenge's error at most another's makes the challenges' errors at most theirs. -/
theorem drawsErrors_le {e e' : ℝ≥0} (h : e ≤ e') : (k : ℕ) →
    Errors.Le (drawsSlot C k).tree (drawsSlot C k).roles (drawsErrors C e k) (drawsErrors C e' k)
  | 0 => trivial
  | k + 1 => Errors.Le.append (drawsSlot C k).tree (drawsSlot C k).roles (drawsErrors_le h k)
      ⟨h, fun _ ↦ trivial⟩

/-! ## The grand-product argument -/

/-- One layer of the grand-product argument over `nside` trees, radix `2 ^ ρ`, at depth `m`: the
combiner, `m` rounds on a cofactor of degree `2 ^ ρ`, each tree's `2 ^ ρ` values at the
descendants, and the `ρ` combination challenges. -/
abbrev stepSlot (nside ρ m : ℕ) : Slot :=
  (((drawSlot C).append (roundsSlot C (2 ^ ρ) m)).append
    (saySlot (Fin nside → Vector C (2 ^ ρ)))).append (drawsSlot C ρ)

/-- The error of one layer, with the combiner's error given: `2 ^ ρ · u` on each round and `u`
on each combination challenge. -/
abbrev stepErrors (nside ρ m : ℕ) (combiner u : ℝ≥0) :
    Errors (stepSlot C nside ρ m).tree (stepSlot C nside ρ m).roles :=
  Errors.append _ _ (Errors.append _ _ (Errors.append (drawSlot C).tree (drawSlot C).roles
    (drawErrors C combiner) (roundsErrors C (2 ^ ρ) (((2 ^ ρ : ℕ) : ℝ≥0) * u) m))
    (sayErrors _)) (drawsErrors C u ρ)

/-- `k` layers of radix four from depth `m`. -/
def stepsSlot (nside : ℕ) : ℕ → ℕ → Slot
  | 0, _ => doneSlot
  | k + 1, m => (stepSlot C nside 2 m).append (stepsSlot nside k (m + 2))

/-- The error of `k` layers of radix four: `(nside − 1) · u` on each combiner. -/
def stepsErrors (nside : ℕ) (u : ℝ≥0) :
    (k m : ℕ) → Errors (stepsSlot C nside k m).tree (stepsSlot C nside k m).roles
  | 0, _ => doneErrors
  | k + 1, m => Errors.append (stepSlot C nside 2 m).tree (stepSlot C nside 2 m).roles
      (stepErrors C nside 2 m (((nside - 1 : ℕ) : ℝ≥0) * u) u) (stepsErrors nside u k (m + 2))

/-- The binary layer at the roots, present when `μ` is odd (`r = μ mod 2`). -/
def oddSlot (nside : ℕ) : ℕ → Slot
  | 0 => doneSlot
  | _ + 1 => stepSlot C nside 1 0

/-- The error of the binary layer. -/
def oddErrors (nside : ℕ) (u : ℝ≥0) :
    (r : ℕ) → Errors (oddSlot C nside r).tree (oddSlot C nside r).roles
  | 0 => doneErrors
  | _ + 1 => stepErrors C nside 1 0 (((nside - 1 : ℕ) : ℝ≥0) * u) u

/-- The grand-product argument for `nside` trees of `2 ^ μ` leaves, from the roots down: one
binary layer first when `μ` is odd, then layers of radix four. -/
abbrev gkrSlot (nside μ : ℕ) : Slot := (oddSlot C nside (μ % 2)).append (stepsSlot C nside (μ / 2) (μ % 2))

/-- The error of the grand-product argument: `(nside − 1) · u` on each combiner, `2 ^ ρ · u` on
each round of radix `2 ^ ρ`, `u` on each combination challenge. -/
abbrev gkrErrors (u : ℝ≥0) (nside μ : ℕ) :
    Errors (gkrSlot C nside μ).tree (gkrSlot C nside μ).roles :=
  Errors.append (oddSlot C nside (μ % 2)).tree (oddSlot C nside (μ % 2)).roles
    (oddErrors C nside u (μ % 2)) (stepsErrors C nside u (μ / 2) (μ % 2))

end
end LeanerVM.Protocol.Typed
