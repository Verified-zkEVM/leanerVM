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

end
end LeanerVM.Protocol.Typed
