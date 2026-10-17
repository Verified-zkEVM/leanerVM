/-
  LeanerVM.Protocol.Spine.Slots

  The slot of every phase on ArkLib's typed framework, with the error charged to each of its
  challenges, as closed forms of the instance: the typed counterparts of `Spine/Errors.lean`'s
  schedules and errors.
-/

module

public import LeanerVM.Protocol.Spine.Errors
public import LeanerVM.Protocol.ToArkLib.Typed.Schedule

/-!
# Typed slots and errors

Each phase's typed component is at the slot written here (the slot is part of its type), and its
security at the errors written here, the numbers `Spine/Errors.lean` charges the same challenges:

* the bus (`busSlot`, `busErrors`): `(α, β)` at `4·2^{μ_bus}/|E|`, the roots at no error, the
  grand-product argument at its errors from the unit `1/|E|`, the boundary values at no error;
* the table sumcheck (`tableSlot`, `tableErrors`): `ξ` at `(B + 2)/|E|`, the `τ_max` rounds of
  degree `3` at `3/|E|` each, the final values at no error;
* the public input (`pubSlot`, `pubErrors`): the challenge `r` at `1/|E|`, then the values of
  the lines marked `sent`.
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters Interaction Interaction.Oracle Typed
open scoped NNReal

@[expose] public section

variable (I : M3Instance)

/-! ## The bus -/

/-- The bus phase's slot: the fingerprint challenges `(α, β)`, the two roots, the grand-product
argument for the three trees, then the boundary columns' values. -/
abbrev busSlot : Slot :=
  (((drawSlot ((Fin 4 → E) × E)).append (saySlot (E × E))).append (gkrSlot E 3 I.μBus)).append
    (saySlot (Vector E I.busClaims))

/-- The bus phase's errors: `4·2^{μ_bus}` on `(α, β)`, then the grand-product argument's at the
unit `1/|E|`. -/
noncomputable abbrev busErrors : Errors (busSlot I).tree (busSlot I).roles :=
  Errors.append _ _ (Errors.append _ _ (Errors.append (drawSlot ((Fin 4 → E) × E)).tree
    (drawSlot ((Fin 4 → E) × E)).roles (drawErrors _ (overE (4 * 2 ^ I.μBus))) (sayErrors _))
    (gkrErrors E (overE 1) 3 I.μBus)) (sayErrors _)

/-! ## The table sumcheck -/

/-- The table sumcheck's slot: the batching challenge `ξ`, one cubic round per variable, then one
value per column of each sumcheck table. -/
abbrev tableSlot : Slot :=
  ((drawSlot E).append (roundsSlot E 3 I.τmax)).append (saySlot (Vector E I.tableColumns))

/-- The table sumcheck's errors: `B + 2` on `ξ`, `3` per round. -/
noncomputable abbrev tableErrors : Errors (tableSlot I).tree (tableSlot I).roles :=
  Errors.append _ _ (Errors.append _ _ (drawErrors E (overE (I.B + 2))) (roundsErrors E 3 (overE 3)
    I.τmax)) (sayErrors _)

/-! ## The public input -/

/-- The public-input phase's tree: the challenge, then the values sent. -/
abbrev pubTree : Oracle.TypeTree.{0} := .public E fun _ ↦ .public (List E) fun _ ↦ .done

/-- The verifier draws the challenge, the prover sends the values. -/
abbrev pubRoles : pubTree.RoleDecoration := ⟨.receiver, fun _ ↦ ⟨.sender, fun _ ↦ ⟨⟩⟩⟩

/-- The public-input phase's slot: the challenge drawn uniformly, then the values sent. -/
abbrev pubSlot : Slot :=
  ⟨pubTree, pubRoles, ⟨PUnit.unit, fun _ ↦ ⟨PUnit.unit, fun _ ↦ ⟨⟩⟩⟩, ($ᵗ E, fun _ _ ↦ PUnit.unit)⟩

/-- The public-input phase's error: `1/|E|` at the challenge. -/
noncomputable abbrev pubErrors : Errors pubSlot.tree pubSlot.roles :=
  (overE 1, fun _ _ ↦ PUnit.unit)

/-! ## Flock -/

/-- The Flock phase's slot for `2 ^ k` compressions: the `k + 1` coordinates of the point, the 64
values, `z_skip`, `8 + k` zerocheck rounds, the two values `v_a, v_b`, `α_lc`, 8 lincheck
rounds, the 64 values, and the six ring-switching challenges. -/
abbrev flockSlotOf (k : ℕ) : Slot :=
  (((((((((drawsSlot E (k + 1)).append (saySlot (Vector E 64))).append (drawSlot E)).append
    (roundsSlot E 2 8)).append (roundsSlot E 2 k)).append (saySlot (Vector E 2))).append
    (drawSlot E)).append (roundsSlot E 2 8)).append (saySlot (Vector E 64))).append
    (drawsSlot E 6)

/-- The ring-switching challenges' errors: `2^{2^{5−p}−1}` over `|E|` on the `p`-th, that is
`2^31, 2^15, 2^7, 8, 2, 1`. -/
noncomputable abbrev ringErrors : Errors (drawsSlot E 6).tree (drawsSlot E 6).roles :=
  drawsErrorsOf E (fun p ↦ overE (2 ^ (2 ^ (5 - p) - 1))) 6

/-- The Flock phase's errors for `2 ^ k` compressions: `1` on each coordinate of the point, `127`
on `z_skip`, `2` on each within-block and lincheck round, `3` on each batch round and on `α_lc`,
and the ring-switching challenges'. -/
noncomputable abbrev flockErrorsOf (k : ℕ) : Errors (flockSlotOf k).tree (flockSlotOf k).roles :=
  Errors.append _ _ (Errors.append _ _ (Errors.append _ _ (Errors.append _ _ (Errors.append _ _
    (Errors.append _ _ (Errors.append _ _ (Errors.append _ _ (Errors.append _ _
    (drawsErrors E (overE 1) (k + 1)) (sayErrors _)) (drawErrors E (overE 127)))
    (roundsErrors E 2 (overE 2) 8)) (roundsErrors E 2 (overE 3) k)) (sayErrors _))
    (drawErrors E (overE 3))) (roundsErrors E 2 (overE 2) 8)) (sayErrors _)) ringErrors

/-- The Flock slot: the Flock phase for the region's compressions, or nothing. -/
def flockSlotOpt : Option (FlockRegion I.toShape) → Slot
  | none => doneSlot
  | some r => flockSlotOf r.kBatch

/-- The Flock phase's errors on the slot of a region or of none. -/
noncomputable def flockErrorsOpt :
    (o : Option (FlockRegion I.toShape)) → Errors (flockSlotOpt I o).tree (flockSlotOpt I o).roles
  | none => doneErrors
  | some r => flockErrorsOf r.kBatch

/-- The Flock phase's slot. -/
abbrev flockPhaseSlot : Slot := flockSlotOpt I I.flock

/-- The Flock phase's errors. -/
noncomputable abbrev flockErrors : Errors (flockPhaseSlot I).tree (flockPhaseSlot I).roles :=
  flockErrorsOpt I I.flock

end
end LeanerVM.Protocol
