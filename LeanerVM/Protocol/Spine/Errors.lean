/-
  LeanerVM.Protocol.Spine.Errors

  The schedule and the error of every slot of the protocol, as closed forms of the instance, and
  the error of the whole protocol with its bound at admissible sizes.
-/

module

public import LeanerVM.Protocol.Spine.Instance
public import LeanerVM.Protocol.ToArkLib.Schedule
public import LeanerVM.Protocol.ToArkLib.SendOracle

/-!
# Schedules and errors

The protocol is `commit ⟫ bus ⟫ table ⟫ pub ⟫ flock ⟫ opening`. This module fixes, for each of
the six slots, the message schedule (`commitSpec`, `busSpec`, `tableSpec`, `pubSpec`,
`flockSpec`, `openingSpec`) and, for the five after the commit, the knowledge error charged to
each challenge (`busError` … `openingError`), all as closed forms of the instance's sizes, from
the generic schedules of `LeanerVM.Protocol.ToArkLib.Schedule` at the challenge field `E`. A
phase fills its slot only at that schedule and that error: no phase declares its own, since a
declared error of `1` would let a phase that checks nothing be knowledge sound. `piopSpec` and
`piopError` are the six side by side, and `piopError_le` bounds the sum of the errors at the
sizes the leanISA instance meets.

The schedules, at leanVM `a386121f84292f6fa663aaa3e570c15bc0240ea2`:

* The commit: the stack, as one message.
* The bus (§5.2–§5.4, `crates/lean_vm/src/leaf.rs:864-935`, `gkr.rs:247-430`): the fingerprint
  challenges `(α, β)`, one draw here and five scalars on the wire; the two roots `(R, R_c)`; the
  grand-product argument for the three trees, radix four from the roots down with one binary
  layer first when `μ_bus` is odd: each layer draws a combiner `λ`, runs one normalized sumcheck
  round per variable of the layer (the cofactor's coefficients, low degree first, then the
  challenge), sends each tree's values at the descendants, and draws the combination challenges
  one by one; a last combiner, read by nothing, follows the last layer; then the boundary
  columns' values.
* The table sumcheck (§5.5, `cpu/mod.rs:726-743`, `constraints.rs:243-291`): the batching
  challenge `ξ`; one round per variable, highest first, of a cubic's four coefficients and a
  challenge; then one value per column of each sumcheck table, table by table.
* The public input (§8.2): the challenge `r`, then the values of the lines marked `sent`.
* Flock (Annex C; `crates/flock/src/hash.rs:983-1010`, `zerocheck.rs:350-430`,
  `lincheck.rs:1137-1216`; `python-verifier/verifier.py:1135-1310`), with `k = kBatch`: the
  `k + 1` sampled coordinates of the point; the 64 values; the challenge `z_skip`; `8 + k`
  zerocheck rounds of three coefficients and a challenge; the two values `v_a, v_b` (the third,
  `v_c`, both verifiers derive from the running claim); the challenge `α_lc`; 8 lincheck rounds;
  the 64 values; the six challenges of the ring switching, which the Python draws after the
  lincheck (`verifier.py:1338-1347`) and the Rust inside the stacked opener (`pcs.rs:128`). An
  instance with no Flock region has an empty slot.
* The opening (§8.5): the batching challenge `λ`, then one oracle query, which is no message.

The oracle protocol sends every coefficient of a round polynomial and its verifier checks each
round; the compiled verifier reads one coefficient less per round and derives it.

The errors, per challenge, over `|E|`: the bus `4·2^{μ_bus}` on `(α, β)` (Theorem 5.1),
`nside − 1 = 2` on each combiner but the last (`0`), `4` on each radix-four round and `2` on a
binary one, `1` on each combination challenge; the table `B + 2` on `ξ`, the degree of the batch
in `ξ`, one less than the specification's count of its powers (§5.5 charges `nside + B`), and
`3` per round; the public input `1`; Flock `1` on each coordinate of the point, `127` on
`z_skip`, `2` on each zerocheck round and `1` more on the last `k`, `3` on `α_lc`, `2` on each
lincheck round, `2^{2^{5−p}−1}` on the `p`-th ring-switching challenge; the opening `J − 1` on
`λ`, `J` the number of pooled claims.
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters OracleComp OracleSpec ProtocolSpec
open scoped NNReal

@[expose] public section

/-! ## Errors as fractions of `|E|` -/

/-- `c / |E|`. -/
noncomputable def overE (c : ℕ) : ℝ≥0 := (c : ℝ≥0) / (Fintype.card E : ℝ≥0)

theorem overE_add (a b : ℕ) : overE (a + b) = overE a + overE b := by
  simp only [overE, Nat.cast_add, add_div]

theorem overE_mono {a b : ℕ} (h : a ≤ b) : overE a ≤ overE b := by
  unfold overE
  exact div_le_div_of_nonneg_right (Nat.cast_le.mpr h) (by positivity)

theorem nat_mul_overE (n c : ℕ) : (n : ℝ≥0) * overE c = overE (n * c) := by
  simp only [overE, Nat.cast_mul]
  ring

/-- The unit `overE 1` is `1 / |E|` with `|E|` counted by `Nat.card`, the form of a generic
component's error. -/
theorem overE_one : overE 1 = (1 / Nat.card E : ℝ≥0) := by
  rw [overE, Nat.card_eq_fintype_card, Nat.cast_one]

/-! ## The six slots -/

variable (I : M3Instance)

/-- The commit: the stack, as one message. -/
abbrev commitSpec : ProtocolSpec 1 := Component.sendSpec (Column I.μ)

/-- The commit has no challenge. -/
def commitError : (commitSpec I).ChallengeIdx → ℝ≥0 := fun _ ↦ 0

/-- The number of rounds of the bus phase. -/
abbrev busRounds : ℕ := 1 + 1 + gkrRounds I.μBus + 1

/-- The bus phase: the fingerprint challenges `(α, β)`, the two roots, the grand-product
argument for the three trees, then the boundary columns' values. -/
def busSpec : ProtocolSpec (busRounds I) :=
  draw ((Fin 4 → E) × E) ++ₚ say (E × E) ++ₚ gkrSpec E 3 I.μBus ++ₚ say (Vector E I.busClaims)

/-! The instances of the bus phase's prefixes, which the phase built one append at a time meets. -/

instance instOracleInterfaceBusRoots :
    ∀ i, OracleInterface ((draw ((Fin 4 → E) × E) ++ₚ say (E × E)).Message i) :=
  msgAppend (instOracleInterfaceDraw _) (instOracleInterfaceSay _)

instance instSampleableTypeBusRoots :
    ∀ i, SampleableType ((draw ((Fin 4 → E) × E) ++ₚ say (E × E)).Challenge i) :=
  chalAppend (instSampleableTypeDraw _) (instSampleableTypeSay _)

instance instOracleInterfaceBusGkr :
    ∀ i, OracleInterface
      ((draw ((Fin 4 → E) × E) ++ₚ say (E × E) ++ₚ gkrSpec E 3 I.μBus).Message i) :=
  msgAppend instOracleInterfaceBusRoots (instOracleInterfaceGkr E 3 I.μBus)

instance instSampleableTypeBusGkr :
    ∀ i, SampleableType
      ((draw ((Fin 4 → E) × E) ++ₚ say (E × E) ++ₚ gkrSpec E 3 I.μBus).Challenge i) :=
  chalAppend instSampleableTypeBusRoots (instSampleableTypeGkr E 3 I.μBus)

instance instOracleInterfaceBus : ∀ i, OracleInterface ((busSpec I).Message i) :=
  msgAppend (instOracleInterfaceBusGkr I) (instOracleInterfaceSay _)

instance instSampleableTypeBus : ∀ i, SampleableType ((busSpec I).Challenge i) :=
  chalAppend (instSampleableTypeBusGkr I) (instSampleableTypeSay _)

/-- The bus phase's error: `4·2^{μ_bus}` on `(α, β)`, then the grand-product argument's. -/
noncomputable def busError : (busSpec I).ChallengeIdx → ℝ≥0 :=
  errAppend (errAppend (errAppend (drawError _ (overE (4 * 2 ^ I.μBus))) (sayError _))
    (gkrError E (overE 1) 3 I.μBus)) (sayError _)

private theorem sum_busError_le :
    ∑ i, busError I i ≤ overE (4 * 2 ^ I.μBus + ((I.μBus + 1) * 2 + 2 * I.μBus * I.μBus +
      3 * I.μBus + 3)) := by
  unfold busError
  show ∑ i : (draw ((Fin 4 → E) × E) ++ₚ say (E × E) ++ₚ gkrSpec E 3 I.μBus ++ₚ
    say (Vector E I.busClaims)).ChallengeIdx, _ ≤ _
  rw [sum_errAppend, sum_errAppend, sum_errAppend, sum_drawError, sum_sayError, sum_sayError,
    add_zero, add_zero, overE_add]
  refine add_le_add le_rfl ((sum_gkrError_le E (overE 1) 3 I.μBus).trans ?_)
  rw [nat_mul_overE, mul_one]

/-- The number of rounds of the table sumcheck. -/
abbrev tableRounds : ℕ := 1 + roundsRounds I.τmax + 1

/-- The table sumcheck: the batching challenge `ξ`, one cubic round per variable, then one
value per column of each sumcheck table. -/
def tableSpec : ProtocolSpec (tableRounds I) :=
  draw E ++ₚ roundsSpec E 3 I.τmax ++ₚ say (Vector E I.tableColumns)

instance instOracleInterfaceTable : ∀ i, OracleInterface ((tableSpec I).Message i) :=
  msgAppend (msgAppend (instOracleInterfaceDraw E) (instOracleInterfaceRounds E 3 _))
    (instOracleInterfaceSay _)

instance instSampleableTypeTable : ∀ i, SampleableType ((tableSpec I).Challenge i) :=
  chalAppend (chalAppend (instSampleableTypeDraw E) (instSampleableTypeRounds E 3 _))
    (instSampleableTypeSay _)

/-- The table sumcheck's error: `B + 2` on `ξ`, `3` per round. -/
noncomputable def tableError : (tableSpec I).ChallengeIdx → ℝ≥0 :=
  errAppend (errAppend (drawError E (overE (I.B + 2))) (roundsError E 3 (overE 3) I.τmax))
    (sayError _)

private theorem sum_tableError :
    ∑ i, tableError I i = overE (I.B + 2) + I.τmax * overE 3 := by
  unfold tableError
  show ∑ i : (draw E ++ₚ roundsSpec E 3 I.τmax ++ₚ say (Vector E I.tableColumns)).ChallengeIdx,
    _ = _
  rw [sum_errAppend, sum_errAppend, sum_drawError, sum_roundsError, sum_sayError, add_zero]

/-- The public-input phase: the challenge `r`, then the values of the lines marked `sent`, as
one message. It is the same for every instance. -/
@[reducible]
def pubSpec : ProtocolSpec 2 := ⟨!v[.V_to_P, .P_to_V], !v[E, List E]⟩

instance instOracleInterfacePub : ∀ i, OracleInterface (pubSpec.Message i)
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => OracleInterface.instDefault

instance instSampleableTypePub : ∀ i, SampleableType (pubSpec.Challenge i)
  | ⟨0, _⟩ => (inferInstance : SampleableType E)
  | ⟨1, h⟩ => nomatch h

/-- The public-input phase's error: `1` on its challenge. -/
noncomputable def pubError : pubSpec.ChallengeIdx → ℝ≥0 := fun _ ↦ overE 1

private theorem sum_pubError : ∑ i, pubError i = overE 1 := by
  show ∑ _i : pubSpec.ChallengeIdx, overE 1 = overE 1
  rw [Finset.sum_const, Finset.card_univ]
  have h : Fintype.card pubSpec.ChallengeIdx = 1 := by decide
  rw [h, one_smul]

/-- The number of rounds of the Flock phase with `2 ^ k` batched compressions. -/
abbrev flockRoundsOf (k : ℕ) : ℕ :=
  (k + 1) + 1 + 1 + roundsRounds 8 + roundsRounds k + 1 + 1 + roundsRounds 8 + 1 + 6

/-- The Flock phase for `2 ^ k` compressions: the `k + 1` coordinates of the point, the 64
values, `z_skip`, `8 + k` zerocheck rounds, the two values `v_a, v_b`, `α_lc`, 8 lincheck
rounds, the 64 values, and the six ring-switching challenges. -/
abbrev flockSpecOf (k : ℕ) : ProtocolSpec (flockRoundsOf k) :=
  draws E (k + 1) ++ₚ say (Vector E 64) ++ₚ draw E ++ₚ roundsSpec E 2 8 ++ₚ roundsSpec E 2 k ++ₚ
    say (Vector E 2) ++ₚ draw E ++ₚ roundsSpec E 2 8 ++ₚ say (Vector E 64) ++ₚ draws E 6

instance instOracleInterfaceFlockOf (k : ℕ) :
    ∀ i, OracleInterface ((flockSpecOf k).Message i) :=
  msgAppend (msgAppend (msgAppend (msgAppend (msgAppend (msgAppend (msgAppend (msgAppend
    (msgAppend (instOracleInterfaceDraws E _) (instOracleInterfaceSay _))
    (instOracleInterfaceDraw E)) (instOracleInterfaceRounds E 2 8))
    (instOracleInterfaceRounds E 2 k)) (instOracleInterfaceSay _)) (instOracleInterfaceDraw E))
    (instOracleInterfaceRounds E 2 8)) (instOracleInterfaceSay _)) (instOracleInterfaceDraws E 6)

instance instSampleableTypeFlockOf (k : ℕ) :
    ∀ i, SampleableType ((flockSpecOf k).Challenge i) :=
  chalAppend (chalAppend (chalAppend (chalAppend (chalAppend (chalAppend (chalAppend (chalAppend
    (chalAppend (instSampleableTypeDraws E _) (instSampleableTypeSay _))
    (instSampleableTypeDraw E)) (instSampleableTypeRounds E 2 8))
    (instSampleableTypeRounds E 2 k)) (instSampleableTypeSay _)) (instSampleableTypeDraw E))
    (instSampleableTypeRounds E 2 8)) (instSampleableTypeSay _)) (instSampleableTypeDraws E 6)

/-- The ring-switching challenges' errors: `2^{2^{5−p}−1}` over `|E|` on the `p`-th, that is
`2^31, 2^15, 2^7, 8, 2, 1`. -/
noncomputable def ringError : (draws E 6).ChallengeIdx → ℝ≥0 :=
  errAppend (errAppend (errAppend (errAppend (errAppend (errAppend (fun i ↦ Fin.elim0 i.1)
    (drawError E (overE (2 ^ 31)))) (drawError E (overE (2 ^ 15))))
    (drawError E (overE (2 ^ 7)))) (drawError E (overE 8))) (drawError E (overE 2)))
    (drawError E (overE 1))

private theorem sum_ringError :
    ∑ i, ringError i = overE (2 ^ 31 + 2 ^ 15 + 2 ^ 7 + 8 + 2 + 1) := by
  rw [ringError]
  erw [sum_errAppend, sum_errAppend, sum_errAppend, sum_errAppend, sum_errAppend, sum_errAppend,
    sum_drawError, sum_drawError, sum_drawError, sum_drawError, sum_drawError, sum_drawError,
    Finset.sum_eq_zero fun i _ ↦ Fin.elim0 i.1, zero_add]
  simp only [overE_add]

/-- The Flock phase's error for `2 ^ k` compressions. -/
noncomputable def flockErrorOf (k : ℕ) : (flockSpecOf k).ChallengeIdx → ℝ≥0 :=
  errAppend (errAppend (errAppend (errAppend (errAppend (errAppend (errAppend (errAppend
    (errAppend (drawsError E (overE 1) (k + 1)) (sayError _)) (drawError E (overE 127)))
    (roundsError E 2 (overE 2) 8)) (roundsError E 2 (overE 3) k)) (sayError _))
    (drawError E (overE 3))) (roundsError E 2 (overE 2) 8)) (sayError _)) ringError

/-- The Flock slot's errors sum to `(4k + 302 + 2^31 + 2^15) / |E|`. -/
theorem sum_flockErrorOf (k : ℕ) :
    ∑ i, flockErrorOf k i = overE (4 * k + 302 + 2 ^ 31 + 2 ^ 15) := by
  simp only [flockErrorOf, sum_errAppend, sum_drawsError, sum_sayError, sum_drawError,
    sum_roundsError, add_zero, nat_mul_overE]
  erw [sum_ringError]
  simp only [← overE_add]
  congr 1
  ring

/-- The number of rounds of the Flock slot: none without a region. -/
def flockRounds : Option (FlockRegion I.toShape) → ℕ
  | none => 0
  | some r => flockRoundsOf r.kBatch

/-- The Flock slot: the Flock phase for the region's compressions, or nothing. -/
def flockSpecOpt : (o : Option (FlockRegion I.toShape)) → ProtocolSpec (flockRounds I o)
  | none => !p[]
  | some r => flockSpecOf r.kBatch

instance instOracleInterfaceFlockOpt :
    (o : Option (FlockRegion I.toShape)) → ∀ i, OracleInterface ((flockSpecOpt I o).Message i)
  | none => (inferInstance : ∀ i, OracleInterface ((!p[] : ProtocolSpec 0).Message i))
  | some r => (inferInstance : ∀ i, OracleInterface ((flockSpecOf r.kBatch).Message i))

instance instSampleableTypeFlockOpt :
    (o : Option (FlockRegion I.toShape)) → ∀ i, SampleableType ((flockSpecOpt I o).Challenge i)
  | none => (inferInstance : ∀ i, SampleableType ((!p[] : ProtocolSpec 0).Challenge i))
  | some r => (inferInstance : ∀ i, SampleableType ((flockSpecOf r.kBatch).Challenge i))

/-- The Flock phase's slot. -/
def flockSpec : ProtocolSpec (flockRounds I I.flock) := flockSpecOpt I I.flock

instance instOracleInterfaceFlock : ∀ i, OracleInterface ((flockSpec I).Message i) :=
  instOracleInterfaceFlockOpt I I.flock

instance instSampleableTypeFlock : ∀ i, SampleableType ((flockSpec I).Challenge i) :=
  instSampleableTypeFlockOpt I I.flock

/-- The Flock phase's error. -/
noncomputable def flockErrorOpt :
    (o : Option (FlockRegion I.toShape)) → (flockSpecOpt I o).ChallengeIdx → ℝ≥0
  | none => fun (i : (!p[] : ProtocolSpec 0).ChallengeIdx) ↦ Fin.elim0 i.1
  | some r => flockErrorOf r.kBatch

/-- The Flock phase's error at its slot. -/
noncomputable def flockError : (flockSpec I).ChallengeIdx → ℝ≥0 := flockErrorOpt I I.flock

private theorem sum_flockErrorOpt_le (o : Option (FlockRegion I.toShape))
    (hk : ∀ r ∈ o, r.kBatch ≤ 32) :
    ∑ i, flockErrorOpt I o i ≤ overE (4 * 32 + 302 + 2 ^ 31 + 2 ^ 15) := by
  cases o with
  | none =>
    exact (Finset.sum_eq_zero fun (i : (flockSpecOpt I none).ChallengeIdx) _ ↦
      Fin.elim0 i.1).le.trans zero_le
  | some r =>
    refine (sum_flockErrorOf r.kBatch).trans_le ?_
    apply overE_mono
    have := hk r rfl
    omega

private theorem sum_flockError_le (hk : ∀ r ∈ I.flock, r.kBatch ≤ 32) :
    ∑ i, flockError I i ≤ overE (4 * 32 + 302 + 2 ^ 31 + 2 ^ 15) :=
  sum_flockErrorOpt_le I I.flock hk

/-- The opening: the batching challenge `λ`; the one oracle query is no message. It is the same
for every instance. -/
abbrev openingSpec : ProtocolSpec 1 := draw E

/-- The opening's error: `J − 1` on `λ`, `J` the number of pooled claims. -/
noncomputable def openingError : openingSpec.ChallengeIdx → ℝ≥0 :=
  drawError E (overE (I.poolSize - 1))

/-! ## The whole protocol -/

/-- The number of rounds of the protocol. -/
abbrev piopRounds : ℕ := 1 + busRounds I + tableRounds I + 2 + flockRounds I I.flock + 1

/-- The protocol's schedule: the six slots side by side. -/
def piopSpec : ProtocolSpec (piopRounds I) :=
  commitSpec I ++ₚ busSpec I ++ₚ tableSpec I ++ₚ pubSpec ++ₚ flockSpec I ++ₚ openingSpec

/-! The instances of the slots' prefixes, which the composition of the phases meets one append
at a time. -/

instance instOracleInterfaceUpToBus :
    ∀ i, OracleInterface ((commitSpec I ++ₚ busSpec I).Message i) :=
  msgAppend inferInstance (instOracleInterfaceBus I)

instance instSampleableTypeUpToBus :
    ∀ i, SampleableType ((commitSpec I ++ₚ busSpec I).Challenge i) :=
  chalAppend inferInstance (instSampleableTypeBus I)

instance instOracleInterfaceUpToTable :
    ∀ i, OracleInterface ((commitSpec I ++ₚ busSpec I ++ₚ tableSpec I).Message i) :=
  msgAppend (instOracleInterfaceUpToBus I) (instOracleInterfaceTable I)

instance instSampleableTypeUpToTable :
    ∀ i, SampleableType ((commitSpec I ++ₚ busSpec I ++ₚ tableSpec I).Challenge i) :=
  chalAppend (instSampleableTypeUpToBus I) (instSampleableTypeTable I)

instance instOracleInterfaceUpToPub :
    ∀ i, OracleInterface ((commitSpec I ++ₚ busSpec I ++ₚ tableSpec I ++ₚ pubSpec).Message i) :=
  msgAppend (instOracleInterfaceUpToTable I) instOracleInterfacePub

instance instSampleableTypeUpToPub :
    ∀ i, SampleableType ((commitSpec I ++ₚ busSpec I ++ₚ tableSpec I ++ₚ pubSpec).Challenge i) :=
  chalAppend (instSampleableTypeUpToTable I) instSampleableTypePub

instance instOracleInterfaceUpToFlock :
    ∀ i, OracleInterface
      ((commitSpec I ++ₚ busSpec I ++ₚ tableSpec I ++ₚ pubSpec ++ₚ flockSpec I).Message i) :=
  msgAppend (instOracleInterfaceUpToPub I) (instOracleInterfaceFlock I)

instance instSampleableTypeUpToFlock :
    ∀ i, SampleableType
      ((commitSpec I ++ₚ busSpec I ++ₚ tableSpec I ++ₚ pubSpec ++ₚ flockSpec I).Challenge i) :=
  chalAppend (instSampleableTypeUpToPub I) (instSampleableTypeFlock I)

instance instOracleInterfacePiop : ∀ i, OracleInterface ((piopSpec I).Message i) :=
  msgAppend (instOracleInterfaceUpToFlock I) (instOracleInterfaceDraw E)

instance instSampleableTypePiop : ∀ i, SampleableType ((piopSpec I).Challenge i) :=
  chalAppend (instSampleableTypeUpToFlock I) (instSampleableTypeDraw E)

/-- The protocol's error per challenge: the six slots' side by side. -/
noncomputable def piopError : (piopSpec I).ChallengeIdx → ℝ≥0 :=
  errAppend (errAppend (errAppend (errAppend (errAppend (commitError I) (busError I))
    (tableError I)) pubError) (flockError I)) (openingError I)

/-- **The protocol's error is small at admissible sizes.** With the bus's leaf stacks of
log-height at most 30, tables of log-height at most 32, at most `2^16` constraints, at most
`2^32` batched compressions and at most `2^16` pooled claims, the errors sum to at most
`(2^32 + 2^31 + 2^20) / |E|`, less than `2^{-159}`, the fingerprint's `2^32` and the ring
switching's `2^31` dominating. -/
theorem piopError_le (hμ : I.μBus ≤ 30) (hτ : I.τmax ≤ 32) (hB : I.B ≤ 2 ^ 16)
    (hk : ∀ r ∈ I.flock, r.kBatch ≤ 32) (hJ : I.poolSize ≤ 2 ^ 16) :
    ∑ i, piopError I i ≤ overE (2 ^ 32 + 2 ^ 31 + 2 ^ 20) := by
  have hcommit : ∑ i, commitError I i = 0 := Finset.sum_eq_zero fun _ _ ↦ rfl
  have hbus := sum_busError_le I
  have htable := sum_tableError I
  have hpub := sum_pubError
  have hflock := sum_flockError_le I hk
  have hopen : ∑ i, openingError I i = overE (I.poolSize - 1) := sum_drawError _ _
  unfold piopError
  show ∑ i : (commitSpec I ++ₚ busSpec I ++ₚ tableSpec I ++ₚ pubSpec ++ₚ flockSpec I ++ₚ
    openingSpec).ChallengeIdx, _ ≤ _
  rw [sum_errAppend, sum_errAppend, sum_errAppend, sum_errAppend, sum_errAppend, hcommit,
    zero_add, htable, hpub, hopen, nat_mul_overE]
  have h2μ : 2 ^ I.μBus ≤ 2 ^ 30 := Nat.pow_le_pow_right (by norm_num) hμ
  have hμμ : I.μBus * I.μBus ≤ 30 * 30 := Nat.mul_le_mul hμ hμ
  have hμμ' : 2 * I.μBus * I.μBus = 2 * (I.μBus * I.μBus) := by ring
  calc ∑ i, busError I i + (overE (I.B + 2) + overE (I.τmax * 3)) + overE 1 +
        ∑ i, flockError I i + overE (I.poolSize - 1)
      ≤ overE (4 * 2 ^ I.μBus + ((I.μBus + 1) * 2 + 2 * I.μBus * I.μBus + 3 * I.μBus + 3)) +
        (overE (I.B + 2) + overE (I.τmax * 3)) + overE 1 +
        overE (4 * 32 + 302 + 2 ^ 31 + 2 ^ 15) + overE (I.poolSize - 1) := by
          gcongr
    _ = overE (4 * 2 ^ I.μBus + ((I.μBus + 1) * 2 + 2 * I.μBus * I.μBus + 3 * I.μBus + 3) +
        (I.B + 2 + I.τmax * 3) + 1 + (4 * 32 + 302 + 2 ^ 31 + 2 ^ 15) + (I.poolSize - 1)) := by
          simp only [overE_add]
    _ ≤ overE (2 ^ 32 + 2 ^ 31 + 2 ^ 20) := by
          apply overE_mono
          rw [hμμ']
          omega

end
end LeanerVM.Protocol
