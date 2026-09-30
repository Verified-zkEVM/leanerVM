/-
  LeanerVM.Protocol.Spine.Errors

  The schedule and the error of every slot of the protocol, as closed forms of the instance, and
  the error of the whole protocol with its bound at admissible sizes.
-/

module

public import LeanerVM.Protocol.Spine.Instance
public import LeanerVM.Protocol.ToArkLib.Component
public import LeanerVM.Protocol.ToArkLib.SendOracle

/-!
# Schedules and errors

The protocol is `commit ⟫ bus ⟫ table ⟫ pub ⟫ flock ⟫ opening`. This module fixes, for each of
the six slots, the message schedule (`commitSpec`, `busSpec`, `tableSpec`, `pubSpec`,
`flockSpec`, `openingSpec`) and, for the five after the commit, the knowledge error charged to
each challenge (`busError` … `openingError`), all as closed forms of the instance's sizes. A
phase fills its slot only at that schedule and that error: no phase declares its own, since a
declared error of `1` would let a phase that checks nothing be knowledge sound. `piopSpec` and
`piopError` are the six side by side, and `piopError_le` bounds the sum of the errors at the
sizes the leanISA instance meets.

The schedules, at leanVM `a386121f84292f6fa663aaa3e570c15bc0240ea2`:

* The commit: the stack, as one message.
* The bus (§5.2–§5.4, `crates/lean_vm/src/gkr.rs:247-430`): the fingerprint challenges
  `(α, β)`; the two roots `(R, R_c)`; the grand-product argument for the three trees, radix
  four from the roots down with one binary layer first when `μ_bus` is odd: each layer draws a
  combiner `λ`, runs one normalized sumcheck round per variable of the layer (the cofactor's
  coefficients, low degree first, then the challenge), sends each tree's values at the
  descendants, and draws the combination challenges one by one; a last combiner, read by
  nothing, follows the last layer; then the boundary columns' values.
* The table sumcheck (§5.5, `cpu/mod.rs:726-735`): the batching challenge `ξ`; one round per
  variable, highest first, of a cubic's four coefficients and a challenge; then one value per
  column of each sumcheck table, table by table.
* The public input (§8.2): the challenge `r`, then the values of the lines marked `sent`.
* Flock (Annex C, `hash_flock.rs`, `python-verifier/verifier.py:1092-1295`), with
  `k = kBatch`: the `k + 1` coordinates of the point; the 64 values; the challenge `z_skip`;
  `8 + k` zerocheck rounds of three coefficients and a challenge; the three values
  `v_a, v_b, v_c`; the challenge `α_lc`; 8 lincheck rounds; the 64 values; the six challenges
  of the ring switching. An instance with no Flock region has an empty slot.
* The opening (§8.5): the batching challenge `λ`, then one oracle query, which is no message.

The oracle protocol sends every coefficient of a round polynomial and its verifier checks each
round; the compiled verifier reads one coefficient less per round and derives it.

The errors, per challenge, over `|E|`: the bus `4·2^{μ_bus}` on `(α, β)`, `nside − 1 = 2` on
each combiner but the last (`0`), `4` on each radix-four round and `2` on a binary one, `1` on
each combination challenge; the table `B + 2` on `ξ` and `3` per round; the public input `1`;
Flock `1` on each coordinate of the point, `127` on `z_skip`, `2` on each zerocheck round and
`1` more on the last `k`, `3` on `α_lc`, `2` on each lincheck round, `2^{2^{5−p}−1}` on the
`p`-th ring-switching challenge; the opening `J − 1` on `λ`, `J` the number of pooled claims.
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

theorem overE_zero : overE 0 = 0 := by simp [overE]

theorem nat_mul_overE (n c : ℕ) : (n : ℝ≥0) * overE c = overE (n * c) := by
  simp only [overE, Nat.cast_mul]
  ring

/-! ## One-round schedules -/

/-- One prover message of type `M`, read whole. Its direction is written as a function, not as
ArkLib's one-message literal, whose message interface is the message type's own; here it is
the trivial one, and the two schedules must not be confused by instance search. -/
abbrev say (M : Type) : ProtocolSpec 1 := ⟨fun _ ↦ .P_to_V, !v[M]⟩

instance instOracleInterfaceSay (M : Type) : ∀ i, OracleInterface ((say M).Message i)
  | ⟨0, _⟩ => OracleInterface.instDefault

instance instSampleableTypeSay (M : Type) : ∀ i, SampleableType ((say M).Challenge i)
  | ⟨0, h⟩ => nomatch h

instance instIsEmptySayChallengeIdx (M : Type) : IsEmpty (say M).ChallengeIdx :=
  ⟨fun i ↦ nomatch i.2⟩

/-- A message has no challenge. -/
def sayError (M : Type) : (say M).ChallengeIdx → ℝ≥0 := fun i ↦ (IsEmpty.false i).elim

/-- One verifier challenge of type `C`, written like `say`. -/
abbrev draw (C : Type) [SampleableType C] : ProtocolSpec 1 := ⟨fun _ ↦ .V_to_P, !v[C]⟩

instance instOracleInterfaceDraw (C : Type) [SampleableType C] :
    ∀ i, OracleInterface ((draw C).Message i)
  | ⟨0, h⟩ => nomatch h

instance instSampleableTypeDraw (C : Type) [SampleableType C] :
    ∀ i, SampleableType ((draw C).Challenge i)
  | ⟨0, _⟩ => (inferInstance : SampleableType C)

instance instUniqueDrawChallengeIdx (C : Type) [SampleableType C] :
    Unique (draw C).ChallengeIdx where
  default := ⟨0, rfl⟩
  uniq := fun _ ↦ Subtype.ext (Subsingleton.elim _ _)

/-- The error `e` on the one challenge. -/
def drawError (C : Type) [SampleableType C] (e : ℝ≥0) : (draw C).ChallengeIdx → ℝ≥0 :=
  fun _ ↦ e

theorem sum_sayError (M : Type) : ∑ i, sayError M i = 0 := Finset.sum_of_isEmpty _

theorem sum_drawError (C : Type) [SampleableType C] (e : ℝ≥0) : ∑ i, drawError C e i = e :=
  Fintype.sum_unique _

/-! ## Instances of appended schedules

Instance search finds ArkLib's instances for the messages and challenges of two schedules side
by side only when the left schedule is not a literal (a literal's type vector reduces under the
appending, and the instance no longer matches), so every appended schedule below declares its
own by applying ArkLib's by name. -/

/-- The message interfaces of two schedules side by side. -/
abbrev msgAppend {m n : ℕ} {p₁ : ProtocolSpec m} {p₂ : ProtocolSpec n}
    (O₁ : ∀ i, OracleInterface (p₁.Message i)) (O₂ : ∀ i, OracleInterface (p₂.Message i)) :
    ∀ i, OracleInterface ((p₁ ++ₚ p₂).Message i) :=
  ProtocolSpec.instOracleInterfaceMessageAppend (O₁ := O₁) (O₂ := O₂)

/-- The challenge samplers of two schedules side by side. -/
abbrev chalAppend {m n : ℕ} {p₁ : ProtocolSpec m} {p₂ : ProtocolSpec n}
    (h₁ : ∀ i, SampleableType (p₁.Challenge i)) (h₂ : ∀ i, SampleableType (p₂.Challenge i)) :
    ∀ i, SampleableType ((p₁ ++ₚ p₂).Challenge i) :=
  ProtocolSpec.instSampleableTypeChallengeAppend (h₁ := h₁) (h₂ := h₂)

/-! ## Repeated rounds -/

/-- `k` challenges in `E`. -/
def draws : (k : ℕ) → ProtocolSpec k
  | 0 => !p[]
  | k + 1 => draws k ++ₚ draw E

instance instOracleInterfaceDraws : (k : ℕ) → ∀ i, OracleInterface ((draws k).Message i)
  | 0 => (inferInstance : ∀ i, OracleInterface ((!p[] : ProtocolSpec 0).Message i))
  | k + 1 => msgAppend (instOracleInterfaceDraws k) (instOracleInterfaceDraw E)

instance instSampleableTypeDraws : (k : ℕ) → ∀ i, SampleableType ((draws k).Challenge i)
  | 0 => (inferInstance : ∀ i, SampleableType ((!p[] : ProtocolSpec 0).Challenge i))
  | k + 1 => chalAppend (instSampleableTypeDraws k) (instSampleableTypeDraw E)

/-- The error `e` on each of `k` challenges. -/
noncomputable def drawsError (e : ℝ≥0) : (k : ℕ) → (draws k).ChallengeIdx → ℝ≥0
  | 0 => fun i ↦ Fin.elim0 i.1
  | k + 1 => errAppend (drawsError e k) (drawError E e)

theorem sum_drawsError (e : ℝ≥0) : (k : ℕ) → ∑ i, drawsError e k i = k * e
  | 0 => by
    rw [Nat.cast_zero, zero_mul]
    exact Finset.sum_eq_zero fun i _ ↦ Fin.elim0 i.1
  | k + 1 => by
    rw [drawsError]
    refine (sum_errAppend _ _).trans ?_
    rw [sum_drawError, sum_drawsError e k]
    push_cast
    ring

/-- One sumcheck round on a polynomial of degree `d`: its `d + 1` coefficients, low degree
first, then the challenge. -/
abbrev roundSpec (d : ℕ) : ProtocolSpec 2 := say (Vector E (d + 1)) ++ₚ draw E

instance instOracleInterfaceRound (d : ℕ) : ∀ i, OracleInterface ((roundSpec d).Message i) :=
  msgAppend (instOracleInterfaceSay _) (instOracleInterfaceDraw E)

instance instSampleableTypeRound (d : ℕ) : ∀ i, SampleableType ((roundSpec d).Challenge i) :=
  chalAppend (instSampleableTypeSay _) (instSampleableTypeDraw E)

/-- The number of rounds of `m` sumcheck rounds. -/
def roundsRounds : ℕ → ℕ
  | 0 => 0
  | m + 1 => 2 + roundsRounds m

/-- `m` sumcheck rounds of degree `d`. -/
def roundsSpec (d : ℕ) : (m : ℕ) → ProtocolSpec (roundsRounds m)
  | 0 => !p[]
  | m + 1 => roundSpec d ++ₚ roundsSpec d m

instance instOracleInterfaceRounds (d : ℕ) :
    (m : ℕ) → ∀ i, OracleInterface ((roundsSpec d m).Message i)
  | 0 => (inferInstance : ∀ i, OracleInterface ((!p[] : ProtocolSpec 0).Message i))
  | m + 1 => msgAppend (instOracleInterfaceRound d) (instOracleInterfaceRounds d m)

instance instSampleableTypeRounds (d : ℕ) :
    (m : ℕ) → ∀ i, SampleableType ((roundsSpec d m).Challenge i)
  | 0 => (inferInstance : ∀ i, SampleableType ((!p[] : ProtocolSpec 0).Challenge i))
  | m + 1 => chalAppend (instSampleableTypeRound d) (instSampleableTypeRounds d m)

/-- The error `e` on each round's challenge. -/
noncomputable def roundsError (d : ℕ) (e : ℝ≥0) :
    (m : ℕ) → (roundsSpec d m).ChallengeIdx → ℝ≥0
  | 0 => fun i ↦ Fin.elim0 i.1
  | m + 1 => errAppend (errAppend (sayError _) (drawError E e)) (roundsError d e m)

theorem sum_roundsError (d : ℕ) (e : ℝ≥0) : (m : ℕ) → ∑ i, roundsError d e m i = m * e
  | 0 => by
    rw [Nat.cast_zero, zero_mul]
    exact Finset.sum_eq_zero fun i _ ↦ Fin.elim0 i.1
  | m + 1 => by
    rw [roundsError]
    refine (sum_errAppend _ _).trans ?_
    rw [sum_errAppend, sum_sayError, sum_drawError, sum_roundsError d e m]
    push_cast
    ring

/-! ## The grand-product argument -/

/-- The number of rounds of one layer of radix `2 ^ ρ` at depth `m`. -/
abbrev stepRounds (ρ m : ℕ) : ℕ := 1 + roundsRounds m + 1 + ρ

/-- One layer of the grand-product argument, radix `2 ^ ρ`, at depth `m` (the point so far has
`m` coordinates): the combiner, `m` normalized rounds on a cofactor of degree `2 ^ ρ`, each
tree's `2 ^ ρ` values at the descendants, and the `ρ` combination challenges. -/
abbrev stepSpec (nside ρ m : ℕ) : ProtocolSpec (stepRounds ρ m) :=
  draw E ++ₚ roundsSpec (2 ^ ρ) m ++ₚ say (Fin nside → Vector E (2 ^ ρ)) ++ₚ draws ρ

instance instOracleInterfaceStep (nside ρ m : ℕ) :
    ∀ i, OracleInterface ((stepSpec nside ρ m).Message i) :=
  msgAppend (msgAppend (msgAppend (instOracleInterfaceDraw E) (instOracleInterfaceRounds _ m))
    (instOracleInterfaceSay _)) (instOracleInterfaceDraws ρ)

instance instSampleableTypeStep (nside ρ m : ℕ) :
    ∀ i, SampleableType ((stepSpec nside ρ m).Challenge i) :=
  chalAppend (chalAppend (chalAppend (instSampleableTypeDraw E) (instSampleableTypeRounds _ m))
    (instSampleableTypeSay _)) (instSampleableTypeDraws ρ)

/-- The error of one layer, with the combiner's error given. -/
noncomputable def stepError (nside ρ m : ℕ) (combiner : ℝ≥0) :
    (stepSpec nside ρ m).ChallengeIdx → ℝ≥0 :=
  errAppend (errAppend (errAppend (drawError E combiner) (roundsError (2 ^ ρ) (overE (2 ^ ρ)) m))
    (sayError _)) (drawsError (overE 1) ρ)

theorem sum_stepError (nside ρ m : ℕ) (combiner : ℝ≥0) :
    ∑ i, stepError nside ρ m combiner i = combiner + m * overE (2 ^ ρ) + ρ * overE 1 := by
  rw [stepError, sum_errAppend, sum_errAppend, sum_errAppend, sum_drawError, sum_roundsError,
    sum_sayError, sum_drawsError]
  ring

/-- The number of rounds of `k` layers of radix four from depth `m`. -/
def stepsRounds : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, m => stepRounds 2 m + stepsRounds k (m + 2)

/-- `k` layers of radix four from depth `m`. -/
def stepsSpec (nside : ℕ) : (k m : ℕ) → ProtocolSpec (stepsRounds k m)
  | 0, _ => !p[]
  | k + 1, m => stepSpec nside 2 m ++ₚ stepsSpec nside k (m + 2)

instance instOracleInterfaceSteps (nside : ℕ) :
    (k m : ℕ) → ∀ i, OracleInterface ((stepsSpec nside k m).Message i)
  | 0, _ => (inferInstance : ∀ i, OracleInterface ((!p[] : ProtocolSpec 0).Message i))
  | k + 1, m =>
    msgAppend (instOracleInterfaceStep nside 2 m) (instOracleInterfaceSteps nside k (m + 2))

instance instSampleableTypeSteps (nside : ℕ) :
    (k m : ℕ) → ∀ i, SampleableType ((stepsSpec nside k m).Challenge i)
  | 0, _ => (inferInstance : ∀ i, SampleableType ((!p[] : ProtocolSpec 0).Challenge i))
  | k + 1, m =>
    chalAppend (instSampleableTypeStep nside 2 m) (instSampleableTypeSteps nside k (m + 2))

/-- The error of `k` layers of radix four: `nside − 1` over `|E|` on each combiner. -/
noncomputable def stepsError (nside : ℕ) :
    (k m : ℕ) → (stepsSpec nside k m).ChallengeIdx → ℝ≥0
  | 0, _ => fun (i : (!p[] : ProtocolSpec 0).ChallengeIdx) ↦ Fin.elim0 i.1
  | k + 1, m => errAppend (stepError nside 2 m (overE (nside - 1))) (stepsError nside k (m + 2))

/-- The layers' errors sum to at most `k` layers of the deepest: a crude bound. -/
theorem sum_stepsError_le (nside : ℕ) :
    (k m : ℕ) → ∑ i, stepsError nside k m i ≤
      k * (overE (nside - 1) + (m + 2 * k) * overE 4 + 2 * overE 1)
  | 0, m => by
    rw [Nat.cast_zero, zero_mul]
    exact le_of_eq (Finset.sum_eq_zero fun i _ ↦ Fin.elim0 i.1)
  | k + 1, m => by
    rw [stepsError]
    refine (sum_errAppend _ _).trans_le ?_
    rw [sum_stepError]
    have ih := sum_stepsError_le nside k (m + 2)
    have h4 : (2 : ℕ) ^ 2 = 4 := by norm_num
    rw [h4]
    push_cast at ih ⊢
    have hk : (m + 2 + 2 * k : ℝ≥0) = m + 2 * (k + 1) := by ring
    rw [hk] at ih
    have hm : (m : ℝ≥0) ≤ m + 2 * (k + 1) := le_add_of_nonneg_right (by positivity)
    calc overE (nside - 1) + ↑m * overE 4 + 2 * overE 1 + ∑ i, stepsError nside k (m + 2) i
        ≤ overE (nside - 1) + (m + 2 * (k + 1)) * overE 4 + 2 * overE 1 +
          k * (overE (nside - 1) + (m + 2 * (k + 1)) * overE 4 + 2 * overE 1) := by
          gcongr
      _ = (k + 1) * (overE (nside - 1) + (m + 2 * (k + 1)) * overE 4 + 2 * overE 1) := by
          ring

/-- The number of rounds of the binary layer, if there is one (`r` is `μ_bus mod 2`). -/
def oddRounds : ℕ → ℕ
  | 0 => 0
  | _ + 1 => stepRounds 1 0

/-- The binary layer at the roots, present when `μ_bus` is odd. -/
def oddSpec (nside : ℕ) : (r : ℕ) → ProtocolSpec (oddRounds r)
  | 0 => !p[]
  | _ + 1 => stepSpec nside 1 0

instance instOracleInterfaceOdd (nside : ℕ) :
    (r : ℕ) → ∀ i, OracleInterface ((oddSpec nside r).Message i)
  | 0 => (inferInstance : ∀ i, OracleInterface ((!p[] : ProtocolSpec 0).Message i))
  | _ + 1 => instOracleInterfaceStep nside 1 0

instance instSampleableTypeOdd (nside : ℕ) :
    (r : ℕ) → ∀ i, SampleableType ((oddSpec nside r).Challenge i)
  | 0 => (inferInstance : ∀ i, SampleableType ((!p[] : ProtocolSpec 0).Challenge i))
  | _ + 1 => instSampleableTypeStep nside 1 0

/-- The error of the binary layer. -/
noncomputable def oddError (nside : ℕ) : (r : ℕ) → (oddSpec nside r).ChallengeIdx → ℝ≥0
  | 0 => fun (i : (!p[] : ProtocolSpec 0).ChallengeIdx) ↦ Fin.elim0 i.1
  | _ + 1 => stepError nside 1 0 (overE (nside - 1))

theorem sum_oddError_le (nside r : ℕ) :
    ∑ i, oddError nside r i ≤ overE (nside - 1) + overE 1 := by
  cases r with
  | zero =>
    exact (Finset.sum_eq_zero fun (i : (oddSpec nside 0).ChallengeIdx) _ ↦
      Fin.elim0 i.1).le.trans zero_le
  | succ r =>
    rw [oddError]
    refine (sum_stepError _ _ _ _).trans_le ?_
    simp

/-- The number of rounds of the grand-product argument for trees of `2 ^ μ` leaves. -/
abbrev gkrRounds (μ : ℕ) : ℕ := oddRounds (μ % 2) + stepsRounds (μ / 2) (μ % 2) + 1

/-- The grand-product argument for `nside` trees of `2 ^ μ` leaves, from the roots (already
in the statement) down to the leaves: one binary layer first when `μ` is odd, then layers of
radix four, and a last combiner that nothing reads (`gkr.rs:247-430`). -/
abbrev gkrSpec (nside μ : ℕ) : ProtocolSpec (gkrRounds μ) :=
  oddSpec nside (μ % 2) ++ₚ stepsSpec nside (μ / 2) (μ % 2) ++ₚ draw E

instance instOracleInterfaceGkr (nside μ : ℕ) :
    ∀ i, OracleInterface ((gkrSpec nside μ).Message i) :=
  msgAppend (msgAppend (instOracleInterfaceOdd nside _) (instOracleInterfaceSteps nside _ _))
    (instOracleInterfaceDraw E)

instance instSampleableTypeGkr (nside μ : ℕ) :
    ∀ i, SampleableType ((gkrSpec nside μ).Challenge i) :=
  chalAppend (chalAppend (instSampleableTypeOdd nside _) (instSampleableTypeSteps nside _ _))
    (instSampleableTypeDraw E)

/-- The error of the grand-product argument: `nside − 1` on each combiner but the last, which
is `0`; `2 ^ ρ` on each round of radix `2 ^ ρ`; `1` on each combination challenge. -/
noncomputable def gkrError (nside μ : ℕ) : (gkrSpec nside μ).ChallengeIdx → ℝ≥0 :=
  errAppend (errAppend (oddError nside (μ % 2)) (stepsError nside (μ / 2) (μ % 2)))
    (drawError E 0)

/-- The grand-product argument's errors sum to at most `(μ + 1)·(nside − 1) + 2μ² + 3μ + 3`
over `|E|`. -/
theorem sum_gkrError_le (nside μ : ℕ) :
    ∑ i, gkrError nside μ i ≤ overE ((μ + 1) * (nside - 1) + 2 * μ * μ + 3 * μ + 3) := by
  rw [gkrError, sum_errAppend, sum_errAppend, sum_drawError, add_zero]
  have h1 := sum_oddError_le nside (μ % 2)
  have h2 := sum_stepsError_le nside (μ / 2) (μ % 2)
  have hk : μ / 2 ≤ μ := Nat.div_le_self μ 2
  have hmμ : μ % 2 + 2 * (μ / 2) = μ := Nat.mod_add_div μ 2
  have hcalc : (μ / 2 : ℕ) * (overE (nside - 1) + ((μ % 2 : ℕ) + 2 * (μ / 2 : ℕ)) * overE 4 +
      2 * overE 1) ≤ overE (μ * (nside - 1) + 2 * μ * μ + 2 * μ) := by
    have hle : ((μ / 2 : ℕ) : ℝ≥0) * (overE (nside - 1) +
        ((μ % 2 : ℕ) + 2 * (μ / 2 : ℕ)) * overE 4 + 2 * overE 1) =
        overE ((μ / 2) * (nside - 1) + (μ / 2) * (μ % 2 + 2 * (μ / 2)) * 4 + (μ / 2) * 2) := by
      simp only [overE, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      ring
    rw [hle]
    apply overE_mono
    rw [hmμ]
    have h2μ : μ / 2 * 2 ≤ μ := Nat.div_mul_le_self μ 2
    have h5 : μ / 2 * (nside - 1) ≤ μ * (nside - 1) := Nat.mul_le_mul_right _ hk
    have h6 : μ / 2 * μ * 4 ≤ μ * μ * 2 := by
      calc μ / 2 * μ * 4 = μ / 2 * 2 * (μ * 2) := by ring
        _ ≤ μ * (μ * 2) := Nat.mul_le_mul_right _ h2μ
        _ = μ * μ * 2 := by ring
    calc μ / 2 * (nside - 1) + μ / 2 * μ * 4 + μ / 2 * 2
        ≤ μ * (nside - 1) + μ * μ * 2 + μ * 2 := by omega
      _ = μ * (nside - 1) + 2 * μ * μ + 2 * μ := by ring
  calc ∑ i, oddError nside (μ % 2) i + ∑ i, stepsError nside (μ / 2) (μ % 2) i
      ≤ (overE (nside - 1) + overE 1) + overE (μ * (nside - 1) + 2 * μ * μ + 2 * μ) :=
        add_le_add h1 (h2.trans hcalc)
    _ = overE ((nside - 1) + 1 + (μ * (nside - 1) + 2 * μ * μ + 2 * μ)) := by
        simp only [overE_add]
    _ ≤ overE ((μ + 1) * (nside - 1) + 2 * μ * μ + 3 * μ + 3) := by
        apply overE_mono
        rw [add_mul, one_mul]
        omega

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
  draw ((Fin 4 → E) × E) ++ₚ say (E × E) ++ₚ gkrSpec 3 I.μBus ++ₚ say (Vector E I.busClaims)

instance instOracleInterfaceBus : ∀ i, OracleInterface ((busSpec I).Message i) :=
  msgAppend (msgAppend (msgAppend (instOracleInterfaceDraw _) (instOracleInterfaceSay _))
    (instOracleInterfaceGkr 3 I.μBus)) (instOracleInterfaceSay _)

instance instSampleableTypeBus : ∀ i, SampleableType ((busSpec I).Challenge i) :=
  chalAppend (chalAppend (chalAppend (instSampleableTypeDraw _) (instSampleableTypeSay _))
    (instSampleableTypeGkr 3 I.μBus)) (instSampleableTypeSay _)

/-- The bus phase's error: `4·2^{μ_bus}` on `(α, β)`, then the grand-product argument's. -/
noncomputable def busError : (busSpec I).ChallengeIdx → ℝ≥0 :=
  errAppend (errAppend (errAppend (drawError _ (overE (4 * 2 ^ I.μBus))) (sayError _))
    (gkrError 3 I.μBus)) (sayError _)

theorem sum_busError_le :
    ∑ i, busError I i ≤ overE (4 * 2 ^ I.μBus + ((I.μBus + 1) * 2 + 2 * I.μBus * I.μBus +
      3 * I.μBus + 3)) := by
  unfold busError
  show ∑ i : (draw ((Fin 4 → E) × E) ++ₚ say (E × E) ++ₚ gkrSpec 3 I.μBus ++ₚ
    say (Vector E I.busClaims)).ChallengeIdx, _ ≤ _
  rw [sum_errAppend, sum_errAppend, sum_errAppend, sum_drawError, sum_sayError, sum_sayError,
    add_zero, add_zero, overE_add]
  refine add_le_add le_rfl ((sum_gkrError_le 3 I.μBus).trans ?_)
  exact overE_mono (by norm_num)

/-- The number of rounds of the table sumcheck. -/
abbrev tableRounds : ℕ := 1 + roundsRounds I.τmax + 1

/-- The table sumcheck: the batching challenge `ξ`, one cubic round per variable, then one
value per column of each sumcheck table. -/
def tableSpec : ProtocolSpec (tableRounds I) :=
  draw E ++ₚ roundsSpec 3 I.τmax ++ₚ say (Vector E I.tableColumns)

instance instOracleInterfaceTable : ∀ i, OracleInterface ((tableSpec I).Message i) :=
  msgAppend (msgAppend (instOracleInterfaceDraw E) (instOracleInterfaceRounds 3 _))
    (instOracleInterfaceSay _)

instance instSampleableTypeTable : ∀ i, SampleableType ((tableSpec I).Challenge i) :=
  chalAppend (chalAppend (instSampleableTypeDraw E) (instSampleableTypeRounds 3 _))
    (instSampleableTypeSay _)

/-- The table sumcheck's error: `B + 2` on `ξ`, `3` per round. -/
noncomputable def tableError : (tableSpec I).ChallengeIdx → ℝ≥0 :=
  errAppend (errAppend (drawError E (overE (I.B + 2))) (roundsError 3 (overE 3) I.τmax))
    (sayError _)

theorem sum_tableError : ∑ i, tableError I i = overE (I.B + 2) + I.τmax * overE 3 := by
  unfold tableError
  show ∑ i : (draw E ++ₚ roundsSpec 3 I.τmax ++ₚ say (Vector E I.tableColumns)).ChallengeIdx,
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

theorem sum_pubError : ∑ i, pubError i = overE 1 := by
  show ∑ _i : pubSpec.ChallengeIdx, overE 1 = overE 1
  rw [Finset.sum_const, Finset.card_univ]
  have h : Fintype.card pubSpec.ChallengeIdx = 1 := by decide
  rw [h, one_smul]

/-- The number of rounds of the Flock phase with `2 ^ k` batched compressions. -/
abbrev flockRoundsOf (k : ℕ) : ℕ :=
  (k + 1) + 1 + 1 + roundsRounds 8 + roundsRounds k + 1 + 1 + roundsRounds 8 + 1 + 6

/-- The Flock phase for `2 ^ k` compressions: the `k + 1` coordinates of the point, the 64
values, `z_skip`, `8 + k` zerocheck rounds, the three values, `α_lc`, 8 lincheck rounds, the
64 values, and the six ring-switching challenges. -/
abbrev flockSpecOf (k : ℕ) : ProtocolSpec (flockRoundsOf k) :=
  draws (k + 1) ++ₚ say (Vector E 64) ++ₚ draw E ++ₚ roundsSpec 2 8 ++ₚ roundsSpec 2 k ++ₚ
    say (Vector E 3) ++ₚ draw E ++ₚ roundsSpec 2 8 ++ₚ say (Vector E 64) ++ₚ draws 6

instance instOracleInterfaceFlockOf (k : ℕ) :
    ∀ i, OracleInterface ((flockSpecOf k).Message i) :=
  msgAppend (msgAppend (msgAppend (msgAppend (msgAppend (msgAppend (msgAppend (msgAppend
    (msgAppend (instOracleInterfaceDraws _) (instOracleInterfaceSay _)) (instOracleInterfaceDraw E))
    (instOracleInterfaceRounds 2 8)) (instOracleInterfaceRounds 2 k)) (instOracleInterfaceSay _))
    (instOracleInterfaceDraw E)) (instOracleInterfaceRounds 2 8)) (instOracleInterfaceSay _))
    (instOracleInterfaceDraws 6)

instance instSampleableTypeFlockOf (k : ℕ) :
    ∀ i, SampleableType ((flockSpecOf k).Challenge i) :=
  chalAppend (chalAppend (chalAppend (chalAppend (chalAppend (chalAppend (chalAppend (chalAppend
    (chalAppend (instSampleableTypeDraws _) (instSampleableTypeSay _)) (instSampleableTypeDraw E))
    (instSampleableTypeRounds 2 8)) (instSampleableTypeRounds 2 k)) (instSampleableTypeSay _))
    (instSampleableTypeDraw E)) (instSampleableTypeRounds 2 8)) (instSampleableTypeSay _))
    (instSampleableTypeDraws 6)

/-- The ring-switching challenges' errors: `2^{2^{5−p}−1}` over `|E|` on the `p`-th, that is
`2^31, 2^15, 2^7, 8, 2, 1`. -/
noncomputable def ringError : (draws 6).ChallengeIdx → ℝ≥0 :=
  errAppend (errAppend (errAppend (errAppend (errAppend (errAppend (fun i ↦ Fin.elim0 i.1)
    (drawError E (overE (2 ^ 31)))) (drawError E (overE (2 ^ 15))))
    (drawError E (overE (2 ^ 7)))) (drawError E (overE 8))) (drawError E (overE 2)))
    (drawError E (overE 1))

theorem sum_ringError : ∑ i, ringError i = overE (2 ^ 31 + 2 ^ 15 + 2 ^ 7 + 8 + 2 + 1) := by
  rw [ringError]
  erw [sum_errAppend, sum_errAppend, sum_errAppend, sum_errAppend, sum_errAppend, sum_errAppend,
    sum_drawError, sum_drawError, sum_drawError, sum_drawError, sum_drawError, sum_drawError,
    Finset.sum_eq_zero fun i _ ↦ Fin.elim0 i.1, zero_add]
  simp only [overE_add]

/-- The Flock phase's error for `2 ^ k` compressions. -/
noncomputable def flockErrorOf (k : ℕ) : (flockSpecOf k).ChallengeIdx → ℝ≥0 :=
  errAppend (errAppend (errAppend (errAppend (errAppend (errAppend (errAppend (errAppend
    (errAppend (drawsError (overE 1) (k + 1)) (sayError _)) (drawError E (overE 127)))
    (roundsError 2 (overE 2) 8)) (roundsError 2 (overE 3) k)) (sayError _))
    (drawError E (overE 3))) (roundsError 2 (overE 2) 8)) (sayError _)) ringError

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

theorem sum_flockErrorOpt_le (o : Option (FlockRegion I.toShape))
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

theorem sum_flockError_le (hk : ∀ r ∈ I.flock, r.kBatch ≤ 32) :
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
