/-
  LeanerVM.Protocol.ToArkLib.Schedule

  Message schedules built from one message, one challenge, sumcheck rounds and the layers of a
  grand-product argument, each with its instances and the error charged to each of its
  challenges. Candidate for ArkLib.
-/

module

public import LeanerVM.Protocol.ToArkLib.Component

/-!
# Schedules and their errors

A `ProtocolSpec` is a sequence of rounds, each a prover message of some type or a verifier
challenge of some type. The combinators here build the schedules interactive proofs are made of,
over any challenge type `C` that can be sampled:

* `say M`: one prover message of type `M`, read whole; `draw C`: one challenge; `draws C k`:
  `k` challenges;
* `roundSpec C d`: one sumcheck round on a polynomial of degree `d`, its `d + 1` coefficients
  (low degree first) then the challenge; `roundsSpec C d m`: `m` such rounds;
* `stepSpec C nside ρ m`: one layer of a grand-product argument over `nside` trees, of radix
  `2 ^ ρ` at depth `m`: a combiner, `m` normalized rounds on a cofactor of degree `2 ^ ρ`, each
  tree's `2 ^ ρ` values at the descendants, and the `ρ` combination challenges;
  `stepsSpec C nside k m`: `k` layers of radix four from depth `m`; `oddSpec C nside r`: a binary
  layer at the roots when `r` is odd; `gkrSpec C nside μ`: the argument for trees of `2 ^ μ`
  leaves, the binary layer first when `μ` is odd, then layers of radix four, then a last combiner
  that nothing reads.

Each schedule comes with its instances (every message can be queried, every challenge can be
sampled) and with an error, one non-negative real per challenge, from the error `u` of one
degree: `drawError C e` charges `e`; `roundsError C d e m` charges `e` per round;
`stepError C nside ρ m combiner u` charges the combiner's error, `2 ^ ρ · u` per round and `u`
per combination challenge; `stepsError`, `oddError` and `gkrError C u nside μ` charge
`(nside − 1) · u` per combiner but the last, which is free. The sums are closed forms
(`sum_roundsError`, `sum_stepError`) or bounds (`sum_stepsError_le`, `sum_gkrError_le`).

Instance search finds ArkLib's instances for the messages and challenges of two schedules side
by side only when the left schedule is not a literal (a literal's type vector reduces under the
appending, and the instance no longer matches), so every appended schedule declares its own by
applying ArkLib's by name (`msgAppend`, `chalAppend`). A one-message schedule writes its
direction as a function, not as ArkLib's one-message literal, whose message interface is the
message type's own; here it is the trivial one, and the two must not be confused by instance
search.
-/

namespace LeanerVM.Protocol

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

@[expose] public section

/-! ## One-round schedules -/

/-- One prover message of type `M`, read whole. -/
abbrev say (M : Type) : ProtocolSpec 1 := ⟨fun _ ↦ .P_to_V, !v[M]⟩

instance instOracleInterfaceSay (M : Type) : ∀ i, OracleInterface ((say M).Message i)
  | ⟨0, _⟩ => OracleInterface.instDefault

instance instSampleableTypeSay (M : Type) : ∀ i, SampleableType ((say M).Challenge i)
  | ⟨0, h⟩ => nomatch h

instance instIsEmptySayChallengeIdx (M : Type) : IsEmpty (say M).ChallengeIdx :=
  ⟨fun i ↦ nomatch i.2⟩

/-- A message has no challenge. -/
def sayError (M : Type) : (say M).ChallengeIdx → ℝ≥0 := fun i ↦ (IsEmpty.false i).elim

variable (C : Type)

/-- One verifier challenge of type `C`, written like `say`. -/
abbrev draw : ProtocolSpec 1 := ⟨fun _ ↦ .V_to_P, !v[C]⟩

instance instOracleInterfaceDraw : ∀ i, OracleInterface ((draw C).Message i)
  | ⟨0, h⟩ => nomatch h

instance instSampleableTypeDraw [SampleableType C] : ∀ i, SampleableType ((draw C).Challenge i)
  | ⟨0, _⟩ => (inferInstance : SampleableType C)

instance instUniqueDrawChallengeIdx : Unique (draw C).ChallengeIdx where
  default := ⟨0, rfl⟩
  uniq := fun _ ↦ Subtype.ext (Subsingleton.elim _ _)

/-- The error `e` on the one challenge. -/
def drawError (e : ℝ≥0) : (draw C).ChallengeIdx → ℝ≥0 := fun _ ↦ e

theorem sum_sayError (M : Type) : ∑ i, sayError M i = 0 := Finset.sum_of_isEmpty _

theorem sum_drawError (e : ℝ≥0) : ∑ i, drawError C e i = e := Fintype.sum_unique _

/-! ## Instances of appended schedules -/

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

/-- `k` challenges in `C`. -/
def draws : (k : ℕ) → ProtocolSpec k
  | 0 => !p[]
  | k + 1 => draws k ++ₚ draw C

instance instOracleInterfaceDraws : (k : ℕ) → ∀ i, OracleInterface ((draws C k).Message i)
  | 0 => (inferInstance : ∀ i, OracleInterface ((!p[] : ProtocolSpec 0).Message i))
  | k + 1 => msgAppend (instOracleInterfaceDraws k) (instOracleInterfaceDraw C)

instance instSampleableTypeDraws [SampleableType C] :
    (k : ℕ) → ∀ i, SampleableType ((draws C k).Challenge i)
  | 0 => (inferInstance : ∀ i, SampleableType ((!p[] : ProtocolSpec 0).Challenge i))
  | k + 1 => chalAppend (instSampleableTypeDraws k) (instSampleableTypeDraw C)

/-- The error `e` on each of `k` challenges. -/
def drawsError (e : ℝ≥0) : (k : ℕ) → (draws C k).ChallengeIdx → ℝ≥0
  | 0 => fun i ↦ Fin.elim0 i.1
  | k + 1 => errAppend (drawsError e k) (drawError C e)

theorem sum_drawsError (e : ℝ≥0) : (k : ℕ) → ∑ i, drawsError C e k i = k * e
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
abbrev roundSpec (d : ℕ) : ProtocolSpec 2 := say (Vector C (d + 1)) ++ₚ draw C

instance instOracleInterfaceRound (d : ℕ) : ∀ i, OracleInterface ((roundSpec C d).Message i) :=
  msgAppend (instOracleInterfaceSay _) (instOracleInterfaceDraw C)

instance instSampleableTypeRound [SampleableType C] (d : ℕ) :
    ∀ i, SampleableType ((roundSpec C d).Challenge i) :=
  chalAppend (instSampleableTypeSay _) (instSampleableTypeDraw C)

/-- The number of rounds of `m` sumcheck rounds. -/
def roundsRounds : ℕ → ℕ
  | 0 => 0
  | m + 1 => 2 + roundsRounds m

/-- `m` sumcheck rounds of degree `d`. -/
def roundsSpec (d : ℕ) : (m : ℕ) → ProtocolSpec (roundsRounds m)
  | 0 => !p[]
  | m + 1 => roundSpec C d ++ₚ roundsSpec d m

instance instOracleInterfaceRounds (d : ℕ) :
    (m : ℕ) → ∀ i, OracleInterface ((roundsSpec C d m).Message i)
  | 0 => (inferInstance : ∀ i, OracleInterface ((!p[] : ProtocolSpec 0).Message i))
  | m + 1 => msgAppend (instOracleInterfaceRound C d) (instOracleInterfaceRounds d m)

instance instSampleableTypeRounds [SampleableType C] (d : ℕ) :
    (m : ℕ) → ∀ i, SampleableType ((roundsSpec C d m).Challenge i)
  | 0 => (inferInstance : ∀ i, SampleableType ((!p[] : ProtocolSpec 0).Challenge i))
  | m + 1 => chalAppend (instSampleableTypeRound C d) (instSampleableTypeRounds d m)

/-- The error `e` on each round's challenge. -/
noncomputable def roundsError (d : ℕ) (e : ℝ≥0) :
    (m : ℕ) → (roundsSpec C d m).ChallengeIdx → ℝ≥0
  | 0 => fun i ↦ Fin.elim0 i.1
  | m + 1 => errAppend (errAppend (sayError _) (drawError C e)) (roundsError d e m)

theorem sum_roundsError (d : ℕ) (e : ℝ≥0) : (m : ℕ) → ∑ i, roundsError C d e m i = m * e
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

/-- One layer of the grand-product argument over `nside` trees, radix `2 ^ ρ`, at depth `m`
(the point so far has `m` coordinates): the combiner, `m` normalized rounds on a cofactor of
degree `2 ^ ρ`, each tree's `2 ^ ρ` values at the descendants, and the `ρ` combination
challenges. -/
abbrev stepSpec (nside ρ m : ℕ) : ProtocolSpec (stepRounds ρ m) :=
  draw C ++ₚ roundsSpec C (2 ^ ρ) m ++ₚ say (Fin nside → Vector C (2 ^ ρ)) ++ₚ draws C ρ

instance instOracleInterfaceStep (nside ρ m : ℕ) :
    ∀ i, OracleInterface ((stepSpec C nside ρ m).Message i) :=
  msgAppend (msgAppend (msgAppend (instOracleInterfaceDraw C) (instOracleInterfaceRounds C _ m))
    (instOracleInterfaceSay _)) (instOracleInterfaceDraws C ρ)

instance instSampleableTypeStep [SampleableType C] (nside ρ m : ℕ) :
    ∀ i, SampleableType ((stepSpec C nside ρ m).Challenge i) :=
  chalAppend (chalAppend (chalAppend (instSampleableTypeDraw C) (instSampleableTypeRounds C _ m))
    (instSampleableTypeSay _)) (instSampleableTypeDraws C ρ)

/-- The error of one layer, with the combiner's error given: `2 ^ ρ · u` on each round and `u`
on each combination challenge. -/
noncomputable def stepError (nside ρ m : ℕ) (combiner u : ℝ≥0) :
    (stepSpec C nside ρ m).ChallengeIdx → ℝ≥0 :=
  errAppend (errAppend (errAppend (drawError C combiner)
    (roundsError C (2 ^ ρ) (((2 ^ ρ : ℕ) : ℝ≥0) * u) m)) (sayError _)) (drawsError C u ρ)

theorem sum_stepError (nside ρ m : ℕ) (combiner u : ℝ≥0) :
    ∑ i, stepError C nside ρ m combiner u i =
      combiner + m * (((2 ^ ρ : ℕ) : ℝ≥0) * u) + ρ * u := by
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
  | k + 1, m => stepSpec C nside 2 m ++ₚ stepsSpec nside k (m + 2)

instance instOracleInterfaceSteps (nside : ℕ) :
    (k m : ℕ) → ∀ i, OracleInterface ((stepsSpec C nside k m).Message i)
  | 0, _ => (inferInstance : ∀ i, OracleInterface ((!p[] : ProtocolSpec 0).Message i))
  | k + 1, m =>
    msgAppend (instOracleInterfaceStep C nside 2 m) (instOracleInterfaceSteps nside k (m + 2))

instance instSampleableTypeSteps [SampleableType C] (nside : ℕ) :
    (k m : ℕ) → ∀ i, SampleableType ((stepsSpec C nside k m).Challenge i)
  | 0, _ => (inferInstance : ∀ i, SampleableType ((!p[] : ProtocolSpec 0).Challenge i))
  | k + 1, m =>
    chalAppend (instSampleableTypeStep C nside 2 m) (instSampleableTypeSteps nside k (m + 2))

/-- The error of `k` layers of radix four: `(nside − 1) · u` on each combiner. -/
noncomputable def stepsError (nside : ℕ) (u : ℝ≥0) :
    (k m : ℕ) → (stepsSpec C nside k m).ChallengeIdx → ℝ≥0
  | 0, _ => fun (i : (!p[] : ProtocolSpec 0).ChallengeIdx) ↦ Fin.elim0 i.1
  | k + 1, m =>
    errAppend (stepError C nside 2 m (((nside - 1 : ℕ) : ℝ≥0) * u) u) (stepsError nside u k (m + 2))

/-- The layers' errors sum to at most `k` layers of the deepest: a crude bound. -/
theorem sum_stepsError_le (nside : ℕ) (u : ℝ≥0) :
    (k m : ℕ) → ∑ i, stepsError C nside u k m i ≤
      ((k * ((nside - 1) + (m + 2 * k) * 4 + 2) : ℕ) : ℝ≥0) * u
  | 0, m => by
    rw [Nat.zero_mul, Nat.cast_zero, zero_mul]
    exact le_of_eq (Finset.sum_eq_zero fun i _ ↦ Fin.elim0 i.1)
  | k + 1, m => by
    rw [stepsError]
    refine (sum_errAppend _ _).trans_le ?_
    rw [sum_stepError]
    have ih := sum_stepsError_le nside u k (m + 2)
    have hnat : (nside - 1) + m * 2 ^ 2 + 2 + k * ((nside - 1) + (m + 2 + 2 * k) * 4 + 2) ≤
        (k + 1) * ((nside - 1) + (m + 2 * (k + 1)) * 4 + 2) := by
      nlinarith
    calc _ ≤ ((nside - 1 : ℕ) : ℝ≥0) * u + (m : ℝ≥0) * (((2 ^ 2 : ℕ) : ℝ≥0) * u) +
          ((2 : ℕ) : ℝ≥0) * u + ((k * ((nside - 1) + (m + 2 + 2 * k) * 4 + 2) : ℕ) : ℝ≥0) * u :=
          add_le_add le_rfl ih
      _ = (((nside - 1) + m * 2 ^ 2 + 2 + k * ((nside - 1) + (m + 2 + 2 * k) * 4 + 2) : ℕ) :
          ℝ≥0) * u := by
          push_cast
          ring
      _ ≤ (((k + 1) * ((nside - 1) + (m + 2 * (k + 1)) * 4 + 2) : ℕ) : ℝ≥0) * u :=
          mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hnat) zero_le

/-- The number of rounds of the binary layer, if there is one (`r` is `μ mod 2`). -/
def oddRounds : ℕ → ℕ
  | 0 => 0
  | _ + 1 => stepRounds 1 0

/-- The binary layer at the roots, present when `μ` is odd. -/
def oddSpec (nside : ℕ) : (r : ℕ) → ProtocolSpec (oddRounds r)
  | 0 => !p[]
  | _ + 1 => stepSpec C nside 1 0

instance instOracleInterfaceOdd (nside : ℕ) :
    (r : ℕ) → ∀ i, OracleInterface ((oddSpec C nside r).Message i)
  | 0 => (inferInstance : ∀ i, OracleInterface ((!p[] : ProtocolSpec 0).Message i))
  | _ + 1 => instOracleInterfaceStep C nside 1 0

instance instSampleableTypeOdd [SampleableType C] (nside : ℕ) :
    (r : ℕ) → ∀ i, SampleableType ((oddSpec C nside r).Challenge i)
  | 0 => (inferInstance : ∀ i, SampleableType ((!p[] : ProtocolSpec 0).Challenge i))
  | _ + 1 => instSampleableTypeStep C nside 1 0

/-- The error of the binary layer. -/
noncomputable def oddError (nside : ℕ) (u : ℝ≥0) :
    (r : ℕ) → (oddSpec C nside r).ChallengeIdx → ℝ≥0
  | 0 => fun (i : (!p[] : ProtocolSpec 0).ChallengeIdx) ↦ Fin.elim0 i.1
  | _ + 1 => stepError C nside 1 0 (((nside - 1 : ℕ) : ℝ≥0) * u) u

theorem sum_oddError_le (nside : ℕ) (u : ℝ≥0) (r : ℕ) :
    ∑ i, oddError C nside u r i ≤ (((nside - 1) + 1 : ℕ) : ℝ≥0) * u := by
  cases r with
  | zero =>
    exact (Finset.sum_eq_zero fun (i : (oddSpec C nside 0).ChallengeIdx) _ ↦
      Fin.elim0 i.1).le.trans zero_le
  | succ r =>
    rw [oddError]
    refine (sum_stepError C nside 1 0 _ u).trans_le (le_of_eq ?_)
    push_cast
    ring

/-- The number of rounds of the grand-product argument for trees of `2 ^ μ` leaves. -/
abbrev gkrRounds (μ : ℕ) : ℕ := oddRounds (μ % 2) + stepsRounds (μ / 2) (μ % 2) + 1

/-- The grand-product argument for `nside` trees of `2 ^ μ` leaves, from the roots (already
in the statement) down to the leaves: one binary layer first when `μ` is odd, then layers of
radix four, and a last combiner that nothing reads. -/
abbrev gkrSpec (nside μ : ℕ) : ProtocolSpec (gkrRounds μ) :=
  oddSpec C nside (μ % 2) ++ₚ stepsSpec C nside (μ / 2) (μ % 2) ++ₚ draw C

instance instOracleInterfaceGkr (nside μ : ℕ) :
    ∀ i, OracleInterface ((gkrSpec C nside μ).Message i) :=
  msgAppend (msgAppend (instOracleInterfaceOdd C nside _) (instOracleInterfaceSteps C nside _ _))
    (instOracleInterfaceDraw C)

instance instSampleableTypeGkr [SampleableType C] (nside μ : ℕ) :
    ∀ i, SampleableType ((gkrSpec C nside μ).Challenge i) :=
  chalAppend (chalAppend (instSampleableTypeOdd C nside _) (instSampleableTypeSteps C nside _ _))
    (instSampleableTypeDraw C)

/-- The error of the grand-product argument: `(nside − 1) · u` on each combiner but the last,
which is free; `2 ^ ρ · u` on each round of radix `2 ^ ρ`; `u` on each combination challenge. -/
noncomputable def gkrError (u : ℝ≥0) (nside μ : ℕ) : (gkrSpec C nside μ).ChallengeIdx → ℝ≥0 :=
  errAppend (errAppend (oddError C nside u (μ % 2)) (stepsError C nside u (μ / 2) (μ % 2)))
    (drawError C 0)

/-- The grand-product argument's errors sum to at most
`((μ + 1)·(nside − 1) + 2μ² + 3μ + 3) · u`. -/
theorem sum_gkrError_le (u : ℝ≥0) (nside μ : ℕ) :
    ∑ i, gkrError C u nside μ i ≤
      (((μ + 1) * (nside - 1) + 2 * μ * μ + 3 * μ + 3 : ℕ) : ℝ≥0) * u := by
  rw [gkrError, sum_errAppend, sum_errAppend, sum_drawError, add_zero]
  have h1 := sum_oddError_le C nside u (μ % 2)
  have h2 := sum_stepsError_le C nside u (μ / 2) (μ % 2)
  have hnat : (nside - 1) + 1 + μ / 2 * ((nside - 1) + (μ % 2 + 2 * (μ / 2)) * 4 + 2) ≤
      (μ + 1) * (nside - 1) + 2 * μ * μ + 3 * μ + 3 := by
    rw [Nat.mod_add_div μ 2]
    have hk : μ / 2 * 2 ≤ μ := Nat.div_mul_le_self μ 2
    nlinarith [Nat.mul_le_mul_right (nside - 1) hk, Nat.mul_le_mul_right μ hk]
  calc _ ≤ (((nside - 1) + 1 : ℕ) : ℝ≥0) * u +
        ((μ / 2 * ((nside - 1) + (μ % 2 + 2 * (μ / 2)) * 4 + 2) : ℕ) : ℝ≥0) * u :=
        add_le_add h1 h2
    _ = (((nside - 1) + 1 + μ / 2 * ((nside - 1) + (μ % 2 + 2 * (μ / 2)) * 4 + 2) : ℕ) :
        ℝ≥0) * u := by
        push_cast
        ring
    _ ≤ (((μ + 1) * (nside - 1) + 2 * μ * μ + 3 * μ + 3 : ℕ) : ℝ≥0) * u :=
        mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hnat) zero_le

end
end LeanerVM.Protocol
