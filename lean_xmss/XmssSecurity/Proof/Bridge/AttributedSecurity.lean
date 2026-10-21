import LeanXmss.MultiUserStatement
import XmssSecurity.Proof.Bridge.Security
import XmssSecurity.Proof.Bridge.AttributedCount

/-!
# leanXMSS, attributed

The real game is at most the model's game against the translated, memoized adversary plus the two
seed guesses (`Security`), the model's game is two units per expected attributable call after key
generation plus lane 1's constant and a second-order term (`concreteScheme_afterKeygenSecurity_expected`),
and the model's expected attributable count is at most the real one plus the guesses' share
(`expectedParameterQueries_le_realAttributedMean`).
-/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.Bridge

open Seeded DeterministicSigning CappedChain

set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] realKeygen

theorem counted_congr {α : Type} {left right : OracleWorld.Domain → Prop}
    [DecidablePred left] [DecidablePred right] (h : ∀ input, left input ↔ right input)
    (computation : OracleComp OracleWorld α) :
    QueryCounting.counted left computation = QueryCounting.counted right computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
      rw [QueryCounting.counted_query_bind, QueryCounting.counted_query_bind]
      simp only [ih, if_congr (h input) rfl rfl]

theorem isAttributed_iff (publicKey : LeanXmss.PublicKey) (input : OracleWorld.Domain) :
    LeanXmss.Security.IsAttributed publicKey input ↔ IsParameterQuery publicKey.parameter input := by
  cases input <;> exact Iff.rfl

theorem realRest_eq_gameRest (adversary : LeanXmss.Security.Adversary)
    (publicKey : LeanXmss.PublicKey) (secretKey : LeanXmss.Seeded.SecretKey) :
    (LeanXmss.Security.gameRest adversary publicKey secretKey : OracleComp OracleWorld Bool) =
      realRest adversary publicKey secretKey := rfl

theorem expectedAttributedQueries_eq (adversary : LeanXmss.Security.Adversary) :
    LeanXmss.Security.expectedAttributedQueries adversary = realAttributedMean adversary := by
  unfold LeanXmss.Security.expectedAttributedQueries LeanXmss.Security.attributedExperiment
    realAttributedMean realCounted
  rw [countMeanFrom_lift_sample_bind, OracleComp.tsum_prEvent_bind_mul]
  refine tsum_congr fun keySeed => congrArg _ ?_
  have hkeygen : (liftM (OracleWorld.query (.inr (LeanXmss.seedHashInput keySeed))) >>=
        countedAfterSeed adversary : OracleComp OracleWorld (Bool × Nat)) =
      (liftM (show OracleComp HashSpec _ from LeanXmss.Seeded.keygenFromSeed keySeed) :
        OracleComp OracleWorld _) >>= fun keys =>
        QueryCounting.counted (IsParameterQuery keys.1.parameter)
          (realRest adversary keys.1 keys.2) := by
    rw [keygenFromSeed_eq, liftM_bind, bind_assoc]
    rfl
  rw [hkeygen]
  unfold countMeanFrom
  rw [run'_lift_hash_bind]
  conv_rhs => rw [OracleComp.tsum_prEvent_bind_mul]
  conv_lhs => rw [OracleComp.tsum_prEvent_bind_mul]
  apply tsum_congr
  intro keys
  congr 1
  have himpl : LeanXmss.Security.attributedOracle keys.1.1 =
      romImpl.withAddCost (fun input => if IsParameterQuery keys.1.1.parameter input then 1 else 0) := by
    unfold LeanXmss.Security.attributedOracle
    congr 1
  rw [himpl, realRest_eq_gameRest]
  conv_rhs => rw [QueryCounting.simulate_withCost]

theorem attributed_arithmetic (q : Nat) (hK : keygenQueries ≤ q) (hq : q < 2 ^ 127)
    (model real : ℝ≥0∞)
    (hmodel : model ≤ real + (((q - 1) * (q - 1) : Nat) / ((2 ^ 256 : Nat) : ℝ≥0∞) +
      ((q - keygenQueries) * (q - keygenQueries) : Nat) / ((2 ^ 256 : Nat) : ℝ≥0∞))) :
    (2 * model + firstLaneExpectedSlack) / ((2 ^ 128 : Nat) : ℝ≥0∞) +
        4 * (((q - keygenQueries + forgeryProbeCount : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞)) *
          ((model + firstLaneExpectedSlack) / ((2 ^ 128 : Nat) : ℝ≥0∞)) +
        ((q - keygenQueries : Nat) : ℝ≥0∞) / ((2 ^ 256 : Nat) : ℝ≥0∞) +
        ((q - 1 : Nat) : ℝ≥0∞) / ((2 ^ 256 : Nat) : ℝ≥0∞) ≤
      (2 * real + 2 ^ 10) / ((2 ^ 128 : Nat) : ℝ≥0∞) +
        4 * q * (real + 2 ^ 10) / ((2 ^ 256 : Nat) : ℝ≥0∞) +
        2 * q / ((2 ^ 256 : Nat) : ℝ≥0∞) := by
  have hKeq := keygenQueries_eq
  have hslack : firstLaneExpectedSlack = 674 := by
    simp [firstLaneExpectedSlack, verifyHashBound, forgeryProbeCount, numChains, chainLength,
      winternitzBits, treeHeight]
  have hprobes : forgeryProbeCount = 290 := by
    simp [forgeryProbeCount, numChains, chainLength, winternitzBits]
  -- The guesses' share of the count is below one half.
  have hguess : (((q - 1) * (q - 1) : Nat) / ((2 ^ 256 : Nat) : ℝ≥0∞) +
      ((q - keygenQueries) * (q - keygenQueries) : Nat) / ((2 ^ 256 : Nat) : ℝ≥0∞)) ≤ 1 / 2 := by
    rw [← ENNReal.add_div, ← Nat.cast_add]
    rw [ENNReal.div_le_iff (by norm_num) (by norm_num)]
    have hsq : (q - 1) * (q - 1) + (q - keygenQueries) * (q - keygenQueries) ≤ 2 ^ 255 := by
      have h1 : (q - 1) * (q - 1) ≤ 2 ^ 254 := by
        calc (q - 1) * (q - 1) ≤ 2 ^ 127 * 2 ^ 127 := Nat.mul_le_mul (by omega) (by omega)
          _ = 2 ^ 254 := by norm_num
      have h2 : (q - keygenQueries) * (q - keygenQueries) ≤ 2 ^ 254 := by
        calc (q - keygenQueries) * (q - keygenQueries) ≤ 2 ^ 127 * 2 ^ 127 :=
            Nat.mul_le_mul (by omega) (by omega)
          _ = 2 ^ 254 := by norm_num
      calc _ ≤ 2 ^ 254 + 2 ^ 254 := Nat.add_le_add h1 h2
        _ = 2 ^ 255 := by norm_num
    calc (((q - 1) * (q - 1) + (q - keygenQueries) * (q - keygenQueries) : Nat) : ℝ≥0∞)
        ≤ ((2 ^ 255 : Nat) : ℝ≥0∞) := by exact_mod_cast hsq
      _ = 1 / 2 * ((2 ^ 256 : Nat) : ℝ≥0∞) := by
        rw [show (2 ^ 256 : Nat) = 2 * 2 ^ 255 by norm_num, Nat.cast_mul, ← mul_assoc,
          show ((2 : Nat) : ℝ≥0∞) = 2 by norm_num, one_div, ENNReal.inv_mul_cancel (by norm_num)
            (by norm_num), one_mul]
  have hmodel' : model ≤ real + 1 / 2 := hmodel.trans (add_le_add le_rfl hguess)
  have hfuel : ((q - keygenQueries + forgeryProbeCount : Nat) : ℝ≥0∞) ≤ q := by
    exact_mod_cast (show q - keygenQueries + forgeryProbeCount ≤ q by omega)
  have hmain : 2 * model + (firstLaneExpectedSlack : ℝ≥0∞) ≤ 2 * real + 2 ^ 10 := by
    calc 2 * model + (firstLaneExpectedSlack : ℝ≥0∞) ≤ 2 * (real + 1 / 2) + 674 := by
          rw [hslack]
          push_cast
          gcongr
      _ = 2 * real + 675 := by
          rw [mul_add, show (2 : ℝ≥0∞) * (1 / 2) = 1 by
            rw [one_div, ENNReal.mul_inv_cancel (by norm_num) (by norm_num)], add_assoc]
          norm_num
      _ ≤ 2 * real + 2 ^ 10 := by gcongr; norm_num
  have hsecond : model + (firstLaneExpectedSlack : ℝ≥0∞) ≤ real + 2 ^ 10 := by
    calc model + (firstLaneExpectedSlack : ℝ≥0∞) ≤ real + 1 / 2 + 674 := by
          rw [hslack]
          push_cast
          gcongr
      _ ≤ real + 1 + 674 := by
          gcongr
          exact ENNReal.half_le_self
      _ ≤ real + 2 ^ 10 := by
          rw [add_assoc]
          gcongr
          norm_num
  have hguesses : ((q - keygenQueries : Nat) : ℝ≥0∞) / ((2 ^ 256 : Nat) : ℝ≥0∞) +
      ((q - 1 : Nat) : ℝ≥0∞) / ((2 ^ 256 : Nat) : ℝ≥0∞) ≤ 2 * q / ((2 ^ 256 : Nat) : ℝ≥0∞) := by
    rw [← ENNReal.add_div]
    gcongr
    calc ((q - keygenQueries : Nat) : ℝ≥0∞) + ((q - 1 : Nat) : ℝ≥0∞) ≤ q + q := by
          gcongr <;> exact_mod_cast Nat.sub_le _ _
      _ = 2 * q := by ring
  have h256 : ((2 ^ 256 : Nat) : ℝ≥0∞) = ((2 ^ 128 : Nat) : ℝ≥0∞) * ((2 ^ 128 : Nat) : ℝ≥0∞) := by
    norm_num
  calc
    _ ≤ (2 * real + 2 ^ 10) / ((2 ^ 128 : Nat) : ℝ≥0∞) +
          4 * ((q : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞)) *
            ((real + 2 ^ 10) / ((2 ^ 128 : Nat) : ℝ≥0∞)) +
          2 * q / ((2 ^ 256 : Nat) : ℝ≥0∞) := by
      rw [add_assoc _ (((q - keygenQueries : Nat) : ℝ≥0∞) / _)]
      gcongr
    _ = _ := by
      congr 2
      rw [h256, ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul,
        ENNReal.mul_inv (by norm_num) (by norm_num)]
      ring

/-- **leanXMSS, attributed.** -/
theorem leanXmss_attributedSecurity : LeanXmss.LeanXmssAttributedSecurityStatement := by
  intro q hq adversary hbound
  have hseeded := seededBudget adversary q (by omega) hbound
  have hK := keygenQueries_le adversary q hseeded
  have hmodel := concreteScheme_afterKeygenSecurity_expected (q - keygenQueries) (by omega)
    (modelAdversary adversary) (afterKeygenBudget adversary q (by omega) hseeded)
  have hcount := expectedParameterQueries_le_realAttributedMean adversary q (by omega) hseeded
  rw [expectedAttributedQueries_eq]
  calc LeanXmss.Security.forgeAdvantage adversary
      ≤ Pr{let x ← (simulateQ romImpl (innerGame adversary)).run' ∅}[x = true] +
        ((q - 1 : Nat) : ℝ≥0∞) / ((2 ^ 256 : Nat) : ℝ≥0∞) :=
          forgeAdvantage_le_inner adversary q hseeded
    _ = Pr{let x ← sampleMasterSeed >>= tableGame adversary}[x = true] +
        ((q - 1 : Nat) : ℝ≥0∞) / ((2 ^ 256 : Nat) : ℝ≥0∞) := by rw [innerGame_eq_tableGame]
    _ ≤ Pr{let x ← cleanGame adversary}[x = true] +
        ((q - keygenQueries : Nat) : ℝ≥0∞) / ((2 ^ 256 : Nat) : ℝ≥0∞) +
          ((q - 1 : Nat) : ℝ≥0∞) / ((2 ^ 256 : Nat) : ℝ≥0∞) :=
      add_le_add (tableGame_le_clean adversary q (by omega) hseeded) le_rfl
    _ ≤ Pr{let x ← refGame adversary}[x = true] +
        ((q - keygenQueries : Nat) : ℝ≥0∞) / ((2 ^ 256 : Nat) : ℝ≥0∞) +
          ((q - 1 : Nat) : ℝ≥0∞) / ((2 ^ 256 : Nat) : ℝ≥0∞) :=
      add_le_add (add_le_add (cleanGame_le_ref adversary) le_rfl) le_rfl
    _ = forgeAdvantage Concrete.scheme (modelAdversary adversary) +
        ((q - keygenQueries : Nat) : ℝ≥0∞) / ((2 ^ 256 : Nat) : ℝ≥0∞) +
          ((q - 1 : Nat) : ℝ≥0∞) / ((2 ^ 256 : Nat) : ℝ≥0∞) := by rw [refGame_eq]
    _ ≤ _ := add_le_add (add_le_add hmodel le_rfl) le_rfl
    _ ≤ _ := attributed_arithmetic q hK hq _ _ hcount

end XmssSecurity.Bridge
