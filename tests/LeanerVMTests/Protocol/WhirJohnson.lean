import LeanerVM.Protocol.Whir.Deployed

/-!
# The opening's interfaces in the Johnson regime, at leanVM's parameters

Category B: Annex B's `thm:mca-johnson` and `thm:rbr`
(`doc/leanvm/body/b-polynomial-commitment-scheme.tex` at leanVM pin
`a386121f84292f6fa663aaa3e570c15bc0240ea2`), the deployed slacks of `scripts/dump-whir-eta-rust.sh`.

* **Annex B's constant.** `mcaConstant n D η` is the formula of `thm:mca-johnson`, transcribed
  below with the Annex's `ρ^{3/2}`, so that a pin bump that changes ArkLib's
  `johnsonComparisonEstimate` is caught.
* **The slacks.** Every entry of the table is a positive normal double below `1`, and two decode
  to the rationals of the probe record (`docs/reviews/whir-mca-budget.md`).
* **Every deployed level.** For each of the 224 levels of the 56 admissible ladders: the level fits
  (`Fits`), so the hypotheses of `mcaJohnson_annexB` hold (`1 ≤ D ≤ n - 2`, `0 < η`,
  `√ρ + η ≤ 1`); and the MCA share of a fold challenge is at most `2 ^ -128`:
  `2 ^ (ℓ - 1) · mcaConstant n D η ≤ 2 ^ 64`, each level's ceilings proved from rational bounds on
  `√ρ` (`mcaConstant_le`).
* **The numbers.** The threshold and list bound at two levels, the range of the list bound `L_0`
  of level 0 over the window, the deployed chain's levels against the ladder, and the exact
  multiplicity where the Rust's double rounding differs.
* **Mutations.** The threshold one off in either direction, and a slack past `1 - √ρ`, do not fit.
-/

namespace LeanerVMTests.Protocol.WhirJohnson

open LeanerVM.Parameters LeanerVM.Parameters.Whir LeanerVM.Protocol LeanerVM.Protocol.Whir
  ReedSolomon.HiddenDerivative

/-! ## Annex B's constant -/

/-- `thm:mca-johnson`'s `a` (`\mcanum`), transcribed: block length `n`, degree bound `D`
(dimension `k = D + 1`), the slightly reduced rate `ρ = (k - 1) / n`, slack `η`, radius
`γ = 1 - √ρ - η`, `θ = max ⌈√ρ / η⌉ 3`, and
`a = (2 (θ + ½)^5 + 3 (θ + ½) γ ρ) / (3 ρ^{3/2}) · n + (θ + ½) / √ρ`. -/
noncomputable def annexConstant (n D : ℕ) (η : ℝ) : ℝ :=
  let ρ : ℝ := (D : ℝ) / n
  let γ : ℝ := 1 - √ρ - η
  let θ : ℕ := max ⌈√ρ / η⌉₊ 3
  (2 * ((θ : ℝ) + 1 / 2) ^ 5 + 3 * ((θ : ℝ) + 1 / 2) * γ * ρ) / (3 * ρ ^ (3 / 2 : ℝ)) * n +
    ((θ : ℝ) + 1 / 2) / √ρ

/-- `mcaConstant` is Annex B's constant. -/
example (n D : ℕ) (η : ℝ) : mcaConstant n D η = annexConstant n D η := by
  unfold mcaConstant johnsonComparisonEstimate johnsonComparisonShift
    johnsonComparisonMultiplicity johnsonGamma johnsonAgreement annexConstant
  dsimp only
  rw [johnson_sqrt_cube_eq_rpow_three_halves]
  simp only [johnsonRhoMinus, Real.rpow_eq_pow]
  ring

/-! ## The slacks -/

/-- Every slack is a positive normal double below `1`: sign `0`, biased exponent in `1..1022`. -/
example : ∀ row ∈ slackTable, ∀ entry ∈ row, ∀ b ∈ entry, 2 ^ 52 ≤ b ∧ b < 1023 * 2 ^ 52 := by
  decide +kernel

/-- Level 0 of `(15, 1)` and level 5 of `(28, 4)`, the record's two levels. -/
example : (slacks 15 1).map (·.head?) = some (some (8247514870967899 / 2 ^ 62)) := by
  decide +kernel

example : (slacks 28 4).map (·[5]?) = some (some (7354347395230781 / 2 ^ 64)) := by
  decide +kernel

/-! ## Every deployed level -/

/-- The levels' codes and slacks: fold count `ℓ`, message variables `κ`, rate exponent `R`, slack
`η`, of the ladder of `μ` variables. -/
def codes : ℕ → List Level → List ℚ → List (ℕ × ℕ × ℕ × ℚ)
  | rem, l :: ls, η :: es => (l.fold, rem - l.fold, l.logInvRate, η) :: codes (rem - l.fold) ls es
  | _, _, _ => []

/-- The codes of an admissible ladder. -/
def ladderCodes (μ R : ℕ) : List (ℕ × ℕ × ℕ × ℚ) :=
  ((ladder μ R).bind fun ls ↦ (slacks μ R).map fun es ↦ codes μ ls es).getD []

/-- Every level of every admissible ladder. -/
def window : List (ℕ × ℕ × ℕ × ℚ) :=
  (List.range 14).flatMap fun i ↦ (List.range 4).flatMap fun r ↦ ladderCodes (i + 15) (r + 1)

/-- There are 224 of them. -/
example : window.length = 224 := by decide +kernel

/-- Every level fits. -/
theorem window_fits : ∀ x ∈ window, Fits x.2.1 x.2.2.1 x.2.2.2 := by decide +kernel

/-- **The hypotheses of `mcaJohnson_annexB` hold at every deployed level**: `1 ≤ D ≤ n - 2`,
`0 < η`, `√ρ + η ≤ 1`, with `n = 2 ^ (κ + R)`, `D = 2 ^ κ - 1`, `ρ = D / n`. -/
theorem window_mcaJohnson_hyps : ∀ x ∈ window,
    1 ≤ 2 ^ x.2.1 - 1 ∧ 2 ^ x.2.1 - 1 ≤ 2 ^ (x.2.1 + x.2.2.1) - 2 ∧ (0 : ℝ) < x.2.2.2 ∧
      √(((2 ^ x.2.1 - 1 : ℕ) : ℝ) / (2 ^ (x.2.1 + x.2.2.1) : ℕ)) + x.2.2.2 ≤ 1 :=
  fun x hx ↦ (window_fits x hx).mcaJohnson_hyps

/-- A lower bound on `√(D / n)`: `⌊√(D n 2^80)⌋ / (n 2^40)`. -/
def sqrtLower (n D : ℕ) : ℚ := (sqrtGuess (D * n * 2 ^ 80) : ℚ) / (n * 2 ^ 40)

/-- The multiplicity `max ⌈√(D / n) / η⌉ 3`, as the least `k` with `D q² ≤ k² p² n` for
`η = p / q`, from a guess at the root. -/
def multiplicity (n D : ℕ) (η : ℚ) : ℕ :=
  let p := η.num.toNat
  let q := η.den
  let r := sqrtGuess (D * q ^ 2 / (p ^ 2 * n))
  max (if D * q ^ 2 ≤ r * r * (p ^ 2 * n) then r else r + 1) 3

/-- **An upper bound on Annex B's constant from rational bounds**: with `ρ = D / n`, if
`0 < l ≤ √ρ` (as `l² ≤ ρ`), `θ ≥ 3` with `⌈√ρ / η⌉ ≤ θ` (as `ρ ≤ (θ η)²`), `0 < η` and
`√ρ + η ≤ 1`, then `mcaConstant n D η` is at most the formula with `θ` for its multiplicity, `l`
for `√ρ` and `1 - l - η` for `γ`. -/
private theorem mcaConstant_le {n D θ : ℕ} {η l : ℝ} (hl : 0 < l) (hlρ : l ^ 2 ≤ (D : ℝ) / n)
    (hθ : 3 ≤ θ) (hθρ : (D : ℝ) / n ≤ (θ * η) ^ 2) (hη : 0 < η) (hone : √((D : ℝ) / n) + η ≤ 1) :
    mcaConstant n D η ≤
      (2 * (θ + 1 / 2) ^ 5 + 3 * (θ + 1 / 2) * (1 - l - η) * ((D : ℝ) / n)) / (3 * l ^ 3) * n +
        (θ + 1 / 2) / l := by
  have hρ : (0 : ℝ) ≤ (D : ℝ) / n := by positivity
  have hls : l ≤ √((D : ℝ) / n) := (Real.le_sqrt hl.le hρ).mpr hlρ
  have hs : 0 < √((D : ℝ) / n) := hl.trans_le hls
  have hM : (johnsonComparisonMultiplicity n D η : ℝ) ≤ θ := by
    have hsη : √((D : ℝ) / n) / η ≤ θ := by
      rw [div_le_iff₀ hη]
      exact Real.sqrt_le_iff.mpr ⟨by positivity, hθρ⟩
    exact_mod_cast max_le (Nat.ceil_le.mpr hsη) hθ
  have hγ : 0 ≤ johnsonGamma n D η := by
    unfold johnsonGamma johnsonAgreement johnsonRhoMinus; linarith
  have hγle : johnsonGamma n D η ≤ 1 - l - η := by
    unfold johnsonGamma johnsonAgreement johnsonRhoMinus; linarith
  unfold mcaConstant johnsonComparisonEstimate johnsonComparisonShift
  simp only [johnsonRhoMinus] at *
  gcongr
  exact add_nonneg (by positivity) (mul_nonneg (mul_nonneg (by positivity) (hγ.trans hγle)) hρ)

/-- `mcaConstant_le`'s bound at the computed `l` and `θ`. -/
def constantBound (n D : ℕ) (η : ℚ) : ℚ :=
  let ρ : ℚ := (D : ℚ) / n
  let l := sqrtLower n D
  let θ : ℚ := multiplicity n D η
  (2 * (θ + 1 / 2) ^ 5 + 3 * (θ + 1 / 2) * (1 - l - η) * ρ) / (3 * l ^ 3) * n + (θ + 1 / 2) / l

/-- The certificate at a level: `0 < l`, `l² ≤ ρ`, `ρ ≤ (θ η)²`, and the budget at the bound. -/
def budgetCert (x : ℕ × ℕ × ℕ × ℚ) : Prop :=
  let n := 2 ^ (x.2.1 + x.2.2.1)
  let D := 2 ^ x.2.1 - 1
  0 < sqrtLower n D ∧ sqrtLower n D ^ 2 ≤ (D : ℚ) / n ∧
    (D : ℚ) / n ≤ ((multiplicity n D x.2.2.2 : ℚ) * x.2.2.2) ^ 2 ∧
    (2 : ℚ) ^ (x.1 - 1) * constantBound n D x.2.2.2 ≤ 2 ^ 64

instance (x : ℕ × ℕ × ℕ × ℚ) : Decidable (budgetCert x) := by
  unfold budgetCert; infer_instance

/-- The certificate holds at every deployed level. -/
theorem window_budgetCert : ∀ x ∈ window, budgetCert x := by decide +kernel

/-- The budget at a level from its certificate. -/
private theorem budget_of_cert {ℓ n D : ℕ} {η : ℚ} (hl : 0 < sqrtLower n D)
    (hlρ : sqrtLower n D ^ 2 ≤ (D : ℚ) / n)
    (hθρ : (D : ℚ) / n ≤ ((multiplicity n D η : ℚ) * η) ^ 2)
    (hb : (2 : ℚ) ^ (ℓ - 1) * constantBound n D η ≤ 2 ^ 64) (hη : (0 : ℝ) < η)
    (hone : √((D : ℝ) / n) + η ≤ 1) :
    (2 : ℝ) ^ (ℓ - 1) * mcaConstant n D η ≤ 2 ^ 64 := by
  have hθ : 3 ≤ multiplicity n D η := le_max_right _ _
  have hlρ' : ((sqrtLower n D : ℚ) : ℝ) ^ 2 ≤ (D : ℝ) / n := by
    have h := (Rat.cast_le (K := ℝ)).mpr hlρ
    rwa [Rat.cast_pow, Rat.cast_div, Rat.cast_natCast, Rat.cast_natCast] at h
  have hθρ' : (D : ℝ) / n ≤ ((multiplicity n D η : ℝ) * η) ^ 2 := by
    have h := (Rat.cast_le (K := ℝ)).mpr hθρ
    rwa [Rat.cast_pow, Rat.cast_mul, Rat.cast_div, Rat.cast_natCast, Rat.cast_natCast,
      Rat.cast_natCast] at h
  have hle := mcaConstant_le (θ := multiplicity n D η) (l := (sqrtLower n D : ℝ))
    (by exact_mod_cast hl) hlρ' hθ hθρ' hη hone
  have hb' : (2 : ℝ) ^ (ℓ - 1) * (constantBound n D η : ℝ) ≤ 2 ^ 64 := by
    have h := (Rat.cast_le (K := ℝ)).mpr hb
    rwa [Rat.cast_mul, Rat.cast_pow, Rat.cast_pow, Rat.cast_ofNat] at h
  refine le_trans (mul_le_mul_of_nonneg_left hle (by positivity)) (le_trans (le_of_eq ?_) hb')
  simp only [constantBound]
  push_cast
  ring

/-- **The MCA share of every deployed fold challenge is at most `2 ^ -128`**:
`2 ^ (ℓ - 1) · mcaConstant n D η ≤ 2 ^ 64` at every level, so the fold row's
`2 ^ (ℓ - j - 1) N / |E|` with `N = ⌊mcaConstant n D η⌋₊` is at most `2 ^ 64 / 2 ^ 192`. -/
theorem window_budget : ∀ x ∈ window,
    (2 : ℝ) ^ (x.1 - 1) * mcaConstant (2 ^ (x.2.1 + x.2.2.1)) (2 ^ x.2.1 - 1) x.2.2.2 ≤ 2 ^ 64 := by
  intro x hx
  obtain ⟨hl, hlρ, hθρ, hb⟩ := window_budgetCert x hx
  obtain ⟨-, -, hη, hone⟩ := (window_fits x hx).mcaJohnson_hyps
  exact budget_of_cert hl hlρ hθρ hb hη hone

/-! ## The numbers -/

/-- Level 0 of `(15, 1)`: `n = 2 ^ 10`, `D = 511`, threshold `726`, list bound `57` (the Annex's
`1 / (2 η √ρ)` is `395.8`). -/
example : threshold 9 1 (8247514870967899 / 2 ^ 62) = 726 := by decide +kernel
example : Code.pairwiseJohnsonListBound (2 ^ 10) 511 726 = 57 := by decide

/-- Level 5 of `(28, 4)`: `n = 2 ^ 21`, `D = 3`, threshold `3345`, list bound `1431`. -/
example : threshold 2 19 (7354347395230781 / 2 ^ 64) = 3345 := by decide +kernel
example : Code.pairwiseJohnsonListBound (2 ^ 21) 3 3345 = 1431 := by decide

/-- There the exact multiplicity `⌈√ρ / η⌉` is `4`, where the Rust's doubles give `3`. -/
example : multiplicity (2 ^ 21) 3 (7354347395230781 / 2 ^ 64) = 4 := by decide +kernel

/-- The list bound `L_0` of level 0 ranges over `23 .. 122` on the window (the Annex's
`1 / (2 η₀ √ρ₀)` over `110 .. 648`). -/
def listSizes0 : List ℕ :=
  (List.range 14).flatMap fun i ↦ (List.range 4).filterMap fun r ↦
    (ladderCodes (i + 15) (r + 1)).head?.map fun x ↦
      Code.pairwiseJohnsonListBound (2 ^ (x.2.1 + x.2.2.1)) (2 ^ x.2.1 - 1)
        (threshold x.2.1 x.2.2.1 x.2.2.2)

example : listSizes0.length = 56 ∧ listSizes0.min? = some 23 ∧ listSizes0.max? = some 122 := by
  decide +kernel

/-- The shapes of a chain. -/
def shapes : {sh : Shape} → {κ : ℕ} → Ladder sh κ → List (ℕ × ℕ × ℕ)
  | sh, _, .last _ _ => [(sh.ℓ, sh.R, sh.t)]
  | sh, _, .cons _ L => (sh.ℓ, sh.R, sh.t) :: shapes L

/-- The deployed chain runs the ladder's levels, with their query counts. -/
example : (List.range 14).all fun i ↦ (List.range 4).all fun r ↦
    (deployed (i + 15) (r + 1)).map (fun c ↦ shapes c.ladder) ==
      (ladder (i + 15) (r + 1)).map (·.map fun l ↦ (l.fold, l.logInvRate, l.queries)) := by
  decide +kernel

/-! ## Mutations -/

/-- At level 0 of `(15, 1)`, the threshold one lower or one higher does not fit: `725` is below
the agreement, `727` is not its ceiling. -/
example : ¬ FitsAt 9 1 8247514870967899 (2 ^ 62) 725 ∧
    ¬ FitsAt 9 1 8247514870967899 (2 ^ 62) 727 ∧ FitsAt 9 1 8247514870967899 (2 ^ 62) 726 := by
  decide +kernel

/-- A slack past `1 - √ρ` (here `√(511 / 1024) + 3 / 10 > 1`) does not fit: the threshold
exceeds the block length. -/
example : ¬ Fits 9 1 (3 / 10) := by decide +kernel

/-- A zero slack does not fit. -/
example : ¬ Fits 9 1 0 := by decide +kernel

end LeanerVMTests.Protocol.WhirJohnson
