/-
  LeanerVM.Protocol.Whir.Johnson

  The interfaces of the soundness of WHIR's opening in the Johnson regime: the encoder's code as
  ArkLib's Reed–Solomon code, mutual correlated agreement at Annex B's constant, the list bound of
  the pairwise Johnson bound, the agreement threshold of a slack, and the parameters of a level.
-/

module

public import LeanerVM.Protocol.Whir.FoldSound
public import LeanerVM.Protocol.ToArkLib.McaJohnson
public import ArkLib.Data.CodingTheory.JohnsonBound.Pairwise

/-!
# The interfaces in the Johnson regime

Category B: Annex B, `thm:mca-johnson` and `thm:johnson-interleaved`
(`doc/leanvm/body/b-polynomial-commitment-scheme.tex`), at leanVM pin
`a386121f84292f6fa663aaa3e570c15bc0240ea2`.

The soundness of WHIR's opening (`whirOpen_rbrSoundness`) takes, per level, an agreement
threshold `a` with a list bound `L` (`ListBound`) and a bound `N` on the bad folds (`McaBound`).
This module inhabits both at the Johnson radius `γ = 1 - √ρ - η`, from ArkLib.

* **The code.** The encoder's words on `2 ^ (κ + R)` positions are ArkLib's Reed–Solomon code
  `code (domainEmb κ R hb) (2 ^ κ)` on the points `x_v` of `K`: every encoding is a codeword
  (`encode_mem_code`), and every codeword is an encoding (`exists_encode_of_mem_code`), since the
  `2 ^ κ` novel polynomials span the polynomials of degree below `2 ^ κ`.
* **Mutual correlated agreement.** `mcaConstant n D η` is Annex B's `a` of `thm:mca-johnson` (in
  `Whir` the letter `a` is the threshold, and the constant is the `N` of `McaBound`), ArkLib's
  `johnsonComparisonEstimate`; `mcaJohnson_annexB` is `McaJohnson F mcaConstant` over every finite
  field. `mcaBound_of_mcaJohnson` turns `McaJohnson` into `McaBound` at `N = ⌊a n D η⌋₊`, with
  `n = 2 ^ (κ + R)` and `D = 2 ^ κ - 1`, for every threshold `a ≥ (√ρ + η) n`: `McaBad` is the
  event of ArkLib's `IsMCA` for the fold line `(1 - c, c)`, whose error is the affine line's
  (`mcaError_foldLine_eq_affineLine`).
* **The list bound.** Two interleaved codewords agree on fewer than `2 ^ κ` positions, so
  ArkLib's pairwise Johnson bound over the alphabet of rows gives `ListBound` at
  `L = ⌊n (a - D) / (a² - n D)⌋` (`listBound_johnson`), not the Annex's `1 / (2 η √ρ)`.
* **A level.** `threshold κ R η` computes `⌈(√ρ + η) n⌉₊` in naturals, for a rational slack;
  `Fits κ R η` is the decidable list of facts the interfaces need of it, among them that the
  computed value is that ceiling (`threshold_eq_ceil`); `johnsonPar` is the level's `Par` from
  them, with the list bound `L`, and `N = ⌊mcaConstant n D η⌋₊`.
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters CompPoly CMlPolynomialEval ReedSolomon ReedSolomon.HiddenDerivative
  CoreDefinitions LinearCode

@[expose] public section

namespace Whir

/-! ## The encoder's code is a Reed–Solomon code -/

/-- A position below `2 ^ (κ + R) ≤ 2 ^ 64` is below `2 ^ 64`. -/
private theorem lt_two_pow_64 {κ R : ℕ} (hb : κ + R ≤ 64) (v : Fin (2 ^ (κ + R))) :
    v.val < 2 ^ 64 :=
  v.2.trans_le (Nat.pow_le_pow_right (by norm_num) hb)

/-- The code's domain: position `v` is the point `x_v` of `K`, in `E`. -/
def domainEmb (κ R : ℕ) (hb : κ + R ≤ 64) : Fin (2 ^ (κ + R)) ↪ E where
  toFun v := algebraMap K E (domainPt v)
  inj' v w h := by
    exact Fin.ext (domainPt_injOn (lt_two_pow_64 hb v) (lt_two_pow_64 hb w)
      ((algebraMap K E).injective h))

open Polynomial in
/-- The polynomial with novel-basis coefficients `m`. -/
private noncomputable def msgPoly (κ : ℕ) (m : Fin (2 ^ κ) → E) : E[X] :=
  ∑ u : Fin (2 ^ κ), Polynomial.C (m u) * (novelPoly κ u).map (algebraMap K E)

open Polynomial in
/-- It has degree below `2 ^ κ`. -/
private theorem msgPoly_mem {κ : ℕ} (hκ : κ ≤ 64) (m : Fin (2 ^ κ) → E) :
    msgPoly κ m ∈ degreeLT E (2 ^ κ) := by
  refine Submodule.sum_mem _ fun u _ ↦ ?_
  rw [← smul_eq_C_mul]
  refine Submodule.smul_mem _ _ (mem_degreeLT.mpr ?_)
  refine (degree_map_le).trans_lt ((degree_le_natDegree).trans_lt ?_)
  rw [natDegree_novelPoly hκ u.2]
  exact_mod_cast u.2

/-- The encoding of `m` evaluates `msgPoly` on the domain. -/
private theorem encode_eq_msgPoly {κ R : ℕ} (hκ : κ ≤ 64) (m : CMlPolynomialEval E κ)
    (v : Fin (2 ^ (κ + R))) :
    encode (algebraMap K E) κ R m v =
      (msgPoly κ fun u ↦ m[u]).eval (algebraMap K E (domainPt v)) := by
  rw [encode_eq_eval (algebraMap K E) hκ]
  rfl

/-- **An encoding is a codeword** of the Reed–Solomon code of dimension `2 ^ κ` on the domain. -/
theorem encode_mem_code {κ R : ℕ} (hb : κ + R ≤ 64) (m : CMlPolynomialEval E κ) :
    (fun v ↦ encode (algebraMap K E) κ R m v) ∈ code (domainEmb κ R hb) (2 ^ κ) :=
  mem_code_iff_eval.mpr ⟨_, Polynomial.mem_degreeLT.mp (msgPoly_mem (by omega) _),
    fun v ↦ (encode_eq_msgPoly (by omega) m v).symm⟩

open Polynomial in
/-- The polynomials with novel-basis coefficients are all the polynomials of degree below
`2 ^ κ`: the map from coefficients is injective (the encoder is) between spaces of dimension
`2 ^ κ`. -/
private theorem exists_msgPoly_eq {κ : ℕ} (hκ : κ ≤ 64) {p : E[X]}
    (hp : p ∈ degreeLT E (2 ^ κ)) : ∃ m : Fin (2 ^ κ) → E, msgPoly κ m = p := by
  let f : (Fin (2 ^ κ) → E) →ₗ[E] degreeLT E (2 ^ κ) :=
    { toFun m := ⟨msgPoly κ m, msgPoly_mem hκ m⟩
      map_add' m m' := Subtype.ext (by
        simp only [msgPoly, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib,
          Submodule.coe_add])
      map_smul' c m := Subtype.ext (by
        simp only [msgPoly, Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc, ← Finset.mul_sum,
          RingHom.id_apply, Submodule.coe_smul, smul_eq_C_mul]) }
  have hinj : Function.Injective f := by
    intro m m' h
    have h' : msgPoly κ m = msgPoly κ m' := congrArg Subtype.val h
    have he : encode (algebraMap K E) κ 0 (Vector.ofFn m) =
        encode (algebraMap K E) κ 0 (Vector.ofFn m') := funext fun v ↦ by
      rw [encode_eq_msgPoly hκ, encode_eq_msgPoly hκ]
      simp only [Fin.getElem_fin, Vector.getElem_ofFn]
      exact congrArg (Polynomial.eval _) h'
    have := encode_injective (algebraMap K E) hκ (algebraMap K E).injective he
    funext u
    simpa using congrArg (·[u]) this
  have hrank : Module.finrank E (Fin (2 ^ κ) → E) = Module.finrank E (degreeLT E (2 ^ κ)) := by
    rw [(degreeLTEquiv E (2 ^ κ)).finrank_eq]
  have : FiniteDimensional E (degreeLT E (2 ^ κ)) :=
    LinearEquiv.finiteDimensional (degreeLTEquiv E (2 ^ κ)).symm
  obtain ⟨m, hm⟩ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).mp hinj
    ⟨p, hp⟩
  exact ⟨m, congrArg Subtype.val hm⟩

/-- **A codeword is an encoding**: every word of the Reed–Solomon code of dimension `2 ^ κ` on the
domain is the encoding of a message. -/
theorem exists_encode_of_mem_code {κ R : ℕ} (hb : κ + R ≤ 64) {c : Fin (2 ^ (κ + R)) → E}
    (hc : c ∈ code (domainEmb κ R hb) (2 ^ κ)) :
    ∃ m : CMlPolynomialEval E κ, ∀ v, encode (algebraMap K E) κ R m v = c v := by
  obtain ⟨p, hp, hpc⟩ := mem_code_iff_eval.mp hc
  obtain ⟨m, hm⟩ := exists_msgPoly_eq (by omega) (Polynomial.mem_degreeLT.mpr hp)
  refine ⟨Vector.ofFn m, fun v ↦ ?_⟩
  rw [encode_eq_msgPoly (by omega)]
  simp only [Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta]
  rw [hm]
  exact hpc v

/-! ## Mutual correlated agreement -/

/-- **Annex B's constant** `a` of `thm:mca-johnson` for a code of block length `n` and degree
bound `D` at slack `η`: with `ρ = D / n`, `θ = max ⌈√ρ / η⌉ 3` and `γ = 1 - √ρ - η`,
`(2 (θ + ½)^5 + 3 (θ + ½) γ ρ) / (3 ρ^{3/2}) · n + (θ + ½) / √ρ`, ArkLib's
`johnsonComparisonEstimate`. -/
noncomputable def mcaConstant (n D : ℕ) (η : ℝ) : ℝ := johnsonComparisonEstimate n D η

/-- **Mutual correlated agreement up to the Johnson bound at Annex B's constant**, over every
finite field (`thm:mca-johnson`). -/
theorem mcaJohnson_annexB (F : Type) [Field F] [Fintype F] [SampleableType F] :
    McaJohnson F mcaConstant :=
  mcaJohnson_comparisonEstimate F

/-- The event `McaBad` is ArkLib's MCA event for the fold line `(1 - c, c)`, the Reed–Solomon code
of dimension `2 ^ κ` on the domain, the pair of lanes, and any radius `δ` whose agreement
`(1 - δ) n` is at most the threshold. -/
private theorem isMCA_of_mcaBad {κ R a : ℕ} (hb : κ + R ≤ 64) {δ : ℝ}
    (hδ : (2 ^ (κ + R) : ℕ) * (1 - δ) ≤ a) {F : LW (κ + R)} {c : E}
    (h : McaBad κ R a F c) :
    IsMCA (FoldLineGenerator E) (code (domainEmb κ R hb) (2 ^ κ)) c
      ![fun y ↦ F y 0, fun y ↦ F y 1] δ := by
  obtain ⟨A, hA, ⟨m, hm⟩, hnot⟩ := h
  refine ⟨A, ?_, ?_, ?_⟩
  · rw [Fintype.card_fin, ge_iff_le]
    exact hδ.trans (by exact_mod_cast hA)
  · refine (mem_projectedCodeSubmod_iff _ _ _).mpr ⟨_, encode_mem_code hb m, funext fun y ↦ ?_⟩
    simp only [projectedWord, Set.domRestrict, Fin.sum_univ_two, FoldLineGenerator,
      Matrix.cons_val_zero, Matrix.cons_val_one, smul_eq_mul]
    exact (hm y y.2).symm
  · by_contra hall
    push Not at hall
    have hrow : ∀ j : Fin 2, ∃ m : CMlPolynomialEval E κ, ∀ y ∈ A,
        encode (algebraMap K E) κ R m y = F y j := by
      intro j
      obtain ⟨w, hw, hwA⟩ := (mem_projectedCodeSubmod_iff _ _ _).mp (hall j)
      obtain ⟨m, hm⟩ := exists_encode_of_mem_code hb hw
      refine ⟨m, fun y hy ↦ ?_⟩
      have := congrFun hwA ⟨y, hy⟩
      simp only [projectedWord, Set.domRestrict] at this
      rw [hm, ← this]
      fin_cases j <;> rfl
    obtain ⟨m₀, h₀⟩ := hrow 0
    obtain ⟨m₁, h₁⟩ := hrow 1
    exact hnot ⟨m₀, m₁, fun y hy ↦ ⟨h₀ y hy, h₁ y hy⟩⟩

/-- The hypotheses of `McaJohnson` at the code on `n = 2 ^ (κ + R)` positions with degree bound
`D = 2 ^ κ - 1`, from `κ, R ≥ 1` and a threshold with `(√ρ + η) n ≤ a ≤ n`: `1 ≤ D ≤ n - 2` and
`√ρ + η ≤ 1`. -/
private theorem mcaJohnson_hyps {κ R a : ℕ} {η : ℝ} (hκ : 1 ≤ κ) (hR : 1 ≤ R)
    (ha : (√(((2 ^ κ - 1 : ℕ) : ℝ) / (2 ^ (κ + R) : ℕ)) + η) * (2 ^ (κ + R) : ℕ) ≤ a)
    (han : a ≤ 2 ^ (κ + R)) :
    1 ≤ 2 ^ κ - 1 ∧ 2 ^ κ - 1 ≤ 2 ^ (κ + R) - 2 ∧
      √(((2 ^ κ - 1 : ℕ) : ℝ) / (2 ^ (κ + R) : ℕ)) + η ≤ 1 := by
  have h2 : 2 ≤ 2 ^ κ := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ κ := Nat.pow_le_pow_right (by norm_num) hκ
  have h2R : 2 * 2 ^ κ ≤ 2 ^ (κ + R) := by
    calc 2 * 2 ^ κ = 2 ^ (κ + 1) := by ring
      _ ≤ 2 ^ (κ + R) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hn : (0 : ℝ) < (2 ^ (κ + R) : ℕ) := by exact_mod_cast Nat.two_pow_pos _
  refine ⟨by omega, by omega, ?_⟩
  have : (√(((2 ^ κ - 1 : ℕ) : ℝ) / (2 ^ (κ + R) : ℕ)) + η) * (2 ^ (κ + R) : ℕ) ≤
      1 * (2 ^ (κ + R) : ℕ) := ha.trans (by rw [one_mul]; exact_mod_cast han)
  exact le_of_mul_le_mul_right this hn

/-- **The adaptor to `McaBound`.** Mutual correlated agreement up to the Johnson bound, with any
constant `c`, bounds the bad folds of the code on `2 ^ (κ + R)` positions of dimension `2 ^ κ`
at every threshold `a` with `(√ρ + η) 2 ^ (κ + R) ≤ a ≤ 2 ^ (κ + R)` by `⌊c n D η⌋₊`, with
`n = 2 ^ (κ + R)`, `D = 2 ^ κ - 1` and `ρ = D / n`. -/
theorem mcaBound_of_mcaJohnson {c : ℕ → ℕ → ℝ → ℝ} (hc : McaJohnson E c) {κ R a : ℕ} {η : ℝ}
    (hκ : 1 ≤ κ) (hR : 1 ≤ R) (hb : κ + R ≤ 64) (hη : 0 < η)
    (ha : (√(((2 ^ κ - 1 : ℕ) : ℝ) / (2 ^ (κ + R) : ℕ)) + η) * (2 ^ (κ + R) : ℕ) ≤ a)
    (han : a ≤ 2 ^ (κ + R)) :
    McaBound κ R a ⌊c (2 ^ (κ + R)) (2 ^ κ - 1) η⌋₊ := by
  intro F
  obtain ⟨hD, hDn, hone⟩ := mcaJohnson_hyps hκ hR ha han
  have hmca := hc.le (2 ^ (κ + R)) (domainEmb κ R hb) (2 ^ κ - 1) η hD hDn hη hone
  rw [Nat.sub_add_cancel Nat.one_le_two_pow, ← mcaError_foldLine_eq_affineLine] at hmca
  refine le_trans ?_ (natCard_isMCA_le_of_mcaError_le _ _ hmca ![fun y ↦ F y 0, fun y ↦ F y 1])
  refine Nat.card_le_card_of_injective (fun x ↦ ⟨x.1, isMCA_of_mcaBad hb ?_ x.2⟩)
    fun x y h ↦ Subtype.ext (by simpa using congrArg Subtype.val h)
  rw [show (1 : ℝ) - (1 - √(((2 ^ κ - 1 : ℕ) : ℝ) / (2 ^ (κ + R) : ℕ)) - η) =
    √(((2 ^ κ - 1 : ℕ) : ℝ) / (2 ^ (κ + R) : ℕ)) + η by ring, mul_comm]
  exact ha

/-- **An upper bound on Annex B's constant from rational bounds**: with `ρ = D / n`, if
`0 < l ≤ √ρ` (as `l² ≤ ρ`), `θ ≥ 3` with `⌈√ρ / η⌉ ≤ θ` (as `ρ ≤ (θ η)²`), `0 < η` and
`√ρ + η ≤ 1`, then `mcaConstant n D η` is at most the formula with `θ` for its multiplicity, `l`
for `√ρ` and `1 - l - η` for `γ`. -/
theorem mcaConstant_le {n D θ : ℕ} {η l : ℝ} (hl : 0 < l) (hlρ : l ^ 2 ≤ (D : ℝ) / n)
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

/-! ## The list bound -/

/-- **The list bound from the pairwise Johnson bound.** At a threshold `a ≥ 2 ^ κ` with
`n D < a²` (`n = 2 ^ (κ + R)`, `D = 2 ^ κ - 1`), at most `⌊n (a - D) / (a² - n D)⌋`
interleaved codewords of `2 ^ m` lanes agree with any word on `a` positions: two distinct ones
agree on at most `D` positions, since a message is determined by `2 ^ κ` values of its encoding. -/
theorem listBound_johnson {κ R a : ℕ} (m : ℕ) (hb : κ + R ≤ 64) (ha : 2 ^ κ ≤ a)
    (hpos : 2 ^ (κ + R) * (2 ^ κ - 1) < a * a) :
    ListBound κ R a m (Code.pairwiseJohnsonListBound (2 ^ (κ + R)) (2 ^ κ - 1) a) := by
  classical
  intro F
  let cw : Msgs m κ → Fin (2 ^ (κ + R)) → Fin (2 ^ m) → E :=
    fun V y u ↦ encode (algebraMap K E) κ R (V u) y
  let rcv : Fin (2 ^ (κ + R)) → Fin (2 ^ m) → E := fun y u ↦ F y u
  have hinj : Function.Injective cw := fun V V' h ↦ funext fun u ↦
    encode_injective (algebraMap K E) (by omega) (algebraMap K E).injective
      (funext fun y ↦ congrFun (congrFun h y) u)
  have hpair : ∀ c ∈ Set.range cw, ∀ c' ∈ Set.range cw, c ≠ c' →
      Code.agree c c' ≤ 2 ^ κ - 1 := by
    rintro _ ⟨V, rfl⟩ _ ⟨V', rfl⟩ hne
    by_contra hlt
    refine hne (congrArg cw (funext fun u ↦ ?_))
    refine encode_eq_of_agree (algebraMap K E) hb (algebraMap K E).injective
      (Finset.univ.filter fun y ↦ cw V y = cw V' y) (by unfold Code.agree at hlt; omega)
      fun y hy ↦ ?_
    exact congrFun (Finset.mem_filter.mp hy).2 u
  obtain ⟨hfin, hcard⟩ := Code.agreementSet_finite_and_ncard_le_pairwiseJohnson
    (Set.range cw) rcv (2 ^ κ - 1) a (by omega) (by rw [Fintype.card_fin]; exact hpos) hpair
  have : Finite {c | c ∈ Set.range cw ∧ a ≤ Code.agree c rcv} := hfin.to_subtype
  rw [Fintype.card_fin, ← Nat.card_coe_set_eq] at hcard
  have hmem : ∀ V : {V : Msgs m κ // Cl κ R a m F V},
      cw V.1 ∈ {c | c ∈ Set.range cw ∧ a ≤ Code.agree c rcv} := fun V ↦
    ⟨⟨V.1, rfl⟩, V.2.trans (le_of_eq (congrArg Finset.card (Finset.filter_congr fun y _ ↦
      ⟨fun h ↦ funext h, fun h u ↦ congrFun h u⟩)))⟩
  refine le_trans (Nat.card_le_card_of_injective (fun V ↦ ⟨cw V.1, hmem V⟩)
    fun V V' h ↦ Subtype.ext (hinj (congrArg Subtype.val h))) hcard

/-! ## The threshold of a slack -/

/-- A guess at `⌊√x⌋` for `x < 2 ^ 256`, by fixing its bits from the top; every use of it is
checked. -/
def sqrtGuess (x : ℕ) : ℕ := go 128 0
where
  /-- Fix the bits of the root below `2 ^ i`, given those above. -/
  go : ℕ → ℕ → ℕ
    | 0, r => r
    | i + 1, r => if (r + 2 ^ i) * (r + 2 ^ i) ≤ x then go i (r + 2 ^ i) else go i r

/-- The agreement threshold `⌈(√ρ + η) n⌉₊` of the code on `n = 2 ^ (κ + R)` positions with
degree bound `D = 2 ^ κ - 1`, `ρ = D / n`, at the slack `η = p / q`, computed in naturals as
`⌈(p n + ⌈√(D n q²)⌉) / q⌉`: the inner root may be rounded up since the rest is an integer. It is
the ceiling when `Fits` holds (`threshold_eq_ceil`). -/
def threshold (κ R : ℕ) (η : ℚ) : ℕ :=
  let n := 2 ^ (κ + R)
  let x := (2 ^ κ - 1) * n * η.den ^ 2
  let r := sqrtGuess x
  let s := if r * r < x then r + 1 else r
  (η.num.toNat * n + s + η.den - 1) / η.den

/-- What the interfaces need of a level's code on `n = 2 ^ (κ + R)` positions with degree bound
`D = 2 ^ κ - 1`, a slack `p / q` and a threshold `a`, every fact in naturals: `κ, R ≥ 1`,
`κ + R ≤ 64`, `p, q > 0`; `(√ρ + p / q) n ≤ a < (√ρ + p / q) n + 1` (`le_agree`, `lt_agree`:
`a` is the ceiling); `2 ^ κ ≤ a ≤ n`; and `n D < a²`. -/
structure FitsAt (κ R p q a : ℕ) : Prop where
  /-- The degree bound `D` is positive. -/
  one_le_κ : 1 ≤ κ
  /-- The rate is at most `1 / 2`, so `D ≤ n - 2`. -/
  one_le_R : 1 ≤ R
  /-- The positions are distinct points of `K`. -/
  hb : κ + R ≤ 64
  /-- The slack is positive. -/
  p_pos : 0 < p
  /-- The slack's denominator is positive. -/
  q_pos : 0 < q
  /-- `η n ≤ a`. -/
  le_agree₁ : p * 2 ^ (κ + R) ≤ a * q
  /-- `√ρ n ≤ a - η n`, squared. -/
  le_agree₂ : (2 ^ κ - 1) * 2 ^ (κ + R) * q ^ 2 ≤ (a * q - p * 2 ^ (κ + R)) ^ 2
  /-- `a - 1 < (√ρ + η) n`. -/
  lt_agree : (a - 1) * q < p * 2 ^ (κ + R) ∨
    ((a - 1) * q - p * 2 ^ (κ + R)) ^ 2 < (2 ^ κ - 1) * 2 ^ (κ + R) * q ^ 2
  /-- A codeword within the threshold determines its message. -/
  dist : 2 ^ κ ≤ a
  /-- The threshold is at most the number of positions. -/
  le_n : a ≤ 2 ^ (κ + R)
  /-- The Johnson bound's denominator `a² - n D` is positive. -/
  johnson : 2 ^ (κ + R) * (2 ^ κ - 1) < a * a

instance (κ R p q a : ℕ) : Decidable (FitsAt κ R p q a) :=
  decidable_of_iff (1 ≤ κ ∧ 1 ≤ R ∧ κ + R ≤ 64 ∧ 0 < p ∧ 0 < q ∧
      p * 2 ^ (κ + R) ≤ a * q ∧
      (2 ^ κ - 1) * 2 ^ (κ + R) * q ^ 2 ≤ (a * q - p * 2 ^ (κ + R)) ^ 2 ∧
      ((a - 1) * q < p * 2 ^ (κ + R) ∨
        ((a - 1) * q - p * 2 ^ (κ + R)) ^ 2 < (2 ^ κ - 1) * 2 ^ (κ + R) * q ^ 2) ∧
      2 ^ κ ≤ a ∧ a ≤ 2 ^ (κ + R) ∧ 2 ^ (κ + R) * (2 ^ κ - 1) < a * a)
    ⟨fun ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ ↦
      ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩,
     fun h ↦ ⟨h.1, h.2, h.3, h.4, h.5, h.6, h.7, h.8, h.9, h.10, h.11⟩⟩

/-- A level's code and slack fit the interfaces: `FitsAt` at the slack's numerator and denominator
and the computed threshold. Decidable, and decided at every deployed level. -/
abbrev Fits (κ R : ℕ) (η : ℚ) : Prop := FitsAt κ R η.num.toNat η.den (threshold κ R η)

/-- From the checks in naturals: `(√(D / n) + p / q) n ≤ a`. -/
private theorem agreement_le {n D p q a : ℕ} (hn : 0 < n) (hq : 0 < q) (h1 : p * n ≤ a * q)
    (h2 : D * n * q ^ 2 ≤ (a * q - p * n) ^ 2) :
    (√((D : ℝ) / n) + (p : ℝ) / q) * n ≤ a := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hsub : ((a * q - p * n : ℕ) : ℝ) = a * q - p * n := by
    rw [Nat.cast_sub h1]; push_cast; ring
  have h2' : (D : ℝ) * n * q ^ 2 ≤ ((a * q - p * n : ℕ) : ℝ) ^ 2 := by exact_mod_cast h2
  have hs : √((D : ℝ) / n) ≤ (a * q - p * n) / (n * q) := by
    refine Real.sqrt_le_iff.mpr ⟨?_, ?_⟩
    · rw [← hsub]; positivity
    · rw [div_pow, div_le_div_iff₀ hn' (by positivity), ← hsub]
      calc (D : ℝ) * (n * q) ^ 2 = D * n * q ^ 2 * n := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right h2' hn'.le
  calc (√((D : ℝ) / n) + (p : ℝ) / q) * n ≤ ((a * q - p * n) / (n * q) + p / q) * n := by
        gcongr
    _ = a := by field_simp; ring

/-- From the checks in naturals: `a < (√(D / n) + p / q) n`. -/
private theorem lt_agreement {n D p q a : ℕ} (hn : 0 < n) (hq : 0 < q)
    (h : a * q < p * n ∨ (a * q - p * n) ^ 2 < D * n * q ^ 2) :
    (a : ℝ) < (√((D : ℝ) / n) + (p : ℝ) / q) * n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  by_cases hlt : a * q < p * n
  · have : (a : ℝ) * q < p * n := by exact_mod_cast hlt
    calc (a : ℝ) < p / q * n := by rw [div_mul_eq_mul_div, lt_div_iff₀ hq']; linarith
      _ ≤ (√((D : ℝ) / n) + (p : ℝ) / q) * n := by
        gcongr; exact le_add_of_nonneg_left (Real.sqrt_nonneg _)
  · have h2 := h.resolve_left hlt
    have hle : p * n ≤ a * q := by omega
    have hsub : ((a * q - p * n : ℕ) : ℝ) = a * q - p * n := by
      rw [Nat.cast_sub hle]; push_cast; ring
    have h2' : ((a * q - p * n : ℕ) : ℝ) ^ 2 < (D : ℝ) * n * q ^ 2 := by exact_mod_cast h2
    have hs : (a * q - p * n) / (n * q) < √((D : ℝ) / n) := by
      rw [Real.lt_sqrt (by rw [← hsub]; positivity), div_pow, div_lt_div_iff₀ (by positivity) hn',
        ← hsub]
      calc ((a * q - p * n : ℕ) : ℝ) ^ 2 * n < D * n * q ^ 2 * n :=
            mul_lt_mul_of_pos_right h2' hn'
        _ = D * (n * q) ^ 2 := by ring
    calc (a : ℝ) = ((a * q - p * n) / (n * q) + p / q) * n := by field_simp; ring
      _ < (√((D : ℝ) / n) + (p : ℝ) / q) * n := by gcongr

/-- A slack with a positive numerator is its numerator over its denominator, in naturals. -/
private theorem cast_slack {η : ℚ} (hp : 0 < η.num.toNat) :
    (η : ℝ) = (η.num.toNat : ℝ) / η.den := by
  have hnum : (0 : ℤ) ≤ η.num := by omega
  rw [Rat.cast_def, ← Int.toNat_of_nonneg hnum]
  push_cast
  rfl

/-- A fitting slack is positive. -/
theorem Fits.slack_pos {κ R : ℕ} {η : ℚ} (h : Fits κ R η) : (0 : ℝ) < η := by
  rw [cast_slack h.p_pos]
  exact div_pos (by exact_mod_cast h.p_pos) (by exact_mod_cast h.q_pos)

/-- **The threshold is at least the agreement**: `(√ρ + η) n ≤ threshold κ R η`. -/
theorem le_threshold {κ R : ℕ} {η : ℚ} (h : Fits κ R η) :
    (√(((2 ^ κ - 1 : ℕ) : ℝ) / (2 ^ (κ + R) : ℕ)) + η) * (2 ^ (κ + R) : ℕ) ≤
      threshold κ R η := by
  rw [cast_slack h.p_pos]
  exact agreement_le (Nat.two_pow_pos _) h.q_pos h.le_agree₁ h.le_agree₂

/-- **A fitting level meets the hypotheses of `mcaJohnson_annexB`** at its code and slack:
`1 ≤ D ≤ n - 2`, `0 < η` and `√ρ + η ≤ 1`, with `n = 2 ^ (κ + R)`, `D = 2 ^ κ - 1`, `ρ = D / n`. -/
theorem Fits.mcaJohnson_hyps {κ R : ℕ} {η : ℚ} (h : Fits κ R η) :
    1 ≤ 2 ^ κ - 1 ∧ 2 ^ κ - 1 ≤ 2 ^ (κ + R) - 2 ∧ (0 : ℝ) < η ∧
      √(((2 ^ κ - 1 : ℕ) : ℝ) / (2 ^ (κ + R) : ℕ)) + η ≤ 1 :=
  have ⟨h1, h2, h3⟩ := Whir.mcaJohnson_hyps h.one_le_κ h.one_le_R (le_threshold h) h.le_n
  ⟨h1, h2, h.slack_pos, h3⟩

/-- **The threshold is the ceiling** of the agreement `(√ρ + η) n` (`ρ = D / n`, `D = 2 ^ κ - 1`,
`n = 2 ^ (κ + R)`): the least number of positions on which a codeword within the Johnson
radius `1 - √ρ - η` of a word agrees with it. -/
theorem threshold_eq_ceil {κ R : ℕ} {η : ℚ} (h : Fits κ R η) :
    threshold κ R η =
      ⌈(√(((2 ^ κ - 1 : ℕ) : ℝ) / (2 ^ (κ + R) : ℕ)) + η) * (2 ^ (κ + R) : ℕ)⌉₊ := by
  have h0 : threshold κ R η ≠ 0 := by have := h.dist; have := Nat.two_pow_pos κ; omega
  refine (Nat.ceil_eq_iff h0).mpr ⟨?_, le_threshold h⟩ |>.symm
  rw [cast_slack h.p_pos]
  exact lt_agreement (Nat.two_pow_pos _) h.q_pos h.lt_agree

/-! ## The parameters of a level -/

/-- **The parameters of a level in the Johnson regime**, from its slack `η`: the threshold
`a = ⌈(√ρ + η) n⌉₊`, the list bound `L = ⌊n (a - D) / (a² - n D)⌋` of the pairwise Johnson
bound, and the bound `N = ⌊mcaConstant n D η⌋₊` on the bad folds (Annex B's constant), with
`n = 2 ^ (κ + R)` and `D = 2 ^ κ - 1`. -/
noncomputable def johnsonPar (sh : Shape) (κ : ℕ) (η : ℚ) (h : Fits κ sh.R η) : Par sh κ where
  a := threshold κ sh.R η
  L := Code.pairwiseJohnsonListBound (2 ^ (κ + sh.R)) (2 ^ κ - 1) (threshold κ sh.R η)
  N := ⌊mcaConstant (2 ^ (κ + sh.R)) (2 ^ κ - 1) η⌋₊
  hdist := h.dist
  hle := h.le_n
  hb := h.hb
  hlist := listBound_johnson sh.ℓ h.hb h.dist h.johnson
  hmca := mcaBound_of_mcaJohnson (mcaJohnson_annexB E) h.one_le_κ h.one_le_R h.hb
    h.slack_pos (le_threshold h) h.le_n

end Whir

end

end LeanerVM.Protocol
