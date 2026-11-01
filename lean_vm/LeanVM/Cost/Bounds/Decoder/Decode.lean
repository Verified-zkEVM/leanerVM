module

public import LeanVM.Cost.Bounds.Decoder.Prune
public import LeanVM.Cost.Bounds.Decoder.Prefixes
public import LeanVM.Cost.Bounds.DecoderShapes

/-!
# Bound: the decoder, compiled

The price of `decodeStacksDistinct μ R W` (`Fast/DecodeAdmissible.lean`, compiled in
`Cost/Extractor/Decode.lean`), lane by lane:

* the parameter search (`gsMultiplicityAt`: one `gsPass` per multiplicity up to
  `gsMultiplicityBoundAt`, `decoderSearchC_cost`), the lane's points (`lanePointsS`), its
  Guruswami–Sudan run (`gsRunDistinctNFC_cost`, `Bounds/Decoder/Prefixes.lean`):
  **`gsLaneDistinctC_cost`**;
* the lane's candidates (`laneEncodedDistinctC_cost`, `Bounds/Decoder/Lane.lean`):
  `decoderLaneC_cost ≤ decoderLaneBound`;
* the Johnson threshold (`johnsonThreshold_cost`), the `2^6` lanes pruned
  (`pruneUpToDistinctC_cost`, at most `2^18` survivors: `pruneUpToDistinct_length_le_johnson`), a
  stack per survivor
  (`stackOf_cost`): **`decodeStacksDistinctC_cost`** `≤ decoderBound μ R BW Lw`, `BW` the word's
  price per column and `Lw` its symbols per column;
* at every admissible shape: **`decodeStacksDistinctC_cost_worst`**, at most
  `(BW + 10·Lw)·2^26 + decoderWorstPrice`.

`DecoderLaneSizes` (the lanes' parameters word-sized) is a hypothesis, decided per shape
(`Bounds/DecoderShapes.lean`, with the bounds at the worst shape `(28, 4)`).
-/

namespace LeanVM.Cost.Bounds.Decoder

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.Library
open LeanVM.Cost.Extractor LeanVM.Parameters CompPoly LeanVM.Extraction LeanVM.Extraction.Fast

/-! The functions compiled on demand, by their short names. -/
open LeanVM.Cost.Auto.LeanVM.Extraction.Fast LeanVM.Cost.Auto.LeanVM.Extraction
open CompPoly.GuruswamiSudan

public section

variable (P : MachineProgram)

/-! ## The parameter search -/

theorem decoderMul_lt {a b i j : ℕ} (ha : a < 2 ^ i) (hb : b < 2 ^ j) : a * b < 2 ^ (i + j) := by
  rw [Nat.pow_add]
  exact Nat.mul_lt_mul'' ha hb

/-- `gsParamsAt k n A m`: at most `20`, the sizes word-sized. -/
theorem decoderParamsAtC_cost (hP : Includes P gsParamsAt.c250.costDeps) {k n A m : ℕ}
    (hn : n < 2 ^ 32) (hA : A ≤ n) (hm : m < 2 ^ 20) :
    machineCost P gsParamsAt.c250.costIdx [encodeValue k, encodeValue n, encodeValue A, encodeValue m] ≤ 20 := by
  rw [gsParamsAt.c250.costEq P hP]
  have hmA : m * A < 2 ^ 52 := decoderMul_lt (i := 20) (j := 32) hm (by omega)
  rw [limbs_of_lt (show m < 2 ^ 64 by omega), limbs_of_lt (show A < 2 ^ 64 by omega),
    limbs_of_lt (show m * A < 2 ^ 64 by omega), limbs_of_lt (show n < 2 ^ 64 by omega)]
  simp

/-- **One parameter check** (`gsPass k n (n − A) (gsParamsAt k n A m)`): at most `120`, the sizes
word-sized. -/
theorem decoderPassC_cost (hP : Includes P gsPass.c253.costDeps) {k n A m : ℕ}
    (hk : k < 2 ^ 32) (hn : n < 2 ^ 32) (hA : A ≤ n) (hm : m < 2 ^ 20) :
    machineCost P gsPass.c253.costIdx [encodeValue k, encodeValue n, encodeValue (n - A), encodeValue (gsParamsAt k n A m)] ≤
      120 := by
  rw [gsPass.c253.costEq P (by includes), gsNumConstraints.c254.costEq P (by includes),
    gsNumVars.c255.costEq P (by includes)]
  dsimp only [gsParamsAt]
  have hmA : m * A < 2 ^ 52 := decoderMul_lt (i := 20) (j := 32) hm (by omega)
  have hmm : m * (m + 1) < 2 ^ 41 := decoderMul_lt (i := 20) (j := 21) hm (by omega)
  have hmm2 : m * (m + 1) / 2 ≤ m * (m + 1) := Nat.div_le_self _ _
  have hnm : n * (m * (m + 1) / 2) < 2 ^ 73 := decoderMul_lt (i := 32) (j := 41) hn (by omega)
  have hW1 : (m * A - 1) / (k - 1) ≤ (m * A - 1) := Nat.div_le_self _ _
  have hW2 : (k - 1) * ((m * A - 1) / (k - 1)) ≤ (m * A - 1) := Nat.mul_div_le _ _
  have hprod : ((m * A - 1) / (k - 1) + 1) *
      (2 * (m * A - 1) + 2 - (k - 1) * ((m * A - 1) / (k - 1))) < 2 ^ 106 :=
    decoderMul_lt (i := 53) (j := 53) (by omega) (by omega)
  have hnv : gsNumVars k (m * A - 1) < 2 ^ 106 := (Nat.div_le_self _ _).trans_lt hprod
  have hm1 : m * (n - (n - A)) < 2 ^ 52 := by rw [show n - (n - A) = A by omega]; exact hmA
  have hl := fun x (h : x < 2 ^ 64) ↦ limbs_of_lt h
  simp (disch := omega) only [hl]
  have h1 := limbs_le_two (x := gsNumConstraints n m) (by unfold gsNumConstraints; omega)
  have h2 := limbs_le_two (x := gsNumVars k (m * A - 1)) (by omega)
  have h3 := limbs_le_two
    (x := ((m * A - 1) / (k - 1) + 1) * (2 * (m * A - 1) + 2 - (k - 1) * ((m * A - 1) / (k - 1))))
    (by omega)
  simp only [Nat.max_self, Nat.mul_one]
  split_ifs <;> omega

/-- `gsMultiplicityBoundAt k n A`: at most `30`, the sizes word-sized. -/
theorem decoderMultBoundC_cost (hP : Includes P gsMultiplicityBoundAt.c256.costDeps) {k n A : ℕ}
    (hk : k < 2 ^ 31) (hn : n < 2 ^ 32) (hA : A ≤ n) :
    machineCost P gsMultiplicityBoundAt.c256.costIdx [encodeValue k, encodeValue n, encodeValue A] ≤ 30 := by
  rw [gsMultiplicityBoundAt.c256.costEq P hP]
  have h1 : (k - 1) * n < 2 ^ 63 := decoderMul_lt (i := 31) (j := 32) (by omega) hn
  have h2 : A * A < 2 ^ 64 := decoderMul_lt (i := 32) (j := 32) (by omega) (by omega)
  have h3 : ((k - 1) * n + 1) / (A * A - (k - 1) * n) ≤ (k - 1) * n + 1 := Nat.div_le_self _ _
  have hl := fun x (h : x < 2 ^ 64) ↦ limbs_of_lt h
  simp (disch := omega) only [hl]
  simp

theorem decoderMultiplicity_le (k n A : ℕ) :
    gsMultiplicityAt k n A ≤ gsMultiplicityBoundAt k n A := by
  unfold gsMultiplicityAt
  cases h : (List.range' 1 (gsMultiplicityBoundAt k n A)).find?
      (fun m ↦ gsPass k n (n - A) (gsParamsAt k n A m)) with
  | none => simp
  | some m =>
    have := List.mem_range'.1 (List.mem_of_find?_eq_some h)
    simp only [Option.getD_some]
    omega

/-- **The parameter search** (`gsMultiplicityAt k n A`: a check per multiplicity below
`b = gsMultiplicityBoundAt k n A`): at most `190·b + 100`, the sizes word-sized, `b < 2^20`. -/
theorem decoderSearchC_cost (hP : Includes P gsMultiplicityAt.c251.costDeps) {k n A : ℕ}
    (hk : k < 2 ^ 31) (hn : n < 2 ^ 32) (hA : A ≤ n) (hb : gsMultiplicityBoundAt k n A < 2 ^ 20) :
    machineCost P gsMultiplicityAt.c251.costIdx [encodeValue k, encodeValue n, encodeValue A] ≤
      190 * gsMultiplicityBoundAt k n A + 100 := by
  rw [gsMultiplicityAt.c251.costEq P hP]
  have h1 := decoderMultBoundC_cost P (by includes) hk hn hA
  have h2 := rangeC_cost P (by includes) (gsMultiplicityBoundAt k n A) 1 (by omega)
  have hf := fun m ↦ RunsApp.of_spec (us := [encodeValue k, encodeValue n, encodeValue A]) (vs := [encodeValue m])
    (gsMultiplicityAt.c251.lam0.costSpec P (by includes) k n A m)
  have h3 := findNat_cost P (by includes) _
    (.closure gsMultiplicityAt.c251.lam0.costIdx [encodeValue k, encodeValue n, encodeValue A]) hf 152
    (List.range' 1 (gsMultiplicityBoundAt k n A)) (fun m hm ↦ by
      have hm' := List.mem_range'.1 hm
      simp only [appCost_fn, List.cons_append, List.nil_append]
      rw [gsMultiplicityAt.c251.lam0.costEq P (by includes),
        limbs_of_lt (show n < 2 ^ 64 by omega), limbs_of_lt (show A < 2 ^ 64 by omega)]
      have := decoderParamsAtC_cost P (by includes) (k := k) hn hA (m := m) (by omega)
      have := decoderPassC_cost P (by includes) (k := k) (by omega) hn hA (m := m) (by omega)
      simp only [Nat.max_self]
      omega)
  simp only [List.length_range'] at h3
  cases List.find? (fun m ↦ gsPass k n (n - A) (gsParamsAt k n A m))
    (List.range' 1 (gsMultiplicityBoundAt k n A)) <;> dsimp only <;> omega

/-! ## A lane -/

/-- **A lane's Guruswami–Sudan run** (`gsLaneDistinct κ R A S u`): at most
`decoderLaneRunBound κ R A BS`, `BS` the price of a symbol `S u v`. -/
theorem gsLaneDistinctC_cost (hP : Includes P gsLaneDistinct.c249.costDeps) (κ R A : ℕ)
    (S : ℕ → ℕ → K) (SVal : MachineValue) (hS : ∀ a b, RunsApp P SVal [encodeValue a, encodeValue b] (encodeValue (S a b)))
    {BS : ℕ} (hBS : ∀ a b : ℕ, appCost P SVal [encodeValue a, encodeValue b] ≤ BS) (u : ℕ)
    (h : DecoderLaneSizes κ R A) :
    machineCost P gsLaneDistinct.c249.costIdx [encodeValue κ, encodeValue R, encodeValue A, SVal, encodeValue u] ≤
      decoderLaneRunBound κ R A BS := by
  obtain ⟨hκR, hA, hb, hs, hk1, hX, hY⟩ := h
  rw [gsLaneDistinct.c249.costEq P hP κ R A S SVal hS]
  have hn : 2 ^ (κ + R) < 2 ^ 32 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hk : 2 ^ κ < 2 ^ 31 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  rw [limbs_shift (show κ < 64 by omega), limbs_shift (show κ + R < 64 by omega),
    limbs_of_lt (show κ < 2 ^ 64 by omega), limbs_of_lt (show R < 2 ^ 64 by omega),
    limbs_of_lt (show κ + R < 2 ^ 64 by omega)]
  have h1 := decoderSearchC_cost P (by includes) hk hn hA hb
  have h2 := decoderParamsAtC_cost P (by includes) (k := 2 ^ κ) hn hA
    (m := gsMultiplicityAt (2 ^ κ) (2 ^ (κ + R)) A)
    ((decoderMultiplicity_le _ _ _).trans_lt hb)
  -- the points
  rw [lanePointsS.c257.costEq P (by includes) _ S SVal hS]
  have hf := fun v ↦ RunsApp.of_spec (us := [encodeValue (2 ^ (κ + R)), SVal, encodeValue u]) (vs := [encodeValue v])
    (lanePointsS.c257.lam0.costSpec P (by includes) (2 ^ (κ + R)) S SVal hS u v)
  have h3 := ofFnFrom_cost P (by includes) (n := 2 ^ (κ + R)) (by omega) _
    (.closure lanePointsS.c257.lam0.costIdx [encodeValue (2 ^ (κ + R)), SVal, encodeValue u]) hf (BS + 9)
    (fun v ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append]
      rw [lanePointsS.c257.lam0.costEq P (by includes) _ S SVal hS]
      have := hBS u v
      omega) 0 (Nat.zero_le _)
  -- the run
  have hd := lanePointsS_distinct (by omega : κ + R ≤ 64) S u
  have h4 := gsRunDistinctNFC_cost P (by includes) (lanePointsS (2 ^ (κ + R)) S u)
    (gsParamsFor (2 ^ κ) (2 ^ (κ + R)) A).interp (gsParamsFor (2 ^ κ) (2 ^ (κ + R)) A).radius
    (by rwa [lanePointsS_size]) hk1 hd
    (by simp only [gsParamsFor, gsParamsAt]; omega) hX hY
    (by simp only [gsParamsFor, gsParamsAt]; omega)
  rw [lanePointsS_size] at h4
  simp only [length_ofFnFrom, Nat.sub_zero] at h3 ⊢
  unfold decoderLaneRunBound
  simp only [Nat.max_self]
  have e : (BS + 28) * 2 ^ (κ + R) = (BS + 9 + 18) * 2 ^ (κ + R) + 2 ^ (κ + R) := by ring
  omega

/-- **A lane's candidates** (`laneEncodedDistinct κ R A S u`): at most
`decoderLaneBound κ R A BS`. -/
theorem decoderLaneC_cost (hP : Includes P laneEncodedDistinctC.costDeps) (κ R A : ℕ)
    (S : ℕ → ℕ → K) (SVal : MachineValue) (hS : ∀ a b, RunsApp P SVal [encodeValue a, encodeValue b] (encodeValue (S a b)))
    {BS : ℕ} (hBS : ∀ a b : ℕ, appCost P SVal [encodeValue a, encodeValue b] ≤ BS) (u : ℕ)
    (h : DecoderLaneSizes κ R A) :
    machineCost P laneEncodedDistinctC.costIdx [encodeValue κ, encodeValue R, encodeValue A, SVal, encodeValue u] ≤
      decoderLaneBound κ R A BS := by
  have hrun := gsLaneDistinctC_cost P (by includes) κ R A S SVal hS hBS u h
  obtain ⟨hκR, -, -, hs, hk1, -, hY⟩ := h
  have hd := lanePointsS_distinct (by omega : κ + R ≤ 64) S u
  have := laneEncodedDistinctC_cost P hP κ R A (by omega) S SVal hS u
    (L := max 1 (interpolationYCap (gsParamsFor (2 ^ κ) (2 ^ (κ + R)) A).interp))
    (k := 2 ^ κ) (gsRunDistinctNF_size_le hd _ _ hk1) (by omega)
    (fun p hp ↦ by
      have := gsRunDistinctNF_mem_size_le hp
      simpa [gsParamsFor, gsParamsAt] using this)
  unfold decoderLaneBound
  omega
/-! ## The decoder -/

/-- **The decoder** (`decodeStacksDistinct μ R W`, the extractor's): at most
`decoderBound μ R BW Lw` at an admissible shape whose lanes are word-sized
(`DecoderLaneSizes`, decided per shape), `BW` the price of a column `W v` and `Lw` its length. -/
theorem decodeStacksDistinctC_cost (hP : Includes P decodeStacksDistinctC.costDeps) (μ R : ℕ)
    (hadm : Whir.Admissible μ R)
    (hsz : DecoderLaneSizes (μ - Whir.initialFold) R (johnsonThreshold μ R))
    (W : ℕ → List K) (WVal : MachineValue) (hW : ∀ a, RunsApp P WVal [encodeValue a] (encodeValue (W a))) {BW Lw : ℕ}
    (hBW : ∀ v : ℕ, v < 2 ^ 64 → appCost P WVal [encodeValue v] ≤ BW) (hLw : ∀ v, (W v).length ≤ Lw) :
    machineCost P decodeStacksDistinctC.costIdx [encodeValue μ, encodeValue R, WVal] ≤ decoderBound μ R BW Lw := by
  have hadm' := hadm
  obtain ⟨h1, h2, h3, h4⟩ := hadm'
  unfold Whir.minLogStack at h1
  unfold Whir.maxLogStack at h2
  unfold Whir.minLogInvRate at h3
  unfold Whir.maxLogInvRate at h4
  have hf : Whir.initialFold = 6 := rfl
  rw [decodeStacksDistinctC.costEq P hP μ R W WVal hW]
  set κ := μ - Whir.initialFold with hκ
  set A := johnsonThreshold μ R with hAdef
  set T := laneTable (2 ^ (κ + R)) W with hT
  have hsz' := hsz
  obtain ⟨hκR, hA, -, -, hk1, -, -⟩ := hsz'
  have hn : 2 ^ (κ + R) < 2 ^ 32 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  -- the threshold
  have hj := johnsonThreshold_cost P (by includes) μ R (by omega) (by omega)
  rw [limbs_of_lt (show μ < 2 ^ 64 by omega)]
  simp only [show limbCount Whir.initialFold = 1 from rfl,
    show limbCount (1 <<< Whir.initialFold) = 1 from rfl, Nat.max_self]
  -- the lanes
  have hSV := fun a b ↦ RunsApp.of_spec (us := [encodeValue T]) (vs := [encodeValue a, encodeValue b])
    (pruneUpToDistinctC.lam1.lam0.costSpec P (by includes) T a b)
  have hLc : ∀ u, (laneEncodedDistinct κ R A (tableSymbol T) u).length ≤
      max 1 (interpolationYCap (gsParamsFor (2 ^ κ) (2 ^ (κ + R)) A).interp) := fun u ↦ by
    rw [laneEncodedDistinct_length]; exact laneListDistinct_length_le (by omega) hk1 _ u
  have hpr := pruneUpToDistinctC_cost P (by includes) κ R A (2 ^ Whir.initialFold) (by omega)
    (by rw [hf]; norm_num) (by omega) W WVal hW hBW hLw
    (G := decoderLaneBound κ R A 12)
    (fun u _ ↦ decoderLaneC_cost P (by includes) κ R A (tableSymbol T)
      (.closure pruneUpToDistinctC.lam1.lam0.costIdx [encodeValue T]) hSV
      (fun a b ↦ by
        simp only [appCost_fn, List.cons_append, List.nil_append]
        rw [pruneUpToDistinctC.lam1.lam0.costEq P (by includes),
          Auto.LeanVM.Extraction.Fast.tableSymbol.c269.costEq P (by includes)]) u hsz)
    hLc (Smax := 2 ^ 18) (fun u _ ↦ by
      rcases Nat.eq_zero_or_pos u with rfl | hu
      · simp [pruneUpToDistinct]
      · exact pruneUpToDistinct_length_le_johnson hadm W hu)
  -- the stacks
  have hsurv := pruneUpToDistinct_length_le_johnson hadm W (U := 2 ^ Whir.initialFold)
    (by rw [hf]; norm_num)
  have hmem := (pruneUpToDistinct_bounds W hLc (2 ^ Whir.initialFold)).2
  have hfm := fun s ↦ RunsApp.of_spec (us := [encodeValue μ]) (vs := [encodeValue s])
    (decodeStacksDistinctC.lam0.costSpec P (by includes) μ s)
  have hm := listMap_le P Auto.List.map.c12.costIdx
    (.closure decodeStacksDistinctC.lam0.costIdx [encodeValue μ])
    (Auto.List.map.c12.costEq_nil P (by includes) _ _ hfm)
    (Auto.List.map.c12.costEq_cons P (by includes) _ _ hfm)
    ((15 * 2 ^ Whir.initialFold + 56) * 2 ^ μ + 23)
    (pruneUpToDistinct κ R A W (2 ^ Whir.initialFold))
    (fun s hs ↦ by
      rw [appCost_fn, List.singleton_append, decodeStacksDistinctC.lam0.costEq P (by includes)]
      have := stackOf_cost P (by includes) μ (by omega) s.1
      rw [(hmem s hs).1] at this
      omega)
  have hm2 : ((15 * 2 ^ Whir.initialFold + 56) * 2 ^ μ + 23 + 11) *
      (pruneUpToDistinct κ R A W (2 ^ Whir.initialFold)).length ≤
      ((15 * 2 ^ Whir.initialFold + 56) * 2 ^ μ + 34) * 2 ^ 18 := Nat.mul_le_mul_left _ hsurv
  unfold decoderBound
  rw [← hκ, ← hAdef]
  omega

/-- The decoder's bound is affine in the word's prices. -/
theorem decoderBound_eq (μ R BW Lw : ℕ) :
    decoderBound μ R BW Lw = (BW + 10 * Lw) * 2 ^ (μ - Whir.initialFold + R) +
      decoderBound μ R 0 0 := by
  unfold decoderBound pruneBound
  ring

/-! ## At every admissible shape -/

/-- **The decoder at every admissible shape**: at most `(BW + 10·Lw)·2^26 + decoderWorstPrice`
(`decoderShape_ok`, `Bounds/DecoderShapes.lean`). -/
theorem decodeStacksDistinctC_cost_worst (hP : Includes P decodeStacksDistinctC.costDeps)
    {μ R : ℕ} (hadm : Whir.Admissible μ R)
    (W : ℕ → List K) (WVal : MachineValue) (hW : ∀ a, RunsApp P WVal [encodeValue a] (encodeValue (W a))) {BW Lw : ℕ}
    (hBW : ∀ v : ℕ, v < 2 ^ 64 → appCost P WVal [encodeValue v] ≤ BW) (hLw : ∀ v, (W v).length ≤ Lw) :
    machineCost P decodeStacksDistinctC.costIdx [encodeValue μ, encodeValue R, WVal] ≤
      (BW + 10 * Lw) * 2 ^ 26 + decoderWorstPrice := by
  obtain ⟨hsz, hle⟩ := decoderShape_ok hadm
  have h := decodeStacksDistinctC_cost P hP μ R hadm hsz W WVal hW hBW hLw
  rw [decoderBound_eq] at h
  have hadm' := hadm
  obtain ⟨-, h2, -, h4⟩ := hadm'
  simp only [Whir.maxLogStack, Whir.maxLogInvRate] at h2 h4
  have hp : 2 ^ (μ - Whir.initialFold + R) ≤ 2 ^ 26 :=
    Nat.pow_le_pow_right (by norm_num) (by simp only [Whir.initialFold]; omega)
  have := Nat.mul_le_mul_left (BW + 10 * Lw) hp
  omega

end

end LeanVM.Cost.Bounds.Decoder
