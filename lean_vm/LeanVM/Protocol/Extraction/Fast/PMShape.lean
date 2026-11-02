module

public import LeanVM.Protocol.Extraction.Fast.LanePM

/-!
# The lane's X-adic problem: its sizes, orders and moduli; the second reduction

The data a cost proof of the lanes' approximant-basis interpolation (`Fast/LanePM.lean`) reads.

The interpolation builds the Guruswami–Sudan modular equations (`buildGSModularDataWithRG`): the
moduli `M_b = G^(m−b)`, `b < m` (`G` the vanishing polynomial of the `n` points, `m` the
multiplicity), and the relation matrix, `ℓ + 1` rows (`interpolationWidth`) and `m` columns, its
column `b` reduced modulo `M_b`. The solver (`windowedFilteredSolutionBasis`, at the bound
`W`, `solveWindow_some`) runs the PM-basis once, on `fullWindowExactNullspaceProblem` at `W`:

* `ℓ + 1 + m` rows of width `m` (`gsProblem_matrix_size`, `gsProblem_row_size`);
* the orders `deg M_b + W + 2 = (m − b)·n + W + 2` (`gsProblem_order`), the largest
  `m·n + W + 2` (`gsProblem_maxOrder`), their sum `n·m(m+1)/2 + m·(W + 2)`
  (`gsProblem_totalOrder`);
* the matrix `reducedExactNullspaceLift`, the relation matrix reduced once more modulo the moduli:
  its entries are reduced already (`natDegree_gsRelationMatrix_entry_lt`: the relation columns
  carry a reduced power, `natDegree_gsRelationColumn_lt`), so this second reduction changes
  nothing (`reducedExactNullspaceLift_gs`: it is the unreduced lift `exactNullspaceLift`,
  `fullWindowExactNullspaceProblem_gs`); executed, each of its `(ℓ+1)·m` remainders takes the
  reversal remainder's first branch (dividend shorter than the modulus: no Newton inverse).

At `(28, 4)` (`laneProblem_28_4`): `k = 2^22`, `n = 2^26`, `A = 16792398` (`johnsonThreshold_28_4`),
`m = 415`, `W = 6968845169`, `ℓ = 1661` (`gsInterp_28_4`): `2077` rows of width `415`, the orders
`(415 − b)·2^26 + 6968845171`, the largest `34819023731 ≈ 2^35.02`, their sum
`8684907886445 ≈ 2^42.98`.
-/

namespace LeanVM.Extraction.Fast

open LeanVM.Parameters LeanVM.Parameters.Whir LeanVM.Extraction
open CompPoly CompPoly.GuruswamiSudan CompPoly.PolynomialMatrix CompPoly.PolynomialMatrix.Approximant
open CompPoly.GuruswamiSudan.ApproximantBasis

public section

section Generic

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

/-! ## The vanishing polynomial and the moduli -/

theorem monic_vanishingFast (xs : Array F) : (vanishingFast xs).toPoly.Monic := by
  rw [vanishingFast_eq]
  exact vanishingPolynomialArray_toPoly_monic xs

/-- The vanishing polynomial of `xs` has degree `|xs|`. -/
theorem natDegree_vanishingFast (xs : Array F) : (vanishingFast xs).natDegree = xs.size := by
  rw [vanishingFast_eq, CPolynomial.natDegree_toPoly, vanishingPolynomialArray_toPoly,
    Polynomial.natDegree_multiset_prod_X_sub_C_eq_card]
  simp

/-- **The moduli**: `M_b = G^(s−b)`, of degree `(s − b)·deg G`. -/
theorem natDegree_gsModuli (mulCtx : CPolynomial.MulContext F) {G : CPolynomial F}
    (hG : G.toPoly.Monic) {b s : Nat} (hb : b < s) :
    ((gsModuli mulCtx G s).getD b 0).natDegree = (s - b) * G.natDegree := by
  rw [gsModuli_getD mulCtx G hb, CPolynomial.natDegree_toPoly, CPolynomial.toPoly_pow,
    hG.natDegree_pow, ← CPolynomial.natDegree_toPoly]

/-! ## The relation matrix is reduced -/

theorem natDegree_C_mul_lt {c : F} {p : CPolynomial F} {D : Nat} (h : p.natDegree < D) :
    (CPolynomial.C c * p).natDegree < D := by
  rw [CPolynomial.natDegree_toPoly, CPolynomial.toPoly_mul, CPolynomial.C_toPoly]
  rw [CPolynomial.natDegree_toPoly] at h
  exact lt_of_le_of_lt (Polynomial.natDegree_C_mul_le _ _) h

theorem natDegree_modByMonicWith_lt (modCtx : CPolynomial.ModContext F) (p : CPolynomial F)
    {M : CPolynomial F} (hM : M.toPoly.Monic) (hD : 1 ≤ M.natDegree) :
    (modByMonicWith modCtx p M).natDegree < M.natDegree := by
  rw [CPolynomial.natDegree_toPoly, CPolynomial.natDegree_toPoly M, modByMonicWith_toPoly modCtx hM]
  refine Polynomial.natDegree_modByMonic_lt _ hM fun h1 ↦ ?_
  rw [CPolynomial.natDegree_toPoly, h1, Polynomial.natDegree_one] at hD
  omega

/-- A remainder of a reduced polynomial is itself. -/
theorem modByMonicWith_eq_self (modCtx : CPolynomial.ModContext F) {p M : CPolynomial F}
    (hM : M.toPoly.Monic) (h : p.natDegree < M.natDegree) : modByMonicWith modCtx p M = p := by
  apply CPolynomial.toPoly_injective
  rw [modByMonicWith_toPoly modCtx hM, Polynomial.modByMonic_eq_self_iff hM]
  rw [CPolynomial.natDegree_toPoly, CPolynomial.natDegree_toPoly M] at h
  exact Polynomial.degree_lt_degree h

/-- A step of `gsRelationColumn`'s loop (CompPoly's, restated). -/
private def colStep (mulCtx : CPolynomial.MulContext F) (modCtx : CPolynomial.ModContext F)
    (reducedR modulus : CPolynomial F) (b : Nat)
    (state : Array (CPolynomial F) × CPolynomial F) (j : Nat) :
    Array (CPolynomial F) × CPolynomial F :=
  (state.1.setIfInBounds j (CPolynomial.C ((j.choose b : F)) * state.2),
   modByMonicWith modCtx (mulCtx.mul state.2 reducedR) modulus)

private theorem gsRelationColumn_eq_colFold (mulCtx : CPolynomial.MulContext F)
    (modCtx : CPolynomial.ModContext F) (R modulus : CPolynomial F) (width b : Nat) :
    gsRelationColumn mulCtx modCtx R modulus width b =
      ((List.range' b (width - b)).foldl
        (colStep mulCtx modCtx (modByMonicWith modCtx R modulus) modulus b)
        (Array.replicate width (0 : CPolynomial F), 1)).1 := by
  rw [gsRelationColumn]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.add_sub_cancel, Nat.div_one, List.forIn_pure_yield_eq_foldl,
    bind_pure_comp, map_pure, Id.run_pure]
  rfl

private theorem colFold_natDegree_lt (mulCtx : CPolynomial.MulContext F)
    (modCtx : CPolynomial.ModContext F) {reducedR modulus : CPolynomial F} (b : Nat) {D : Nat}
    (hD : 0 < D) (hstep : ∀ p, (modByMonicWith modCtx p modulus).natDegree < D) :
    ∀ (l : List Nat) (col : Array (CPolynomial F)) (pow : CPolynomial F),
      (∀ j, (col.getD j 0).natDegree < D) → pow.natDegree < D →
      ∀ j, ((l.foldl (colStep mulCtx modCtx reducedR modulus b) (col, pow)).1.getD j 0).natDegree
        < D := by
  intro l
  induction l with
  | nil => intro col pow hcol _ j; exact hcol j
  | cons i l ih =>
    intro col pow hcol hpow
    rw [List.foldl_cons]
    refine ih _ _ ?_ (hstep _)
    intro j
    show ((col.setIfInBounds i (CPolynomial.C ((i.choose b : F)) * pow)).getD j 0).natDegree < D
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
    split
    · split
      · exact natDegree_C_mul_lt hpow
      · rw [Option.getD_none, CPolynomial.natDegree_toPoly, CPolynomial.toPoly_zero,
          Polynomial.natDegree_zero]
        exact hD
    · rw [← Array.getD_eq_getD_getElem?]
      exact hcol j

/-- **A relation column is reduced** modulo a monic modulus of positive degree. -/
theorem natDegree_gsRelationColumn_lt (mulCtx : CPolynomial.MulContext F)
    (modCtx : CPolynomial.ModContext F) (R : CPolynomial F) {modulus : CPolynomial F}
    (hM : modulus.toPoly.Monic) (hD : 1 ≤ modulus.natDegree) (width b j : Nat) :
    ((gsRelationColumn mulCtx modCtx R modulus width b).getD j 0).natDegree <
      modulus.natDegree := by
  rw [gsRelationColumn_eq_colFold]
  refine colFold_natDegree_lt mulCtx modCtx b (by omega)
    (fun p ↦ natDegree_modByMonicWith_lt modCtx p hM hD) _ _ _ ?_ ?_ j
  · intro j
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
    split <;> simp only [Option.getD_some, Option.getD_none] <;>
      rw [CPolynomial.natDegree_toPoly, CPolynomial.toPoly_zero, Polynomial.natDegree_zero] <;> omega
  · rw [CPolynomial.natDegree_toPoly, CPolynomial.toPoly_one, Polynomial.natDegree_one]
    omega

/-- **The relation matrix is reduced**: entry `(k, b)` has degree below `deg M_b`. -/
theorem natDegree_gsRelationMatrix_entry_lt (mulCtx : CPolynomial.MulContext F)
    (modCtx : CPolynomial.ModContext F) (R G : CPolynomial F) (params : GSInterpParams)
    (hG : G.toPoly.Monic) (hG1 : 1 ≤ G.natDegree) {k b : Nat}
    (hk : k < interpolationWidth params) (hb : b < params.multiplicity) :
    (rowGet ((gsRelationMatrixWithModuli mulCtx modCtx R
        (gsModuli mulCtx G params.multiplicity) params).getD k #[]) b).natDegree <
      ((gsModuli mulCtx G params.multiplicity).getD b 0).natDegree := by
  rw [gsRelationMatrixWithModuli_entry _ _ _ _ _ hk hb, gsModuli_getD_one _ _ hb,
    gsModuli_getD _ _ hb]
  have hMon : (G ^ (params.multiplicity - b)).toPoly.Monic := by
    rw [CPolynomial.toPoly_pow]
    exact hG.pow _
  refine natDegree_gsRelationColumn_lt _ _ _ hMon ?_ _ _ _
  rw [CPolynomial.natDegree_toPoly, CPolynomial.toPoly_pow, hG.natDegree_pow,
    ← CPolynomial.natDegree_toPoly]
  exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))

/-! ## The second reduction changes nothing -/

omit [BEq F] [LawfulBEq F] in
theorem ofFn_congr {rows width : Nat} {e e' : Nat → Nat → CPolynomial F}
    (h : ∀ i j, i < rows → j < width → e i j = e' i j) :
    PolynomialMatrix.ofFn rows width e = PolynomialMatrix.ofFn rows width e' := by
  unfold PolynomialMatrix.ofFn
  congr 1
  refine List.map_congr_left fun i hi ↦ ?_
  congr 1
  exact List.map_congr_left fun j hj ↦ h i j (List.mem_range.1 hi) (List.mem_range.1 hj)

omit [BEq F] [LawfulBEq F] in
theorem ofFn_eq_ofFn_rowGet (rows width : Nat) (e : Nat → Nat → CPolynomial F) :
    PolynomialMatrix.ofFn rows width e = PolynomialMatrix.ofFn rows width
      (fun i j ↦ rowGet ((PolynomialMatrix.ofFn rows width e).getD i #[]) j) :=
  ofFn_congr fun _ _ hi hj ↦ (ofFn_rowGet _ _ _ hi hj).symm

/-- **The second reduction changes nothing**: on the Guruswami–Sudan data (`G` monic, of positive
degree), the reduced exact-nullspace lift is the unreduced one. -/
theorem reducedExactNullspaceLift_gs (mulCtx : CPolynomial.MulContext F)
    (modCtx : CPolynomial.ModContext F) (R G : CPolynomial F) (params : GSInterpParams)
    (hG : G.toPoly.Monic) (hG1 : 1 ≤ G.natDegree) :
    reducedExactNullspaceLift modCtx (modularEquation (buildGSModularDataWithRG mulCtx modCtx R G params)) =
      exactNullspaceLift (modularEquation (buildGSModularDataWithRG mulCtx modCtx R G params)) := by
  set moduli := gsModuli mulCtx G params.multiplicity with hmod
  set M := gsRelationMatrixWithModuli mulCtx modCtx R moduli params with hM
  have heq : modularEquation (buildGSModularDataWithRG mulCtx modCtx R G params) =
      { moduli := moduli, matrix := M } := rfl
  have hMofFn : M = PolynomialMatrix.ofFn (interpolationWidth params) params.multiplicity
      (fun i j ↦ rowGet (M.getD i #[]) j) :=
    ofFn_eq_ofFn_rowGet _ _ _
  rw [heq, reducedExactNullspaceLift, exactNullspaceLift]
  congr 1
  simp only [ModularEquation.solutionWidth, ModularEquation.modularWidth]
  rw [hM, gsRelationMatrixWithModuli_size, hmod, gsModuli_size, ← hmod, ← hM]
  conv_rhs => rw [hMofFn]
  refine ofFn_congr fun i j hi hj ↦ ?_
  have hMon : (moduli.getD j 0).toPoly.Monic := by
    rw [hmod, gsModuli_getD _ _ hj, CPolynomial.toPoly_pow]
    exact hG.pow _
  exact modByMonicWith_eq_self modCtx hMon
    (natDegree_gsRelationMatrix_entry_lt mulCtx modCtx R G params hG hG1 hi hj)

/-- The solver's X-adic problem on the Guruswami–Sudan data, without the second reduction. -/
theorem fullWindowExactNullspaceProblem_gs (mulCtx : CPolynomial.MulContext F)
    (modCtx : CPolynomial.ModContext F) (R G : CPolynomial F) (params : GSInterpParams)
    (hG : G.toPoly.Monic) (hG1 : 1 ≤ G.natDegree) (bound : Nat) :
    fullWindowExactNullspaceProblem modCtx
        (modularEquation (buildGSModularDataWithRG mulCtx modCtx R G params)) bound =
      { orders := (gsModuli mulCtx G params.multiplicity).map
          fun modulus ↦ modulus.natDegree + bound + 2
        matrix := exactNullspaceLift
          (modularEquation (buildGSModularDataWithRG mulCtx modCtx R G params)) } := by
  rw [fullWindowExactNullspaceProblem, reducedExactNullspaceLift_gs mulCtx modCtx R G params hG hG1]
  rfl

/-! ## The problem's sizes and orders -/

omit [BEq F] [LawfulBEq F] in
/-- The window the lanes' solver runs at: the weighted degree `W`. -/
theorem solveWindow_some (equation : ModularEquation F) (shift : Array Nat) (bound : Nat) :
    solveWindow equation shift (some bound) = bound := rfl

omit [BEq F] [LawfulBEq F] in
theorem mem_ofFn_size {rows width : Nat} {e : Nat → Nat → CPolynomial F} {r : PolynomialRow F}
    (h : r ∈ (PolynomialMatrix.ofFn rows width e).toList) : r.size = width := by
  simp only [PolynomialMatrix.ofFn, List.toList_toArray, List.mem_map] at h
  obtain ⟨i, -, rfl⟩ := h
  simp

/-- **`ℓ + 1 + m` rows.** -/
theorem gsProblem_matrix_size (mulCtx : CPolynomial.MulContext F)
    (modCtx : CPolynomial.ModContext F) (R G : CPolynomial F) (params : GSInterpParams)
    (bound : Nat) :
    (fullWindowExactNullspaceProblem modCtx
        (modularEquation (buildGSModularDataWithRG mulCtx modCtx R G params)) bound).matrix.size =
      interpolationWidth params + params.multiplicity := by
  show (reducedExactNullspaceLift modCtx _).size = _
  rw [reducedExactNullspaceLift, Array.size_append, negativeDiagonalRows]
  simp only [PolynomialMatrix.ofFn, List.size_toArray, List.length_map, List.length_range]
  show (gsRelationMatrixWithModuli mulCtx modCtx R _ params).size + (gsModuli mulCtx G _).size = _
  rw [gsRelationMatrixWithModuli_size, gsModuli_size]

/-- **Rows of width `m`.** -/
theorem gsProblem_row_size (mulCtx : CPolynomial.MulContext F)
    (modCtx : CPolynomial.ModContext F) (R G : CPolynomial F) (params : GSInterpParams)
    (bound : Nat) {r : PolynomialRow F}
    (hr : r ∈ (fullWindowExactNullspaceProblem modCtx
        (modularEquation (buildGSModularDataWithRG mulCtx modCtx R G params)) bound).matrix.toList) :
    r.size = params.multiplicity := by
  change r ∈ (reducedExactNullspaceLift modCtx _).toList at hr
  rw [reducedExactNullspaceLift, negativeDiagonalRows, Array.toList_append, List.mem_append] at hr
  rcases hr with hr | hr <;> rw [mem_ofFn_size hr] <;>
    exact gsModuli_size mulCtx G params.multiplicity

theorem gsProblem_orders_size (mulCtx : CPolynomial.MulContext F)
    (modCtx : CPolynomial.ModContext F) (R G : CPolynomial F) (params : GSInterpParams)
    (bound : Nat) :
    (fullWindowExactNullspaceProblem modCtx
        (modularEquation (buildGSModularDataWithRG mulCtx modCtx R G params)) bound).orders.size =
      params.multiplicity := by
  show ((gsModuli mulCtx G params.multiplicity).map _).size = _
  rw [Array.size_map, gsModuli_size]

/-- **The orders**: `deg M_b + W + 2 = (m − b)·deg G + W + 2`. -/
theorem gsProblem_order (mulCtx : CPolynomial.MulContext F)
    (modCtx : CPolynomial.ModContext F) (R G : CPolynomial F) (params : GSInterpParams)
    (hG : G.toPoly.Monic) (bound : Nat) {b : Nat} (hb : b < params.multiplicity) :
    (fullWindowExactNullspaceProblem modCtx
        (modularEquation (buildGSModularDataWithRG mulCtx modCtx R G params)) bound).orders.getD b 0 =
      (params.multiplicity - b) * G.natDegree + bound + 2 := by
  show ((gsModuli mulCtx G params.multiplicity).map _).getD b 0 = _
  have hs := gsModuli_size mulCtx G params.multiplicity
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_eq_getElem (by omega),
    Option.map_some, Option.getD_some]
  have h := natDegree_gsModuli mulCtx hG hb
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by omega), Option.getD_some] at h
  rw [h]

/-- The orders, as a list: `(i + 1)·deg G + W + 2` for `i < m`, reversed. -/
theorem gsProblem_orders_toList (mulCtx : CPolynomial.MulContext F)
    (modCtx : CPolynomial.ModContext F) (R G : CPolynomial F) (params : GSInterpParams)
    (hG : G.toPoly.Monic) (bound : Nat) :
    (fullWindowExactNullspaceProblem modCtx
        (modularEquation (buildGSModularDataWithRG mulCtx modCtx R G params)) bound).orders.toList =
      ((List.range params.multiplicity).map
        fun i ↦ (i + 1) * G.natDegree + bound + 2).reverse := by
  show ((gsModuli mulCtx G params.multiplicity).map _).toList = _
  rw [gsModuli_eq, Array.toList_map, Array.toList_reverse, List.map_reverse, List.map_map]
  congr 1
  refine List.map_congr_left fun i _ ↦ ?_
  simp only [Function.comp_apply]
  rw [CPolynomial.natDegree_toPoly, CPolynomial.toPoly_pow, hG.natDegree_pow,
    ← CPolynomial.natDegree_toPoly]

private theorem foldl_add_eq (l : List Nat) (acc : Nat) :
    l.foldl (fun a o ↦ a + o) acc = acc + l.sum := by
  induction l generalizing acc with
  | nil => simp
  | cons x l ih => rw [List.foldl_cons, ih, List.sum_cons]; omega

private theorem two_mul_sum_orders (n c : Nat) : ∀ m : Nat,
    2 * ((List.range m).map fun i ↦ (i + 1) * n + c).sum = n * m * (m + 1) + 2 * m * c
  | 0 => by simp
  | m + 1 => by
    have ih := two_mul_sum_orders n c m
    rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]
    nlinarith [ih]

/-- **The total order**: `2·Σ_b (deg M_b + W + 2) = deg G·m·(m+1) + 2m·(W + 2)`. -/
theorem gsProblem_totalOrder (mulCtx : CPolynomial.MulContext F)
    (modCtx : CPolynomial.ModContext F) (R G : CPolynomial F) (params : GSInterpParams)
    (hG : G.toPoly.Monic) (bound : Nat) :
    2 * totalOrder (fullWindowExactNullspaceProblem modCtx
        (modularEquation (buildGSModularDataWithRG mulCtx modCtx R G params)) bound) =
      G.natDegree * params.multiplicity * (params.multiplicity + 1) +
        2 * params.multiplicity * (bound + 2) := by
  rw [totalOrder, ← Array.foldl_toList, gsProblem_orders_toList mulCtx modCtx R G params hG,
    foldl_add_eq, List.sum_reverse, Nat.zero_add]
  have h := two_mul_sum_orders G.natDegree (bound + 2) params.multiplicity
  simp only [← Nat.add_assoc] at h
  exact h

private theorem foldl_max_le {v : Nat} :
    ∀ (l : List Nat) (acc : Nat), acc ≤ v → (∀ x ∈ l, x ≤ v) → l.foldl max acc ≤ v
  | [], _, h, _ => h
  | x :: l, acc, h, hl => by
    rw [List.foldl_cons]
    exact foldl_max_le l _ (max_le h (hl x (by simp))) fun y hy ↦ hl y (by simp [hy])

private theorem le_foldl_max :
    ∀ (l : List Nat) (acc x : Nat), x ∈ l ∨ x ≤ acc → x ≤ l.foldl max acc
  | [], _, _, h => by simpa using h
  | y :: l, acc, x, h => by
    rw [List.foldl_cons]
    refine le_foldl_max l _ x ?_
    rcases h with h | h
    · rcases List.mem_cons.1 h with rfl | h
      · exact Or.inr (le_max_right _ _)
      · exact Or.inl h
    · exact Or.inr (le_trans h (le_max_left _ _))

/-- **The largest order**: `m·deg G + W + 2`. -/
theorem gsProblem_maxOrder (mulCtx : CPolynomial.MulContext F)
    (modCtx : CPolynomial.ModContext F) (R G : CPolynomial F) (params : GSInterpParams)
    (hG : G.toPoly.Monic) (bound : Nat) (hm : 0 < params.multiplicity) :
    maxOrder (fullWindowExactNullspaceProblem modCtx
        (modularEquation (buildGSModularDataWithRG mulCtx modCtx R G params)) bound) =
      params.multiplicity * G.natDegree + bound + 2 := by
  rw [maxOrder, ← Array.foldl_toList, gsProblem_orders_toList mulCtx modCtx R G params hG]
  refine le_antisymm (foldl_max_le _ _ (Nat.zero_le _) fun x hx ↦ ?_) (le_foldl_max _ _ _ ?_)
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 (List.mem_reverse.1 hx)
    have := Nat.mul_le_mul_right G.natDegree (show i + 1 ≤ params.multiplicity from
      List.mem_range.1 hi)
    omega
  · refine Or.inl (List.mem_reverse.2 (List.mem_map.2 ⟨params.multiplicity - 1,
      List.mem_range.2 (by omega), ?_⟩))
    rw [Nat.sub_add_cancel hm]

end Generic

/-! ## At `(28, 4)` -/

theorem johnsonThreshold_28_4 : johnsonThreshold 28 4 = 16792398 := by decide +kernel

/-- The decoder's parameters at `(28, 4)`: `k = 2^22`, `m = 415`, `W = 6968845169`. -/
theorem gsInterp_28_4 : (gsParamsFor (2 ^ 22) (2 ^ (22 + 4)) 16792398).interp =
    { messageDegree := 2 ^ 22, multiplicity := 415, weightedDegreeBound := 6968845169 } := by
  decide +kernel

/-- `ℓ + 1 = 1662` at `(28, 4)`. -/
theorem interpolationWidth_28_4 :
    interpolationWidth (gsParamsFor (2 ^ 22) (2 ^ (22 + 4)) 16792398).interp = 1662 := by
  rw [gsInterp_28_4]
  decide

/-- **The lane's X-adic problem at `(28, 4)`**, for every interpolation polynomial `R` and
contexts: `2077` rows of width `415`, the unreduced lift, `415` orders
`(415 − b)·2^26 + 6968845171`, the largest `34819023731 ≈ 2^35.02`, their sum
`8684907886445 ≈ 2^42.98`. -/
theorem laneProblem_28_4 (mulCtx : CPolynomial.MulContext K) (modCtx : CPolynomial.ModContext K)
    (Sym : ℕ → ℕ → K) (u : ℕ) (R : CPolynomial K) :
    let points := lanePointsS (2 ^ (22 + 4)) Sym u
    let params := (gsParamsFor (2 ^ 22) (2 ^ (22 + 4)) 16792398).interp
    let G := vanishingFast (points.map fun point ↦ point.1)
    let P := fullWindowExactNullspaceProblem modCtx
      (modularEquation (buildGSModularDataWithRG mulCtx modCtx R G params))
      params.weightedDegreeBound
    P.matrix = exactNullspaceLift
        (modularEquation (buildGSModularDataWithRG mulCtx modCtx R G params)) ∧
      P.matrix.size = 2077 ∧ (∀ r ∈ P.matrix.toList, r.size = 415) ∧
      P.orders.size = 415 ∧
      (∀ b < 415, P.orders.getD b 0 = (415 - b) * 2 ^ 26 + 6968845171) ∧
      maxOrder P = 34819023731 ∧ totalOrder P = 8684907886445 := by
  intro points params G P
  have hG : G.toPoly.Monic := monic_vanishingFast _
  have hn : G.natDegree = 2 ^ 26 := by
    rw [natDegree_vanishingFast]
    simp [points, lanePointsS]
  have hm : params.multiplicity = 415 := by simp only [params, gsInterp_28_4]
  have hW : params.weightedDegreeBound = 6968845169 := by simp only [params, gsInterp_28_4]
  have hw : interpolationWidth params = 1662 := interpolationWidth_28_4
  refine ⟨?_, ?_, fun r hr ↦ ?_, ?_, fun b hb ↦ ?_, ?_, ?_⟩
  · show (fullWindowExactNullspaceProblem _ _ _).matrix = _
    rw [fullWindowExactNullspaceProblem_gs mulCtx modCtx R G params hG (by omega)]
  · rw [gsProblem_matrix_size, hw, hm]
  · rw [gsProblem_row_size mulCtx modCtx R G params _ hr, hm]
  · rw [gsProblem_orders_size, hm]
  · rw [gsProblem_order mulCtx modCtx R G params hG _ (by omega), hm, hn, hW]
  · rw [gsProblem_maxOrder mulCtx modCtx R G params hG _ (by omega), hm, hn, hW]
    norm_num
  · have h : 2 * totalOrder P = G.natDegree * params.multiplicity * (params.multiplicity + 1) +
        2 * params.multiplicity * (params.weightedDegreeBound + 2) :=
      gsProblem_totalOrder mulCtx modCtx R G params hG params.weightedDegreeBound
    rw [hm, hn, hW] at h
    norm_num at h
    omega

end

end LeanVM.Extraction.Fast
