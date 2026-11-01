module

public import LeanVM.Protocol.Extraction.Fast.Truncate
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.Algebra.Polynomial.Roots
public import CompPoly.Bivariate.GuruswamiSudan.Interpolation.Basic
public import LeanVM.Protocol.Extraction.Fast.Extract
import all CompPoly.Univariate.Basic
import all CompPoly.Univariate.Raw.Core
import all CompPoly.Data.Array.Lemmas

/-!
# Roth–Ruckenstein: the number of nodes

The extractor's root finder (`prefixesTruncD`, `Fast/Truncate.lean`, falling back to
`prefixesWithFuelFast`) walks a tree: at a node with polynomial `Q`, stripped of its `X`-adic
factor to `Qn`, each root `a` of `P = Qn(0, Y)` (`initialCoefficientPolynomial`) is a child, with
polynomial `Qn(X, a + X·Y)` (`substituteFast`). Each node is one call of the recursion.

**The degree potential** (`rrDeg Q`, the degree of `P`): a child's degree is at most the
multiplicity `μ_a` of its root (`rrDeg_residualFast_le`): the coefficient of `X^μ·Y^μ` in
`Q(X, a + X·Y)` is the `μ`-th Taylor coefficient of `P` at `a`, nonzero, so the child's
`X`-adic order is `s ≤ μ`; its row `X^s` has `Y`-degree at most `s`, as every row `X^i` of the
substitution has `Y`-degree at most `i`. The roots are distinct (`FieldRootContext`s that list
each root once, as CompPoly's finite-field root finder does: `fieldRootCtx_nodup`), so their
number and the sum of their multiplicities are at most `deg P` (`sum_rootMultiplicity_le`).
Hence a subtree of depth `fuel` has at most `1 + fuel·rrDeg Q` nodes (**`rrNodes_le`**,
**`rrNodesTrunc_le`**, the latter for the truncated recursion the extractor runs, its fallback
included): at most `deg_Y Q ≤ ℓ` nodes per level, `1 + k·ℓ` in all.

**Sizes**: the substitution keeps the number of `Y`-coefficients (`YLenLe.substituteFast`) and
adds at most that number to the `X`-length (`XLenLe.substituteFast`); truncation keeps
`X`-lengths below `M`; stripping and truncating do not grow them. So a truncated node has
`ℓ + 1` rows of at most `k` coefficients, an exact one (the fallback's) `ℓ + 1` rows of at most
`W + 1 + depth·(ℓ + 1)` (`replayPath_lenLe`, `TInv`, `WInv`).

**Costs**: a cost paying at most `c` per call on nodes of these sizes is at most `c` per node
(`rrCost_le_nodes`, `rrCostTrunc_le_nodes`). At the extractor (`gsRunNoCheck`, on an interpolation
polynomial of weighted degree `≤ W`): at most `1 + k·ℓ` nodes (**`gsRun_nodes_le`**), with the
sizes above (`gsRun_tInv`); CompPoly's root finder lists each root once (`fieldRootCtx_nodup`).

Reference: R. M. Roth and G. Ruckenstein, *Efficient decoding of Reed–Solomon codes beyond half
the minimum distance*, IEEE Trans. Inform. Theory 46 (2000), §IV (the tree of the recursion, the
count of its nodes by the multiplicities of the roots).

Credits: the algorithm and its `X`-adic order lemmas are CompPoly's (github.com/Verified-zkEVM/CompPoly,
Apache-2.0, "Copyright (c) 2026 CompPoly Contributors"; `Bivariate/GuruswamiSudan/Root/`,
Valerii Huhnin), used, not copied; `substituteFast`, `prefixesTruncD` are this repository's
(`Fast/RothRuckenstein.lean`, `Fast/Truncate.lean`).
-/

namespace LeanVM.Cost.Bounds

open CompPoly CompPoly.GuruswamiSudan LeanVM.Extraction.Fast

public section

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]

/-! ## Distinct roots -/

/-- A root finder that lists each root once. -/
def RootsNodup (fr : FieldRootContext F) : Prop :=
  ∀ p, (fr.rootsInField p).toList.Nodup

omit [DecidableEq F] in
theorem rootsInFieldForNonzeroEquation_nodup {fr : FieldRootContext F} (hfr : RootsNodup fr)
    (p : CPolynomial F) : (rootsInFieldForNonzeroEquation fr p).toList.Nodup := by
  unfold rootsInFieldForNonzeroEquation
  split
  · simp
  · exact hfr p

omit [DecidableEq F] in
theorem rootsInFieldForNonzeroEquation_of_eq_zero (fr : FieldRootContext F) :
    rootsInFieldForNonzeroEquation fr 0 = #[] := by
  simp [rootsInFieldForNonzeroEquation]

omit [BEq F] [LawfulBEq F] [DecidableEq F] in
/-- **Distinct roots, counted with multiplicity, are at most the degree.** -/
theorem sum_rootMultiplicity_le (P : Polynomial F) (L : Finset F) :
    ∑ a ∈ L, P.rootMultiplicity a ≤ P.natDegree := by
  classical
  calc ∑ a ∈ L, P.rootMultiplicity a = ∑ a ∈ L, P.roots.count a := by
        simp [Polynomial.count_roots]
    _ ≤ ∑ a ∈ L ∪ P.roots.toFinset, P.roots.count a :=
        Finset.sum_le_sum_of_subset Finset.subset_union_left
    _ = ∑ a ∈ P.roots.toFinset, P.roots.count a := by
        refine (Finset.sum_subset Finset.subset_union_right fun a _ ha ↦ ?_).symm
        exact Multiset.count_eq_zero.2 fun h ↦ ha (Multiset.mem_toFinset.2 h)
    _ = Multiset.card P.roots := Multiset.toFinset_sum_count_eq _
    _ ≤ P.natDegree := Polynomial.card_roots' P

/-! ## The degree potential -/

/-- **The degree at a node**: the degree of `Qn(0, Y)`, `Qn` the node's polynomial stripped of its
`X`-adic factor; the number of roots, and the sum of their multiplicities, are at most it. -/
@[expose] def rrDeg (Q : CBivariate F) : ℕ :=
  (initialCoefficientPolynomial (CBivariate.stripXAdicFactor Q)).natDegree

omit [BEq F] [LawfulBEq F] [DecidableEq F] in
theorem cbivariate_coeff_eq (Q : CBivariate F) (i j : ℕ) :
    CBivariate.coeff Q i j = (Q.val.coeff j).coeff i := rfl

theorem toPoly_initialCoefficientPolynomial_coeff (Q : CBivariate F) (j : ℕ) :
    (initialCoefficientPolynomial Q).toPoly.coeff j = CBivariate.coeff Q 0 j := by
  rw [← CPolynomial.coeff_toPoly, coeff_initialCoefficientPolynomial]

omit [DecidableEq F] in
theorem natDegree_le_of_coeff_zero (p : CPolynomial F) (d : ℕ)
    (h : ∀ j, d < j → p.coeff j = 0) : p.natDegree ≤ d := by
  rw [CPolynomial.natDegree_toPoly, Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro j hj
  rw [← CPolynomial.coeff_toPoly]
  exact h j hj

/-- The coefficient of `X^μ·Y^μ` in `Q(X, a + X·Y)` is the `μ`-th Taylor coefficient at `a` of
`P = Q(0, Y)`. -/
theorem substCoeff_diag_eq_taylor (Q : CBivariate F) (a : F) (μ : ℕ)
    (hμ : μ < Q.val.size) :
    substCoeff Q a μ μ = ((initialCoefficientPolynomial Q).toPoly.taylor a).coeff μ := by
  set P := (initialCoefficientPolynomial Q).toPoly
  rw [Polynomial.taylor_coeff]
  have hN : (Polynomial.hasseDeriv μ P).natDegree < Q.val.size - μ := by
    have : (Polynomial.hasseDeriv μ P).natDegree ≤ Q.val.size - μ - 1 := by
      rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro n hn
      rw [Polynomial.hasseDeriv_coeff, toPoly_initialCoefficientPolynomial_coeff,
        cbivar_coeff_eq_zero_of_y_size_le Q (by omega), mul_zero]
    omega
  rw [Polynomial.eval_eq_sum_range' hN, substCoeff]
  rw [← Finset.sum_range_add_sum_Ico _ hμ.le]
  rw [Finset.sum_eq_zero (s := Finset.range μ) fun y hy ↦ by
    have := Finset.mem_range.1 hy
    simp [show ¬ μ ≤ y by omega], zero_add, Finset.sum_Ico_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Polynomial.hasseDeriv_coeff, toPoly_initialCoefficientPolynomial_coeff,
    cbivariate_coeff_eq]
  simp only [Nat.le_add_right, le_refl, and_self, ↓reduceIte, Nat.sub_self, Nat.add_sub_cancel_left]
  rw [Nat.add_comm i μ]
  ring

omit [DecidableEq F] in
/-- A nonzero coefficient `X^i` bounds the `X`-adic order. -/
theorem xAdicOrder?_le_of_coeff_ne_zero {S : CBivariate F} {i j : ℕ}
    (h : CBivariate.coeff S i j ≠ 0) : ∃ s, CBivariate.xAdicOrder? S = some s ∧ s ≤ i := by
  cases hS : CBivariate.xAdicOrder? S with
  | none =>
    exact absurd (by rw [cbivar_xAdicOrder?_none_eq_zero hS, CBivariate.coeff_zero]) h
  | some s =>
    refine ⟨s, rfl, ?_⟩
    by_contra hlt
    exact h (cbivar_xAdicOrder?_some_coeff_eq_zero_of_lt hS (by omega))

/-- **A child's degree is at most its root's multiplicity**: for `P = Qn(0, Y) ≠ 0`, the node
of root `a` (`residualFast Qn a`, `Qn(X, a + X·Y)` stripped) has degree at most the
multiplicity of `a` in `P`. -/
theorem rrDeg_residualFast_le [CharP F 2] (Qn : CBivariate F) (a : F)
    (hP : initialCoefficientPolynomial Qn ≠ 0) :
    rrDeg (residualFast Qn a) ≤ (initialCoefficientPolynomial Qn).toPoly.rootMultiplicity a := by
  set P := (initialCoefficientPolynomial Qn).toPoly
  set μ := P.rootMultiplicity a
  have hP' : P ≠ 0 := by
    intro h; apply hP; rw [← CPolynomial.toPoly_inj, CPolynomial.toPoly_zero]; exact h
  -- `deg P < |Qn|` and `μ ≤ deg P`
  have hdeg : P.natDegree < Qn.val.size := by
    by_contra hge
    have hlead : P.leadingCoeff = 0 := by
      rw [Polynomial.leadingCoeff, toPoly_initialCoefficientPolynomial_coeff,
        cbivar_coeff_eq_zero_of_y_size_le Qn (by omega)]
    exact hP' (Polynomial.leadingCoeff_eq_zero.1 hlead)
  have hμ : μ ≤ P.natDegree := by
    have := sum_rootMultiplicity_le P {a}
    simpa [μ] using this
  -- the coefficient of `X^μ·Y^μ` is nonzero
  set S := substituteFast Qn a
  have hdiag : CBivariate.coeff S μ μ ≠ 0 := by
    rw [coeff_substituteFast, substCoeff_diag_eq_taylor Qn a μ (by omega)]
    have ht : P.taylor a ≠ 0 := by rwa [Ne, Polynomial.taylor_eq_zero]
    have hμt : μ = (P.taylor a).natTrailingDegree := by
      rw [Polynomial.taylor_apply]; exact Polynomial.rootMultiplicity_eq_natTrailingDegree
    rw [hμt]
    exact mt Polynomial.trailingCoeff_eq_zero.1 ht
  obtain ⟨s, hs, hsμ⟩ := xAdicOrder?_le_of_coeff_ne_zero hdiag
  -- the child's equation is row `X^s`, of `Y`-degree at most `s`
  rw [rrDeg, residualFast, stripXAdicFactor_stripXAdicFactor, stripXAdicFactor_of_order hs]
  refine (natDegree_le_of_coeff_zero _ s fun j hj ↦ ?_).trans hsμ
  rw [coeff_initialCoefficientPolynomial, cbivar_coeff_divXPower, Nat.zero_add,
    coeff_substituteFast, substCoeff]
  refine Finset.sum_eq_zero fun y _ ↦ ?_
  simp [show ¬ j ≤ s by omega]

/-! ## The number of nodes -/

theorem list_sum_map_le {α : Type*} {l : List α} {f g : α → ℕ} (h : ∀ a ∈ l, f a ≤ g a) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (h x (by simp)) (ih fun a ha ↦ h a (by simp [ha]))

/-- The roots at a node: those of `Qn(0, Y)`, `Qn` the node's polynomial stripped. -/
@[expose] def rrRoots (fr : FieldRootContext F) (Q : CBivariate F) : Array F :=
  rootsInFieldForNonzeroEquation fr (initialCoefficientPolynomial (CBivariate.stripXAdicFactor Q))

theorem initialCoefficientPolynomial_zero :
    initialCoefficientPolynomial (0 : CBivariate F) = 0 := by
  refine CPolynomial.eq_iff_coeff.2 fun j ↦ ?_
  rw [coeff_initialCoefficientPolynomial, CBivariate.coeff_zero, CPolynomial.coeff_zero]

/-- A node whose stripped polynomial is zero has no children (`prefixesWithFuelFast`'s
`Qnorm == 0` branch). -/
theorem rrRoots_of_strip_eq_zero (fr : FieldRootContext F) {Q : CBivariate F}
    (h : CBivariate.stripXAdicFactor Q = 0) : rrRoots fr Q = #[] := by
  rw [rrRoots, h, initialCoefficientPolynomial_zero, rootsInFieldForNonzeroEquation_of_eq_zero]

/-- **One level**: the children of a node, weighted by `1 + fuel·(their degree)`, sum to at most
`(fuel + 1)·(the node's degree)`. -/
theorem rr_children_le [CharP F 2] {fr : FieldRootContext F} (hfr : RootsNodup fr)
    (Q : CBivariate F) (fuel : ℕ) :
    ((rrRoots fr Q).toList.map fun a ↦
        1 + fuel * rrDeg (residualFast (CBivariate.stripXAdicFactor Q) a)).sum ≤
      (fuel + 1) * rrDeg Q := by
  set Qn := CBivariate.stripXAdicFactor Q
  set P := initialCoefficientPolynomial Qn
  by_cases hP : P = 0
  · rw [rrRoots, show initialCoefficientPolynomial Qn = 0 from hP,
      rootsInFieldForNonzeroEquation_of_eq_zero]
    simp
  have hroots : rrRoots fr Q = fr.rootsInField P := by
    rw [rrRoots]
    simp [rootsInFieldForNonzeroEquation, P, Qn, hP]
  rw [hroots]
  set L := (fr.rootsInField P).toList
  have hL : L.Nodup := hfr P
  rw [← List.sum_toFinset _ hL]
  have hmult : ∀ a ∈ L.toFinset,
      1 + fuel * rrDeg (residualFast Qn a) ≤
        (fuel + 1) * P.toPoly.rootMultiplicity a := by
    intro a ha
    have hroot : CPolynomial.eval a P = 0 := fr.sound P a (List.mem_toFinset.1 ha)
    have hP' : P.toPoly ≠ 0 := by
      intro h; apply hP; rw [← CPolynomial.toPoly_inj, CPolynomial.toPoly_zero]; exact h
    have hpos : 0 < P.toPoly.rootMultiplicity a := by
      rw [Polynomial.rootMultiplicity_pos hP', Polynomial.IsRoot, ← CPolynomial.eval_toPoly]
      exact hroot
    have h1 : rrDeg (residualFast Qn a) ≤ P.toPoly.rootMultiplicity a :=
      rrDeg_residualFast_le Qn a hP
    have h2 := Nat.mul_le_mul_left fuel h1
    rw [Nat.succ_mul]
    omega
  refine (Finset.sum_le_sum hmult).trans ?_
  rw [← Finset.mul_sum]
  refine Nat.mul_le_mul_left _ ((sum_rootMultiplicity_le _ _).trans ?_)
  rw [rrDeg, ← CPolynomial.natDegree_toPoly]

/-- **The nodes of `prefixesWithFuelFast`**: one per call. -/
@[expose] def rrNodes (fr : FieldRootContext F) : ℕ → CBivariate F → ℕ
  | 0, _Q => 1
  | fuel + 1, Q =>
    1 + ((rrRoots fr Q).toList.map fun a ↦
      rrNodes fr fuel (residualFast (CBivariate.stripXAdicFactor Q) a)).sum

/-- **Roth–Ruckenstein's tree has at most `1 + fuel·rrDeg Q` nodes.** -/
theorem rrNodes_le [CharP F 2] {fr : FieldRootContext F} (hfr : RootsNodup fr) (fuel : ℕ) :
    ∀ Q : CBivariate F, rrNodes fr fuel Q ≤ 1 + fuel * rrDeg Q := by
  induction fuel with
  | zero => intro Q; simp [rrNodes]
  | succ fuel ih =>
    intro Q
    rw [rrNodes]
    have := (list_sum_map_le fun a _ ↦ ih (residualFast (CBivariate.stripXAdicFactor Q) a)).trans
      (rr_children_le hfr Q fuel)
    omega

/-- **The nodes of the truncated recursion** (`prefixesTruncD`, the extractor's): one per call,
the fallback's (`prefixesWithFuelFast` on the exact polynomial) included. -/
@[expose] def rrNodesTrunc (fr : FieldRootContext F) :
    ℕ → CBivariate F → ℕ → CBivariate F → List F → ℕ
  | 0, _q, _M, _Q₀, _path => 1
  | fuel + 1, q, M, Q₀, path =>
    match CBivariate.xAdicOrder? q with
    | some s =>
      if s < M then
        1 + ((rootsInFieldForNonzeroEquation fr
            (initialCoefficientPolynomial (CBivariate.divXPower q s))).toList.map fun a ↦
          rrNodesTrunc fr fuel (CBivariate.truncateX (substituteFast (CBivariate.divXPower q s) a)
            (M - s)) (M - s) Q₀ (path ++ [a])).sum
      else rrNodes fr (fuel + 1) (replayPath Q₀ path)
    | none => rrNodes fr (fuel + 1) (replayPath Q₀ path)

/-- **The truncated recursion visits at most `1 + fuel·rrDeg E` nodes**, `E` the exact
polynomial (`replayPath`): the truncation sees the same roots as the exact recursion. -/
theorem rrNodesTrunc_le [CharP F 2] {fr : FieldRootContext F} (hfr : RootsNodup fr)
    (fuel : ℕ) :
    ∀ (S : CBivariate F) (M : ℕ) (Q₀ : CBivariate F) (path : List F),
      CBivariate.stripXAdicFactor S = CBivariate.stripXAdicFactor (replayPath Q₀ path) →
      rrNodesTrunc fr fuel (CBivariate.truncateX S M) M Q₀ path ≤
        1 + fuel * rrDeg (replayPath Q₀ path) := by
  induction fuel with
  | zero => intro S M Q₀ path _; simp [rrNodesTrunc]
  | succ fuel ih =>
    intro S M Q₀ path hSE
    rw [rrNodesTrunc]
    cases hq : CBivariate.xAdicOrder? (CBivariate.truncateX S M) with
    | none => exact rrNodes_le hfr _ _
    | some s =>
      obtain ⟨hsM, hS⟩ := xAdicOrder?_of_truncateX hq
      simp only [hsM, ↓reduceIte]
      set E := replayPath Q₀ path
      have hstrip : CBivariate.stripXAdicFactor E = CBivariate.divXPower S s := by
        rw [← hSE, stripXAdicFactor_of_order hS]
      have hQn : CBivariate.divXPower (CBivariate.truncateX S M) s =
          CBivariate.truncateX (CBivariate.divXPower S s) (M - s) := divXPower_truncateX S M s
      have hinit : initialCoefficientPolynomial
            (CBivariate.divXPower (CBivariate.truncateX S M) s) =
          initialCoefficientPolynomial (CBivariate.stripXAdicFactor E) := by
        refine CPolynomial.eq_iff_coeff.2 fun j ↦ ?_
        rw [coeff_initialCoefficientPolynomial, coeff_initialCoefficientPolynomial, hQn,
          cbivar_coeff_truncateX, hstrip]
        simp only [show 0 < M - s by omega, ↓reduceIte]
      rw [hinit]
      have hchild : ∀ a ∈ (rootsInFieldForNonzeroEquation fr
            (initialCoefficientPolynomial (CBivariate.stripXAdicFactor E))).toList,
          rrNodesTrunc fr fuel
              (CBivariate.truncateX (substituteFast (CBivariate.divXPower
                (CBivariate.truncateX S M) s) a) (M - s)) (M - s) Q₀ (path ++ [a]) ≤
            1 + fuel * rrDeg (residualFast (CBivariate.stripXAdicFactor E) a) := by
        intro a _
        rw [hQn, truncateX_substituteFast]
        have hpath : replayPath Q₀ (path ++ [a]) =
            residualFast (CBivariate.stripXAdicFactor E) a := by
          simp [replayPath, List.foldl_append, E]
        rw [← hpath]
        refine ih _ _ _ _ ?_
        rw [hpath, residualFast, stripXAdicFactor_stripXAdicFactor, hstrip]
      have := (list_sum_map_le hchild).trans (rr_children_le hfr E fuel)
      omega

/-! ## Sizes

`YLenLe Q Y`: no coefficient `Y^j`, `j ≥ Y`; `XLenLe Q X`: no coefficient `X^i`, `i ≥ X`. They
bound the arrays (`YLenLe.val_size_le`, `XLenLe.val_size_le`): `Q` has at most `Y` rows, each of
at most `X` coefficients. -/

omit [BEq F] [LawfulBEq F] [DecidableEq F] in
/-- A canonical polynomial whose coefficients vanish from `X` on is an array of at most `X`
coefficients. -/
theorem cpoly_val_size_le_of_coeff {R : Type*} [Zero R] [BEq R] [LawfulBEq R]
    (p : CPolynomial R) (X : ℕ) (h : ∀ i, X ≤ i → p.coeff i = 0) : p.val.size ≤ X := by
  by_contra hlt
  rcases CPolynomial.Raw.Trim.isCanonical_iff_size_eq_zero_or_getLastD_ne_zero.mp p.property with
    h0 | hne
  · omega
  · apply hne
    have := h (p.val.size - 1) (by omega)
    rw [CPolynomial.coeff, CPolynomial.Raw.coeff, Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_getElem (by omega), Option.getD_some] at this
    rw [Array.getLastD, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by omega),
      Option.getD_some]
    exact this

/-- No coefficient `Y^j` with `j ≥ Y`. -/
def YLenLe (Q : CBivariate F) (Y : ℕ) : Prop := ∀ i j, Y ≤ j → CBivariate.coeff Q i j = 0

/-- No coefficient `X^i` with `i ≥ X`. -/
def XLenLe (Q : CBivariate F) (X : ℕ) : Prop := ∀ i j, X ≤ i → CBivariate.coeff Q i j = 0

omit [DecidableEq F] in
/-- **At most `Y` rows.** -/
theorem YLenLe.val_size_le {Q : CBivariate F} {Y : ℕ} (h : YLenLe Q Y) : Q.val.size ≤ Y := by
  refine cpoly_val_size_le_of_coeff (R := CPolynomial F) Q Y fun j hj ↦ ?_
  exact CPolynomial.eq_iff_coeff.2 fun i ↦ by rw [CPolynomial.coeff_zero]; exact h i j hj

omit [DecidableEq F] in
/-- **Every row of at most `X` coefficients.** -/
theorem XLenLe.val_size_le {Q : CBivariate F} {X : ℕ} (h : XLenLe Q X) (j : ℕ) :
    (Q.val.coeff j).val.size ≤ X :=
  cpoly_val_size_le_of_coeff _ X fun i hi ↦ h i j hi

omit [BEq F] [LawfulBEq F] [DecidableEq F] in
theorem YLenLe.mono {Q : CBivariate F} {Y Y' : ℕ} (h : YLenLe Q Y) (hY : Y ≤ Y') : YLenLe Q Y' :=
  fun i j hj ↦ h i j (by omega)

omit [BEq F] [LawfulBEq F] [DecidableEq F] in
theorem XLenLe.mono {Q : CBivariate F} {X X' : ℕ} (h : XLenLe Q X) (hX : X ≤ X') : XLenLe Q X' :=
  fun i j hi ↦ h i j (by omega)

theorem YLenLe.substituteFast [CharP F 2] {Q : CBivariate F} {Y : ℕ} (h : YLenLe Q Y) (a : F) :
    YLenLe (substituteFast Q a) Y := by
  intro i j hj
  rw [coeff_substituteFast, substCoeff]
  refine Finset.sum_eq_zero fun y _ ↦ ?_
  split
  · rename_i hy
    rw [← cbivariate_coeff_eq, h _ y (by omega)]; ring
  · rfl

/-- **The substitution adds at most `Y` to the `X`-length.** -/
theorem XLenLe.substituteFast [CharP F 2] {Q : CBivariate F} {X Y : ℕ} (hX : XLenLe Q X)
    (hY : YLenLe Q Y) (a : F) : XLenLe (substituteFast Q a) (X + Y) := by
  intro i j hi
  rw [coeff_substituteFast, substCoeff]
  refine Finset.sum_eq_zero fun y _ ↦ ?_
  split
  · rename_i hy
    rw [← cbivariate_coeff_eq]
    by_cases hyY : Y ≤ y
    · rw [hY _ y hyY]; ring
    · rw [hX _ y (by omega)]; ring
  · rfl

omit [DecidableEq F] in
theorem XLenLe.truncateX (Q : CBivariate F) (M : ℕ) : XLenLe (CBivariate.truncateX Q M) M := by
  intro i j hi
  rw [cbivar_coeff_truncateX]
  simp [show ¬ i < M by omega]

omit [DecidableEq F] in
theorem YLenLe.truncateX {Q : CBivariate F} {Y : ℕ} (h : YLenLe Q Y) (M : ℕ) :
    YLenLe (CBivariate.truncateX Q M) Y := by
  intro i j hj
  rw [cbivar_coeff_truncateX]
  split
  · exact h i j hj
  · rfl

omit [DecidableEq F] in
theorem YLenLe.divXPower {Q : CBivariate F} {Y : ℕ} (h : YLenLe Q Y) (s : ℕ) :
    YLenLe (CBivariate.divXPower Q s) Y := by
  intro i j hj
  rw [cbivar_coeff_divXPower]
  exact h _ j hj

omit [DecidableEq F] in
theorem XLenLe.divXPower {Q : CBivariate F} {X : ℕ} (h : XLenLe Q X) (s : ℕ) :
    XLenLe (CBivariate.divXPower Q s) X := by
  intro i j hi
  rw [cbivar_coeff_divXPower]
  exact h _ j (by omega)

omit [DecidableEq F] in
theorem stripXAdicFactor_cases (Q : CBivariate F) :
    CBivariate.stripXAdicFactor Q = 0 ∨
      ∃ s, CBivariate.stripXAdicFactor Q = CBivariate.divXPower Q s := by
  cases h : CBivariate.xAdicOrder? Q with
  | none =>
    left
    rw [CBivariate.stripXAdicFactor, h]
    rfl
  | some s => exact Or.inr ⟨s, stripXAdicFactor_of_order h⟩

omit [DecidableEq F] in
theorem YLenLe.zero (Y : ℕ) : YLenLe (0 : CBivariate F) Y := by
  intro i j _; rw [CBivariate.coeff_zero]

omit [DecidableEq F] in
theorem XLenLe.zero (X : ℕ) : XLenLe (0 : CBivariate F) X := by
  intro i j _; rw [CBivariate.coeff_zero]

omit [DecidableEq F] in
theorem YLenLe.strip {Q : CBivariate F} {Y : ℕ} (h : YLenLe Q Y) :
    YLenLe (CBivariate.stripXAdicFactor Q) Y := by
  rcases stripXAdicFactor_cases Q with h0 | ⟨s, hs⟩
  · rw [h0]; exact YLenLe.zero Y
  · rw [hs]; exact h.divXPower s

omit [DecidableEq F] in
theorem XLenLe.strip {Q : CBivariate F} {X : ℕ} (h : XLenLe Q X) :
    XLenLe (CBivariate.stripXAdicFactor Q) X := by
  rcases stripXAdicFactor_cases Q with h0 | ⟨s, hs⟩
  · rw [h0]; exact XLenLe.zero X
  · rw [hs]; exact h.divXPower s

theorem YLenLe.residualFast [CharP F 2] {Q : CBivariate F} {Y : ℕ} (h : YLenLe Q Y) (a : F) :
    YLenLe (residualFast Q a) Y :=
  (h.substituteFast a).strip

/-- **A step of the exact recursion adds at most `Y` to the `X`-length.** -/
theorem XLenLe.residualFast [CharP F 2] {Q : CBivariate F} {X Y : ℕ} (hX : XLenLe Q X)
    (hY : YLenLe Q Y) (a : F) : XLenLe (residualFast Q a) (X + Y) :=
  (hX.substituteFast hY a).strip

/-- **The exact polynomial after `d` roots** (`replayPath`, the fallback's input): at most `Y`
rows, of at most `X + d·Y` coefficients. -/
theorem replayPath_lenLe [CharP F 2] {Q₀ : CBivariate F} {X Y : ℕ} (hX : XLenLe Q₀ X)
    (hY : YLenLe Q₀ Y) (path : List F) :
    YLenLe (replayPath Q₀ path) Y ∧ XLenLe (replayPath Q₀ path) (X + path.length * Y) := by
  induction path using List.reverseRecOn with
  | nil => exact ⟨hY, by simpa [replayPath] using hX⟩
  | append_singleton path a ih =>
    have e : replayPath Q₀ (path ++ [a]) =
        residualFast (CBivariate.stripXAdicFactor (replayPath Q₀ path)) a := by
      simp [replayPath, List.foldl_append]
    rw [e, List.length_append, List.length_singleton, Nat.add_mul, Nat.one_mul, ← Nat.add_assoc]
    exact ⟨ih.1.strip.residualFast a, ih.2.strip.residualFast ih.1.strip a⟩

/-- **The degree at a node is below the number of rows.** -/
theorem rrDeg_le {Q : CBivariate F} {Y : ℕ} (h : YLenLe Q Y) : rrDeg Q ≤ Y - 1 := by
  refine natDegree_le_of_coeff_zero _ _ fun j hj ↦ ?_
  rw [coeff_initialCoefficientPolynomial]
  exact h.strip 0 j (by omega)

/-- **An interpolation polynomial has at most `ℓ + 1` rows, of at most `W + 1` coefficients**
(`ValidInterpolationWitness`: weighted degree `i + (k − 1)·j ≤ W`; `ℓ = ⌊W/(k − 1)⌋`). -/
theorem lenLe_of_validInterpolation {points : Array (F × F)} {params : GSInterpParams}
    {Q : CBivariate F} (hQ : ValidInterpolationWitness points params Q)
    (hk : 1 < params.messageDegree) :
    YLenLe Q (interpolationYCap params + 1) ∧ XLenLe Q (params.weightedDegreeBound + 1) := by
  have hw := (CBivariate.natWeightedDegree_le_iff_coeff Q 1 (yWeight params) _).1 hQ.2.1
  have hy : 0 < yWeight params := by simp [yWeight]; omega
  refine ⟨fun i j hj ↦ ?_, fun i j hi ↦ ?_⟩
  · by_contra hne
    have h1 := hw i j hne
    have h2 : params.weightedDegreeBound / yWeight params < j := by
      simp only [interpolationYCap] at hj; omega
    have h3 := (Nat.div_lt_iff_lt_mul hy).1 h2
    rw [Nat.mul_comm] at h3
    omega
  · by_contra hne
    have := hw i j hne
    omega

/-! ## Costs per node

A cost of the recursion that pays at most `c` per call, on calls whose polynomials have the sizes
the recursion keeps, is at most `c` per node. The sizes: the exact recursion's polynomial at
remaining fuel `f`, of a run started at fuel `f₀` on `X₀` columns and `Y` rows, has `Y` rows and
at most `X₀ + (f₀ − f)·Y ≤ Xmax − f·Y` columns, `Xmax = X₀ + f₀·Y` (`WInv`); the truncated
recursion's has `Y` rows and at most `M ≤ M₀` columns, its exact polynomial `WInv`'s (`TInv`). -/

/-- The sizes at an exact node with remaining fuel `fuel`. -/
def WInv (Y Xmax fuel : ℕ) (Q : CBivariate F) : Prop :=
  YLenLe Q Y ∧ XLenLe Q (Xmax - fuel * Y) ∧ fuel * Y ≤ Xmax

theorem WInv.residualFast [CharP F 2] {Y Xmax fuel : ℕ} {Q : CBivariate F}
    (h : WInv Y Xmax (fuel + 1) Q) (a : F) :
    WInv Y Xmax fuel (LeanVM.Extraction.Fast.residualFast (CBivariate.stripXAdicFactor Q) a) := by
  obtain ⟨hY, hX, hle⟩ := h
  refine ⟨hY.strip.residualFast a, (hX.strip.residualFast hY.strip a).mono ?_, ?_⟩
  · rw [Nat.succ_mul] at hle ⊢; omega
  · rw [Nat.succ_mul] at hle; omega

/-- **A cost of `prefixesWithFuelFast` paying at most `c` per call is at most `c` per node.** -/
theorem rrCost_le_nodes [CharP F 2] (fr : FieldRootContext F) (Y Xmax : ℕ)
    (T : ℕ → CBivariate F → ℕ) (c : ℕ)
    (h0 : ∀ Q, WInv Y Xmax 0 Q → T 0 Q ≤ c)
    (hs : ∀ fuel Q, WInv Y Xmax (fuel + 1) Q → T (fuel + 1) Q ≤ c + ((rrRoots fr Q).toList.map
      fun a ↦ T fuel (residualFast (CBivariate.stripXAdicFactor Q) a)).sum) (fuel : ℕ) :
    ∀ Q, WInv Y Xmax fuel Q → T fuel Q ≤ c * rrNodes fr fuel Q := by
  induction fuel with
  | zero => intro Q hQ; simpa [rrNodes] using h0 Q hQ
  | succ fuel ih =>
    intro Q hQ
    rw [rrNodes, Nat.mul_add, Nat.mul_one, ← List.sum_map_mul_left]
    exact (hs fuel Q hQ).trans
      (Nat.add_le_add_left (list_sum_map_le fun a _ ↦ ih _ (hQ.residualFast a)) c)

/-- The sizes at a truncated node: `q` has `Y` rows of at most `M ≤ M₀` coefficients, and the
exact polynomial `WInv`'s sizes. -/
def TInv (Y M₀ Xmax : ℕ) (Q₀ : CBivariate F) (fuel : ℕ) (q : CBivariate F) (M : ℕ)
    (path : List F) : Prop :=
  YLenLe q Y ∧ XLenLe q M ∧ M ≤ M₀ ∧ WInv Y Xmax fuel (replayPath Q₀ path)

/-- **A cost of the truncated recursion paying at most `c` per call is at most `c` per node**
(the fallback `TW`'s, at most `c` per node of `rrNodes`, by `rrCost_le_nodes`). -/
theorem rrCostTrunc_le_nodes [CharP F 2] (fr : FieldRootContext F) (Y M₀ Xmax : ℕ)
    (Q₀ : CBivariate F)
    (T : ℕ → CBivariate F → ℕ → List F → ℕ) (TW : ℕ → CBivariate F → ℕ)
    (c : ℕ) (hW : ∀ fuel Q, WInv Y Xmax fuel Q → TW fuel Q ≤ c * rrNodes fr fuel Q)
    (h0 : ∀ q M path, TInv Y M₀ Xmax Q₀ 0 q M path → T 0 q M path ≤ c)
    (hs : ∀ fuel q M path, TInv Y M₀ Xmax Q₀ (fuel + 1) q M path → T (fuel + 1) q M path ≤
      match CBivariate.xAdicOrder? q with
      | some s =>
        if s < M then
          c + ((rootsInFieldForNonzeroEquation fr
              (initialCoefficientPolynomial (CBivariate.divXPower q s))).toList.map fun a ↦
            T fuel (CBivariate.truncateX (substituteFast (CBivariate.divXPower q s) a) (M - s))
              (M - s) (path ++ [a])).sum
        else TW (fuel + 1) (replayPath Q₀ path)
      | none => TW (fuel + 1) (replayPath Q₀ path)) (fuel : ℕ) :
    ∀ q M path, TInv Y M₀ Xmax Q₀ fuel q M path →
      T fuel q M path ≤ c * rrNodesTrunc fr fuel q M Q₀ path := by
  induction fuel with
  | zero => intro q M path hI; simpa [rrNodesTrunc] using h0 q M path hI
  | succ fuel ih =>
    intro q M path hI
    have h := hs fuel q M path hI
    obtain ⟨hY, hX, hM, hE⟩ := hI
    rw [rrNodesTrunc]
    cases heq : CBivariate.xAdicOrder? q with
    | none =>
      simp only [heq] at h
      exact h.trans (hW _ _ hE)
    | some s =>
      simp only [heq] at h
      dsimp only
      by_cases hlt : s < M
      · simp only [hlt, ↓reduceIte] at h ⊢
        rw [Nat.mul_add, Nat.mul_one, ← List.sum_map_mul_left]
        refine h.trans (Nat.add_le_add_left (list_sum_map_le fun a _ ↦ ih _ _ _ ?_) c)
        have hpath : replayPath Q₀ (path ++ [a]) =
            residualFast (CBivariate.stripXAdicFactor (replayPath Q₀ path)) a := by
          simp [replayPath, List.foldl_append]
        refine ⟨((hY.divXPower s).substituteFast a).truncateX _, XLenLe.truncateX _ _,
          by omega, ?_⟩
        rw [hpath]
        exact hE.residualFast a
      · simp only [hlt, ↓reduceIte] at h ⊢
        exact h.trans (hW _ _ hE)

/-! ## Distinct roots of the extractor's root finder -/

omit [BEq F] [LawfulBEq F] [DecidableEq F] in
theorem eraseDups_nodup {α : Type*} [BEq α] [LawfulBEq α] (xs : Array α) :
    xs.eraseDups.toList.Nodup := by
  rw [Array.eraseDups, ← Array.foldl_toList]
  have h : ∀ (l : List α) (out : Array α), out.toList.Nodup →
      (l.foldl (fun out x ↦ if out.contains x then out else out.push x) out).toList.Nodup := by
    intro l
    induction l with
    | nil => intro out h; exact h
    | cons x l ih =>
      intro out hout
      rw [List.foldl_cons]
      apply ih
      split
      · exact hout
      · rename_i hx
        rw [Array.toList_push, List.nodup_append]
        refine ⟨hout, List.nodup_singleton x, fun a ha b hb ↦ ?_⟩
        rw [List.mem_singleton] at hb
        subst hb
        rintro rfl
        exact hx (Array.contains_iff_mem.2 (Array.mem_def.2 ha))
  exact h _ _ (by simp)

open LeanVM.Extraction LeanVM.Parameters in
/-- **The extractor's root finder lists each root once** (CompPoly's finite-field root finder
ends with `eraseDups`). -/
theorem fieldRootCtx_nodup : RootsNodup fieldRootCtx := by
  intro p
  show (CPolynomial.Roots.FiniteField.rootsInFiniteFieldWith _ _ _ _ p).toList.Nodup
  unfold CPolynomial.Roots.FiniteField.rootsInFiniteFieldWith
  split
  · simp
  · split
    · simp
    · split
      · exact eraseDups_nodup _
      · exact eraseDups_nodup _

/-! ## At the extractor's parameters -/

open LeanVM.Extraction LeanVM.Parameters in
/-- **The extractor's root finding visits at most `1 + k·ℓ` nodes**: on an interpolation
polynomial `Q` (weighted degree `≤ W`, `ℓ = ⌊W/(k − 1)⌋`), `gsRunNoCheck`'s call
`prefixesTruncD fieldRootCtx k (Q mod X^k) k Q [] …` makes at most `1 + k·ℓ` calls, its
fallback's included. -/
theorem gsRun_nodes_le {points : Array (K × K)} {params : GSInterpParams} {Q : CBivariate K}
    (hQ : ValidInterpolationWitness points params Q) (hk : 1 < params.messageDegree) :
    rrNodesTrunc fieldRootCtx params.messageDegree
        (CBivariate.truncateX Q params.messageDegree) params.messageDegree Q [] ≤
      1 + params.messageDegree * interpolationYCap params := by
  have h := rrNodesTrunc_le fieldRootCtx_nodup params.messageDegree Q params.messageDegree Q []
    (by simp [replayPath])
  have hd := rrDeg_le (lenLe_of_validInterpolation hQ hk).1
  simp only [replayPath, List.foldl_nil, Nat.add_sub_cancel] at h hd
  have := Nat.mul_le_mul_left params.messageDegree hd
  omega

open LeanVM.Extraction LeanVM.Parameters in
/-- **The sizes at the extractor's root finding**: every call of `gsRunNoCheck`'s
`prefixesTruncD` has `ℓ + 1` rows of at most `k` coefficients, and its exact polynomial `ℓ + 1`
rows of at most `W + 1 + k·(ℓ + 1)` coefficients (`TInv`, kept by the recursion as
`rrCostTrunc_le_nodes` uses it). -/
theorem gsRun_tInv {points : Array (K × K)} {params : GSInterpParams} {Q : CBivariate K}
    (hQ : ValidInterpolationWitness points params Q) (hk : 1 < params.messageDegree) :
    TInv (interpolationYCap params + 1) params.messageDegree
      (params.weightedDegreeBound + 1 + params.messageDegree * (interpolationYCap params + 1)) Q
      params.messageDegree (CBivariate.truncateX Q params.messageDegree) params.messageDegree [] := by
  obtain ⟨hY, hX⟩ := lenLe_of_validInterpolation hQ hk
  refine ⟨hY.truncateX _, XLenLe.truncateX _ _, le_refl _, hY, ?_, by omega⟩
  simpa [replayPath] using hX

end

end LeanVM.Cost.Bounds
