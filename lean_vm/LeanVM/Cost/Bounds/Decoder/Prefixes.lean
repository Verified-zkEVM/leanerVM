module

public import LeanVM.Cost.Bounds.Decoder.GsRun
public import LeanVM.Cost.Bounds.RothRuckenstein
import all CompPoly.Univariate.Raw.Core
import all CompPoly.Univariate.Basic

/-!
# Bound: Roth–Ruckenstein's recursion, compiled

The price of `prefixesNF fieldRootCtxFast` (`Fast/TruncNoFallback.lean`, compiled on demand in
`Cost/Extractor/GsRun.lean` as `prefixesNF.c188`, its fold closure `prefixesNF.c188.lam0`) on a
node of at most `Y` rows of at most `M ≤ X` coefficients, at most `k` levels deep:

* a node pays its `X`-adic order, the division by `X^s`, the initial coefficient polynomial and
  its roots (`rrNodePrice X Y`); each child, in its parent's fold, the substitution
  `Y := a + X·Y`, the truncation and the prefix extended (`rrChildPrice X Y k`), and the
  concatenation of the prefixes, at most the node's subtree (`prefixesNF_size_le_nodes`);
* **`prefixesNFC_cost`**: at most `(rrNodePrice X Y + rrChildPrice X Y k + Y·fuel)` per node, the
  nodes `rrNodesNF` (`Bounds/RothRuckenstein.lean`, at most `1 + k·ℓ` on the interpolated
  polynomial: `gsRunNF_nodes_le`);
* **`gsRunDistinctNFC_cost`**: one lane's Guruswami–Sudan run in closed form (`gsRunBound`).

The nodes are at most `1 + k·ℓ` (ℓ paths of `k` levels), each of `ℓ + 1` rows of at most `W + 1`
coefficients: the substitution, `≈ 960·(W + 1)·(ℓ + 1)²` per node, dominates.
-/

namespace LeanVM.Cost.Bounds.Decoder

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.Library
open LeanVM.Cost.Extractor LeanVM.Parameters CompPoly LeanVM.Extraction.Fast

/-! The functions compiled on demand, by their short names. -/
open LeanVM.Cost.Auto.LeanVM.Extraction.Fast

public section

variable (P : Program)

/-! ## Sizes -/

/-- **`prefixesNF` returns at most one prefix per node.** -/
theorem prefixesNF_size_le_nodes (fr : GuruswamiSudan.FieldRootContext K) (fuel : ℕ) :
    ∀ (q : CBivariate K) (M depth : ℕ) (pref : CPolynomial K),
      (prefixesNF fr fuel q M depth pref).size ≤ rrNodesNF fr fuel q M := by
  induction fuel with
  | zero => intro q M depth pref; simp [prefixesNF, rrNodesNF]
  | succ fuel ih =>
    intro q M depth pref
    rw [prefixesNF, rrNodesNF]
    cases CBivariate.xAdicOrder? q with
    | none => simp
    | some s =>
      dsimp only
      split
      · rw [← Array.foldl_toList, foldl_append_size, Array.size_empty, Nat.zero_add]
        exact (list_sum_map_le fun a _ ↦ ih _ _ _ _).trans (Nat.le_add_left _ _)
      · simp

theorem prefixesNodes_pos (fr : GuruswamiSudan.FieldRootContext K) (fuel : ℕ) (q : CBivariate K)
    (M : ℕ) : 1 ≤ rrNodesNF fr fuel q M := by
  cases fuel with
  | zero => simp [rrNodesNF]
  | succ fuel =>
    rw [rrNodesNF]
    cases CBivariate.xAdicOrder? q with
    | none => simp
    | some s => dsimp only; split <;> omega

/-- The roots at a node: at most the initial coefficient polynomial's length. -/
theorem prefixesRoots_size_le (p : CPolynomial K) :
    (GuruswamiSudan.rootsInFieldForNonzeroEquation fieldRootCtxFast p).size ≤ p.val.size - 1 := by
  unfold GuruswamiSudan.rootsInFieldForNonzeroEquation
  split
  · simp
  · exact (rootsInFieldFast_size_le p).trans (natDegree_le_size_sub_one p)

theorem prefixesInnerLe_of_xLenLe {Q : CBivariate K} {X : ℕ} (h : XLenLe Q X) : InnerLe Q.val X :=
  fun c hc ↦ by
    obtain ⟨y, hy, rfl⟩ := Array.getElem_of_mem hc
    have := h.val_size_le y
    have hc' : Q.val.coeff y = Q.val[y] := by
      rw [CPolynomial.Raw.coeff, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hy]
      rfl
    rwa [hc'] at this

/-! ## The fold -/

/-- **`List.foldl`, the closure's price depending on the element, the accumulator's size bounded
along the fold**: an accumulator of size `sz acc` grows by at most `g b` at `b`, the sizes
summing to at most `S`. -/
theorem prefixesFoldl_le {α β : Type} [Enc α] [Enc β] (hP : Includes P listFoldl.costDeps)
    (f : α → β → α) (fVal : Val) (hf : ∀ a b, RunsApp P fVal [enc a, enc b] (enc (f a b)))
    (sz : α → ℕ) (g B : β → ℕ) (S : ℕ)
    (hstep : ∀ acc b, sz acc + g b ≤ S →
      sz (f acc b) ≤ sz acc + g b ∧ appCost P fVal [enc acc, enc b] ≤ B b) :
    ∀ (l : List β) (init : α), sz init + (l.map g).sum ≤ S →
      machineCost P listFoldl.costIdx [fVal, enc init, enc l] ≤
        (l.map fun b ↦ B b + 9).sum + 3 := by
  intro l
  induction l with
  | nil => intro init _; rw [listFoldl.costEq_nil P hP f fVal hf]; simp
  | cons b l ih =>
    intro init hS
    rw [listFoldl.costEq_cons P hP f fVal hf]
    simp only [List.map_cons, List.sum_cons] at hS ⊢
    obtain ⟨h1, h2⟩ := hstep init b (by omega)
    have := ih (f init b) (by omega)
    omega

theorem prefixesNodes_some {fr : GuruswamiSudan.FieldRootContext K} {fuel : ℕ} {q : CBivariate K}
    {M s : ℕ} (hs : CBivariate.xAdicOrder? q = some s) (hsM : s < M) :
    rrNodesNF fr (fuel + 1) q M = 1 + ((GuruswamiSudan.rootsInFieldForNonzeroEquation fr
        (initialCoeffFast (divXPowerFast q s))).toList.map fun a ↦
      rrNodesNF fr fuel (CBivariate.truncateX (substituteFast (divXPowerFast q s) a) (M - s))
        (M - s)).sum := by
  rw [rrNodesNF, hs]
  simp [hsM]

theorem prefixesSum_map_add_mul {α : Type} (l : List α) (c G : ℕ) (f : α → ℕ) :
    (l.map fun a ↦ c + G * f a).sum = l.length * c + G * (l.map f).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; ring

/-! ## The recursion -/

/-- `rrChildPrice` but the fold's `9` per element. -/
@[expose] def rrChildCore (X Y k : ℕ) : ℕ :=
  substBound X Y + (27 * (X + Y) + 80) * Y + 222 * k + 391

/-- **Roth–Ruckenstein's recursion** (`prefixesNF.c188`, on `fieldRootCtxFast`), on a node of at
most `Y` rows of at most `M ≤ X` coefficients, its prefix of at most `depth` coefficients,
`depth + fuel ≤ k`: with the child price `rrChildPrice X Y k` (paid by the parent), at most
`rrNodePrice X Y + rrChildPrice X Y k + Y·fuel` per node. -/
theorem prefixesNFC_cost_nodes (hP : Includes P prefixesNF.c188.costDeps) {X Y k : ℕ}
    (hX : X < 2 ^ 56) (hY : Y < 2 ^ 28) (hY2 : 2 ≤ Y) (hk : k < 2 ^ 56) (fuel : ℕ) :
    ∀ (q : CBivariate K) (M depth : ℕ) (pref : CPolynomial K),
      YLenLe q Y → XLenLe q M → M ≤ X → pref.val.size ≤ depth → depth + fuel ≤ k →
      machineCost P prefixesNF.c188.costIdx [enc fuel, enc q, enc M, enc depth, enc pref] +
          rrChildPrice X Y k ≤
        (rrNodePrice X Y + rrChildPrice X Y k + Y * fuel) *
          rrNodesNF fieldRootCtxFast fuel q M := by
  induction fuel with
  | zero =>
    intro q M depth pref _ _ _ _ _
    rw [prefixesNF.c188.costEq_zero P hP]
    simp only [rrNodesNF, Nat.mul_zero, Nat.add_zero, Nat.mul_one]
    unfold rrNodePrice
    omega
  | succ fuel ih =>
    intro q M depth pref hqY hqX hMX hpref hdk
    rw [prefixesNF.c188.costEq_succ P hP]
    have hqs := hqY.val_size_le
    have hqi := prefixesInnerLe_of_xLenLe (hqX.mono hMX)
    have hxa := xAdicOrderBC_cost P (by includes) q (X := X) (by omega) hqi (by omega)
    have h1 : (38 * X + 72) * q.val.size ≤ (38 * X + 72) * Y := Nat.mul_le_mul_left _ hqs
    have hfuel : fuel + 1 < 2 ^ 64 := by omega
    rw [limbs_of_lt hfuel]
    have hNP : (65 * X + 220) * Y = (38 * X + 72) * Y + (27 * X + 81) * Y + 67 * Y := by ring
    cases hs : CBivariate.xAdicOrder? q with
    | none =>
      rw [rrNodesNF, hs]
      dsimp only
      have := Nat.le_mul_of_pos_right (rrNodePrice X Y + rrChildPrice X Y k + Y * (fuel + 1))
        (show 0 < 1 by omega)
      unfold rrNodePrice at *
      omega
    | some s =>
      dsimp only
      by_cases hsM : s < M
      · simp only [hsM, ↓reduceIte]
        rw [prefixesNodes_some hs hsM]
        rw [limbs_of_lt (show s < 2 ^ 64 by omega), limbs_of_lt (show M < 2 ^ 64 by omega)]
        set Qn := divXPowerFast q s with hQn
        have hQnY : YLenLe Qn Y := hqY.divXPowerFast s
        have hQnX : XLenLe Qn M := by rw [hQn, divXPowerFast_eq]; exact hqX.divXPower s
        have hQns := hQnY.val_size_le
        have hQni := prefixesInnerLe_of_xLenLe (hQnX.mono hMX)
        have hdv := divXPowerFastC_cost P (by includes) q s (X := X) (by omega) hqi (by omega)
        have h2 : (27 * X + 81) * q.val.size ≤ (27 * X + 81) * Y := Nat.mul_le_mul_left _ hqs
        have hic := initialCoeffFastC_cost P (by includes) Qn (by omega)
        have hics := initialCoeffFast_size_le Qn
        have hro := rootsNonzeroC_cost P (by includes) hY hY2 (initialCoeffFast Qn) (by omega)
        set roots := GuruswamiSudan.rootsInFieldForNonzeroEquation fieldRootCtxFast
          (initialCoeffFast Qn) with hroots
        have hr : roots.size ≤ Y := (prefixesRoots_size_le _).trans (by omega)
        -- the children
        set S := (roots.toList.map fun a ↦ rrNodesNF fieldRootCtxFast fuel
          (CBivariate.truncateX (substituteFast Qn a) (M - s)) (M - s)).sum with hS
        set G := rrNodePrice X Y + rrChildPrice X Y k + Y * fuel with hG
        have hT : ∀ a, machineCost P prefixesNF.c188.costIdx
            [enc fuel, enc (CBivariate.truncateX (substituteFast Qn a) (M - s)), enc (M - s),
              enc (depth + 1), enc (GuruswamiSudan.extendPrefix pref depth a)] +
              rrChildPrice X Y k ≤
            G * rrNodesNF fieldRootCtxFast fuel
              (CBivariate.truncateX (substituteFast Qn a) (M - s)) (M - s) :=
          fun a ↦ ih _ (M - s) (depth + 1) _ ((hQnY.substituteFast a).truncateX _)
            (XLenLe.truncateX _ _) (by omega)
            (by have := extendPrefix_size_le pref depth a; omega) (by omega)
        have hf := fun out a ↦ RunsApp.of_spec
          (us := [enc s, enc fuel, enc M, enc depth, enc pref, enc Qn]) (vs := [enc out, enc a])
          (prefixesNF.c188.lam0.costSpec P (by includes) s fuel M depth pref Qn out a)
        have h202 : prefixesNF.c188.lam0.costIdx = 202 := rfl
        have hfold := prefixesFoldl_le P (by includes) _
          (.fn prefixesNF.c188.lam0.costIdx [enc s, enc fuel, enc M, enc depth, enc pref, enc Qn])
          hf Array.size (fun a ↦ rrNodesNF fieldRootCtxFast fuel
            (CBivariate.truncateX (substituteFast Qn a) (M - s)) (M - s))
          (fun a ↦ rrChildCore X Y k + S + machineCost P prefixesNF.c188.costIdx
            [enc fuel, enc (CBivariate.truncateX (substituteFast Qn a) (M - s)), enc (M - s),
              enc (depth + 1), enc (GuruswamiSudan.extendPrefix pref depth a)]) S
          (fun out a hout ↦ by
            have hres := prefixesNF_size_le_nodes fieldRootCtxFast fuel
              (CBivariate.truncateX (substituteFast Qn a) (M - s)) (M - s)
              (depth + 1) (GuruswamiSudan.extendPrefix pref depth a)
            refine ⟨by simp only [Array.size_append]; exact Nat.add_le_add_left hres _, ?_⟩
            simp only [appCost_fn, List.cons_append, List.nil_append]
            rw [prefixesNF.c188.lam0.costEq P (by includes)]
            have hsb := substituteFastC_cost P (by includes) Qn a (X := X) (Y := Y) (by omega)
              (by omega) hQni hQns
            obtain ⟨hss, hsi⟩ := substituteFast_sizes hQni a
            have htr := truncateXC_cost P (by includes) (substituteFast Qn a) (M - s)
              (X := X + Y) (by omega) (hsi.mono (by omega)) (by omega)
            have h3 : (27 * (X + Y) + 80) * (substituteFast Qn a).val.size ≤
                (27 * (X + Y) + 80) * Y := Nat.mul_le_mul_left _ (by omega)
            have hep := extendPrefixC_cost P (by includes) pref depth a (by omega) (by omega)
            rw [limbs_of_lt (show M < 2 ^ 64 by omega), limbs_of_lt (show s < 2 ^ 64 by omega),
              limbs_of_lt (show depth < 2 ^ 64 by omega)]
            simp only [Nat.max_self]
            unfold rrChildCore
            omega)
          roots.toList #[] (by simp [hS])
        rw [h202] at hfold
        -- the sum over the children
        have hsum : (roots.toList.map fun a ↦ rrChildCore X Y k + S +
            machineCost P prefixesNF.c188.costIdx
              [enc fuel, enc (CBivariate.truncateX (substituteFast Qn a) (M - s)), enc (M - s),
                enc (depth + 1), enc (GuruswamiSudan.extendPrefix pref depth a)] + 9).sum ≤
            roots.size * S + G * S := by
          have := list_sum_map_le (l := roots.toList)
            (f := fun a ↦ rrChildCore X Y k + S +
              machineCost P prefixesNF.c188.costIdx
                [enc fuel, enc (CBivariate.truncateX (substituteFast Qn a) (M - s)), enc (M - s),
                  enc (depth + 1), enc (GuruswamiSudan.extendPrefix pref depth a)] + 9)
            (g := fun a ↦ S + G * rrNodesNF fieldRootCtxFast fuel
              (CBivariate.truncateX (substituteFast Qn a) (M - s)) (M - s)) fun a _ ↦ by
              have := hT a
              unfold rrChildPrice at this
              unfold rrChildCore
              omega
          refine this.trans (le_of_eq ?_)
          rw [prefixesSum_map_add_mul, Array.length_toList]
        have hrS : roots.size * S ≤ Y * S := Nat.mul_le_mul_right _ hr
        have e : (rrNodePrice X Y + rrChildPrice X Y k + Y * (fuel + 1)) * (1 + S) =
            G + Y + G * S + Y * S := by rw [hG]; ring
        have hG' : G = (65 * X + 220) * Y + rootsBound Y + 200 + rrChildPrice X Y k + Y * fuel := by
          rw [hG, rrNodePrice]
        rw [e]
        omega
      · -- the order is below the rows' length `M`
        obtain ⟨y, -, hy⟩ := GuruswamiSudan.cbivar_xAdicOrder?_some_exists hs
        exact absurd (hqX s y (by omega)) hy

/-! ## On the interpolated polynomial -/

open CompPoly.GuruswamiSudan in
/-- **Roth–Ruckenstein's search on the interpolated polynomial** (`prefixesNF.c188`, the call
`gsRunDistinctNF` makes): at most `rrBound (W + 1) (ℓ + 2) k ℓ`, at most `1 + k·ℓ` nodes
(`gsRunNF_nodes_le`) of at most `ℓ + 1` rows of at most `W + 1` coefficients. -/
theorem prefixesNFC_cost (hP : Includes P prefixesNF.c188.costDeps) {points : Array (K × K)}
    {params : GSInterpParams} {Q : CBivariate K} (hQ : ValidInterpolationWitness points params Q)
    (hk1 : 1 < params.messageDegree) (hX : params.weightedDegreeBound + 1 < 2 ^ 56)
    (hY : interpolationYCap params + 2 < 2 ^ 28) (hk : params.messageDegree < 2 ^ 56) :
    machineCost P prefixesNF.c188.costIdx
        [enc params.messageDegree, enc (CBivariate.truncateX Q (params.weightedDegreeBound + 1)),
          enc (params.weightedDegreeBound + 1), enc 0, enc (default : CPolynomial K)] ≤
      rrBound (params.weightedDegreeBound + 1) (interpolationYCap params + 2)
        params.messageDegree (interpolationYCap params) := by
  have hl := lenLe_of_validInterpolation hQ hk1
  have h := prefixesNFC_cost_nodes P hP (X := params.weightedDegreeBound + 1)
    (Y := interpolationYCap params + 2) (k := params.messageDegree) hX hY (by omega) hk
    params.messageDegree (CBivariate.truncateX Q (params.weightedDegreeBound + 1))
    (params.weightedDegreeBound + 1) 0 default ((hl.1.truncateX _).mono (by omega))
    (XLenLe.truncateX _ _) le_rfl (by show (default : CPolynomial K).val.size ≤ 0; rfl)
    (by omega)
  have hn := Nat.mul_le_mul_left (rrNodePrice (params.weightedDegreeBound + 1)
      (interpolationYCap params + 2) + rrChildPrice (params.weightedDegreeBound + 1)
      (interpolationYCap params + 2) params.messageDegree +
    (interpolationYCap params + 2) * params.messageDegree) (gsRunNF_nodes_le hQ hk1)
  unfold rrBound
  omega

open CompPoly.GuruswamiSudan in
/-- **One lane's Guruswami–Sudan run** (`gsRunDistinctNF`: the interpolation, Roth–Ruckenstein's
search, the candidates filtered): at most the interpolation's bound, the truncation, the
search (`rrBound`) and `max 1 ℓ` filter tests of `(272·k + 34)·n + 30` each: `gsRunBound`. -/
theorem gsRunDistinctNFC_cost (hP : Includes P gsRunDistinctNFC.costDeps)
    (points : Array (K × K)) (params : GSInterpParams) (radius : ℕ)
    (hs : InterpSizes points.size params) (hk1 : 1 < params.messageDegree)
    (hd : DistinctXCoordinates points) (hr : radius < 2 ^ 64)
    (hX : params.weightedDegreeBound + 1 < 2 ^ 56) (hY : interpolationYCap params + 2 < 2 ^ 28)
    (hk56 : params.messageDegree < 2 ^ 56) :
    machineCost P gsRunDistinctNFC.costIdx [enc points, enc params, enc radius] ≤
      gsRunBound points.size params := by
  have ⟨hn, hW, hk, hyW, hw, _⟩ := hs
  rw [gsRunDistinctNFC.costEq P hP]
  have hi := interpolateDistinctC_cost P (by includes) points params hs hk1
  generalize hQ : interpolateDistinct points params = oQ at hi
  cases oQ with
  | none => dsimp only; unfold gsRunBound; omega
  | some Q =>
    dsimp only
    have hsz := interpolateDistinct_sizes hd hQ hk1
    have hrr := prefixesNFC_cost P (by includes) (interpolateDistinct_valid hd hQ) hk1 hX hY hk56
    have hQi : InnerLe Q.val (params.weightedDegreeBound + 1) := fun c hc ↦ by
      obtain ⟨y, hy, rfl⟩ := Array.getElem_of_mem hc
      have := hsz.2 y
      have hc' : Q.val.coeff y = Q.val[y] := by
        rw [CPolynomial.Raw.coeff, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hy]
        rfl
      rw [hc'] at this
      exact this.trans (Nat.sub_le _ _)
    have := truncateXC_cost P (by includes) Q (params.weightedDegreeBound + 1) (by omega) hQi
      (by omega)
    have h1 : (27 * (params.weightedDegreeBound + 1) + 80) * Q.val.size ≤
        (27 * (params.weightedDegreeBound + 1) + 80) * (interpolationYCap params + 1) :=
      Nat.mul_le_mul_left _ hsz.1
    have hres := prefixesNF_size_le hd hQ hk1
    have hmem : ∀ p ∈ prefixesNF fieldRootCtxFast params.messageDegree
        (CBivariate.truncateX Q (params.weightedDegreeBound + 1)) (params.weightedDegreeBound + 1) 0
        default, p.val.size ≤ params.messageDegree := by
      have hv := interpolateDistinct_valid hd hQ
      rw [prefixesNF_eq_truncD hv, prefixesTruncD_eq,
        prefixesTrunc_eq fieldRootCtxFast _ Q _ (fun _ ↦ replayPath Q []) 0 default rfl]
      intro p hp
      have := prefixesWithFuelFast_mem_size_le fieldRootCtxFast _ _ 0 default
        (by show (default : CPolynomial K).val.size ≤ 0; rfl) p hp
      omega
    have hfv := fun p ↦ RunsApp.of_spec (us := [enc points, enc params, enc radius]) (vs := [enc p])
      (gsRunDistinctNFC.lam0.costSpec P (by includes) points params radius p)
    generalize hR : prefixesNF fieldRootCtxFast params.messageDegree
      (CBivariate.truncateX Q (params.weightedDegreeBound + 1)) (params.weightedDegreeBound + 1) 0
      default = res at hres hmem
    have hfil := filterC_cost P (by includes) _
      (.fn gsRunDistinctNFC.lam0.costIdx [enc points, enc params, enc radius]) hfv
      ((272 * params.messageDegree + 34) * points.size + 30) res.toList (fun p hp ↦ by
        have hps := hmem p (by simpa using hp)
        simp only [appCost_fn, List.cons_append, List.nil_append]
        rw [gsRunDistinctNFC.lam0.costEq P (by includes),
          Auto.CompPoly.GuruswamiSudan.degreeLtBool.c208.costEq P (by includes)]
        cost_simp
        split_ifs with hdeg
        · simp only [degreeLtBool, decide_eq_true_eq] at hdeg
          rw [passesDistanceFast.c209.costEq P (by includes)]
          have := mismatchCountC_cost P (by includes) points p (by omega)
          have := mismatchCountFast_le points p
          have := Nat.mul_le_mul_right points.size (show 272 * p.val.size + 34 ≤
            272 * params.messageDegree + 34 by omega)
          cost_simp
          omega
        · omega)
    have hfl := List.length_filter_le (fun p ↦ degreeLtBool p params.messageDegree &&
      passesDistanceFast points radius p) res.toList
    simp only [Array.length_toList] at hfil hfl
    have h2 : ((272 * params.messageDegree + 34) * points.size + 50) * res.size ≤
        ((272 * params.messageDegree + 34) * points.size + 50) * max 1 (interpolationYCap params) :=
      Nat.mul_le_mul_left _ hres
    have e2 : ((272 * params.messageDegree + 34) * points.size + 50) * res.size =
        ((272 * params.messageDegree + 34) * points.size + 30 + 13) * res.size + 7 * res.size := by
      ring
    unfold gsRunBound
    cost_simp
    omega

end

end LeanVM.Cost.Bounds.Decoder
