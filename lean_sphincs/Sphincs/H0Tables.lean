import Sphincs.H0Tensor

/-! **The codeword tables.** The codeword counts `pmf(m) = #{w : lut w = m}` by point increments,
their prefix sums `K(m) = #{w : lut w ≤ m} = 256 H(m)`, and the numerators
`F(u) = Σ_m K(m)^u Δ*K(m)` and `F2(u) = Σ_m K(m)^u Δ*(K^2)(m)`, so that `f(u) = F(u) / 256^(u+1)` and
`f2(u) = F2(u) / 256^(u+2)`. All numerators up to a bound are computed in one pass over the grid. -/

open ENNReal

namespace SphincsLayered.Security.H0


set_option linter.unusedSectionVars false
attribute [local irreducible] lut codewordCodes

/-! ### Linearity of the forward difference -/

theorem D1_const_mul (c : ℝ) (h : FPos → ℝ) (y : FPos) : D1 (fun y => c * h y) y = c * D1 h y := by
  unfold D1
  split_ifs <;> ring

theorem deltaF_const_mul (c : ℝ) : ∀ (d : ℕ) (g : (Fin d → FPos) → ℝ) (m : Fin d → FPos),
    deltaF d (fun m => c * g m) m = c * deltaF d g m
  | 0, _, _ => rfl
  | d + 1, g, m => by
      simp only [deltaF]
      have h : ∀ y : FPos, deltaF d (fun m' => c * g (Fin.cons y m')) (Fin.tail m) =
          c * deltaF d (fun m' => g (Fin.cons y m')) (Fin.tail m) := fun y => deltaF_const_mul c d _ _
      simp only [h]
      exact D1_const_mul c _ _

/-! ### The codeword counts -/

/-- The codeword counts. -/
def pmfT : NT childChains :=
  (List.finRange 256).foldl (fun t w => incT childChains t (lut w)) (zeroT childChains)

theorem getT_foldl_incT (L : List LutIdx) (t : NT childChains) (m : FChain → FPos) :
    getT childChains (L.foldl (fun t w => incT childChains t (lut w)) t) m =
      getT childChains t m + (L.filter fun w => decide (m = lut w)).length := by
  induction L generalizing t with
  | nil => simp
  | cons w L ih =>
      rw [List.foldl_cons, ih, getT_incT, List.filter_cons]
      by_cases h : m = lut w
      · simp [h]; ring
      · simp [h]

theorem getT_pmfT (m : FChain → FPos) :
    getT childChains pmfT m = (Finset.univ.filter fun w : LutIdx => lut w = m).card := by
  unfold pmfT
  rw [getT_foldl_incT, getT_zeroT, zero_add]
  congr 1
  rw [← List.toFinset_card_of_nodup ((List.nodup_finRange 256).filter _)]
  congr 1
  ext w
  simp [eq_comm]

/-- The CDF counts `K(m) = #{w : lut w ≤ m}`. -/
def KT : NT childChains := cumT childChains pmfT

theorem getT_KT (m : FChain → FPos) : (getT childChains KT m : ℝ) = 256 * Hm m := by
  unfold KT
  rw [getT_cumT]
  unfold cumF Hm avgR
  simp only [getT_pmfT, Int.cast_natCast, Fintype.card_fin]
  rw [← mul_assoc, show (256 : ℝ) * ((256 : ℕ) : ℝ)⁻¹ = 1 by norm_num, one_mul]
  -- both sides count the codewords below `m`
  have h : ∀ y : FChain → FPos, (if ∀ i, y i ≤ m i then
      ((Finset.univ.filter fun w : LutIdx => lut w = y).card : ℝ) else 0) =
      ∑ w : LutIdx, if lut w = y ∧ ∀ i, y i ≤ m i then (1 : ℝ) else 0 := by
    intro y
    split_ifs with hy
    · rw [Finset.card_filter]
      push_cast
      refine Finset.sum_congr rfl fun w _ => ?_
      simp [hy]
    · exact (Finset.sum_eq_zero fun w _ => ite_eq_right (fun h => hy h.2)).symm
  simp only [h]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Finset.sum_eq_single (lut w)]
  · have hiff : (lut w = lut w ∧ ∀ i, lut w i ≤ m i) ↔ ∀ i, (lut w i).val ≤ (m i).val :=
      ⟨fun h i => Fin.le_iff_val_le_val.1 (h.2 i), fun h => ⟨rfl, fun i => Fin.le_iff_val_le_val.2 (h i)⟩⟩
    by_cases hall : ∀ i, (lut w i).val ≤ (m i).val
    · rw [ite_eq_left (hiff.2 hall), ite_eq_left hall]
    · rw [ite_eq_right (fun h => hall (hiff.1 h)), ite_eq_right hall]
  · intro x _ hx
    rw [ite_eq_right]
    rintro ⟨h1, _⟩
    exact hx h1.symm
  · simp


/-! ### The numerators of `f` and `f2` -/

/-- Forward differences of the CDF counts. -/
def DK : NT childChains := deltaT childChains KT

/-- Forward differences of the squared CDF counts. -/
def DK2 : NT childChains := deltaT childChains (mapT childChains (fun k => k * k) KT)

/-- The numerators, for every `u ≤ U`, in one pass over the grid. -/
def sumTL : (d : ℕ) → (ℤ → ℤ → List ℤ) → NT d → NT d → List ℤ
  | 0, f, a, b => f (show ℤ from a) (show ℤ from b)
  | d + 1, f, a, b =>
      let a' := (show Five (NT d) from a)
      let b' := (show Five (NT d) from b)
      List.zipWith (· + ·) (List.zipWith (· + ·) (List.zipWith (· + ·) (List.zipWith (· + ·)
        (sumTL d f a'.c0 b'.c0) (sumTL d f a'.c1 b'.c1)) (sumTL d f a'.c2 b'.c2)) (sumTL d f a'.c3 b'.c3))
        (sumTL d f a'.c4 b'.c4)

/-- The powers `k^u dk` for `u ≤ U`. -/
def powsL (U : ℕ) (k dk : ℤ) : List ℤ := (List.range (U + 1)).map fun u => k ^ u * dk

theorem length_sumTL (U : ℕ) : ∀ (d : ℕ) (a b : NT d), (sumTL d (powsL U) a b).length = U + 1
  | 0, _, _ => by simp [sumTL, powsL]
  | d + 1, a, b => by
      simp only [sumTL, List.length_zipWith, length_sumTL U d]
      simp

theorem getD_zipWith_add (l l' : List ℤ) (hl : l.length = l'.length) (u : ℕ) :
    (List.zipWith (· + ·) l l').getD u 0 = l.getD u 0 + l'.getD u 0 := by
  rcases lt_or_ge u l.length with h | h
  · rw [List.getD_eq_getElem _ _ (by simp [List.length_zipWith]; omega), List.getD_eq_getElem _ _ h,
      List.getD_eq_getElem _ _ (by omega), List.getElem_zipWith]
  · rw [List.getD_eq_default _ _ (by simp [List.length_zipWith]; omega), List.getD_eq_default _ _ h,
      List.getD_eq_default _ _ (by omega)]
    ring

theorem getD_sumTL (U u : ℕ) (hu : u ≤ U) : ∀ (d : ℕ) (a b : NT d),
    (sumTL d (powsL U) a b).getD u 0 = sumT2 d (fun k dk => k ^ u * dk) a b
  | 0, a, b => by
      simp only [sumTL, sumT2, powsL]
      rw [List.getD_eq_getElem _ _ (by simp; omega)]
      simp
  | d + 1, a, b => by
      simp only [sumTL, sumT2]
      rw [getD_zipWith_add _ _ (by simp [List.length_zipWith, length_sumTL]),
        getD_zipWith_add _ _ (by simp [List.length_zipWith, length_sumTL]),
        getD_zipWith_add _ _ (by simp [List.length_zipWith, length_sumTL]),
        getD_zipWith_add _ _ (by simp [length_sumTL])]
      simp only [getD_sumTL U u hu d]

/-! ### The numerators grouped by count

`sumTL d (powsL U) a b` lists, for each `u ≤ U`, the sum of `a(m)^u b(m)` over the `5^d` grid points.
The values `a(m)` (the counts `K(m) ≤ 256`) are few and `b(m)` vanishes at most points, so the
kernel first sums the `b(m)` in buckets indexed by `a(m)` (`groupT`, into a binary trie `BT` on
the bits of `a(m)`), then takes the powers bucket by bucket (`sumPowsL`): `sumTL_powsL_eq_group`.
Raising every grid point to every power instead costs the kernel many times the memory. -/

/-- Integer buckets: a binary trie, read to a depth `n` (`BT.toList`) as the buckets `k < 2^n`,
low bit first. A leaf read deeper is its children `leaf 0`, and a node read as a bucket is `0`. -/
inductive BT where
  | leaf : ℤ → BT
  | node : BT → BT → BT

/-- The bucket of a leaf. -/
def BT.val : BT → ℤ
  | .leaf c => c
  | .node _ _ => 0

/-- The buckets of the low bit `0`. -/
def BT.left : BT → BT
  | .leaf _ => .leaf 0
  | .node l _ => l

/-- The buckets of the low bit `1`. -/
def BT.right : BT → BT
  | .leaf _ => .leaf 0
  | .node _ r => r

theorem BT.left_node (l r : BT) : (BT.node l r).left = l := rfl

theorem BT.right_node (l r : BT) : (BT.node l r).right = r := rfl

/-- Adds `c` to bucket `k`, at depth `n`. -/
def BT.add : ℕ → ℕ → ℤ → BT → BT
  | 0, _, c, t => .leaf (t.val + c)
  | n + 1, k, c, t =>
      if k % 2 = 0 then .node (BT.add n (k / 2) c t.left) t.right
      else .node t.left (BT.add n (k / 2) c t.right)

/-- The nonzero buckets at depth `n` as pairs `(off + st k, c)`, before `acc`. -/
def BT.toList : ℕ → ℕ → ℕ → BT → List (ℤ × ℤ) → List (ℤ × ℤ)
  | 0, off, _, t, acc => if t.val = 0 then acc else ((off : ℤ), t.val) :: acc
  | n + 1, off, st, t, acc => BT.toList n off (2 * st) t.left (BT.toList n (off + st) (2 * st) t.right acc)

/-- The pairs `(a(m), b(m))` with `b(m) ≠ 0`, summed by `a(m)`: into the buckets when
`0 ≤ a(m) < 512`, onto the list otherwise. -/
def groupT : (d : ℕ) → NT d → NT d → BT × List (ℤ × ℤ) → BT × List (ℤ × ℤ)
  | 0, a, b, acc =>
      if (show ℤ from b) = 0 then acc
      else if 0 ≤ (show ℤ from a) ∧ (show ℤ from a) < 512 then
        (BT.add 9 (show ℤ from a).toNat (show ℤ from b) acc.1, acc.2)
      else (acc.1, ((show ℤ from a), (show ℤ from b)) :: acc.2)
  | d + 1, a, b, acc =>
      let a' := (show Five (NT d) from a)
      let b' := (show Five (NT d) from b)
      groupT d a'.c0 b'.c0 (groupT d a'.c1 b'.c1 (groupT d a'.c2 b'.c2 (groupT d a'.c3 b'.c3
        (groupT d a'.c4 b'.c4 acc))))

/-- The grouped pairs of two tensors. -/
def groupList (d : ℕ) (a b : NT d) : List (ℤ × ℤ) :=
  let G := groupT d a b (.leaf 0, [])
  BT.toList 9 0 1 G.1 G.2

/-- `[c, k c, k^2 c, …]`, `U + 1` terms. -/
def powList (k : ℤ) : ℕ → ℤ → List ℤ
  | 0, c => [c]
  | U + 1, c => c :: powList k U (k * c)

/-- The sums `Σ k^u c` over the pairs `(k, c)`, for every `u ≤ U`. -/
def sumPowsL (U : ℕ) (L : List (ℤ × ℤ)) : List ℤ :=
  L.foldr (fun p acc => List.zipWith (· + ·) (powList p.1 U p.2) acc) (List.replicate (U + 1) 0)

/-- `Σ k^u c` over a list of pairs. -/
def wsumL (u : ℕ) (L : List (ℤ × ℤ)) : ℤ := (L.map fun p => p.1 ^ u * p.2).sum

theorem wsumL_cons (u : ℕ) (p : ℤ × ℤ) (L : List (ℤ × ℤ)) : wsumL u (p :: L) = p.1 ^ u * p.2 + wsumL u L := by
  simp [wsumL]

theorem wsumL_nil (u : ℕ) : wsumL u [] = 0 := rfl

theorem wsumL_toList_acc (u : ℕ) : ∀ (n off st : ℕ) (t : BT) (acc : List (ℤ × ℤ)),
    wsumL u (BT.toList n off st t acc) = wsumL u (BT.toList n off st t []) + wsumL u acc
  | 0, off, st, t, acc => by
      simp only [BT.toList]
      split_ifs <;> simp [wsumL_cons, wsumL_nil]
  | n + 1, off, st, t, acc => by
      simp only [BT.toList]
      rw [wsumL_toList_acc u n off (2 * st) _ (BT.toList n (off + st) (2 * st) _ acc),
        wsumL_toList_acc u n (off + st) (2 * st) _ acc,
        wsumL_toList_acc u n off (2 * st) _ (BT.toList n (off + st) (2 * st) _ [])]
      ring

theorem wsumL_toList_zero (u : ℕ) (off st : ℕ) (t : BT) :
    wsumL u (BT.toList 0 off st t []) = (off : ℤ) ^ u * t.val := by
  simp only [BT.toList]
  split_ifs with h <;> simp [wsumL_cons, wsumL_nil, h]

theorem wsumL_toList_add (u : ℕ) : ∀ (n off st k : ℕ) (c : ℤ) (t : BT), k < 2 ^ n →
    wsumL u (BT.toList n off st (BT.add n k c t) []) =
      ((off + st * k : ℕ) : ℤ) ^ u * c + wsumL u (BT.toList n off st t [])
  | 0, off, st, k, c, t, hk => by
      have : k = 0 := by simpa using hk
      subst this
      rw [wsumL_toList_zero, wsumL_toList_zero]
      simp only [BT.add, BT.val, Nat.mul_zero, Nat.add_zero]
      ring
  | n + 1, off, st, k, c, t, hk => by
      have hk2 : k / 2 < 2 ^ n := by rw [pow_succ] at hk; omega
      simp only [BT.add, BT.toList]
      split_ifs with h
      · simp only [BT.left_node, BT.right_node]
        rw [wsumL_toList_acc u n off (2 * st) _ (BT.toList n (off + st) (2 * st) _ []),
          wsumL_toList_add u n off (2 * st) (k / 2) c _ hk2,
          wsumL_toList_acc u n off (2 * st) t.left (BT.toList n (off + st) (2 * st) _ [])]
        have : off + 2 * st * (k / 2) = off + st * k := by
          have := Nat.div_add_mod k 2
          rw [h, Nat.add_zero] at this
          conv_rhs => rw [← this]
          ring
        rw [this]
        ring
      · simp only [BT.left_node, BT.right_node]
        rw [wsumL_toList_acc u n off (2 * st) _ (BT.toList n (off + st) (2 * st) _ []),
          wsumL_toList_add u n (off + st) (2 * st) (k / 2) c _ hk2,
          wsumL_toList_acc u n off (2 * st) t.left (BT.toList n (off + st) (2 * st) t.right [])]
        have : off + st + 2 * st * (k / 2) = off + st * k := by
          have := Nat.div_add_mod k 2
          rw [show k % 2 = 1 by omega] at this
          conv_rhs => rw [← this]
          ring
        rw [this]
        ring

theorem wsumL_toList_leaf0 (u : ℕ) : ∀ (n off st : ℕ), wsumL u (BT.toList n off st (.leaf 0) []) = 0
  | 0, off, st => by rw [wsumL_toList_zero]; simp [BT.val]
  | n + 1, off, st => by
      simp only [BT.toList, show (BT.leaf 0).left = .leaf 0 from rfl, show (BT.leaf 0).right = .leaf 0 from rfl]
      rw [wsumL_toList_acc, wsumL_toList_leaf0 u n, wsumL_toList_leaf0 u n, zero_add]

/-- The value of a grouping at the power `u`. -/
def groupVal (u : ℕ) (G : BT × List (ℤ × ℤ)) : ℤ := wsumL u (BT.toList 9 0 1 G.1 G.2)

theorem groupVal_groupT (u : ℕ) : ∀ (d : ℕ) (a b : NT d) (G : BT × List (ℤ × ℤ)),
    groupVal u (groupT d a b G) = sumT2 d (fun k dk => k ^ u * dk) a b + groupVal u G
  | 0, a, b, G => by
      change ℤ at a b
      simp only [groupT, sumT2, groupVal]
      split_ifs with hb ha
      · simp [hb]
      · dsimp only
        rw [wsumL_toList_acc, wsumL_toList_add u 9 0 1 _ _ _ (by omega), wsumL_toList_acc u 9 0 1 G.1 G.2]
        have : (((0 + 1 * a.toNat : ℕ) : ℤ)) = a := by
          simp only [Nat.zero_add, Nat.one_mul]; exact Int.toNat_of_nonneg ha.1
        rw [this]
        ring
      · dsimp only
        rw [wsumL_toList_acc, wsumL_cons, wsumL_toList_acc u 9 0 1 G.1 G.2]
        ring
  | d + 1, a, b, G => by
      simp only [groupT, sumT2]
      rw [groupVal_groupT u d, groupVal_groupT u d, groupVal_groupT u d, groupVal_groupT u d,
        groupVal_groupT u d]
      ring

theorem powList_eq (k : ℤ) : ∀ (U : ℕ) (c : ℤ), powList k U c = (List.range (U + 1)).map fun u => k ^ u * c
  | 0, c => by simp [powList]
  | U + 1, c => by
      rw [powList, powList_eq k U (k * c)]
      conv_rhs => rw [List.range_succ_eq_map]
      rw [List.map_cons, List.map_map]
      simp only [pow_zero, one_mul, List.cons.injEq, true_and]
      refine List.map_congr_left fun u _ => ?_
      simp only [Function.comp, pow_succ]
      ring

theorem sumPowsL_eq (U : ℕ) : ∀ L : List (ℤ × ℤ), sumPowsL U L = (List.range (U + 1)).map fun u => wsumL u L
  | [] => by
      simp only [sumPowsL, List.foldr_nil, wsumL_nil]
      rw [List.map_const', List.length_range]
  | p :: L => by
      have := sumPowsL_eq U L
      simp only [sumPowsL, List.foldr_cons] at this ⊢
      rw [this, powList_eq, List.zipWith_map, List.zipWith_self]
      refine List.map_congr_left fun u _ => ?_
      rw [wsumL_cons]

/-- **The grid sums from the grouped pairs.** -/
theorem sumTL_powsL_eq_group (U d : ℕ) (a b : NT d) :
    sumTL d (powsL U) a b = sumPowsL U (groupList d a b) := by
  rw [sumPowsL_eq]
  apply List.ext_getElem (by rw [length_sumTL]; simp)
  intro u h1 h2
  have hu : u ≤ U := by rw [length_sumTL] at h1; omega
  rw [← List.getD_eq_getElem _ 0 h1, getD_sumTL U u hu, List.getElem_map, List.getElem_range]
  have := groupVal_groupT u d a b (.leaf 0, [])
  simp only [groupVal, wsumL_toList_leaf0, add_zero] at this
  exact this.symm

/-- The numerator of `f(u)`. -/
def fNum (u : ℕ) : ℤ := sumT2 childChains (fun k dk => k ^ u * dk) KT DK

/-- The numerator of `f2(u)`. -/
def f2Num (u : ℕ) : ℤ := sumT2 childChains (fun k dk => k ^ u * dk) KT DK2

theorem fR_num (u : ℕ) : fR u = (fNum u : ℝ) / 256 ^ (u + 1) := by
  rw [fR_grid]
  have hH : Hm = fun m => (1 / 256 : ℝ) * (getT childChains KT m : ℝ) := funext fun m => by rw [getT_KT]; ring
  have hD : ∀ m, deltaF childChains Hm m = (1 / 256 : ℝ) * (getT childChains DK m : ℝ) := by
    intro m
    rw [hH, deltaF_const_mul, DK, getT_deltaT]
  simp only [hD]
  unfold fNum
  rw [sumT2_eq, Finset.sum_div]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [hH]
  simp only []
  rw [mul_pow, div_pow, one_pow]
  push_cast
  field_simp
  ring

theorem f2R_num (u : ℕ) : f2R u = (f2Num u : ℝ) / 256 ^ (u + 2) := by
  rw [f2R_grid]
  have hH : Hm = fun m => (1 / 256 : ℝ) * (getT childChains KT m : ℝ) := funext fun m => by rw [getT_KT]; ring
  have hD : ∀ m, deltaF childChains (fun m => Hm m ^ 2) m = (1 / 65536 : ℝ) * (getT childChains DK2 m : ℝ) := by
    intro m
    have hsq : (fun m => Hm m ^ 2) = fun m => (1 / 65536 : ℝ) *
        (getT childChains (mapT childChains (fun k => k * k) KT) m : ℝ) := funext fun m => by
      rw [getT_mapT, hH]
      push_cast
      ring
    rw [hsq, deltaF_const_mul, DK2, getT_deltaT]
  simp only [hD]
  unfold f2Num
  rw [sumT2_eq, Finset.sum_div]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [hH]
  simp only []
  rw [mul_pow, div_pow, one_pow]
  push_cast
  field_simp
  ring
end SphincsLayered.Security.H0
