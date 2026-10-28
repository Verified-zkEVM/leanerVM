module

public import LeanDa.Membership

/-!
# The deployed dual codeword is the dual codeword

Proposition prop:ntt of `doc/leanvm/body/d-novel-basis.tex` for the crate's membership vector:
the additive NTT of `dualCodeword` (`verifier/src/da.rs:24-85`) computes `dual`
(`dualCodeword_eq_dual`), so the membership vector of a root is the dual codeword of its
challenges (`membershipVector_eq_dual`).

* **The twiddles.** `subspaceRow i` tabulates `W_i`, the subspace polynomial of the span of
  `e_0 … e_(i-1)`, on `e_i … e_14` by `W_(i+1)(x) = W_i(x) (W_i(x) + W_i(e_i))`
  (`subspaceRow_eq`), so `subspaceEvaluations i` tabulates `Ŵ_i` (`subspaceEvaluations_eq`). `Ŵ_i`
  is additive, so the twiddle of block `b` is `Ŵ_i` at the block's first point
  (`twiddle_eq`).
* **The novel basis.** `novelEval n m x` is the value at `x` of the polynomial with coefficients
  `m` on `X_0 … X_(2^n - 1)`, split on the top bit: `X_(2^(n-1) + k) = Ŵ_(n-1) X_k`. The tensor
  `⊗_j (1, z_j)` takes the value `∏_j (1 + z_j Ŵ_j(x))` (`novelEval_tensor`).
* **The NTT** (Lin-Chung-Han). Entering layer `14 - s`, block `b` of `2^(s+1)` entries holds the
  coefficients of a polynomial agreeing with the message's on the block's points, the coset
  `point (b · 2^(s+1)) + span(e_0 … e_s)` (`Stage`). On the block `Ŵ_s` is `t` on the first half and
  `t + 1` on the second, `t` the twiddle, so a butterfly splits the block into two such blocks
  (`stage_encodeLayer`). After the last layer the blocks are the values (`encode_eq_novelEval`).

This module is part of the instantiation of Benedikt Wagner's framework for erasure code
commitments (`PqDas`, ported from https://github.com/b-wagn/fv-pq-da) with LeanDA.
-/

open Polynomial

namespace LeanDa

@[expose] public section

/-! ## The normalized subspace polynomials -/

/-- `Ŵ_s` as a function on `K`, indexed by a natural number: `normW s` for `s < 14`
(`normW_eval`). -/
noncomputable def wHat (s : ℕ) (x : K) : K :=
  (AdditiveNTT.normalizedW (ZMod 2) basis (Fin.ofNat 16 s)).eval x

/-- `W_s` as a function on `K`. -/
noncomputable def wSub (s : ℕ) (x : K) : K :=
  (AdditiveNTT.W (ZMod 2) basis (Fin.ofNat 16 s)).eval x

/-- `e_c = point (2^c)`. -/
theorem basis_ofNat {c : ℕ} (hc : c < 16) : basis (Fin.ofNat 16 c) = point (2 ^ c) := by
  simp [basis, point, Nat.mod_eq_of_lt hc]

/-- `normW j` is `Ŵ_j`. -/
theorem normW_eval (j : Fin 14) (x : K) : (normW j).eval x = wHat j x := by
  have h : Fin.castLE (by omega) j = Fin.ofNat 16 j :=
    Fin.ext (by simp [Nat.mod_eq_of_lt (by omega : (j : ℕ) < 16)])
  rw [normW, wHat, h]

/-- `Ŵ_s` as an additive map. -/
noncomputable def wHatHom (s : ℕ) : K →+ K :=
  ((AdditiveNTT.normalizedW_is_additive (ZMod 2) basis (Fin.ofNat 16 s)).mk' _).toAddMonoidHom

/-- `wHatHom s` is `Ŵ_s`. -/
theorem wHatHom_apply (s : ℕ) (x : K) : wHatHom s x = wHat s x := rfl

/-- `Ŵ_s` is additive. -/
theorem wHat_add (s : ℕ) (x y : K) : wHat s (x + y) = wHat s x + wHat s y :=
  map_add (wHatHom s) x y

/-- `Ŵ_s(0) = 0`. -/
theorem wHat_zero (s : ℕ) : wHat s 0 = 0 := map_zero (wHatHom s)

/-- The point of index `0` is `0`. -/
theorem point_zero : point 0 = 0 := ofBits_zero

/-- `Ŵ_s(x) = W_s(x) / W_s(e_s)`. -/
theorem wHat_eq (s : ℕ) (hs : s < 16) (x : K) :
    wHat s x = wSub s x * (wSub s (point (2 ^ s)))⁻¹ := by
  rw [wHat, AdditiveNTT.normalizedW, eval_mul, eval_C, wSub, wSub, basis_ofNat hs, one_div,
    mul_comm]

/-- `Ŵ_s` vanishes at `e_k` for `k < s`. -/
theorem wHat_two_pow_of_lt {s k : ℕ} (hs : s < 16) (hk : k < s) : wHat s (point (2 ^ k)) = 0 :=
  AdditiveNTT.normalizedWᵢ_vanishing (ZMod 2) basis _ _
    (AdditiveNTT.β_lt_mem_U (ZMod 2) basis (Fin.ofNat 16 s)
      ⟨k, by simp [Nat.mod_eq_of_lt hs, hk]⟩)

/-- `Ŵ_s(e_s) = 1`. -/
theorem wHat_two_pow_self {s : ℕ} (hs : s < 16) : wHat s (point (2 ^ s)) = 1 := by
  rw [wHat, ← basis_ofNat hs]
  exact AdditiveNTT.normalizedWᵢ_eval_βᵢ_eq_1 (ZMod 2) basis

/-! ## Points as sums of basis elements -/

/-- A point whose index has disjoint high and low bits is the sum of the two points. -/
theorem point_mul_add {q n r : ℕ} (hr : r < 2 ^ n) :
    point (q * 2 ^ n + r) = point (q * 2 ^ n) + point r := by
  rw [point_add]
  congr 1
  refine Nat.eq_of_testBit_eq fun j ↦ ?_
  rw [Nat.mul_comm, Nat.testBit_two_pow_mul_add _ hr, Nat.testBit_xor, Nat.testBit_two_pow_mul]
  by_cases hj : j < n
  · simp [hj, Nat.not_le.mpr hj]
  · have hle : 2 ^ n ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    simp [hj, Nat.le_of_not_lt hj, Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hr hle)]

/-- An additive map at `point (a · 2^o)` is its sum at the `e_(o+k)` over the bits `k` of `a`. -/
theorem map_point_mul {M : Type*} [AddCommMonoid M] (f : K →+ M) (o : ℕ) :
    ∀ n a, a < 2 ^ n → f (point (a * 2 ^ o)) =
      (((List.range n).filter a.testBit).map fun k ↦ f (point (2 ^ (o + k)))).sum
  | 0, a, ha => by simp [show a = 0 by omega, point_zero]
  | n + 1, a, ha => by
    obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 2 ^ n ∧ a = q * 2 ^ n + r :=
      ⟨a / 2 ^ n, a % 2 ^ n, Nat.mod_lt _ (by positivity), (Nat.div_add_mod' a (2 ^ n)).symm⟩
    have hq : q < 2 := by
      by_contra h
      have : 2 * 2 ^ n ≤ q * 2 ^ n := Nat.mul_le_mul_right _ (by omega)
      rw [pow_succ] at ha
      omega
    have hro : r * 2 ^ o < 2 ^ (o + n) := by
      rw [pow_add, mul_comm (2 ^ o)]
      exact Nat.mul_lt_mul_of_pos_right hr (by positivity)
    have hbit : ∀ k, (q * 2 ^ n + r).testBit k = if k < n then r.testBit k else q.testBit (k - n) :=
      fun k ↦ by rw [Nat.mul_comm, Nat.testBit_two_pow_mul_add _ hr]
    have hfilt : (List.range n).filter (q * 2 ^ n + r).testBit = (List.range n).filter r.testBit :=
      List.filter_congr fun k hk ↦ by simp [hbit, List.mem_range.mp hk]
    rw [List.range_succ, List.filter_append, List.map_append, List.sum_append, hfilt,
      ← map_point_mul f o n r hr,
      show (q * 2 ^ n + r) * 2 ^ o = q * 2 ^ (o + n) + r * 2 ^ o by ring, point_mul_add hro,
      map_add, add_comm]
    congr 1
    interval_cases q
    · simp [point_zero, Nat.testBit_eq_false_of_lt hr]
    · simp [Nat.testBit_two_pow_add_eq, Nat.testBit_eq_false_of_lt hr]

/-- `Ŵ_s` vanishes on the span of `e_0 … e_(s-1)`. -/
theorem wHat_of_lt {s y : ℕ} (hs : s < 16) (hy : y < 2 ^ s) : wHat s (point y) = 0 := by
  have h := map_point_mul (wHatHom s) 0 s y hy
  simp only [pow_zero, mul_one, zero_add, wHatHom_apply] at h
  rw [h]
  refine List.sum_eq_zero fun x hx ↦ ?_
  simp only [List.mem_map, List.mem_filter, List.mem_range] at hx
  obtain ⟨k, ⟨hk, _⟩, rfl⟩ := hx
  exact wHat_two_pow_of_lt hs hk

/-! ## The twiddles -/

/-- `W_0 = X`. -/
theorem wSub_zero (x : K) : wSub 0 x = x := by
  rw [wSub, show Fin.ofNat 16 0 = 0 from rfl, AdditiveNTT.W₀_eq_X, eval_X]

/-- `W_(i+1)(x) = W_i(x) (W_i(x) + W_i(e_i))`. -/
theorem wSub_succ {i : ℕ} (hi : i < 15) (x : K) :
    wSub (i + 1) x = wSub i x * (wSub i x + wSub i (point (2 ^ i))) := by
  have h := AdditiveNTT.W_linear_comp_decomposition (ZMod 2) basis (Fin.ofNat 16 i)
    (by simp [Nat.mod_eq_of_lt (by omega : i < 16)]; omega) X
  have hi1 : Fin.ofNat 16 i + 1 = Fin.ofNat 16 (i + 1) :=
    Fin.ext (by simp [Fin.val_add])
  rw [comp_X, comp_X, ZMod.card, hi1] at h
  rw [← basis_ofNat (by omega)]
  simp only [wSub, h, eval_add, eval_pow, eval_mul, eval_C, CharTwo.sub_eq_add]
  ring

/-- `subspaceRow i` is `W_i` at `e_i … e_14`. -/
theorem subspaceRow_eq : ∀ {i : ℕ}, i ≤ 14 →
    subspaceRow i = (List.range (15 - i)).map fun k ↦ wSub i (point (2 ^ (i + k)))
  | 0, _ => by simp [subspaceRow, logM, wSub_zero, point]
  | i + 1, hi => by
    rw [subspaceRow, subspaceRow_eq (by omega), show 15 - i = 14 - i + 1 by omega,
      List.range_succ_eq_map, show 15 - (i + 1) = 14 - i by omega]
    simp only [List.map_cons, List.map_map, List.headD_cons, List.drop_succ_cons, List.drop_zero,
      add_zero]
    refine List.map_congr_left fun k _ ↦ ?_
    simp only [Function.comp, Nat.succ_eq_add_one]
    rw [wSub_succ (by omega), show i + (k + 1) = i + 1 + k by ring]

/-- `subspaceEvaluations i` is `Ŵ_i` at `e_i … e_14`. -/
theorem subspaceEvaluations_eq {i : ℕ} (hi : i ≤ 14) :
    subspaceEvaluations i = (List.range (15 - i)).map fun k ↦ wHat i (point (2 ^ (i + k))) := by
  rw [subspaceEvaluations, subspaceRow_eq hi, show 15 - i = 14 - i + 1 by omega,
    List.range_succ_eq_map]
  simp only [List.map_cons, List.map_map, List.headD_cons, add_zero]
  rw [wHat_eq i (by omega)]
  refine congrArg _ (List.map_congr_left fun k _ ↦ ?_)
  simp only [Function.comp]
  rw [wHat_eq i (by omega)]

/-- A sum accumulated by a left fold. -/
theorem foldl_add_eq_sum {M : Type*} [AddCommMonoid M] (g : ℕ → M) :
    ∀ (l : List ℕ) (c : M), l.foldl (fun t k ↦ t + g k) c = c + (l.map g).sum
  | [], c => by simp
  | k :: l, c => by
    rw [List.foldl_cons, foldl_add_eq_sum g l, List.map_cons, List.sum_cons, add_assoc]

/-- The twiddle of block `b` of layer `14 - s` is `Ŵ_s` at the block's first point. -/
theorem twiddle_eq {s b : ℕ} (hs : s < 14) (hb : b < 2 ^ (14 - s)) :
    ((List.range (14 - s)).filter b.testBit).foldl
      (fun t bit ↦ t + ((subspaceEvaluations s).drop 1).getD bit 0) 0 =
      wHat s (point (b * 2 ^ (s + 1))) := by
  rw [foldl_add_eq_sum, zero_add, ← wHatHom_apply,
    map_point_mul (wHatHom s) (s + 1) (14 - s) b hb]
  refine congrArg _ (List.map_congr_left fun k hk ↦ ?_)
  simp only [List.mem_filter, List.mem_range] at hk
  rw [subspaceEvaluations_eq (by omega), List.getD_eq_getElem?_getD, List.getElem?_drop,
    List.getElem?_map, List.getElem?_range (by omega), Option.map_some, Option.getD_some,
    wHatHom_apply, show s + (1 + k) = s + 1 + k by ring]

/-! ## The novel basis -/

/-- The value at `x` of the polynomial with coefficients `m` on `X_0 … X_(2^n - 1)`: the first
half's plus `Ŵ_(n-1)(x)` times the second half's. -/
noncomputable def novelEval : ℕ → List E → K → E
  | 0, m, _ => m.headD 0
  | n + 1, m, x => novelEval n (m.take (2 ^ n)) x + ι (wHat n x) * novelEval n (m.drop (2 ^ n)) x

/-- Scaling the coefficients scales the value. -/
theorem novelEval_map_mul (c : E) :
    ∀ (n : ℕ) (m : List E) (x : K), novelEval n (m.map (· * c)) x = novelEval n m x * c
  | 0, m, x => by cases m <;> simp [novelEval]
  | n + 1, m, x => by
    rw [novelEval, ← List.map_take, ← List.map_drop, novelEval_map_mul c n, novelEval_map_mul c n,
      novelEval]
    ring

/-- The value is linear in the coefficients. -/
theorem novelEval_zipWith (c : E) : ∀ (n : ℕ) (a b : List E), a.length = b.length → ∀ x,
    novelEval n (List.zipWith (fun u v ↦ u + v * c) a b) x = novelEval n a x + novelEval n b x * c
  | 0, a, b, h, x => by
    cases a <;> cases b <;> simp_all [novelEval]
  | n + 1, a, b, h, x => by
    rw [novelEval, List.take_zipWith, List.drop_zipWith,
      novelEval_zipWith c n _ _ (by simp [h]), novelEval_zipWith c n _ _ (by simp [h]), novelEval,
      novelEval]
    ring

/-- The tensor `⊗_j (1, z_j)` as `dualCodeword` builds it, of value `∏_j (1 + z_j Ŵ_j(x))`. -/
theorem novelEval_tensor : ∀ (n : ℕ) (z : Fin n → E),
    ((List.ofFn z).foldl (fun t c ↦ t ++ t.map (· * c)) [1]).length = 2 ^ n ∧
      ∀ x, novelEval n ((List.ofFn z).foldl (fun t c ↦ t ++ t.map (· * c)) [1]) x =
        ∏ i, (1 + z i * ι (wHat i x))
  | 0, z => ⟨rfl, fun x ↦ by simp [novelEval]⟩
  | n + 1, z => by
    obtain ⟨hlen, heval⟩ := novelEval_tensor n fun i ↦ z i.castSucc
    rw [List.ofFn_succ_last, List.foldl_append, List.foldl_cons, List.foldl_nil]
    refine ⟨by rw [List.length_append, List.length_map, hlen, pow_succ, mul_two], fun x ↦ ?_⟩
    rw [novelEval, List.take_left' hlen, List.drop_left' (by rw [hlen]), novelEval_map_mul,
      heval, Fin.prod_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    ring

/-! ## The additive NTT -/

/-- Block `b` of `2^n` entries of a list. -/
def block (n : ℕ) (cw : List E) (b : ℕ) : List E := (cw.drop (b * 2 ^ n)).take (2 ^ n)

/-- A block within the list has `2^n` entries. -/
theorem length_block {n b : ℕ} {cw : List E} (h : b * 2 ^ n + 2 ^ n ≤ cw.length) :
    (block n cw b).length = 2 ^ n := by
  rw [block, List.length_take, List.length_drop]
  omega

/-- The halves of block `b` of `2^(s+1)` entries are the blocks `2b` and `2b + 1` of `2^s`. -/
theorem block_block {s b e : ℕ} (he : e < 2) (cw : List E) :
    block s (block (s + 1) cw b) e = block s cw (2 * b + e) := by
  rw [block, block, block, List.drop_take, List.take_take, List.drop_drop,
    show (2 * b + e) * 2 ^ s = b * 2 ^ (s + 1) + e * 2 ^ s by ring]
  congr 1
  rw [pow_succ]
  interval_cases e <;> omega

/-- The blocks of a concatenation of lists of `2^k` entries are the lists. -/
theorem block_flatMap {k : ℕ} (g : ℕ → List E) : ∀ N, (∀ b < N, (g b).length = 2 ^ k) →
    ((List.range N).flatMap g).length = N * 2 ^ k ∧
      ∀ b < N, block k ((List.range N).flatMap g) b = g b
  | 0, _ => by simp
  | N + 1, hg => by
    obtain ⟨hlen, hblock⟩ := block_flatMap g N fun b hb ↦ hg b (by omega)
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine ⟨by rw [List.length_append, hlen, hg N (by omega), add_mul, one_mul], fun b hb ↦ ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hb with hb | rfl
    · have hle : b * 2 ^ k + 2 ^ k ≤ N * 2 ^ k := by
        rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hb
      rw [← hblock b hb, block, block,
        List.drop_append_of_le_length (hlen ▸ Nat.mul_le_mul_right _ hb.le),
        List.take_append_of_le_length (by
          rw [List.length_drop, hlen]
          exact Nat.le_sub_of_add_le (by rw [add_comm]; exact hle))]
    · rw [block, List.drop_left' hlen, List.take_of_length_le (by rw [hg b (by omega)])]

/-- A butterfly on a block of `2^(s+1)` entries: `u + v t` on the halves, then `v + u`. -/
theorem butterfly_eq_halves {s : ℕ} {B : List E} (hB : B.length = 2 ^ (s + 1)) (t : K) :
    butterfly t B = List.zipWith (fun u v ↦ u + v * ι t) (B.take (2 ^ s)) (B.drop (2 ^ s)) ++
      List.zipWith (fun u v ↦ u + v * 1) (B.drop (2 ^ s))
        (List.zipWith (fun u v ↦ u + v * ι t) (B.take (2 ^ s)) (B.drop (2 ^ s))) := by
  simp only [butterfly, hB, pow_succ, Nat.mul_div_cancel _ (by norm_num : 0 < 2), mul_one]
  rfl

/-- Entering layer `14 - s`, the codeword in blocks of `2^n = 2^(s+1)` entries: on each block's
points, the block's polynomial is `F`. -/
def Stage (F : K → E) (n : ℕ) (cw : List E) : Prop :=
  cw.length = 2 ^ 15 ∧ ∀ b < 2 ^ (15 - n), ∀ y < 2 ^ n,
    novelEval n (block n cw b) (point (b * 2 ^ n + y)) = F (point (b * 2 ^ n + y))

/-- Layer `14 - s` is a butterfly on each block of `2^(s+1)` entries, of twiddle `Ŵ_s` at the
block's first point. -/
theorem encodeLayer_eq_blocks {s : ℕ} (hs : s < 14) {cw : List E} (hcw : cw.length = 2 ^ 15) :
    encodeLayer (14 - s) cw = (List.range (2 ^ (14 - s))).flatMap fun b ↦
      butterfly (wHat s (point (b * 2 ^ (s + 1)))) (block (s + 1) cw b) := by
  have h2 : logM - (14 - s) = s + 1 := by unfold logM; omega
  have h3 : cw.length / 2 ^ (s + 1) = 2 ^ (14 - s) := by
    rw [hcw, Nat.pow_div (by omega) (by norm_num)]
    congr 1
    omega
  simp only [encodeLayer, h2, h3, Nat.add_sub_cancel]
  exact List.flatMap_congr fun b hb ↦ by rw [twiddle_eq hs (List.mem_range.mp hb)]; rfl

/-- **A layer of the NTT**: it halves the blocks. -/
theorem stage_encodeLayer {F : K → E} {s : ℕ} (hs : s < 14) {cw : List E}
    (h : Stage F (s + 1) cw) : Stage F s (encodeLayer (14 - s) cw) := by
  obtain ⟨hlen, hcw⟩ := h
  have hpow : 2 ^ (14 - s) * 2 ^ (s + 1) = 2 ^ 15 := by rw [← pow_add]; congr 1; omega
  have hpow' : 2 ^ (15 - s) = 2 * 2 ^ (14 - s) := by rw [← pow_succ']; congr 1; omega
  have hB : ∀ b < 2 ^ (14 - s), (block (s + 1) cw b).length = 2 ^ (s + 1) := fun b hb ↦
    length_block (by
      rw [hlen, ← hpow, ← Nat.succ_mul]
      exact Nat.mul_le_mul_right _ hb)
  obtain ⟨hlen', hblock⟩ := block_flatMap (k := s + 1)
    (fun b ↦ butterfly (wHat s (point (b * 2 ^ (s + 1)))) (block (s + 1) cw b)) (2 ^ (14 - s))
    fun b hb ↦ by
      rw [butterfly_eq_halves (hB b hb)]
      simp [hB b hb, pow_succ, mul_two]
  rw [encodeLayer_eq_blocks hs hlen]
  refine ⟨by rw [hlen', hpow], fun b hb y hy ↦ ?_⟩
  obtain ⟨b', e, he, rfl⟩ : ∃ b' e, e < 2 ∧ b = 2 * b' + e :=
    ⟨b / 2, b % 2, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod b 2).symm⟩
  have hb' : b' < 2 ^ (14 - s) := by omega
  have hey : e * 2 ^ s + y < 2 ^ (s + 1) := by
    rw [pow_succ]
    interval_cases e <;> omega
  rw [← block_block he, hblock b' hb', show (2 * b' + e) * 2 ^ s + y =
    b' * 2 ^ (s + 1) + (e * 2 ^ s + y) by ring,
    ← hcw b' (by rw [show 15 - (s + 1) = 14 - s by omega]; exact hb') _ hey,
    butterfly_eq_halves (hB b' hb')]
  have hw : wHat s (point (b' * 2 ^ (s + 1) + (e * 2 ^ s + y))) =
      wHat s (point (b' * 2 ^ (s + 1))) + e := by
    rw [point_mul_add hey, wHat_add, point_mul_add hy, wHat_add, wHat_of_lt (by omega) hy,
      add_zero]
    interval_cases e
    · simp [point_zero, wHat_zero]
    · simp [wHat_two_pow_self (by omega : s < 16)]
  set B := block (s + 1) cw b'
  set t := wHat s (point (b' * 2 ^ (s + 1)))
  have h2s : 2 ^ (s + 1) = 2 ^ s + 2 ^ s := by rw [pow_succ, mul_two]
  have hTB : (B.take (2 ^ s)).length = (B.drop (2 ^ s)).length := by
    simp [B, hB b' hb', h2s]
  have hT : (List.zipWith (fun u v ↦ u + v * ι t) (B.take (2 ^ s)) (B.drop (2 ^ s))).length =
      2 ^ s := by
    simp [B, hB b' hb', h2s]
  have hx := novelEval_zipWith (ι t) s _ _ hTB
  rw [novelEval, hw]
  interval_cases e
  · rw [block, zero_mul, List.drop_zero, List.take_left' hT, hx, map_add, Nat.cast_zero, map_zero,
      add_zero]
    ring
  · rw [block, one_mul, List.drop_left' hT, List.take_of_length_le (by simp [B, hB b' hb', h2s]),
      novelEval_zipWith 1 s _ _ (by simp [B, hB b' hb', h2s]), hx, Nat.cast_one,
      map_add, map_one]
    ring

/-- **The NTT evaluates**: the codeword of novel-basis coefficients `m` is the values of their
polynomial on the domain. -/
theorem encode_eq_novelEval {m : List E} (hm : m.length = 2 ^ 14) :
    encode m = List.ofFn fun b : Fin (2 ^ 15) ↦ novelEval 14 m (point b) := by
  have hstage : ∀ k ≤ 14, Stage (novelEval 14 m) (14 - k)
      ((List.range' 1 k).foldl (fun codeword layer ↦ encodeLayer layer codeword) (m ++ m)) := by
    intro k hk
    induction k with
    | zero =>
      show Stage (novelEval 14 m) 14 (m ++ m)
      refine ⟨by rw [List.length_append, hm]; norm_num, fun b hb y _ ↦ ?_⟩
      have : block 14 (m ++ m) b = m := by
        interval_cases b
        · rw [block, zero_mul, List.drop_zero, List.take_left' hm]
        · rw [block, one_mul, List.drop_left' hm, List.take_of_length_le hm.le]
      rw [this]
    | succ k ih =>
      rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil,
        show 1 + 1 * k = 14 - (13 - k) by omega, show 14 - (k + 1) = 13 - k by omega]
      exact stage_encodeLayer (by omega)
        (by rw [show 13 - k + 1 = 14 - k by omega]; exact ih (by omega))
  obtain ⟨hlen, heval⟩ : Stage (novelEval 14 m) 0 _ := hstage 14 le_rfl
  rw [encode, show logM - 1 = 14 from rfl]
  refine List.ext_getElem (by rw [hlen, List.length_ofFn]) fun b hb _ ↦ ?_
  have h := heval b (by rw [Nat.sub_zero, ← hlen]; exact hb) 0 (by norm_num)
  rw [block, pow_zero, mul_one, add_zero, List.drop_eq_getElem_cons hb,
    novelEval.eq_1] at h
  rw [List.getElem_ofFn]
  exact h

/-! ## The dual codeword -/

/-- **The deployed dual codeword is the dual codeword**: entry `b` of the NTT of the tensor
`⊗_j (1, z_j)` is `∏_j (1 + z_j Ŵ_j(point b))`. -/
theorem dualCodeword_eq_dual (z : Fin 14 → E) :
    dualCodeword (List.ofFn z) = List.ofFn (dual z) := by
  obtain ⟨hlen, heval⟩ := novelEval_tensor 14 z
  rw [dualCodeword, encode_eq_novelEval hlen]
  congr 1
  funext b
  rw [heval, dual]
  simp only [normW_eval]

variable (H : List UInt8 → Common.KDigest) (P : LeanVM.Semantics.KState → LeanVM.Semantics.KState)

/-- `Sponge.samplesM n` draws `n` challenges. -/
theorem length_samples : ∀ (n : ℕ) (s : Sponge),
    (Id.run (Sponge.samplesM (m := Id) (fun L ↦ pure (P L)) n s)).length = n
  | 0, _ => rfl
  | n + 1, s => congrArg Nat.succ
      (length_samples n (Id.run (Sponge.sampleM (m := Id) (fun L ↦ pure (P L)) s)).2)

/-- A root has `14` challenges. -/
theorem length_membershipChallenges (root : Common.KDigest) :
    (membershipChallenges H P root).length = 14 :=
  length_samples P logK _

/-- **The membership vector of a root is the dual codeword of its challenges.** -/
theorem membershipVector_eq_dual (root : Common.KDigest) (z : Fin 14 → E)
    (hz : membershipChallenges H P root = List.ofFn z) :
    membershipVector H P root = List.ofFn (dual z) := by
  rw [membershipVector, hz, dualCodeword_eq_dual]

/-- The membership vector of a root is the dual codeword of its challenges, `z_i` entry `i` of
`membershipChallenges`. -/
theorem membershipVector_eq_dual_challenges (root : Common.KDigest) :
    membershipVector H P root = List.ofFn (dual fun i : Fin 14 ↦
      (membershipChallenges H P root)[(i : ℕ)]'(by
        rw [length_membershipChallenges]; exact i.isLt)) :=
  membershipVector_eq_dual H P root _
    (List.ext_getElem (by simp [length_membershipChallenges]) fun i _ _ ↦ by rw [List.getElem_ofFn])

end

end LeanDa
