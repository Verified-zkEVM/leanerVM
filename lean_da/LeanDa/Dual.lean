module

public import LeanDa.Membership
public import LeanDa.Subspace

/-!
# The deployed dual codeword is the dual codeword

Proposition prop:ntt of `doc/leanvm/body/d-novel-basis.tex` for the crate's membership vector:
the additive NTT of `dualCodeword` (`verifier/src/da.rs:24-85`) computes `dualCodewordAt`
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
    dualCodeword (List.ofFn z) = List.ofFn (dualCodewordAt z) := by
  obtain ⟨hlen, heval⟩ := novelEval_tensor 14 z
  rw [dualCodeword, encode_eq_novelEval hlen]
  congr 1
  funext b
  rw [heval, dualCodewordAt]
  simp only [normW_eval]

variable (H : List UInt8 → Common.DigestBytes) (P : LeanVM.Semantics.KeccakState → LeanVM.Semantics.KeccakState)

/-- `Sponge.samplesWith n` draws `n` challenges. -/
theorem length_samples : ∀ (n : ℕ) (s : Sponge),
    (Id.run (Sponge.samplesWith (m := Id) (fun L ↦ pure (P L)) n s)).length = n
  | 0, _ => rfl
  | n + 1, s => congrArg Nat.succ
      (length_samples n (Id.run (Sponge.sampleWith (m := Id) (fun L ↦ pure (P L)) s)).2)

/-- A root has `14` challenges. -/
theorem length_membershipChallenges (root : Common.DigestBytes) :
    (membershipChallenges H P root).length = 14 :=
  length_samples P logK _

/-- **The membership vector of a root is the dual codeword of its challenges.** -/
theorem membershipVector_eq_dual (root : Common.DigestBytes) (z : Fin 14 → E)
    (hz : membershipChallenges H P root = List.ofFn z) :
    membershipVector H P root = List.ofFn (dualCodewordAt z) := by
  rw [membershipVector, hz, dualCodeword_eq_dual]

/-- The membership vector of a root is the dual codeword of its challenges, `z_i` entry `i` of
`membershipChallenges`. -/
theorem membershipVector_eq_dual_challenges (root : Common.DigestBytes) :
    membershipVector H P root = List.ofFn (dualCodewordAt fun i : Fin 14 ↦
      (membershipChallenges H P root)[(i : ℕ)]'(by
        rw [length_membershipChallenges]; exact i.isLt)) :=
  membershipVector_eq_dual H P root _
    (List.ext_getElem (by simp [length_membershipChallenges]) fun i _ _ ↦ by rw [List.getElem_ofFn])

end

end LeanDa
