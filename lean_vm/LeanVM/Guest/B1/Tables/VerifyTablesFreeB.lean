/-
  LeanVM.Guest.B1.Tables.VerifyTablesFreeB

  `verify_tables`' facts read off its runs free of `BLAKE2S`, under any semantics: the heights
  and padding weights, the blocks' offsets and selectors, the index chains, the copies, the
  values, `air_acc`.
-/

module

public import LeanVM.Guest.B1.Tables.VerifyTablesBaseM
public import LeanVM.Guest.B1.Tables.VerifyTablesFront
public import LeanVM.Guest.B1.Tables.VerifyTablesCopies
public import LeanVM.Guest.B1.Tables.VerifyTablesVals
public import LeanVM.Guest.B1.Tables.VerifyTablesTail

/-!
# `verify_tables`' hash-free facts under any semantics

The lemmas of `VerifyTablesPad`, `Sort`, `Sel`, `Front`, `Copies`, `Vals` and `Tail` that read
`verify_tables`' body only at runs free of `BLAKE2S`, over `VtHoldsB S` for `VtHolds`: each run
holds as deployed (`VtHoldsB.slice`, `VtHoldsB.atom`, with the run's freedom over `vtFree`
checked by the kernel, `vt_pad_free`, …), so each proof is the deployed one. `vt_valsB` reads its
windows by `window_evalB`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The runs' freedom -/

/-- The padding blocks are free of `BLAKE2S` over `vtFree`. -/
theorem vt_pad_free : ∀ t < 6, Stmt.freeInList vtFree (vtPad t) = true := by decide +kernel

/-- The side stores are free of `BLAKE2S`. -/
theorem vt_side_free : ∀ b < 102, Stmt.freeInList vtFree
    [.atom (.const (.n (26 + b)) (word (vtBlockSide b) 0 0)),
      .atom (.load (.n (26 + b)) (.n 25) b)] = true := by decide +kernel

/-- The ranks `0` are free of `BLAKE2S`. -/
theorem vt_rank0_free : Stmt.freeInList vtFree (vtRank0 129 0 0) = true ∧
    Stmt.freeInList vtFree (vtRank0 1043 74 2) = true := by decide +kernel

/-- The push ranks are free of `BLAKE2S`. -/
theorem vt_push_ranks_free : ∀ q < 36, Stmt.freeInList vtFree
    (vtRankN (rkV 129 q) (rkKa 129 q) (rkGl 129 q) (rkGo 129 q) (q + 1) 0) = true := by
  decide +kernel

/-- The count ranks are free of `BLAKE2S`. -/
theorem vt_count_ranks_free : ∀ q < 27, Stmt.freeInList vtFree
    (vtRankN (rkV 1043 q) (rkKa 1043 q) (rkGl 1043 q) (rkGo 1043 q) (75 + q) 2) = true := by
  decide +kernel

/-- The selector blocks are free of `BLAKE2S` over `vtFree`. -/
theorem sel_free : ∀ i < 65, Stmt.freeInList vtFree
    (selT (selBlk.getD i 0) (selVal.getD i 0) (selNames.getD i "")) = true := by decide +kernel

/-- The index factors' stores are free of `BLAKE2S`. -/
theorem vt_idxc_free : ∀ t < 34, Stmt.freeInList vtFree
    [.atom (.const (.n (1818 + t)) (word (kToNat (1 + gpowK (2 ^ t))) 0 0)),
      .atom (.load (.n (1818 + t)) (.n 1817) t)] = true := by decide +kernel

/-- The index chains are free of `BLAKE2S` over `vtFree`. -/
theorem vt_idx_free : Stmt.freeInList vtFree (idxT 1925 1893 "__loop14" 1) = true ∧
    Stmt.freeInList vtFree (idxT 2029 1997 "__loop16" 2) = true := by decide +kernel

/-- The `air_acc` blocks are free of `BLAKE2S`. -/
theorem air_free : ∀ t < 6, Stmt.freeInList vtFree
    (airT (airQ.getD t 0) (airTau.getD t 0) (airCe.getD t 0)) = true := by decide +kernel

variable {S : BlakeSem}

/-- **The tables' heights and padding weights** (G:1546-1557): table `t`'s rows are `n ≤ 2^τ`
with `log2Ceil n = τ < 29`, `dims_g[t + 1] = g^τ`, and, once the point has `τ` coordinates, its
padding weight is `paddingWeight` over them. -/
theorem vt_padsB {κ : ℕ} (hκ : κ ≤ 32) (Lm : MemImage κ) {σ : Val} (h : VtHoldsB S Lm.read σ)
    {point : List E} (hz : ReadsAt Lm.read (σ (.n 5)) point) :
    ∀ t < 6, ∃ τ n : ℕ, τ < 29 ∧ n ≤ 2 ^ τ ∧ log2Ceil n = τ ∧ σ (.n (1733 + 14 * t)) = gen ^ τ ∧
      LoadHolds Lm.read (σ (.n 7)) (t + 1) (gen ^ τ) ∧
      LoadHolds Lm.read (σ (.n 8)) t (eOfNat n) ∧
      (τ ≤ point.length → σ (.n (1739 + 14 * t)) = paddingWeight (point.take τ) n) := by
  intro t ht
  obtain ⟨k, hb⟩ := h.slice _ _ (vt_pad_blocks t ht) (vt_pad_free t ht)
  simp only [vtPad, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true, true_and, word_one,
    word_zero, List.map_cons, List.map_nil] at hb
  obtain ⟨l0, c1, ⟨r0, r1, r2⟩, l5, ⟨j, hj, hjx, hrel⟩, c9, ae, c10, a11, ⟨m13, e13⟩⟩ := hb
  obtain ⟨τ, hτ, hgτ⟩ := rc_sound' hκ Lm (K := 29) (by omega) (by decide)
    (by rw [c1]; exact word_g28) r0 r1 r2
  have hj29 : j < 29 := by simpa [pwNames] using hj
  have hjτ : j = τ := by
    rw [hgτ, gen_pow_eq_ofK] at hjx
    exact (gpow_injOn (by simp only [Set.mem_Iio]; omega)
      (by simp only [Set.mem_Iio]; omega) (ofK_injective hjx)).symm
  subst hjτ
  obtain ⟨n, zs, hn, hrows, hzl, hzs, hret⟩ := pw_dispatch j hj hrel
  simp only [List.cons.injEq, and_true] at hret
  obtain ⟨e6, e7, e8⟩ := hret
  have hlead : pwLead j n = 1 := by rw [← e7, ← c9]; exact e_add_eq_zero_iff.mp ae
  have hrest : pwRest j n ≠ 0 := by
    intro h0
    rw [a11, c10, add_zero, e8, h0, zero_mul] at m13
    exact zero_ne_one (m13.symm.trans e13)
  refine ⟨j, n, hτ, hn, (lead_rest_iff (by omega) hn).mp ⟨hlead, hrest⟩, hgτ,
    by rw [← hgτ]; exact l0, by rw [← hrows]; exact l5, fun hle => ?_⟩
  have hzs' : zs = point.take j := by
    apply List.ext_getElem (by simp [hzl]; omega)
    intro k h1 h2
    have hk : k < point.length := by simp at h2; omega
    rw [List.getElem_take]
    exact loadHolds_unique (hzs k h1) (hz k hk)
  rw [show 1739 + 14 * t = 1733 + 14 * t + 6 by ring, e6, hzs']

/-- **The bus blocks' offsets** (G:1495-1525): with `block_kappa = g^ks` (`ks < 34`) and the
exponent tables, the push blocks `0 .. 36` and the count blocks `74 .. 101` hold at
`block_off_g` their `stackOffsets` offsets within their side. -/
theorem vt_offsetsB {κ : ℕ} (hκ : κ ≤ 32) (Lm : MemImage κ) {σ : Val} (h : VtHoldsB S Lm.read σ)
    (ks : ℕ → ℕ) (hks : ∀ b < 102, ks b < 34)
    (hbk : ∀ b < 102, LoadHolds Lm.read (σ (.n 9)) b (gen ^ ks b))
    (hsq : ∀ j < 34, LoadHolds Lm.read (σ (.n 10)) j (gen ^ 2 ^ j)) :
    (∀ i < 37, LoadHolds Lm.read (σ (.n 128)) i
      (gen ^ (stackOffsets ((List.range 37).map ks)).1.getD i 0)) ∧
    ∀ i < 28, LoadHolds Lm.read (σ (.n 128)) (74 + i)
      (gen ^ (stackOffsets ((List.range 28).map fun i => ks (74 + i))).1.getD i 0) := by
  have hside : ∀ b < 102, LoadHolds Lm.read (σ (.n 25)) b (word (vtBlockSide b) 0 0) := by
    intro b hb
    obtain ⟨k, hs⟩ := h.slice _ _ (vt_side_blocks b hb) (vt_side_free b hb)
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hs
    rw [← hs.1]; exact hs.2
  have hvs : ∀ b, vtBlockSide b < 3 := fun b => by unfold vtBlockSide; split_ifs <;> omega
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · have := vt_side_offsets (v0 := 129) (side := 0) (start := 0) (n := 37) (by omega)
      (fun r hr => ?_) ?_ hside (fun b hb hw => ?_) ks hks hbk hsq i hi
    · simpa using this
    · rcases Nat.eq_zero_or_pos r with rfl | hr0
      · obtain ⟨k, hr⟩ := h.slice _ _ vt_push_rank0 vt_rank0_free.1
        exact (vtRank0_facts hκ Lm hr).1
      · obtain ⟨q, rfl⟩ : ∃ q, r = q + 1 := ⟨r - 1, by omega⟩
        obtain ⟨k, hr⟩ := h.slice _ _ (vt_push_ranks q (by omega))
          (vt_push_ranks_free q (by omega))
        exact vtRankN_facts hκ Lm (so0 := 0) (by simpa using hr)
    · obtain ⟨k, hr⟩ := h.slice _ _ vt_push_rank0 vt_rank0_free.1
      exact (vtRank0_facts hκ Lm hr).2
    · have := word_small_inj (hvs b) (by omega) hw
      unfold vtBlockSide at this; split_ifs at this; omega
  · have := vt_side_offsets (v0 := 1043) (side := 2) (start := 74) (n := 28) (by omega)
      (fun r hr => ?_) ?_ hside (fun b hb hw => ?_) ks hks hbk hsq i hi
    · exact this
    · rcases Nat.eq_zero_or_pos r with rfl | hr0
      · obtain ⟨k, hr⟩ := h.slice _ _ vt_count_rank0 vt_rank0_free.2
        exact (vtRank0_facts hκ Lm hr).1
      · obtain ⟨q, rfl⟩ : ∃ q, r = q + 1 := ⟨r - 1, by omega⟩
        obtain ⟨k, hr⟩ := h.slice _ _ (vt_count_ranks q (by omega))
          (vt_count_ranks_free q (by omega))
        exact vtRankN_facts hκ Lm (so0 := 74) (by rw [show 74 + (q + 1) = 75 + q by omega]; exact hr)
    · obtain ⟨k, hr⟩ := h.slice _ _ vt_count_rank0 vt_rank0_free.2
      exact (vtRank0_facts hκ Lm hr).2
    · have := word_small_inj (hvs b) (by omega) hw
      unfold vtBlockSide at this; split_ifs at this <;> omega

/-- **A block's selector** (G:1572-1594): block `b = selBlk i` of log-height `k < 34`, at offset
`off`, with the bus point at `zeta` of length `μ = log g_bus_mu`: `k ≤ μ`, the offset is below
`2^μ` and aligned to `2^k`, and the selector at value `selVal i + 23` is the placement's
`eqAbove` at the point. -/
theorem vt_selB {κ : ℕ} (hκ : κ ≤ 32) (Lm : MemImage κ) {σ : Val} (h : VtHoldsB S Lm.read σ)
    {i : ℕ} (hi : i < 65) {k off : ℕ} (hk : k < 34)
    (hbk : LoadHolds Lm.read (σ (.n 9)) (selBlk.getD i 0) (gen ^ k))
    (hoff : LoadHolds Lm.read (σ (.n 128)) (selBlk.getD i 0) (gen ^ off)) (hoff62 : off < 2 ^ 62)
    {point : List E} (hz : ReadsAt Lm.read (σ (.n 5)) point) (hmu : σ (.n 6) = gen ^ point.length)
    (hml : point.length < 33) (hsq : ∀ j < 34, LoadHolds Lm.read (σ (.n 10)) j (gen ^ 2 ^ j)) :
    k ≤ point.length ∧ off < 2 ^ point.length ∧ 2 ^ k ∣ off ∧
      σ (.n (selVal.getD i 0 + 23)) = ({ vars := k, index := off } : Placement).eqAbove point := by
  set b := selBlk.getD i 0
  set v := selVal.getD i 0
  obtain ⟨kr, hb⟩ := h.slice _ _ (sel_blocks i hi) (sel_free i hi)
  simp only [selT, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true, true_and, word_one,
    List.map_cons, List.map_nil] at hb
  obtain ⟨l0, -, -, m6, c6, rc5, m10, -, l13, m14, c17, s17, c18, s18, c19, a20, c21, -, hloop,
    m22, l23, m24, l25, l26, ae⟩ := hb
  have ev : σ (.n v) = gen ^ k := loadHolds_unique l0 hbk
  obtain ⟨e, he, hee⟩ := rc_sound' hκ Lm (K := 34) (by omega) (by decide)
    (by rw [c6]; exact word_g33) rc5.1 rc5.2.1 rc5.2.2
  rw [hmu, hee, ev, ← pow_add] at m6
  have hmue : point.length = e + k := gen_pow_inj' (by omega) (by omega) m6
  -- the loop
  have hB := Main.loop_sound (B := SelBody Lm.read (σ (.n (v + 14))) (σ (.n (v + 15)))
      (σ (.n (v + 10))) (σ (.n (v + 16))) (σ (.n 10)) (σ (.n v)))
    (ps := [σ (.n (v + 5)), σ (.n (v + 14)), σ (.n (v + 15)), σ (.n (v + 10)), σ (.n (v + 16)),
      σ (.n 10), σ (.n v)]) (N := σ (.n (v + 5))) (m := e) (by unfold ordG; omega) hee
    (fun x hx => sel_step (sel_ok i hi) hx) (fun hne => by
      have := hloop (by rw [a20, c19]; exact hne)
      rw [c21] at this
      exact this)
  unfold SelBody at hB
  classical
  let bit : ℕ → E := fun t => if ht : t < e then Classical.choose (hB t ht) else 0
  have hbit : ∀ t (ht : t < e), ∃ e' z o s', LoadHolds Lm.read (σ (.n (v + 14)) * gen ^ t) 0 (bit t) ∧
      bit t * bit t = bit t ∧ LoadHolds Lm.read (σ (.n (v + 15)) * gen ^ t) 0 e' ∧
      LoadHolds Lm.read (σ (.n (v + 10)) * gen ^ t) 0 z ∧
      LoadHolds Lm.read (σ (.n (v + 15)) * gen ^ t) 1 (e' * (1 + bit t + z)) ∧
      LoadHolds Lm.read (σ (.n (v + 16)) * gen ^ t) 0 o ∧
      LoadHolds Lm.read (σ (.n 10) * (σ (.n v) * gen ^ t)) 0 s' ∧
      LoadHolds Lm.read (σ (.n (v + 16)) * gen ^ t) 1 (o * (1 + bit t * (s' + 1))) := fun t ht => by
    simp only [bit, ht, ↓reduceDIte]
    exact Classical.choose_spec (hB t ht)
  -- the chains
  have hzk : ∀ t < e, ∀ z, LoadHolds Lm.read (σ (.n (v + 10)) * gen ^ t) 0 z →
      z = point.getD (k + t) 0 := fun t ht z hl => by
    rw [m10, ev, mul_assoc, ← pow_add, loadHolds_gen_pow_mul, Nat.add_zero] at hl
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact loadHolds_unique hl (hz _ (by omega))
  have hchain : ∀ t ≤ e,
      LoadHolds Lm.read (σ (.n (v + 15))) t
        (∏ j ∈ Finset.range t, (1 + bit j + point.getD (k + j) 0)) ∧
      LoadHolds Lm.read (σ (.n (v + 16))) t
        (∏ j ∈ Finset.range t, (1 + bit j * (gen ^ 2 ^ (k + j) + 1))) := by
    intro t ht
    induction t with
    | zero =>
      simp only [Finset.range_zero, Finset.prod_empty]
      exact ⟨by rw [← c17]; exact s17, by rw [← c18]; exact s18⟩
    | succ t ih =>
      obtain ⟨ih1, ih2⟩ := ih (by omega)
      obtain ⟨e', z, o, s', -, -, le, lz, le1, lo, ls, lo1⟩ := hbit t (by omega)
      rw [loadHolds_gen_pow_mul, Nat.add_zero] at le lo
      rw [loadHolds_gen_pow_mul] at le1 lo1
      rw [← mul_assoc, ev, mul_assoc, ← pow_add, loadHolds_gen_pow_mul, Nat.add_zero] at ls
      rw [loadHolds_unique le ih1, hzk t (by omega) z lz] at le1
      rw [loadHolds_unique lo ih2, loadHolds_unique ls (hsq _ (by omega))] at lo1
      rw [Finset.prod_range_succ, Finset.prod_range_succ]
      exact ⟨le1, lo1⟩
  obtain ⟨hc1, hc2⟩ := hchain e le_rfl
  rw [m22, hee, loadHolds_gen_pow_mul, Nat.add_zero] at l23
  rw [m24, hee, loadHolds_gen_pow_mul, Nat.add_zero] at l25
  have e23 := loadHolds_unique l23 hc1
  have e25 := loadHolds_unique l25 hc2
  have e26 := loadHolds_unique l26 hoff
  rw [e_add_eq_zero_iff, e25, e26] at ae
  -- the rebuilt offset is the block's
  obtain ⟨off', hoff', hdvd, hprod, hbits⟩ := sel_rebuild (M := point.length) (κ := k)
    (b := fun j => bit (j - k)) (by omega) (fun t ht => by
      simp only [Nat.add_sub_cancel_left]
      obtain ⟨-, -, -, -, -, hb2, -⟩ := hbit t (by omega)
      exact hb2)
  simp only [Nat.add_sub_cancel_left] at hprod hbits
  rw [show point.length - k = e by omega] at hprod hbits
  rw [hprod] at ae
  have h32 : 2 ^ point.length ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) (by omega)
  have hoo : off' = off := gen_pow_inj' (by omega) (by omega) ae
  subst hoo
  refine ⟨by omega, hoff', hdvd, ?_⟩
  rw [e23, eqAbove_prod (M := point.length) point rfl, show point.length - k = e by omega]
  exact Finset.prod_congr rfl fun t ht => by rw [hbits t (Finset.mem_range.mp ht)]

/-- `INDEX_MLE_FACTORS` under `S` (`vt_idxc`). -/
theorem vt_idxcB {rd : Reader} {σ : Val} (h : VtHoldsB S rd σ) :
    ∀ t < 34, LoadHolds rd (σ (.n 1817)) t (1 + gen ^ 2 ^ t) := by
  intro t ht
  obtain ⟨k, hb⟩ := h.slice _ _ (vt_idxc_blocks t ht) (vt_idxc_free t ht)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hb
  obtain ⟨c, l⟩ := hb
  rw [c, word_ofK, ofBits_kToNat, ofK_add', ofK_one, gpowK_eq (by unfold u128Bound; exact Nat.pow_lt_pow_right (by decide) (by omega)),
    ← gen_pow_eq_ofK] at l
  exact l

/-- **An index chain** (G:1622-1627): over `g^m` with `m` at most the point's length, its end is
`indexMle` of the point's first `m` coordinates, stored at `block_index_mle[slot]`. -/
theorem vt_idx_genB {rd : Reader} {σ : Val} (h : VtHoldsB S rd σ) {n c kv slot : ℕ} {self : String}
    (hok : idxOk self = true) (heq : stmtsEqb (idxT c kv self slot) ((vtPre.drop n).take 10) = true)
    (hf : Stmt.freeInList vtFree (idxT c kv self slot) = true)
    {m : ℕ} (hkm : σ (.n kv) = gen ^ m) (hm : m < 34) {point : List E}
    (hz : ReadsAt rd (σ (.n 5)) point) (hml : m ≤ point.length) :
    σ (.n (c + 6)) = indexMle (point.take m) ∧ LoadHolds rd (σ (.n 1852)) slot (σ (.n (c + 6))) := by
  obtain ⟨kr, hb⟩ := h.slice _ _ heq hf
  simp only [idxT, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true, true_and, word_one,
    List.map_cons, List.map_nil] at hb
  obtain ⟨c1, l1, c2, a3, c4, -, hloop, m5, l6, s6⟩ := hb
  have hidxc := vt_idxcB h
  have hB := Main.loop_sound (B := fun x => ∃ c' zt ft, LoadHolds rd (σ (.n c) * x) 0 c' ∧
      LoadHolds rd (σ (.n 5) * x) 0 zt ∧ LoadHolds rd (σ (.n 1817) * x) 0 ft ∧
      LoadHolds rd (σ (.n c) * x) 1 (c' * (1 + zt * ft)))
    (ps := [σ (.n kv), σ (.n c), σ (.n 5), σ (.n 1817)]) (N := σ (.n kv)) (m := m)
    (by unfold ordG; omega) hkm (fun x hx => idx_step hok hx) (fun hne => by
      have := hloop (by rw [a3, c2]; exact hne)
      rw [c4] at this
      exact this)
  have hch : ∀ t ≤ m, LoadHolds rd (σ (.n c)) t
      (∏ j ∈ Finset.range t, (1 + point.getD j 0 * (1 + gen ^ 2 ^ j))) := by
    intro t ht
    induction t with
    | zero => simp only [Finset.range_zero, Finset.prod_empty]; rw [← c1]; exact l1
    | succ t ih =>
      obtain ⟨c', zt, ft, lc, lz, lf, lc1⟩ := hB t (by omega)
      rw [loadHolds_gen_pow_mul, Nat.add_zero] at lc lz lf
      rw [loadHolds_gen_pow_mul] at lc1
      rw [loadHolds_unique lc (ih (by omega)), loadHolds_unique lz (hz t (by omega)),
        loadHolds_unique lf (hidxc t (by omega)), ← List.getD_eq_getElem point 0 (by omega)] at lc1
      rw [Finset.prod_range_succ]
      exact lc1
  rw [m5, hkm, loadHolds_gen_pow_mul, Nat.add_zero] at l6
  have e6 := loadHolds_unique l6 (hch m le_rfl)
  refine ⟨?_, s6⟩
  rw [e6, indexMle_eq, List.length_take, Nat.min_eq_left hml]
  exact Finset.prod_congr rfl fun t ht => by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_take_of_lt (Finset.mem_range.mp ht)]

/-- The copies followed back, under `S` (`vt_resolve`). -/
theorem vt_resolveB {rd : Reader} {σ : Val} (h : VtHoldsB S rd σ) :
    ∀ fuel v, σ (.n v) = σ (.n (vtResolve fuel v))
  | 0, v => rfl
  | fuel + 1, v => by
    unfold vtResolve
    split
    · next c hc =>
      have hm := List.mem_of_find?_eq_some hc
      have hv : c.2.1 = v := by simpa using List.find?_some hc
      have hok := List.all_eq_true.mp vt_copies_ok c hm
      have := h.atom' c.1 (.copy (.n c.2.1) (.n c.2.2)) hok rfl
      simp only [Atom.Holds] at this
      rw [← hv, this]
      exact vt_resolveB h fuel c.2.2
    · rfl

/-- **The `eq_hi`**: each is its block's selector. -/
theorem vt_eqhiB {rd : Reader} {σ : Val} (h : VtHoldsB S rd σ) {t s k : ℕ} (ht : t < 6) (hs : s < 3)
    (hk : k < ((vtEqhiVars.getD t []).getD s []).length) :
    σ (.n (((vtEqhiVars.getD t []).getD s []).getD k 0)) =
      σ (.n (selVal.getD (eqhiSel t s k) 0 + 23)) := by
  rw [vt_resolveB h 2, vt_eqhi_ok t ht s hs k hk]

/-- The GKR values' copies. -/
theorem vt_tree_copiesB {rd : Reader} {σ : Val} (h : VtHoldsB S rd σ) :
    σ (.n 21) = σ (.n 16) ∧ σ (.n 22) = σ (.n 17) ∧ σ (.n 23) = σ (.n 18) := by
  have := vt_resolveB h 1
  exact ⟨this 21, this 22, this 23⟩

/-- **The values**: the three bus totals and each table's `constraint_eval`, as expressions in the
valuation and the weights `χ`, and the sumcheck's target. -/
theorem vt_valsB {rd : Reader} {σ : Val} (h : VtHoldsB S rd σ) {w : List E} (hw : 16 ≤ w.length)
    (hfw : ReadsAt rd (σ (.n 11)) w) (h1 : LoadHolds rd (σ (.n 1852)) 1 (σ (.n 1931)))
    (h2 : LoadHolds rd (σ (.n 1852)) 2 (σ (.n 2035)))
    (hm : ReadsAt rd (σ (.n 13)) [σ (.n 1937), σ (.n 1955), σ (.n 1973)]) :
    σ (.n 3326) = pushTotalEx.eval (fun k => σ (.n k)) (fun i => w.getD i 0) ∧
      σ (.n 3705) = pullTotalEx.eval (fun k => σ (.n k)) (fun i => w.getD i 0) ∧
      σ (.n 4553) = countTotalEx.eval (fun k => σ (.n k)) (fun i => w.getD i 0) ∧
      (∀ t : Fin 6, σ (.n (vtCeVars.getD t 0)) =
        (ceEx t).eval (fun k => σ (.n k)) (fun i => w.getD i 0)) ∧
      σ (.n 4631) = σ (.n 4624) * σ (.n 3326) + σ (.n 4625) * σ (.n 3705) +
        σ (.n 4626) * σ (.n 4553) := by
  have hL := vt_fpw_sound hw hfw
  obtain ⟨kret, hb⟩ := h
  have hE : LoadTab.Sound rd σ (fun i => w.getD i 0) [] := fun _ hq => absurd hq (by simp)
  refine ⟨window_evalB vtPre_noRet hb hL 1505 1587 3326 pushTotalEx vt_push_total,
    window_evalB vtPre_noRet hb (vt_pullTab_sound hw hfw h1 h2 hm) 1505 1892 3705 pullTotalEx
      vt_pull_total,
    window_evalB vtPre_noRet hb hE 3397 876 4553 countTotalEx vt_count_total, fun t => ?_, ?_⟩
  · fin_cases t
    · exact window_evalB vtPre_noRet hb hL 4374 481 5140 (ceEx 0) vt_ce0
    · exact window_evalB vtPre_noRet hb hL 4862 521 5668 (ceEx 1) vt_ce1
    · exact window_evalB vtPre_noRet hb hL 5391 269 5945 (ceEx 2) vt_ce2
    · exact window_evalB vtPre_noRet hb hL 5668 515 6468 (ceEx 3) vt_ce3
    · exact window_evalB vtPre_noRet hb hL 6191 494 6970 (ceEx 4) vt_ce4
    · exact window_evalB vtPre_noRet hb hL 6693 1153 8131 (ceEx 5) vt_ce5
  · have hv : VtHoldsB S rd σ := ⟨kret, hb⟩
    have a0 := hv.atom 4333 (.mul (.n 4627) (.n 4624) (.n 3326)) (by decide +kernel)
    have a1 := hv.atom 4334 (.mul (.n 4628) (.n 4625) (.n 3705)) (by decide +kernel)
    have a2 := hv.atom 4335 (.add (.n 4629) (.n 4627) (.n 4628)) (by decide +kernel)
    have a3 := hv.atom 4336 (.mul (.n 4630) (.n 4626) (.n 4553)) (by decide +kernel)
    have a4 := hv.atom 4337 (.add (.n 4631) (.n 4629) (.n 4630)) (by decide +kernel)
    simp only [Atom.Holds] at a0 a1 a2 a3 a4
    rw [a4, a2, a0, a1, a3]

/-- **`air_acc`** (G:1812): with the table sumcheck's prefix products in `cprod` and `peq`, each
table's `constraint_eval` enters weighted by `cprod[n - τ]·peq[τ]`. -/
theorem vt_airB {rd : Reader} {σ : Val} (h : VtHoldsB S rd σ) {n : ℕ} (τ : ℕ → ℕ)
    (hτ : ∀ t < 6, τ t ≤ n) (hgn : σ (.n 4554) = gen ^ n)
    (htau : ∀ t < 6, σ (.n (airTau.getD t 0)) = gen ^ τ t) {cp pq : ℕ → E}
    (hcp : ∀ j ≤ n, LoadHolds rd (σ (.n 4639)) j (cp j))
    (hpq : ∀ k ≤ n, LoadHolds rd (σ (.n 4655)) k (pq k)) :
    ∀ t < 6, σ (.n (airAcc t)) = ((List.range (t + 1)).map fun s =>
      cp (n - τ s) * pq (τ s) * σ (.n (airCe.getD s 0))).sum := by
  have hterm : ∀ t < 6, σ (.n (airQ.getD t 0 + 6)) =
      cp (n - τ t) * pq (τ t) * σ (.n (airCe.getD t 0)) := by
    intro t ht
    obtain ⟨hb, -, -⟩ := air_blocks t ht
    obtain ⟨k, hb⟩ := h.slice _ _ hb (air_free t ht)
    simp only [airT, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hb
    obtain ⟨m0, m1, l2, m3, l4, m5, m6⟩ := hb
    rw [hgn, htau t ht] at m0
    have hq := gen_pow_cancel (hτ t ht) m0
    rw [m1, hq, loadHolds_gen_pow_mul, Nat.add_zero] at l2
    rw [m3, htau t ht, loadHolds_gen_pow_mul, Nat.add_zero] at l4
    rw [m6, m5, loadHolds_unique l2 (hcp _ (by omega)), loadHolds_unique l4 (hpq _ (hτ t ht))]
  intro t ht
  induction t with
  | zero => simpa [airAcc, airQ] using hterm 0 (by omega)
  | succ t ih =>
    obtain ⟨-, hadd, -⟩ := air_blocks (t + 1) ht
    have ha := h.atom' _ _ (hadd (by omega)) rfl
    simp only [Atom.Holds, Nat.add_sub_cancel] at ha
    rw [ha, ih (by omega), hterm (t + 1) ht, List.range_succ (n := t + 1), List.map_append,
      List.sum_append]
    simp

end
end LeanVM.Guest.B1.VerifySub
