/-
  LeanVM.Guest.B1.VerifySub.Mid

  `verify_sub`'s sizes, `block_kappa` and the push side's total (G:3182-3204).
-/

module

public import LeanVM.Guest.B1.VerifySub.Template
public import LeanVM.Guest.B1.VerifySub.Sizes
public import LeanVM.Guest.B1.Bits.GPower
public import LeanVM.Guest.B1.Bits.Log2

/-!
# The sizes, `block_kappa`, the push total

* `vsSizesT_holds`: the rate exponent `lir ∈ [1, 4]` and the memory's log-size
  `logMem ∈ [16, 32]` as `g`-powers (`g_power_of_word`, range checks), `dims` stored after
  `g^logMem`, and `kappa_base = [1, g^logMem, dims…]`.
* `vsKappaT_holds`: `block_kappa` is `blockKappaWords` of `kappa_base`.
* `vsPushT_holds`: the push blocks' product of `g_squares[κ_b]` is `g^Σ 2^κ_b`, and the bus depth is
  `g^(log2Ceil Σ)`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val} {next : Prop} {kret : List E → Prop}

/-! ## Range checks on `g`-powers -/

/-- A range check against `g^a` (`a ≤ 32`): the value is `g^e`, `e ≤ a`. -/
theorem rc_pow {κ : ℕ} (hκ : κ ≤ 32) (hκ6 : 6 ≤ κ) (L : MemImage κ) {x y t1 t2 k : V} {a : ℕ}
    (ha : a ≤ 32) (hk : σ k = gen ^ a) (h : (Atom.rangeCheck x y t1 t2 k).Holds L.read σ) :
    ∃ e ≤ a, σ x = gen ^ e := by
  obtain ⟨l1, m, l2⟩ := h
  have hK : a + 1 ≤ 2 ^ κ :=
    calc a + 1 ≤ 2 ^ 6 := by omega
      _ ≤ 2 ^ κ := Nat.pow_le_pow_right (by norm_num) hκ6
  obtain ⟨e, he, hx⟩ := (rangeCheck_iff hκ L (σ x) (K := a + 1) (by omega) hK).1
    ⟨σ y, σ t1, σ t2, l1, by rw [show a + 1 - 1 = a by omega, ← gen_pow_eq_ofK, ← hk, m], l2⟩
  exact ⟨e, by omega, by rw [hx, gen_pow_eq_ofK]⟩

theorem gen_pow_eq_iff {a b : ℕ} (ha : a < 2 ^ 40) (hb : b < 2 ^ 40) (h : gen ^ a = gen ^ b) :
    a = b :=
  gen_pow_inj (by omega) (by omega) h

theorem word_pow2 {a : ℕ} (h : a < 64) : word (2 ^ a) 0 0 = gen ^ a := word_two_pow h

/-! ## The sizes -/

/-- **The sizes** (G:3182-3193): the rate exponent and the memory's log-size, `dims`, and
`kappa_base`. -/
theorem vsSizesT_holds {κ : ℕ} (hκ : κ ≤ 32) (hκ6 : 6 ≤ κ) (L : MemImage κ)
    (hC : CallRel.Le C (coreProgram.Rel L.read))
    (h : Stmt.HoldsList C L.read σ vsSizesT next kret) :
    ∃ lir logMem : ℕ, 1 ≤ lir ∧ lir ≤ 4 ∧ σ (.n 112) = eOfNat lir ∧ σ (.n 124) = gen ^ (lir - 1) ∧
      16 ≤ logMem ∧ logMem ≤ 32 ∧ σ (.n 29) = eOfNat logMem ∧ σ (.n 130) = gen ^ logMem ∧
      ∃ ds : List E, ds.length = 6 ∧ ReadsAt L.read (σ (.n 129)) (gen ^ logMem :: ds) ∧
        ReadsAt L.read (σ (.n 141)) (1 :: gen ^ logMem :: ds) ∧ next := by
  rw [vsSizesT, show (List.range 6) = [0, 1, 2, 3, 4, 5] from rfl] at h
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.cons_append,
    List.nil_append, Stmt.HoldsList, Stmt.Holds, vsCall, vsConst, vsMul, vsRange, vsAlloc, vsLd,
    List.map_cons, List.map_nil, Atom.Holds, true_and] at h
  obtain ⟨c112, e123, m122, e125, r124, c29, e131, r130, e135, e136, m130, r137, l130, e142,
    l142, l130', l0, l0', l1, l1', l2, l2', l3, l3', l4, l4', l5, l5', hn⟩ := h
  -- the rate
  obtain ⟨n, hn64, h112, hr122⟩ := (g_power_of_word_holds _ _ _).1 (hC _ _ _ c112)
  simp only [List.cons.injEq, and_true] at hr122
  obtain ⟨e, he, h124⟩ := rc_pow hκ hκ6 L (a := 3) (by norm_num)
    (by rw [e125, show (8 : ℕ) = 2 ^ 3 from rfl, word_pow2 (by norm_num)]) r124
  have hne : n = e + 1 := by
    rw [hr122, h124, e123, word_gen, ← pow_succ] at m122
    exact gen_pow_eq_iff (by omega) (by omega) m122
  -- the memory's log-size
  obtain ⟨m, hm64, h29, hr130⟩ := (g_power_of_word_holds _ _ _).1 (hC _ _ _ c29)
  simp only [List.cons.injEq, and_true] at hr130
  obtain ⟨e1, he1, h130⟩ := rc_pow hκ hκ6 L (a := 32) le_rfl
    (by rw [e131, word_pow2 (by norm_num)]) r130
  obtain ⟨e2, he2, h137⟩ := rc_pow hκ hκ6 L (a := 32) le_rfl
    (by rw [e135, word_pow2 (by norm_num)]) r137
  have hm1 : m = e1 := by rw [hr130] at h130; exact gen_pow_eq_iff (by omega) (by omega) h130
  have hm2 : m = e2 + 16 := by
    rw [hr130, h137, e136, show (65536 : ℕ) = 2 ^ 16 from rfl, word_pow2 (by norm_num),
      ← pow_add] at m130
    exact gen_pow_eq_iff (by omega) (by omega) m130
  refine ⟨n, m, by omega, by omega, h112, by rw [h124, hne]; rfl, by omega, by omega, h29, hr130,
    [σ (.n 143), σ (.n 144), σ (.n 145), σ (.n 146), σ (.n 147), σ (.n 148)], rfl, ?_, ?_, hn⟩
  · intro k hk
    simp only [List.length_cons, List.length_nil] at hk
    interval_cases k
    · simp only [List.getElem_cons_zero]; rw [← hr130]; exact l130
    · exact l0
    · exact l1
    · exact l2
    · exact l3
    · exact l4
    · exact l5
  · intro k hk
    simp only [List.length_cons, List.length_nil] at hk
    interval_cases k
    · simp only [List.getElem_cons_zero]
      rw [show (1 : E) = σ (.n 142) by rw [e142, word_one]]; exact l142
    · simp only [List.getElem_cons_succ, List.getElem_cons_zero]; rw [← hr130]; exact l130'
    · exact l0'
    · exact l1'
    · exact l2'
    · exact l3'
    · exact l4'
    · exact l5'

/-! ## `block_kappa` -/

theorem blockKappaSrc_lt : ∀ b < Tables.nBlocks, Tables.blockKappaSrc.getD b 0 < 8 := by
  decide +kernel

theorem vsKappaStep_holds {g : E} {ds : List E} (hds : ds.length = 6)
    (hkb : ReadsAt rd (σ (.n 141)) (1 :: g :: ds)) {b : ℕ} (hb : b < Tables.nBlocks)
    {nx : Prop} (h : Stmt.HoldsList C rd σ (vsKappaStep b) nx kret) :
    LoadHolds rd (σ (.n 149)) b
      ((1 :: g :: ds).getD (Tables.blockKappaSrc.getD b 0) 0 * gen ^ Tables.blockKappaAdj b) ∧ nx := by
  have hs := blockKappaSrc_lt b hb
  have hsrc : LoadHolds rd (σ (.n 141)) (Tables.blockKappaSrc.getD b 0)
      ((1 :: g :: ds).getD (Tables.blockKappaSrc.getD b 0) 0) := by
    rw [List.getD_eq_getElem (1 :: g :: ds) _ (by simp only [List.length_cons, hds]; omega)]
    exact hkb _ _
  unfold vsKappaStep at h
  split at h
  · rename_i h0
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, vsLd] at h
    obtain ⟨l1, l2, hn⟩ := h
    rw [h0, pow_zero, mul_one, ← loadHolds_unique l1 hsrc]
    exact ⟨l2, hn⟩
  · rename_i h0
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, vsLd, vsConst, vsMul] at h
    obtain ⟨l1, c, m, l2, hn⟩ := h
    have hadj : Tables.blockKappaAdj b = 19 := by
      unfold Tables.blockKappaAdj at h0 ⊢; split <;> simp_all
    rw [hadj, ← loadHolds_unique l1 hsrc, ← word_pow2 (by norm_num), ← c, ← m]
    exact ⟨l2, hn⟩

theorem kappa_loop {g : E} {ds : List E} (hds : ds.length = 6)
    (hkb : ReadsAt rd (σ (.n 141)) (1 :: g :: ds)) :
    ∀ (l : List ℕ), (∀ b ∈ l, b < Tables.nBlocks) → ∀ {nx : Prop},
      Stmt.HoldsList C rd σ (l.flatMap vsKappaStep) nx kret →
      (∀ b ∈ l, LoadHolds rd (σ (.n 149)) b
        ((1 :: g :: ds).getD (Tables.blockKappaSrc.getD b 0) 0 * gen ^ Tables.blockKappaAdj b)) ∧ nx
  | [], _, _, h => ⟨fun _ hb ↦ absurd hb (by simp), h⟩
  | b :: l, hl, _, h => by
    rw [List.flatMap_cons, holdsList_append] at h
    obtain ⟨hb, h⟩ := vsKappaStep_holds hds hkb (hl b (List.mem_cons_self ..)) h
    obtain ⟨hr, h⟩ := kappa_loop hds hkb l (fun x hx ↦ hl x (List.mem_cons_of_mem _ hx)) h
    refine ⟨fun x hx ↦ ?_, h⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · exact hb
    · exact hr x hx

/-- **`block_kappa`** (G:3194-3198): block `b`'s `g^κ`, over `kappa_base`. -/
theorem vsKappaT_holds {g : E} {ds : List E} (hds : ds.length = 6)
    (hkb : ReadsAt rd (σ (.n 141)) (1 :: g :: ds))
    (h : Stmt.HoldsList C rd σ vsKappaT next kret) :
    ReadsAt rd (σ (.n 149)) (Tables.blockKappaWords g ds) ∧ next := by
  unfold vsKappaT at h
  simp only [Stmt.HoldsList, Stmt.Holds, vsAlloc, Atom.Holds, true_and] at h
  obtain ⟨hr, hn⟩ := kappa_loop hds hkb _ (fun b hb ↦ List.mem_range.1 hb) h
  refine ⟨fun b hb ↦ ?_, hn⟩
  have hb' : b < Tables.nBlocks := by simpa [Tables.blockKappaWords] using hb
  simp only [Tables.blockKappaWords, List.getElem_map, List.getElem_range]
  exact hr b (List.mem_range.2 hb')

/-! ## The push total -/

theorem kbase_getD {logMem : ℕ} {hs : List ℕ} (hl : hs.length = 6) {i : ℕ} (hi : i < 8) :
    (1 :: gen ^ logMem :: hs.map (gen ^ ·)).getD i 0 = gen ^ (([0, logMem] ++ hs).getD i 0) := by
  match hs, hl with
  | [h0, h1, h2, h3, h4, h5], _ => interval_cases i <;> simp

theorem bkw_getD {logMem : ℕ} {hs : List ℕ} (hl : hs.length = 6) {b : ℕ} (hb : b < Tables.nBlocks) :
    (Tables.blockKappaWords (gen ^ logMem) (hs.map (gen ^ ·))).getD b 0 =
      gen ^ pushKappa logMem hs b := by
  rw [Tables.blockKappaWords, List.getD_eq_getElem _ _ (by simpa using hb), List.getElem_map,
    List.getElem_range, kbase_getD hl (blockKappaSrc_lt b hb), ← pow_add]
  rfl

theorem kbase_le {logMem : ℕ} {hs : List ℕ} (hh : ∀ x ∈ hs, x < 29) (hm : logMem ≤ 32) (s : ℕ) :
    ([0, logMem] ++ hs).getD s 0 ≤ 32 := by
  rw [List.getD_eq_getElem?_getD]
  rcases hx : ([0, logMem] ++ hs)[s]? with _ | x
  · simp
  · have hmem := List.mem_of_getElem? hx
    simp only [List.cons_append, List.mem_cons, List.nil_append] at hmem
    simp only [Option.getD_some]
    rcases hmem with rfl | rfl | hmem
    · omega
    · exact hm
    · have := hh x hmem; omega

theorem push_adj : ∀ b < 54, Tables.blockKappaAdj b ≠ 0 → Tables.blockKappaSrc.getD b 0 = 0 := by
  decide +kernel

theorem pushKappa_lt {logMem : ℕ} {hs : List ℕ} (hh : ∀ x ∈ hs, x < 29) (hm : logMem ≤ 32)
    {b : ℕ} (hb : b < 54) : pushKappa logMem hs b < 34 := by
  unfold pushKappa
  by_cases h0 : Tables.blockKappaAdj b = 0
  · have := kbase_le hh hm (Tables.blockKappaSrc.getD b 0); omega
  · rw [push_adj b hb h0]
    have : Tables.blockKappaAdj b ≤ 19 := by unfold Tables.blockKappaAdj; split <;> omega
    simp only [List.cons_append, List.getD_cons_zero]
    omega

/-- One push block: `g_squares[κ_b] = g^(2^κ_b)` read through `block_kappa[b] = g^κ_b`. -/
theorem push_read {κ : ℕ} {L : MemImage κ} (hexp : B1.ExpTables L.read (σ (.n 4)) (σ (.n 5)))
    {kb q : V} {k : ℕ} (hk : k < 34) (hkb : σ kb = gen ^ k) {a : V} (ha : σ a = σ (.n 5) * σ kb)
    (hq : LoadHolds L.read (σ a) 0 (σ q)) : σ q = gen ^ 2 ^ k := by
  rw [ha, hkb, loadHolds_mul_gen_pow, add_zero] at hq
  exact loadHolds_unique hq (hexp k hk).2

theorem push_loop {κ : ℕ} {L : MemImage κ} (hexp : B1.ExpTables L.read (σ (.n 4)) (σ (.n 5)))
    {logMem : ℕ} {hs : List ℕ} (hl : hs.length = 6) (hh : ∀ x ∈ hs, x < 29) (hm : logMem ≤ 32)
    (hbk : ReadsAt L.read (σ (.n 149)) (Tables.blockKappaWords (gen ^ logMem) (hs.map (gen ^ ·)))) :
    ∀ n < 54, ∀ {nx : Prop},
      Stmt.HoldsList C L.read σ ((List.range (n + 1)).flatMap vsPushStep) nx kret →
      σ (.n (vsPV n)) = gen ^ ((List.range (n + 1)).map fun b ↦ 2 ^ pushKappa logMem hs b).sum ∧ nx := by
  have hkw : ∀ b < 54, ∀ v, LoadHolds L.read (σ (.n 149)) b v → v = gen ^ pushKappa logMem hs b := by
    intro b hb v hv
    have hb' : b < (Tables.blockKappaWords (gen ^ logMem) (hs.map (gen ^ ·))).length := by
      simp only [Tables.blockKappaWords, List.length_map, List.length_range]; show b < 153; omega
    rw [loadHolds_unique hv (hbk b hb'), ← List.getD_eq_getElem _ 0 hb',
      bkw_getD hl (by show b < 153; omega)]
  intro n
  induction n with
  | zero =>
    intro _ nx h
    rw [show List.range (0 + 1) = [0] from rfl] at h
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, vsPushStep,
      ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds, vsLd, vsMul] at h
    obtain ⟨l1, m, l2, hn⟩ := h
    refine ⟨?_, hn⟩
    rw [show vsPV 0 = 309 from rfl,
      push_read hexp (pushKappa_lt hh hm (by norm_num)) (hkw 0 (by norm_num) _ l1) m l2]
    simp
  | succ n ih =>
    intro hn nx h
    rw [List.range_succ, List.flatMap_append, holdsList_append] at h
    obtain ⟨hp, h⟩ := ih (by omega) h
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, vsPushStep,
      Nat.add_one_ne_zero, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds, vsLd, vsMul] at h
    obtain ⟨l1, m, l2, m2, hn'⟩ := h
    refine ⟨?_, hn'⟩
    rw [m2, Nat.add_sub_cancel, hp,
      push_read hexp (pushKappa_lt hh hm hn) (hkw (n + 1) hn _ l1) m l2, ← pow_add,
      List.range_succ (n := n + 1), List.map_append, List.sum_append]
    simp

theorem push_sum_lt {logMem : ℕ} {hs : List ℕ} (hh : ∀ x ∈ hs, x < 29) (hm : logMem ≤ 32) :
    ((List.range 54).map fun b ↦ 2 ^ pushKappa logMem hs b).sum < 2 ^ 40 := by
  have hle := List.sum_le_length_nsmul ((List.range 54).map fun b ↦ 2 ^ pushKappa logMem hs b)
    (2 ^ 33) (by
      intro x hx
      obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hx
      exact Nat.pow_le_pow_right (by norm_num)
        (by have := pushKappa_lt hh hm (List.mem_range.1 hb); omega))
  simp only [List.length_map, List.length_range, smul_eq_mul] at hle
  omega

/-- **The push total** (G:3199-3204): the bus depth `g^(log2Ceil Σ)` over the push blocks'
`Σ 2^κ_b`. -/
theorem vsPushT_holds {κ : ℕ} (hκ : κ ≤ 32) (hκ6 : 6 ≤ κ) (L : MemImage κ)
    (hC : CallRel.Le C (coreProgram.Rel L.read)) (hexp : B1.ExpTables L.read (σ (.n 4)) (σ (.n 5)))
    {logMem : ℕ} {hs : List ℕ} (hl : hs.length = 6) (hh : ∀ x ∈ hs, x < 29) (hm : logMem ≤ 32)
    (hbk : ReadsAt L.read (σ (.n 149)) (Tables.blockKappaWords (gen ^ logMem) (hs.map (gen ^ ·))))
    (h : Stmt.HoldsList C L.read σ vsPushT next kret) :
    σ (.n 522) = gen ^ log2Ceil ((List.range 54).map fun b ↦ 2 ^ pushKappa logMem hs b).sum ∧
      log2Ceil ((List.range 54).map fun b ↦ 2 ^ pushKappa logMem hs b).sum < 34 ∧ next := by
  unfold vsPushT at h
  rw [holdsList_append] at h
  obtain ⟨hp, h⟩ := push_loop hexp hl hh hm hbk 53 (by norm_num) h
  simp only [Stmt.HoldsList, Stmt.Holds, vsCall, List.map_cons, List.map_nil, Atom.Holds,
    true_and] at h
  obtain ⟨hc, hn⟩ := h
  obtain ⟨N, hN, hgN, hlt, -, -, hr⟩ :=
    (log2_ceil_in_the_exponent_L0_L34_iff hκ hκ6 L hexp _).1 (hC _ _ _ hc)
  rw [show vsPV 53 = 521 from rfl] at hp
  have hS : ((List.range 54).map fun b ↦ 2 ^ pushKappa logMem hs b).sum = N :=
    gen_pow_eq_iff (push_sum_lt hh hm) (by omega) (hp.symm.trans hgN)
  simp only [List.cons.injEq, and_true, Nat.zero_max] at hr hlt
  exact ⟨by rw [hr, hS], by rw [hS]; exact hlt, hn⟩

end
end LeanVM.Guest.B1.VerifySub
