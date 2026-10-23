/-
  LeanVM.Guest.B1.VerifySub.Mid

  `verify_sub`'s sizes, `block_kappa` and the push side's total (G:3189-3211).
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

/-- **The sizes** (G:3189-3200): the rate exponent and the memory's log-size, `dims`, and
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

/-- **`block_kappa`** (G:3201-3205): block `b`'s `g^κ`, over `kappa_base`. -/
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

end
end LeanVM.Guest.B1.VerifySub
