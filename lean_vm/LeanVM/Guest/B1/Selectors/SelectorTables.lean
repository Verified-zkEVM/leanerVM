/-
  LeanVM.Guest.B1.Selectors.SelectorTables

  B1 for `selector_tables`: it writes the opening point's eq tables over each nibble's top
  coordinates and the `g`-power shares of the nibbles' indices.
-/

module

public import LeanVM.Guest.B1.Selectors.ColumnSelector

/-!
# `selector_tables` (TRIAGE G #69)

`selector_tables(point, point1)` (G:3049-3073) allocates `sel_eq` (`7·30` words) and `sel_g`
(`7·16`), and for each nibble `j < 7` computes the eq levels over its top coordinates
`4j + 3, 4j + 2, …` (level `t` from level `t - 1`: entry `i` times `1 + r`, then times `r`) and
stores them at `sel_eq[30j ..]`, then stores the sixteen compile-time shares
`g^(Σ_t u_t 2^(4j+3-t))` at `sel_g[16j ..]`.

The body is `stPre ++ [ret]` (`stFound`, by kernel evaluation): nibble `j`'s values from
`4 + 52j` (`stNib`), level `t`'s entry `i` at value `stLv j t i`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The shares -/

/-- Share `u` of nibble `j`, in `K`: the product of `g^(2^(4j+3-t))` over the bits `t` of `u`,
each from the squares table. -/
def stShareK (j u : ℕ) : K :=
  ∏ t ∈ Finset.range 4, if u.testBit t then K.ofBits (tbGSquaresBits.getD (4 * j + 3 - t) 0) else 1

/-- The share's word. -/
def stShare (j u : ℕ) : ℕ := kToNat (stShareK j u)

theorem word_stShare {j u : ℕ} (hj : j < 7) (hu : u < 16) :
    word (stShare j u) 0 0 = (gTable (topShares j)).getD u 0 := by
  rw [gTable_getD (n := 4) (by simp [topShares]) hu, tb_word_eOfNat, stShare, eOfNat,
    ofBits_kToNat, stShareK]
  change (algebraMap K E) _ = _
  rw [map_prod (algebraMap K E)]
  refine Finset.prod_congr rfl fun t ht => ?_
  have ht' := Finset.mem_range.mp ht
  rw [bitPick, topShares_getD ht']
  split
  · rw [← eOfNat_tbGSquaresBits _ (by simp only [tbSizeBits]; omega)]; rfl
  · exact map_one (algebraMap K E)

/-! ## The template -/

/-- Nibble `j`'s first value. -/
def stB (j : ℕ) : ℕ := 4 + 52 * j

/-- Level `t ≥ 1`'s first product, past its two loads. -/
def stM (j t : ℕ) : ℕ := stB j + [0, 4, 10, 20].getD t 0

/-- The value of level `t`'s entry `i`. -/
def stLv (j t i : ℕ) : ℕ :=
  if t = 0 then stB j + i
  else if i < 2 ^ t then stM j t + 2 * i else stM j t + 2 * (i - 2 ^ t) + 1

/-- Level `t ≥ 1` of nibble `j`: the coordinate and its complement, then the products. -/
def stLevel (j t : ℕ) : List Stmt :=
  [.atom (.load (.n (stM j t - 2)) (.n 0) (4 * j + 3 - t)),
    .atom (.load (.n (stM j t - 1)) (.n 1) (4 * j + 3 - t))] ++
  ((List.range (2 ^ t)).map fun i ↦
    [.atom (.mul (.n (stM j t + 2 * i)) (.n (stLv j (t - 1) i)) (.n (stM j t - 1))),
      .atom (.mul (.n (stM j t + 2 * i + 1)) (.n (stLv j (t - 1) i)) (.n (stM j t - 2)))]).flatten

/-- The value of the eq levels' entry `e < 30`, level by level. -/
def stEq (j e : ℕ) : ℕ :=
  if e < 2 then stLv j 0 e else if e < 6 then stLv j 1 (e - 2) else if e < 14 then stLv j 2 (e - 6)
  else stLv j 3 (e - 14)

/-- Nibble `j`. -/
def stNib (j : ℕ) : List Stmt :=
  [.atom (.load (.n (stB j)) (.n 1) (4 * j + 3)), .atom (.load (.n (stB j + 1)) (.n 0) (4 * j + 3))] ++
    stLevel j 1 ++ stLevel j 2 ++ stLevel j 3 ++
    (List.range 30).map (fun e ↦ .atom (.load (.n (stEq j e)) (.n 2) (30 * j + e))) ++
    ((List.range 16).map fun u ↦
      [.atom (.const (.n (stB j + 36 + u)) (word (stShare j u) 0 0)),
        .atom (.load (.n (stB j + 36 + u)) (.n 3) (16 * j + u))]).flatten

/-- `selector_tables`'s statements before its `ret`. -/
def stPre : List Stmt :=
  [.atom (.hint (.alloc (.n 2) 210)), .atom (.hint (.alloc (.n 3) 112))] ++
    ((List.range 7).map stNib).flatten ++ [.atom (.copy (.n 368) (.n 2)), .atom (.copy (.n 369) (.n 3))]

/-- The function found by name is the template. -/
noncomputable def stCheck : Bool :=
  match coreProgram.find? "selector_tables" with
  | some fn => decide (fn.params = [.n 0, .n 1]) &&
      tbStmtsEqb fn.body (stPre ++ [.ret [.n 368, .n 369]])
  | none => false

theorem stCheck_eq : stCheck = true := by decide +kernel

theorem stFound : ∃ fn : Fn, coreProgram.find? "selector_tables" = some fn ∧
    fn.params = [.n 0, .n 1] ∧ fn.body = stPre ++ [.ret [.n 368, .n 369]] := by
  have h := stCheck_eq
  unfold stCheck at h
  split at h
  · rename_i fn hf
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨fn, hf, h.1, tbStmtsEqb_sound h.2⟩
  · exact absurd h (by simp)

theorem stLevel_noRet (j t : ℕ) : Stmt.noRetList (stLevel j t) = true := by
  rw [stLevel, tb_noRetList_append]
  simp only [Bool.and_eq_true]
  refine ⟨rfl, ?_⟩
  generalize 2 ^ t = m
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.flatten_append, tb_noRetList_append, ih]; rfl

theorem stShares_noRet (j : ℕ) : ∀ m : ℕ, Stmt.noRetList ((List.range m).map fun u ↦
    [Stmt.atom (.const (.n (stB j + 36 + u)) (word (stShare j u) 0 0)),
      Stmt.atom (.load (.n (stB j + 36 + u)) (.n 3) (16 * j + u))]).flatten = true
  | 0 => rfl
  | m + 1 => by
    rw [List.range_succ, List.map_append, List.flatten_append, tb_noRetList_append,
      stShares_noRet j m]; rfl

theorem stAtoms_noRet (n : ℕ) (f : ℕ → Atom) :
    Stmt.noRetList ((List.range n).map fun e ↦ Stmt.atom (f e)) = true := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.range_succ, List.map_append, tb_noRetList_append, ih]; rfl

theorem stNib_noRet (j : ℕ) : Stmt.noRetList (stNib j) = true := by
  simp only [stNib, tb_noRetList_append, stLevel_noRet, stShares_noRet, stAtoms_noRet]; rfl

theorem stPre_noRet : Stmt.noRetList stPre = true := by
  rw [stPre, tb_noRetList_append, tb_noRetList_append]
  have : Stmt.noRetList ((List.range 7).map stNib).flatten = true := by
    generalize 7 = m
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [List.range_succ, List.map_append, List.flatten_append, tb_noRetList_append, ih,
        List.map_singleton, List.flatten_singleton, stNib_noRet]; rfl
  rw [this]; rfl

section Sem

variable {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}

/-- What level `t ≥ 1` of nibble `j` gives: the coordinate, its complement, the products. -/
theorem holds_stLevel {j t : ℕ} (h : Stmt.HoldsList C rd σ (stLevel j t) True kret) :
    LoadHolds rd (σ (.n 0)) (4 * j + 3 - t) (σ (.n (stM j t - 2))) ∧
    LoadHolds rd (σ (.n 1)) (4 * j + 3 - t) (σ (.n (stM j t - 1))) ∧
    ∀ i < 2 ^ t, σ (.n (stM j t + 2 * i)) = σ (.n (stLv j (t - 1) i)) * σ (.n (stM j t - 1)) ∧
      σ (.n (stM j t + 2 * i + 1)) = σ (.n (stLv j (t - 1) i)) * σ (.n (stM j t - 2)) := by
  rw [stLevel, tb_holdsList_append_noRet rfl, tb_holdsList_flatten_range _ _ (fun _ => rfl)] at h
  obtain ⟨h1, h2⟩ := h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at h1
  refine ⟨h1.1, h1.2, fun i hi => ?_⟩
  have := h2 i hi
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at this
  exact this

/-- The parts of nibble `j`. -/
theorem holds_stNib {j : ℕ} (h : Stmt.HoldsList C rd σ (stNib j) True kret) :
    (LoadHolds rd (σ (.n 1)) (4 * j + 3) (σ (.n (stB j))) ∧
      LoadHolds rd (σ (.n 0)) (4 * j + 3) (σ (.n (stB j + 1)))) ∧
    Stmt.HoldsList C rd σ (stLevel j 1) True kret ∧ Stmt.HoldsList C rd σ (stLevel j 2) True kret ∧
    Stmt.HoldsList C rd σ (stLevel j 3) True kret ∧
    (∀ e < 30, LoadHolds rd (σ (.n 2)) (30 * j + e) (σ (.n (stEq j e)))) ∧
    (∀ u < 16, σ (.n (stB j + 36 + u)) = word (stShare j u) 0 0 ∧
      LoadHolds rd (σ (.n 3)) (16 * j + u) (σ (.n (stB j + 36 + u)))) := by
  have n0 : Stmt.noRetList [Stmt.atom (.load (.n (stB j)) (.n 1) (4 * j + 3)),
      Stmt.atom (.load (.n (stB j + 1)) (.n 0) (4 * j + 3))] = true := rfl
  rw [stNib, tb_holdsList_append_noRet (by simp only [tb_noRetList_append, stLevel_noRet,
      stAtoms_noRet, n0, Bool.and_self]),
    tb_holdsList_append_noRet (by simp only [tb_noRetList_append, stLevel_noRet, n0,
      Bool.and_self]),
    tb_holdsList_append_noRet (by simp only [tb_noRetList_append, stLevel_noRet, n0,
      Bool.and_self]),
    tb_holdsList_append_noRet (by simp only [tb_noRetList_append, stLevel_noRet, n0,
      Bool.and_self]),
    tb_holdsList_append_noRet n0, tb_holdsList_mapAtoms,
    tb_holdsList_flatten_range _ _ (fun _ => rfl)] at h
  obtain ⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩ := h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at h0 h5
  exact ⟨h0, h1, h2, h3, h4, h5⟩

/-- **The eq levels of nibble `j`**: level `t`'s entry `i` is the eq weight of `i`'s bits against
the coordinates `4j + 3, …, 4j + 3 - t`. -/
theorem stLevels {j : ℕ} (hj : j < 7) {p p1 : List E} (hp : p.length = 28) (hp1 : p1.length = 28)
    (hpt : TbReadsAt rd (σ (.n 0)) p) (hpt1 : TbReadsAt rd (σ (.n 1)) p1)
    (h : Stmt.HoldsList C rd σ (stNib j) True kret) :
    ∀ t < 4, ∀ i < 2 ^ (t + 1), σ (.n (stLv j t i)) = ∏ s ∈ Finset.range (t + 1),
      bitPick i s ((topNib p j).getD s 0) ((topNib p1 j).getD s 0) := by
  obtain ⟨⟨l0, l1⟩, hL1, hL2, hL3, -, -⟩ := holds_stNib h
  have hrd : ∀ (q : List E) (pq : E), q.length = 28 → TbReadsAt rd pq q → ∀ s < 4, ∀ w,
      LoadHolds rd pq (4 * j + 3 - s) w → w = (topNib q j).getD s 0 := fun q pq hq hr s hs w hw => by
    rw [topNib_getD hq hj hs]
    have := hr (4 * j + 3 - s) (by omega)
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact tb_loadHolds_unique hw this
  intro t ht
  induction t with
  | zero =>
    intro i hi
    have e0 := hrd p1 _ hp1 hpt1 0 (by omega) _ (by simpa using l0)
    have e1 := hrd p _ hp hpt 0 (by omega) _ (by simpa using l1)
    rw [Finset.prod_range_one]
    interval_cases i
    · simp only [stLv, ↓reduceIte, Nat.add_zero, bitPick, Nat.zero_testBit,
        Bool.false_eq_true, e0]
    · simp only [stLv, ↓reduceIte, bitPick, Nat.testBit_zero, e1]; rfl
  | succ t ih =>
    intro i hi
    have hL : Stmt.HoldsList C rd σ (stLevel j (t + 1)) True kret := by
      have ht3 : t < 3 := by omega
      interval_cases t
      · exact hL1
      · exact hL2
      · exact hL3
    obtain ⟨hz, hz1, hm⟩ := holds_stLevel hL
    have ez := hrd p _ hp hpt (t + 1) ht _ hz
    have ez1 := hrd p1 _ hp1 hpt1 (t + 1) ht _ hz1
    rw [Finset.prod_range_succ]
    by_cases hlo : i < 2 ^ (t + 1)
    · obtain ⟨h1, -⟩ := hm i hlo
      have hv : stLv j (t + 1) i = stM j (t + 1) + 2 * i := by
        simp only [stLv, Nat.succ_ne_zero, ↓reduceIte, hlo]
      rw [hv, h1, Nat.add_sub_cancel, ih (by omega) i hlo, ez1, bitPick,
        testBit_lt_two_pow hlo]
      rfl
    · obtain ⟨v, rfl⟩ : ∃ v, i = 2 ^ (t + 1) + v := ⟨i - 2 ^ (t + 1), by omega⟩
      have hv' : v < 2 ^ (t + 1) := by rw [pow_succ 2 (t + 1)] at hi; omega
      obtain ⟨-, h2⟩ := hm v hv'
      have hv : stLv j (t + 1) (2 ^ (t + 1) + v) = stM j (t + 1) + 2 * v + 1 := by
        simp only [stLv, Nat.succ_ne_zero, ↓reduceIte, hlo, Nat.add_sub_cancel_left]
      rw [hv, h2, Nat.add_sub_cancel, ih (by omega) v hv', ez, bitPick,
        testBit_two_pow_add_self hv']
      simp only [↓reduceIte]
      exact congrArg (· * _) (Finset.prod_congr rfl fun s hs => by
        simp only [bitPick, testBit_two_pow_add hv' (Finset.mem_range.mp hs)])

end Sem

theorem topNib_length {p : List E} (hp : p.length = 28) {j : ℕ} (hj : j < 7) :
    (topNib p j).length = 4 := by
  simp [topNib, nib, hp]; omega

/-- **`selector_tables` is sound**: for the point and its complements read at its arguments, the
returned buffers hold their eq tables and the `g`-power tables. -/
theorem selector_tables_sound {rd : Reader} {args rets : List E}
    (h : coreProgram.Rel rd "selector_tables" args rets) : SelTablesOut rd args rets := by
  obtain ⟨fn, hf, hp, hb⟩ := stFound
  obtain ⟨σ, hpar, hpre, hret⟩ := (tb_rel_pre hf hb stPre_noRet args rets).mp h
  rw [hp] at hpar
  simp only [List.map_cons, List.map_nil] at hpar hret
  subst hpar hret
  have hnr : Stmt.noRetList ([Stmt.atom (.hint (.alloc (.n 2) 210)),
      Stmt.atom (.hint (.alloc (.n 3) 112))] ++ ((List.range 7).map stNib).flatten) = true := by
    have := stPre_noRet
    rw [stPre, tb_noRetList_append] at this
    simp only [Bool.and_eq_true] at this
    exact this.1
  rw [stPre, tb_holdsList_append_noRet hnr, tb_holdsList_append_noRet rfl,
    tb_holdsList_flatten_range _ _ stNib_noRet] at hpre
  obtain ⟨⟨-, hnibs⟩, hcopy⟩ := hpre
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hcopy
  simp only [SelTablesOut]
  intro p p1 hp hp1 hpt hpt1
  refine ⟨fun j hj => ?_, fun j hj => ?_⟩
  · have hN := hnibs j hj
    have hlev := stLevels hj hp hp1 hpt hpt1 hN
    obtain ⟨-, -, -, -, heq, -⟩ := holds_stNib hN
    have hl := topNib_length hp hj
    have hl1 := topNib_length hp1 hj
    intro e he
    have he' : e < 30 := by rw [eqLevels_length hl hl1] at he; simpa using he
    have hval : σ (.n (stEq j e)) = (eqLevels (topNib p j) (topNib p1 j)).getD e 0 := by
      obtain ⟨t, i, ht, hi, hei, hst⟩ : ∃ t i, t < 4 ∧ i < 2 ^ (t + 1) ∧
          e = 2 ^ (t + 1) - 2 + i ∧ stEq j e = stLv j t i := by
        by_cases e2 : e < 2
        · exact ⟨0, e, by omega, by simpa using e2, by simp, by simp [stEq, e2]⟩
        by_cases e6 : e < 6
        · exact ⟨1, e - 2, by omega, by simp; omega, by simp; omega, by simp [stEq, e2, e6]⟩
        by_cases e14 : e < 14
        · exact ⟨2, e - 6, by omega, by simp; omega, by simp; omega, by simp [stEq, e2, e6, e14]⟩
        · exact ⟨3, e - 14, by omega, by simp; omega, by simp; omega, by simp [stEq, e2, e6, e14]⟩
      rw [hst, hlev t ht i hi, hei, eqLevels_getD (hl.trans hl1.symm) (by omega) (by omega) hi]
    rw [hcopy.1, tb_loadHolds_mul_gen_pow, ← List.getD_eq_getElem _ _ he, ← hval]
    exact heq e he'
  · obtain ⟨-, -, -, -, -, hsh⟩ := holds_stNib (hnibs j hj)
    intro u hu
    have hu' : u < 16 := by rw [gTable_length (n := 4) (by simp [topShares])] at hu; simpa using hu
    obtain ⟨h1, h2⟩ := hsh u hu'
    rw [hcopy.2, tb_loadHolds_mul_gen_pow, ← List.getD_eq_getElem _ _ hu, ← word_stShare hj hu',
      ← h1]
    exact h2

theorem selector_tables_holds : selector_tables_Spec := fun _ _ _ h => selector_tables_sound h

end
end LeanVM.Guest.B1.Tables
