/-
  LeanVM.Guest.B1.Tables.Vt.Shared

  `verify_tables`' selector tables: the index MLE's factors, `1 + ζ`, and each table's shared
  nibble tables over the bus point above its height.
-/

module

public import LeanVM.Guest.B1.Tables.Vt.Pads
public import LeanVM.Guest.B1.Tables.Squares
public import LeanVM.Guest.B1.Eq.PlusOne
public import LeanVM.Guest.B1.Selectors.SharedTables

/-!
# The selector tables (G:2012-2030)

* `vt_idxc`: `idxc_tab[g^t] = 1 + g^(2^t)`, `t < 34` (statements 2258-2325);
* `vt_zeta1`: `zeta1` holds `1 + ζ_k` for the bus point's `μ` coordinates (`plus_one_run`, 2327);
* `vt_shared`: table `t`'s run `μ - τ_t` long (`shared_len[t] = g^(μ - τ_t)`) has its nibble
  tables at `shared_eq·g^(288 t)`, `shared_g·g^(144 t)`, over the coordinates above `τ_t`, their
  complements and their shares (`shared_selector_tables`, 2330-2403).
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- `idxc_tab`'s stores. -/
def vtIdxcT : List Stmt :=
  ((List.range 34).map fun t ↦ [.atom (.const (.n (2733 + t))
    (word (tbGSquaresBits.getD t 0 ^^^ 1) 0 0)), .atom (.load (.n (2733 + t)) (.n 2732) t)]).flatten

theorem vtIdxc_check : tbStmtsEqb vtIdxcT ((vtPre.drop 2258).take vtIdxcT.length) = true := by
  simp only [vtPre_drop]; decide +kernel

theorem vtZeta1_check : tbStmtsEqb [.dispatch (.n 9) plusOneRunNames [.n 2767, .n 8] [.n 2768]]
    ((vtPre.drop 2327).take 1) = true := by
  simp only [vtPre_drop]; decide +kernel

/-- `g^(288 t)`'s and `g^(144 t)`'s words, `t ≤ 5`. -/
def vtShC1 : List ℕ := [1, 299140177199104, 116417108763, 12802355687494521950, 91479367452269810,
  6352872356067089515]
def vtShC2 : List ℕ := [1, 21299200, 299140177199104, 4977884963127958635, 116417108763,
  2137722311186776064]

theorem vtShC_eq : ∀ t < 6, K.ofBits (vtShC1.getD t 0) = Parameters.gpow (288 * t) ∧
    K.ofBits (vtShC2.getD t 0) = Parameters.gpow (144 * t) := by
  decide +kernel

/-- Table `t`'s shared tables, `t ≥ 1`, values from `v`. -/
def vtShT (v t : ℕ) : List Stmt :=
  [.atom (.load (.n v) (.n 10) (t + 1)), .atom (.mul (.n 9) (.n (v + 1)) (.n v)),
    .atom (.copy (.n (v + 2)) (.n (v + 1))), .atom (.const (.n (v + 3)) vtW33),
    .atom (.rangeCheck (.n (v + 2)) (.n (v + 4)) (.n (v + 5)) (.n (v + 6)) (.n (v + 3))),
    .atom (.const (.n (v + 7)) (word (vtShC1.getD t 0) 0 0)),
    .atom (.mul (.n (v + 8)) (.n 2769) (.n (v + 7))),
    .atom (.const (.n (v + 9)) (word (vtShC2.getD t 0) 0 0)),
    .atom (.mul (.n (v + 10)) (.n 2770) (.n (v + 9))),
    .atom (.mul (.n (v + 11)) (.n 8) (.n v)), .atom (.mul (.n (v + 12)) (.n 2767) (.n v)),
    .atom (.mul (.n (v + 13)) (.n 13) (.n v)),
    .call "shared_selector_tables" [.n (v + 8), .n (v + 10), .n (v + 11), .n (v + 12), .n (v + 13),
      .n (v + 2)] []]

/-- Table `0`'s, values from `2771`. -/
def vtSh0T : List Stmt :=
  [.atom (.load (.n 2771) (.n 10) 1), .atom (.mul (.n 9) (.n 2772) (.n 2771)),
    .atom (.copy (.n 2773) (.n 2772)), .atom (.const (.n 2774) vtW33),
    .atom (.rangeCheck (.n 2773) (.n 2775) (.n 2776) (.n 2777) (.n 2774)),
    .atom (.mul (.n 2778) (.n 8) (.n 2771)), .atom (.mul (.n 2779) (.n 2767) (.n 2771)),
    .atom (.mul (.n 2780) (.n 13) (.n 2771)),
    .call "shared_selector_tables" [.n 2769, .n 2770, .n 2778, .n 2779, .n 2780, .n 2773] []]

theorem vtSh0_check : tbStmtsEqb vtSh0T ((vtPre.drop 2330).take vtSh0T.length) = true := by
  simp only [vtPre_drop]; decide +kernel

theorem vtSh_check : ∀ t < 6, 1 ≤ t →
    tbStmtsEqb (vtShT (2781 + 14 * (t - 1)) t)
      ((vtPre.drop (2339 + 13 * (t - 1))).take (vtShT (2781 + 14 * (t - 1)) t).length) = true := by
  simp only [vtPre_drop]; decide +kernel

/-- Table `t`'s `shared_len` value. -/
def vtShLen (t : ℕ) : ℕ := if t = 0 then 2773 else 2781 + 14 * (t - 1) + 2

theorem vt_idxc {rd : Reader} {σ : Val} (h : VtH rd σ) :
    ∀ t < 34, LoadHolds rd (σ (.n 2732)) t (1 + gen ^ 2 ^ t) := by
  obtain ⟨k, hs⟩ := h.slice 2258 vtIdxcT vtIdxc_check
  rw [vtIdxcT, tb_holdsList_flatten_range _ _ (fun _ => rfl)] at hs
  intro t ht
  have := hs t ht
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at this
  obtain ⟨e1, e2⟩ := this
  rw [e1] at e2
  have e : word (tbGSquaresBits.getD t 0 ^^^ 1) 0 0 = 1 + gen ^ 2 ^ t := by
    rw [tb_word_eOfNat, eOfNat_xor, eOfNat_one, gen_pow_two_pow_eq ht, add_comm]
  rw [← e]
  exact e2

theorem vt_zeta1 {rd : Reader} {σ : Val} (h : VtH rd σ) {point : List E}
    (hz : TbReadsAt rd (σ (.n 8)) point) (hmu : σ (.n 9) = gen ^ point.length)
    (hml : point.length < 34) : TbReadsAt rd (σ (.n 2767)) (point.map (1 + ·)) := by
  obtain ⟨j, hj, hjv, hrel⟩ := h.dispatch 2327 _ _ _ _ vtZeta1_check
  have hj34 : j ≤ 33 := by simp [plusOneRunNames] at hj; omega
  rw [hmu, ← gen_pow_eq_ofK] at hjv
  obtain rfl : point.length = j := gen_pow_inj (by omega) (by omega) hjv
  have hm := (plus_one_run_holds _ hj34 rd _ _).mp
    (by rw [List.getD_eq_getElem _ _ hj]; exact hrel)
  simp only [List.map_cons, List.map_nil, MeaningPlusOneRun] at hm
  obtain ⟨⟨xs, hxl, hxs, hout⟩, -⟩ := hm
  obtain rfl := tbReadsAt_unique hxs hz hxl
  exact hout

theorem vtShC1_word {t : ℕ} (ht : t < 6) : word (vtShC1.getD t 0) 0 0 = gen ^ (288 * t) := by
  rw [tb_word_eOfNat, eOfNat, (vtShC_eq t ht).1, gen_pow_eq_ofK]

theorem vtShC2_word {t : ℕ} (ht : t < 6) : word (vtShC2.getD t 0) 0 0 = gen ^ (144 * t) := by
  rw [tb_word_eOfNat, eOfNat, (vtShC_eq t ht).2, gen_pow_eq_ofK]

theorem tbReadsAt_drop {rd : Reader} {p : E} {l : List E} (h : TbReadsAt rd p l) (a : ℕ) :
    TbReadsAt rd (p * gen ^ a) (l.drop a) := by
  rw [tbReadsAt_gen_pow_mul]
  intro k hk
  rw [List.getElem_drop]
  exact h _ _

theorem tbReadsAt_take {rd : Reader} {p : E} {l : List E} (h : TbReadsAt rd p l) (a : ℕ) :
    TbReadsAt rd p (l.take a) := fun k hk => by
  rw [List.getElem_take]; exact h _ _

/-- Table `t`'s `dims_g` value. -/
def vtShV (t : ℕ) : ℕ := if t = 0 then 2771 else 2781 + 14 * (t - 1)

theorem vt_shared_raw {μ : ℕ} (hμ : μ ≤ 32) (Lm : MemoryImage μ) {σ : Val} (h : VtH Lm.read σ)
    {t : ℕ} (ht : t < 6) :
    LoadHolds Lm.read (σ (.n 10)) (t + 1) (σ (.n (vtShV t))) ∧
      σ (.n 9) = σ (.n (vtShLen t)) * σ (.n (vtShV t)) ∧ (∃ d < 34, σ (.n (vtShLen t)) = gen ^ d) ∧
      coreProgram.Rel Lm.read "shared_selector_tables"
        [σ (.n 2769) * gen ^ (288 * t), σ (.n 2770) * gen ^ (144 * t), σ (.n 8) * σ (.n (vtShV t)),
          σ (.n 2767) * σ (.n (vtShV t)), σ (.n 13) * σ (.n (vtShV t)), σ (.n (vtShLen t))] [] := by
  rcases Nat.eq_zero_or_pos t with rfl | ht0
  · obtain ⟨k, hs⟩ := h.slice 2330 _ vtSh0_check
    simp only [vtSh0T, Stmt.HoldsList, Stmt.Holds, and_true, List.map_cons, List.map_nil] at hs
    obtain ⟨l0, m1, c2, c3, rc, mz, mz1, msq, hcall⟩ := hs
    simp only [Atom.Holds] at l0 m1 c2 c3 mz mz1 msq
    simp only [vtShV, vtShLen, ↓reduceIte, Nat.mul_zero, pow_zero, mul_one]
    refine ⟨l0, by rw [m1, c2], vt_rc hμ Lm (K := 34) (by omega) (by norm_num)
      (by rw [c3]; exact word_g33) rc, ?_⟩
    rw [← mz, ← mz1, ← msq]
    exact hcall
  · obtain ⟨k, hs⟩ := h.slice _ _ (vtSh_check t ht ht0)
    simp only [vtShT, Stmt.HoldsList, Stmt.Holds, and_true, List.map_cons, List.map_nil] at hs
    obtain ⟨l0, m1, c2, c3, rc, c7, m8, c9, m10, mz, mz1, msq, hcall⟩ := hs
    simp only [Atom.Holds] at l0 m1 c2 c3 c7 m8 c9 m10 mz mz1 msq
    have ev : vtShV t = 2781 + 14 * (t - 1) := by simp [vtShV, show t ≠ 0 by omega]
    have el : vtShLen t = 2781 + 14 * (t - 1) + 2 := by simp [vtShLen, show t ≠ 0 by omega]
    rw [ev, el]
    refine ⟨l0, by rw [m1, c2], vt_rc hμ Lm (K := 34) (by omega) (by norm_num)
      (by rw [c3]; exact word_g33) rc, ?_⟩
    rw [← vtShC1_word ht, ← vtShC2_word ht, ← c7, ← c9, ← m8, ← m10, ← mz, ← mz1, ← msq]
    exact hcall

/-- **Table `t`'s shared tables.** -/
theorem vt_shared {μ : ℕ} (hμ : μ ≤ 32) (Lm : MemoryImage μ) {σ : Val} (h : VtH Lm.read σ)
    {point : List E} (hz : TbReadsAt Lm.read (σ (.n 8)) point)
    (hmu : σ (.n 9) = gen ^ point.length) (hml : point.length < 33)
    (hz1 : TbReadsAt Lm.read (σ (.n 2767)) (point.map (1 + ·)))
    (hsq : TbReadsAt Lm.read (σ (.n 13)) gSquaresList)
    {t τ : ℕ} (ht : t < 6) (hτ : τ < 29) (hdim : LoadHolds Lm.read (σ (.n 10)) (t + 1) (gen ^ τ)) :
    ∃ d, σ (.n (vtShLen t)) = gen ^ d ∧ point.length = d + τ ∧
      RunTables Lm.read (σ (.n 2769) * gen ^ (288 * t)) (σ (.n 2770) * gen ^ (144 * t)) d
        (point.drop τ) ((point.map (1 + ·)).drop τ) ((gSquaresList.drop τ).take d) := by
  obtain ⟨l0, m1, ⟨d, hd, hdv⟩, hcall⟩ := vt_shared_raw hμ Lm h ht
  have ev := tb_loadHolds_unique l0 hdim
  rw [hmu, hdv, ev, ← pow_add] at m1
  have hμd := gen_pow_inj (by omega) (by omega) m1
  refine ⟨d, hdv, hμd, ?_⟩
  have hs := shared_selector_tables_holds _ _ _ hcall
  simp only [SharedSelOut] at hs
  obtain ⟨n, hn, hnv, hrun⟩ := hs
  rw [hdv] at hnv
  obtain rfl := gen_pow_inj (by omega) (by omega) hnv
  rw [ev] at hrun
  have hsql : gSquaresList.length = 34 := by simp [gSquaresList]
  exact hrun _ _ _ (by simp; omega) (by simp; omega) (by simp [hsql]; omega)
    (tbReadsAt_drop hz τ) (tbReadsAt_drop hz1 τ) (tbReadsAt_take (tbReadsAt_drop hsq τ) d)

end
end LeanVM.Guest.B1.Tables
