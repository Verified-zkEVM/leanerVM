module

public import LeanVM.Cost.Bounds.Guest.Readers
public import LeanVM.Cost.Decoder.Signatures

/-!
# Bounds on the guest decoder's prices: the signatures

The readers of a leanSPHINCS signature off its check's valuations, off the readers' tables as
arrays (`Cost/Decoder/Signatures.lean`: `sphincsSigOfNC` is `sphincsSigOfA`,
`Guest/Fast/Sphincs.lean`; leanXMSS's in `Xmss.lean`), in the price `S` of an application of a
valuation: a signature has a fixed shape, so its price is `a·S + b`:

* the tables' facts (`gLanes_ok`, `spTabs_lits_ok`, … by kernel evaluation of the literals), and
  of the arrays built from them (`SpTabsOK`: `spTabs_ok`), an entry read in constant time
  (`offAtA`: `8`);
* an exponent off the lanes of `g^k` given (`idxBelow_cost`, `logGTWith_cost`: `23·bound + 25`),
  a sibling (`sibN_cost`), a chain's start cell (`cwCellA_cost`: `S + 1543`);
* leanSPHINCS, its four valuations (`verify_sig_lean_sphincs`' and the three `sp_wots` frames)
  each of price at most `S`: `forsOpeningA_cost` (`41·S + 1300`), `layerA_cost`
  (`169·S + 104200`), **`sphincsSigOfA_cost`**: `1492·S + 345000`; the words of a layer's call of
  `sp_wots` (`spWotsArgs_cost`, `spWotsRets_cost`), by which the decoder finds its frame.
-/

namespace LeanVM.Cost.Bounds.Guest

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.Library LeanVM.Parameters
open LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.Fast

public section

variable (P : MachineProgram)

/-! ## Tables -/

/-- A table's rows: at most `M` entries, each below `2^20`. -/
@[expose] def RowsOK (M : ℕ) (tab : List (List ℕ)) : Prop :=
  ∀ r ∈ tab, r.length ≤ M ∧ ∀ x ∈ r, x < 2 ^ 20

instance (M : ℕ) (tab : List (List ℕ)) : Decidable (RowsOK M tab) := by
  unfold RowsOK; infer_instance

/-- A list of at most `M` entries, each below `2^20`. -/
@[expose] def ListOK (M : ℕ) (l : List ℕ) : Prop := l.length ≤ M ∧ ∀ x ∈ l, x < 2 ^ 20

instance (M : ℕ) (l : List ℕ) : Decidable (ListOK M l) := by
  unfold ListOK; infer_instance

theorem gLanes_ok : gLanes.length = 256 ∧ ∀ x ∈ gLanes, x < 2 ^ 64 := by decide +kernel

theorem spTabs_lits_ok : RowsOK 64 spFirst ∧ RowsOK 64 spRest ∧ RowsOK 64 spLast ∧
    spFirst.length ≤ 3 ∧ spRest.length ≤ 3 ∧ spLast.length ≤ 1 ∧ ListOK 22 spSel := by
  decide +kernel

theorem getD_lt_of {l : List ℕ} {B : ℕ} (h : ∀ x ∈ l, x < B) (hB : 0 < B) (k : ℕ) :
    l.getD k 0 < B := by
  rw [List.getD_eq_getElem?_getD]
  cases hk : l[k]? with
  | none => simpa using hB
  | some x => exact h x (List.mem_of_getElem? hk)

theorem getD_row {tab : List (List ℕ)} {M : ℕ} (h : RowsOK M tab) (r : ℕ) :
    (tab.getD r []).length ≤ M ∧ ∀ x ∈ tab.getD r [], x < 2 ^ 20 := by
  rw [List.getD_eq_getElem?_getD]
  cases hk : tab[r]? with
  | none => simp
  | some x => exact h x (List.mem_of_getElem? hk)

theorem offAt_lt {tab : List (List ℕ)} {M : ℕ} (h : RowsOK M tab) (r k : ℕ) :
    offAt tab r k < 2 ^ 20 :=
  getD_lt_of (getD_row h r).2 (by norm_num) k

/-! ## The tables as arrays -/

theorem offAtA_tabA_lt {tab : List (List ℕ)} {M : ℕ} (h : RowsOK M tab) (r k : ℕ) :
    offAtA (tabA tab) r k < 2 ^ 20 := by
  rw [offAtA_tabA]; exact offAt_lt h r k

theorem getD_toArray_lt {l : List ℕ} {M : ℕ} (h : ListOK M l) (k : ℕ) :
    l.toArray.getD k 0 < 2 ^ 20 := by
  rw [getD_toArray]; exact getD_lt_of h.2 (by norm_num) k

/-- `sp_wots`' tables as arrays, their entries small (`spTabs_ok`). -/
structure SpTabsOK (T : SpTabs) : Prop where
  lanes : ∀ x ∈ T.lanes, x < 2 ^ 64
  sel : ∀ k, T.sel.getD k 0 < 2 ^ 20
  first : ∀ r k, offAtA T.first r k < 2 ^ 20
  rest : ∀ r k, offAtA T.rest r k < 2 ^ 20
  last : ∀ r k, offAtA T.last r k < 2 ^ 20

theorem spTabs_ok : SpTabsOK spTabs := by
  obtain ⟨h1, h2, h3, -, -, -, hsel⟩ := spTabs_lits_ok
  exact ⟨gLanes_ok.2, getD_toArray_lt hsel, offAtA_tabA_lt h1, offAtA_tabA_lt h2,
    offAtA_tabA_lt h3⟩

/-- A table of rows as arrays (`tabAC`), its rows at most `M` entries: at most
`(M + 15)·rows + rows + 7`. -/
theorem tabA_cost (hP : Includes P Decoder.tabAC.costDeps) (t : List (List ℕ)) (M : ℕ)
    (hM : ∀ r ∈ t, r.length ≤ M) :
    machineCost P Decoder.tabAC.costIdx [encodeValue t] ≤ (M + 15) * t.length + t.length + 7 := by
  rw [Decoder.tabAC.costEq P hP, List.length_map]
  have := map_cost P (by includes) List.toArray (.closure Decoder.tabAC.lam0.costIdx [])
    (fun xs ↦ RunsApp.of_spec (Decoder.tabAC.lam0.costSpec P (by includes) xs)) (M + 2) t
    (fun r hr ↦ by
      rw [appCost_fn, List.nil_append, Decoder.tabAC.lam0.costEq P (by includes), List.length_nil]
      have := hM r hr; omega)
  rw [show M + 2 + 13 = M + 15 by omega] at this
  omega

/-- **`sp_wots`' tables, built** (`spTabsC`): at most `3621`. -/
theorem spTabs_cost (hP : Includes P Decoder.spTabsC.costDeps) :
    machineCost P Decoder.spTabsC.costIdx [] ≤ 3621 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := spTabs_lits_ok
  have t1 := tabA_cost P (by includes) spFirst 64 fun r hr ↦ (h1 r hr).1
  have t2 := tabA_cost P (by includes) spRest 64 fun r hr ↦ (h2 r hr).1
  have t3 := tabA_cost P (by includes) spLast 64 fun r hr ↦ (h3 r hr).1
  have := Nat.mul_le_mul_left (64 + 15) h4
  have := Nat.mul_le_mul_left (64 + 15) h5
  have := Nat.mul_le_mul_left (64 + 15) h6
  rw [Decoder.spTabsC.costEq P hP, Decoder.gLanesC.costEq P (by includes),
    Decoder.spSelC.costEq P (by includes), Decoder.spFirstC.costEq P (by includes),
    Decoder.spRestC.costEq P (by includes), Decoder.spLastC.costEq P (by includes),
    show spSel.length = 22 from rfl]
  omega

/-! ## The exponent off the lanes -/

theorem idxBelow_le (w : ℕ) : ∀ (l : List ℕ) (i m : ℕ), idxBelow w l i m ≤ i + m
  | [], _, _ => by simp [idxBelow]
  | _ :: _, _, 0 => by simp [idxBelow]
  | t :: ts, i, m + 1 => by
    rw [idxBelow]
    split_ifs
    · omega
    · have := idxBelow_le w ts (i + 1) m; omega

theorem logGTWith_le (lanes : List ℕ) (x : E) (b : ℕ) : logGTWith lanes x b ≤ b := by
  unfold logGTWith; split_ifs
  · have := idxBelow_le (x.limb 0).lane.toNat lanes 0 b; omega
  · omega

/-- The search among the lanes (`idxBelowC`), `m` entries: at most `23·m + 9`. -/
theorem idxBelow_cost (hP : Includes P Decoder.idxBelowC.costDeps) (w : ℕ)
    (hw : w < 2 ^ 64) : ∀ (l : List ℕ) (i m : ℕ), (∀ x ∈ l, x < 2 ^ 64) → i + m < 2 ^ 64 →
      machineCost P Decoder.idxBelowC.costIdx
        [encodeValue w, encodeValue l, encodeValue i, encodeValue m] ≤ 23 * m + 9
  | [], i, m, _, _ => by rw [Decoder.idxBelowC.costEq_nil P hP]; omega
  | t :: ts, i, m, hl, him => by
    rw [Decoder.idxBelowC.costEq_cons P hP, limbs_of_lt (by omega : m < 2 ^ 64)]
    cases m with
    | zero => simp
    | succ k =>
      have ht := hl t (by simp)
      have := idxBelow_cost hP w hw ts (i + 1) k (fun x hx ↦ hl x (by simp [hx])) (by omega)
      dsimp only
      rw [limbs_of_lt hw, limbs_of_lt ht, limbs_of_lt (by omega : i < 2 ^ 64),
        limbs_of_lt (by omega : i + 1 < 2 ^ 64)]
      split_ifs <;> omega

/-- **An exponent off the lanes given** (`logGTWithC`), `bound < 2^32`: at most
`23·bound + 25`. -/
theorem logGTWith_cost (hP : Includes P Decoder.logGTWithC.costDeps) (lanes : List ℕ)
    (hl : ∀ x ∈ lanes, x < 2 ^ 64) (x : E) (b : ℕ) (hb : b < 2 ^ 32) :
    machineCost P Decoder.logGTWithC.costIdx [encodeValue lanes, encodeValue x, encodeValue b] ≤
      23 * b + 25 := by
  rw [Decoder.logGTWithC.costEq P hP]
  have := idxBelow_cost P (by includes) (x.limb 0).lane.toNat (UInt64.toNat_lt _) lanes 0 b hl
    (by omega)
  split_ifs <;> omega

section Val

variable {σ : Val} {σV : MachineValue}
  (hσ : ∀ v : V, RunsApp P σV [encodeValue v] (encodeValue (σ v)))
  {S : ℕ} (hS : ∀ v : V, appCost P σV [encodeValue v] ≤ S)
include hσ hS

/-- A path level's sibling (`sibNC`): at most `4·S + 71`. -/
theorem sibN_cost (hP : Includes P Decoder.sibNC.costDeps) (bit b : ℕ)
    (hb : b + 1 < 2 ^ 64) :
    machineCost P Decoder.sibNC.costIdx [σV, encodeValue bit, encodeValue b] ≤
      4 * S + 71 := by
  rw [Decoder.sibNC.costEq P hP σ σV hσ, limbs_of_lt hb, limbs_of_lt (by omega : b < 2 ^ 64)]
  have := hS (.n bit); have := hS (.n b); have := hS (.n (b + 1))
  split_ifs <;> omega

/-- **A chain's start cell, off arrays** (`cwCellC`, `cwCellA`): the lanes below `2^64`, the
selectors and the tables' entries below `2^20`: at most `S + 1543`. -/
theorem cwCellA_cost (hP : Includes P Decoder.cwCellC.costDeps) (lanes : List ℕ)
    (hlanes : ∀ x ∈ lanes, x < 2 ^ 64) (G : ℕ) (sel : Array ℕ) (first rest last : Array (Array ℕ))
    (hsel : ∀ k, sel.getD k 0 < 2 ^ 20) (hf : ∀ r k, offAtA first r k < 2 ^ 20)
    (hr : ∀ r k, offAtA rest r k < 2 ^ 20) (hl : ∀ r k, offAtA last r k < 2 ^ 20)
    (hG : G < 2 ^ 20) (i : ℕ) (hi : i < 2 ^ 20) :
    machineCost P Decoder.cwCellC.costIdx [encodeValue lanes, encodeValue G, encodeValue sel,
      encodeValue first, encodeValue rest, encodeValue last, σV, encodeValue i] ≤ S + 1543 := by
  rw [Decoder.cwCellC.costEq P hP _ _ _ _ _ _ σ σV hσ]
  have hsl := hsel (i / 3)
  rw [limbs_of_lt (by omega : i < 2 ^ 64), limbs_of_lt (by omega : i / 3 < 2 ^ 64),
    limbs_of_lt (by omega : G < 2 ^ 64), limbs_of_lt (by omega : sel.getD (i / 3) 0 < 2 ^ 64)]
  have := hS (.n (sel.getD (i / 3) 0))
  have := logGTWith_cost P (by includes) lanes hlanes (σ (.n (sel.getD (i / 3) 0))) 64
    (by norm_num)
  have := logGTWith_cost P (by includes) lanes hlanes (σ (.n (sel.getD (i / 3) 0))) 4
    (by norm_num)
  rw [Decoder.offAtAC.costEq P (by includes), Decoder.offAtAC.costEq P (by includes)]
  have h1 := hf (i % 3) (logGTWith lanes (σ (.n (sel.getD (i / 3) 0))) 64)
  have h2 := hr (i % 3) (logGTWith lanes (σ (.n (sel.getD (i / 3) 0))) 64)
  have h3 := hl (i % 3) (logGTWith lanes (σ (.n (sel.getD (i / 3) 0))) 4)
  split_ifs with c1 c2
  · rw [limbs_of_lt (by omega : offAtA first (i % 3)
      (logGTWith lanes (σ (.n (sel.getD (i / 3) 0))) 64) < 2 ^ 64),
      limbs_of_lt (by omega : sel.getD (i / 3) 0 + offAtA first (i % 3)
      (logGTWith lanes (σ (.n (sel.getD (i / 3) 0))) 64) < 2 ^ 64)]
    omega
  · rw [limbs_of_lt (by omega : offAtA rest (i % 3)
      (logGTWith lanes (σ (.n (sel.getD (i / 3) 0))) 64) < 2 ^ 64),
      limbs_of_lt (by omega : sel.getD (i / 3) 0 + offAtA rest (i % 3)
      (logGTWith lanes (σ (.n (sel.getD (i / 3) 0))) 64) < 2 ^ 64)]
    omega
  · rw [limbs_of_lt (by omega : offAtA last (i % 3)
      (logGTWith lanes (σ (.n (sel.getD (i / 3) 0))) 4) < 2 ^ 64),
      limbs_of_lt (by omega : sel.getD (i / 3) 0 + offAtA last (i % 3)
      (logGTWith lanes (σ (.n (sel.getD (i / 3) 0))) 4) < 2 ^ 64)]
    omega

/-! ## leanSPHINCS -/

/-- **FORS tree `c`'s opening** (`forsOpeningAC`), `c < 24`: its secret and ten siblings, at most
`41·S + 1300`. -/
theorem forsOpeningA_cost (hP : Includes P Decoder.forsOpeningAC.costDeps) (c : ℕ) (hc : c < 24) :
    machineCost P Decoder.forsOpeningAC.costIdx [σV, encodeValue c] ≤ 41 * S + 1300 := by
  rw [Decoder.forsOpeningAC.costEq P hP σ σV hσ, ofFnFrom_length,
    limbs_of_lt (by omega : 233 * c < 2 ^ 64), limbs_of_lt (by omega : c < 2 ^ 64),
    limbs_of_lt (by omega : 1225 + 233 * c < 2 ^ 64)]
  have := hS (.n (1225 + 233 * c))
  have := cellNat_cost P (by includes) (σ (.n (1225 + 233 * c)))
  have m := ofFnFrom_cost P (by includes) (n := Sphincs.forsTreeHeight) (by decide) _
    (.closure Decoder.forsOpeningAC.lam0.costIdx [σV, encodeValue c])
    (fun l ↦ RunsApp.of_spec (Decoder.forsOpeningAC.lam0.costSpec P (by includes) σ σV hσ c l))
    (4 * S + 104) (fun l ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.nil_append,
        Decoder.forsOpeningAC.lam0.costEq P (by includes) σ σV hσ]
      simp only [List.length_cons, List.length_nil]
      have hl := l.isLt
      simp only [Sphincs.forsTreeHeight] at hl
      have := sibN_cost P hσ hS (by includes) (77 + 10 * c + l.val) (1247 + 233 * c + 23 * l.val)
        (by omega)
      have := cellNat_cost P (by includes) (sibN σ (77 + 10 * c + l.val) (1247 + 233 * c + 23 * l.val))
      rw [limbs_of_lt (by omega : 10 * c < 2 ^ 64), limbs_of_lt (by omega : c < 2 ^ 64),
        limbs_of_lt (by omega : 77 + 10 * c < 2 ^ 64), limbs_of_lt (by omega : l.val < 2 ^ 64),
        limbs_of_lt (by omega : 77 + 10 * c + l.val < 2 ^ 64),
        limbs_of_lt (by omega : 233 * c < 2 ^ 64), limbs_of_lt (by omega : 1247 + 233 * c < 2 ^ 64),
        limbs_of_lt (by omega : 23 * l.val < 2 ^ 64),
        limbs_of_lt (by omega : 1247 + 233 * c + 23 * l.val < 2 ^ 64)]
      omega) 0 (Nat.zero_le _)
  simp only [Sphincs.forsTreeHeight, Nat.sub_zero] at m ⊢
  omega

/-- **A layer's signature** (`layerAC`), its counter's cell, its path's base and its first bit
below `2^20`, its chains off the `sp_wots` frame `w` (a valuation of price at most `S`, like `σ`),
`sp_wots`' tables `T`: at most `169·S + 104200`. -/
theorem layerA_cost (hP : Includes P Decoder.layerAC.costDeps) (T : SpTabs) (hT : SpTabsOK T)
    {w : Val} {wV : MachineValue} (hw : ∀ v : V, RunsApp P wV [encodeValue v] (encodeValue (w v)))
    (hW : ∀ v : V, appCost P wV [encodeValue v] ≤ S) (ctr path bit : ℕ) (hpath : path < 2 ^ 20)
    (hbit : bit < 2 ^ 20) (layer : Sphincs.Layer) :
    machineCost P Decoder.layerAC.costIdx [encodeValue T, σV, wV, encodeValue ctr,
      encodeValue path, encodeValue bit, encodeValue layer] ≤ 169 * S + 104200 := by
  rw [Decoder.layerAC.costEq P hP T σ σV hσ w wV hw, ofFnFrom_length, ofFnFrom_length,
    Auto.Sphincs.layerHeight.c848.costEq P (by includes)]
  have := hS (.n ctr)
  have := cellNat_cost P (by includes) (σ (.n ctr))
  have hl1 := limbs_le_of_lt (x := Sig.cellNat (σ (.n ctr))) (k := 2) (by norm_num)
    (Decoder.cellNat_lt _)
  rw [limbs_of_lt (by norm_num : 2 ^ 32 - 1 < 2 ^ 64)]
  have hlay := layer.isLt
  simp only [Sphincs.layerCount] at hlay
  rw [limbs_of_lt (by omega : layer.val < 2 ^ 64)]
  have hh : Sphincs.layerHeight layer ≤ 10 := by unfold Sphincs.layerHeight; split <;> omega
  have m0 := ofFnFrom_cost P (by includes) (n := Sphincs.chainCount) (by decide) _
    (.closure Decoder.layerAC.lam0.costIdx [encodeValue T, wV])
    (fun i ↦ RunsApp.of_spec (Decoder.layerAC.lam0.costSpec P (by includes) T w wV hw i))
    (2 * S + 1580) (fun i ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.nil_append,
        Decoder.layerAC.lam0.costEq P (by includes) T w wV hw]
      simp only [List.length_cons, List.length_nil]
      have := cwCellA_cost P hw hW (by includes) T.lanes hT.lanes 21 T.sel T.first T.rest T.last
        hT.sel hT.first hT.rest hT.last (by norm_num) i.val
        (by have := i.isLt; simp only [Sphincs.chainCount] at this; omega)
      have := cellNat_cost P (by includes)
        (w (.n (cwCellA T.lanes 21 T.sel T.first T.rest T.last w i.val)))
      have := hW (.n (cwCellA T.lanes 21 T.sel T.first T.rest T.last w i.val))
      omega) 0 (Nat.zero_le _)
  have m1 := ofFnFrom_cost P (by includes) (n := Sphincs.layerHeight layer) (by omega) _
    (.closure Decoder.layerAC.lam1.costIdx [σV, encodeValue path, encodeValue bit, encodeValue layer])
    (fun l ↦ RunsApp.of_spec (Decoder.layerAC.lam1.costSpec P (by includes) σ σV hσ path bit layer l))
    (4 * S + 98) (fun l ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.cons_append,
        List.nil_append, Decoder.layerAC.lam1.costEq P (by includes) σ σV hσ]
      simp only [List.length_cons, List.length_nil]
      have hl := l.isLt
      have := sibN_cost P hσ hS (by includes) (bit + l.val) (path + 21 * l.val) (by omega)
      have := cellNat_cost P (by includes) (sibN σ (bit + l.val) (path + 21 * l.val))
      rw [limbs_of_lt (by omega : bit < 2 ^ 64), limbs_of_lt (by omega : l.val < 2 ^ 64),
        limbs_of_lt (by omega : bit + l.val < 2 ^ 64), limbs_of_lt (by omega : 21 * l.val < 2 ^ 64),
        limbs_of_lt (by omega : path < 2 ^ 64), limbs_of_lt (by omega : path + 21 * l.val < 2 ^ 64)]
      omega) 0 (Nat.zero_le _)
  have hm1 : (4 * S + 98 + 16) * (Sphincs.layerHeight layer - 0) ≤ (4 * S + 114) * 10 := by
    rw [Nat.sub_zero]; exact Nat.mul_le_mul_left _ hh
  simp only [Sphincs.chainCount, Nat.sub_zero, ite_self] at m0 ⊢
  omega

/-- **A leanSPHINCS signature, off `sp_wots`' tables `T`** (`sphincsSigOfNC`, `sphincsSigOfA`):
`verify_sig_lean_sphincs`' valuation `σ` and the three `sp_wots` frames `w0`, `w1`, `w2`, each a
valuation of price at most `S`: at most `1492·S + 345000`. -/
theorem sphincsSigOfA_cost (hP : Includes P Decoder.sphincsSigOfNC.costDeps) (T : SpTabs)
    (hT : SpTabsOK T) {w0 w1 w2 : Val} {w0V w1V w2V : MachineValue}
    (hw0 : ∀ v : V, RunsApp P w0V [encodeValue v] (encodeValue (w0 v)))
    (hW0 : ∀ v : V, appCost P w0V [encodeValue v] ≤ S)
    (hw1 : ∀ v : V, RunsApp P w1V [encodeValue v] (encodeValue (w1 v)))
    (hW1 : ∀ v : V, appCost P w1V [encodeValue v] ≤ S)
    (hw2 : ∀ v : V, RunsApp P w2V [encodeValue v] (encodeValue (w2 v)))
    (hW2 : ∀ v : V, appCost P w2V [encodeValue v] ≤ S) :
    machineCost P Decoder.sphincsSigOfNC.costIdx [encodeValue T, σV, w0V, w1V, w2V] ≤
      1492 * S + 345000 := by
  rw [Decoder.sphincsSigOfNC.costEq P hP T σ σV hσ w0 w0V hw0 w1 w1V hw1 w2 w2V hw2,
    ofFnFrom_length]
  have := hS (.n 3)
  have := cellNat_cost P (by includes) (σ (.n 3))
  have m0 := ofFnFrom_cost P (by includes) (n := Sphincs.forsTreeCount) (by decide) _
    (.closure Decoder.sphincsSigOfNC.lam0.costIdx [σV])
    (fun c ↦ RunsApp.of_spec (Decoder.sphincsSigOfNC.lam0.costSpec P (by includes) σ σV hσ c))
    (41 * S + 1304) (fun c ↦ by
      rw [appCost_fn, List.cons_append, List.nil_append,
        Decoder.sphincsSigOfNC.lam0.costEq P (by includes) σ σV hσ]
      simp only [List.length_cons, List.length_nil]
      have := forsOpeningA_cost P hσ hS (by includes) c.val
        (by have := c.isLt; simp only [Sphincs.forsTreeCount] at this; omega)
      omega) 0 (Nat.zero_le _)
  have l0 := layerA_cost P hσ hS (by includes) T hT hw0 hW0 (spCtr 0) (spPath 0) (spBit 0)
    (by decide) (by decide) 0
  have l1 := layerA_cost P hσ hS (by includes) T hT hw1 hW1 (spCtr 1) (spPath 1) (spBit 1)
    (by decide) (by decide) 1
  have l2 := layerA_cost P hσ hS (by includes) T hT hw2 hW2 (spCtr 2) (spPath 2) (spBit 2)
    (by decide) (by decide) 2
  rw [Decoder.spCtrC.costEq P (by includes), Decoder.spCtrC.costEq P (by includes),
    Decoder.spCtrC.costEq P (by includes), Decoder.spPathC.costEq P (by includes),
    Decoder.spPathC.costEq P (by includes), Decoder.spPathC.costEq P (by includes),
    Decoder.spBitC.costEq P (by includes), Decoder.spBitC.costEq P (by includes),
    Decoder.spBitC.costEq P (by includes), Auto.Fin.ofNat.c851.costEq P (by includes),
    Auto.Fin.ofNat.c851.costEq P (by includes),
    Auto.Fin.ofNat.c851.costEq P (by includes)]
  simp only [Sphincs.forsTreeCount, Sphincs.layerCount, Nat.sub_zero] at m0 ⊢
  simp only [limbs_of_lt (by norm_num : (0 : ℕ) < 2 ^ 64), limbs_of_lt (by norm_num : (1 : ℕ) < 2 ^ 64),
    limbs_of_lt (by norm_num : (2 : ℕ) < 2 ^ 64), limbs_of_lt (by norm_num : (3 : ℕ) < 2 ^ 64),
    ite_self, ↓reduceIte, Nat.one_ne_zero, OfNat.ofNat_ne_zero, Nat.mul_one,
    limbs_of_lt (by norm_num : 8 * 2 < 2 ^ 64), limbs_of_lt (by norm_num : 51 + 8 * 2 < 2 ^ 64),
    limbs_of_lt (by norm_num : 8 < 2 ^ 64), limbs_of_lt (by norm_num : 51 + 8 < 2 ^ 64),
    limbs_of_lt (by norm_num : 51 + 8 * 0 < 2 ^ 64)]
  omega

/-- **A layer's call of `sp_wots`, its arguments** (`spWotsArgsC`), `l < 3`: three words, at most
`3·S + 59`. -/
theorem spWotsArgs_cost (hP : Includes P Decoder.spWotsArgsC.costDeps) (l : ℕ) (hl : l < 3) :
    machineCost P Decoder.spWotsArgsC.costIdx [σV, encodeValue l] ≤ 3 * S + 59 := by
  rw [Decoder.spWotsArgsC.costEq P hP σ σV hσ, Auto.LeanVM.Guest.Fast.spAt.c853.costEq P (by includes),
    Auto.LeanVM.Guest.Fast.spEnc.c854.costEq P (by includes), limbs_of_lt (by omega : l < 2 ^ 64)]
  have := hS (.n 2); have := hS (.n (spAt l)); have := hS (.n (spEnc l))
  simp only [ite_self]
  split_ifs <;> omega

/-- **A layer's call of `sp_wots`, its return** (`spWotsRetsC`), `l < 3`: at most `S + 24`. -/
theorem spWotsRets_cost (hP : Includes P Decoder.spWotsRetsC.costDeps) (l : ℕ) (hl : l < 3) :
    machineCost P Decoder.spWotsRetsC.costIdx [σV, encodeValue l] ≤ S + 24 := by
  rw [Decoder.spWotsRetsC.costEq P hP σ σV hσ, Auto.LeanVM.Guest.Fast.spLeaf.c856.costEq P (by includes),
    limbs_of_lt (by omega : l < 2 ^ 64)]
  have := hS (.n (spLeaf l))
  simp only [ite_self]
  split_ifs <;> omega

end Val

end

end LeanVM.Cost.Bounds.Guest
