module

public import LeanVM.Cost.Bounds.Guest.Readers
public import LeanVM.Cost.Decoder.Signatures

/-!
# Bounds on the guest decoder's prices: the signatures

The readers of a leanXMSS and a leanSPHINCS signature off their checks' valuations, off the
readers' tables as arrays (`Cost/Decoder/Signatures.lean`: `xmssSigOfNC` is `xmssSigOfA`,
`sphincsSigOfNC` is `sphincsSigOfA`, `Guest/Fast/{Xmss,Sphincs}.lean`), in the price `S` of an
application of the valuation: a signature has a fixed shape, so its price is `a·S + b`:

* the tables' facts (`gLanes_ok`, `xTabs_ok`, `sTabs_ok`, … by kernel evaluation of the literals),
  and of the arrays built from them (`XmssTabsOK`, `SphincsTabsOK`: `xmssTabs_ok`,
  `sphincsTabs_ok`), an entry read in constant time (`offAtA`: `8`);
* an exponent off the lanes of `g^k` given (`idxBelow_cost`, `logGTWith_cost`: `23·bound + 25`),
  a sibling (`sibN_cost`), the bits of a leaf index (`bitsN_cost`), a chain's start cell
  (`cwCellA_cost`: `S + 1543`);
* `xPartA_cost`, **`xmssSigOfN_cost`**: `458·S + 210280`;
* `subOpeningAt_cost`, `subOpeningA_cost`, `coordOpeningAt_cost`, `coordOpeningA_cost`,
  **`sphincsSigOfN_cost`**: `450·S + 220065`.
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

theorem xTabs_ok : RowsOK 64 xFirst ∧ RowsOK 64 xRest ∧ RowsOK 64 xLast ∧ xFirst.length ≤ 3 ∧
    xRest.length ≤ 3 ∧ xLast.length ≤ 3 ∧ ListOK 22 xSel0 ∧ ListOK 22 xSel1 ∧
    ListOK 16 xPath0 ∧ ListOK 16 xPath1 := by decide +kernel

theorem sTabs_ok : RowsOK 64 sFirst ∧ RowsOK 64 sRest ∧ RowsOK 64 sLast ∧ sFirst.length ≤ 3 ∧
    sRest.length ≤ 3 ∧ sLast.length ≤ 3 ∧ ListOK 22 sSel ∧ ListOK 26 sPath ∧ RowsOK 6 fkOff ∧
    fkOff.length ≤ 256 := by decide +kernel

theorem sCoordTab_ok : sCoordTab.length ≤ 8 ∧ ∀ r ∈ sCoordTab, r.b < 2 ^ 19 ∧ r.f0 < 2 ^ 20 ∧
    r.p00 < 2 ^ 20 ∧ r.p01 < 2 ^ 20 ∧ r.s1 < 2 ^ 20 ∧ r.f1 < 2 ^ 20 ∧ r.p10 < 2 ^ 20 ∧
    r.p11 < 2 ^ 20 ∧ r.top < 2 ^ 20 ∧ r.q0 < 2 ^ 20 ∧ r.q1 < 2 ^ 20 := by decide +kernel

theorem sCoord_getD_ok (k : ℕ) : (sCoordTab.getD k sCoord0).b < 2 ^ 19 ∧
    (sCoordTab.getD k sCoord0).f0 < 2 ^ 20 ∧ (sCoordTab.getD k sCoord0).s1 < 2 ^ 20 ∧
    (sCoordTab.getD k sCoord0).f1 < 2 ^ 20 ∧ (sCoordTab.getD k sCoord0).top < 2 ^ 20 := by
  rw [List.getD_eq_getElem?_getD]
  rcases hk : sCoordTab[k]? with _ | x
  · simp [sCoord0]
  · obtain ⟨a1, a2, -, -, a5, a6, -, -, a9, -, -⟩ := sCoordTab_ok.2 x (List.mem_of_getElem? hk)
    exact ⟨a1, a2, a5, a6, a9⟩

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

/-- leanXMSS's tables as arrays, their entries small (`xmssTabs_ok`). -/
structure XmssTabsOK (T : XmssTabs) : Prop where
  lanes : ∀ x ∈ T.lanes, x < 2 ^ 64
  first : ∀ r k, offAtA T.first r k < 2 ^ 20
  rest : ∀ r k, offAtA T.rest r k < 2 ^ 20
  last : ∀ r k, offAtA T.last r k < 2 ^ 20
  sel0 : ∀ k, T.sel0.getD k 0 < 2 ^ 20
  sel1 : ∀ k, T.sel1.getD k 0 < 2 ^ 20
  path0 : ∀ k, T.path0.getD k 0 < 2 ^ 20
  path1 : ∀ k, T.path1.getD k 0 < 2 ^ 20

theorem xmssTabs_ok : XmssTabsOK xmssTabs := by
  obtain ⟨h1, h2, h3, -, -, -, s0, s1, p0, p1⟩ := xTabs_ok
  exact ⟨gLanes_ok.2, offAtA_tabA_lt h1, offAtA_tabA_lt h2, offAtA_tabA_lt h3,
    getD_toArray_lt s0, getD_toArray_lt s1, getD_toArray_lt p0, getD_toArray_lt p1⟩

/-- leanSPHINCS's tables as arrays, their entries small (`sphincsTabs_ok`). -/
structure SphincsTabsOK (T : SphincsTabs) : Prop where
  lanes : ∀ x ∈ T.lanes, x < 2 ^ 64
  fkOff : ∀ r k, offAtA T.fkOff r k < 2 ^ 20
  coords : ∀ k, (T.coords.getD k sCoord0).b < 2 ^ 19 ∧ (T.coords.getD k sCoord0).f0 < 2 ^ 20 ∧
    (T.coords.getD k sCoord0).s1 < 2 ^ 20 ∧ (T.coords.getD k sCoord0).f1 < 2 ^ 20 ∧
    (T.coords.getD k sCoord0).top < 2 ^ 20
  sel : ∀ k, T.sel.getD k 0 < 2 ^ 20
  first : ∀ r k, offAtA T.first r k < 2 ^ 20
  rest : ∀ r k, offAtA T.rest r k < 2 ^ 20
  last : ∀ r k, offAtA T.last r k < 2 ^ 20
  path : ∀ k, T.path.getD k 0 < 2 ^ 20

theorem sphincsTabs_ok : SphincsTabsOK sphincsTabs := by
  obtain ⟨h1, h2, h3, -, -, -, hsel, hpath, hk, -⟩ := sTabs_ok
  refine ⟨gLanes_ok.2, offAtA_tabA_lt hk, fun k ↦ ?_, getD_toArray_lt hsel, offAtA_tabA_lt h1,
    offAtA_tabA_lt h2, offAtA_tabA_lt h3, getD_toArray_lt hpath⟩
  simp only [show sphincsTabs.coords = sCoordTab.toArray from rfl, getD_toArray]
  exact sCoord_getD_ok k

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

/-- **leanXMSS's tables, built** (`xmssTabsC`): at most `4043`. -/
theorem xmssTabs_cost (hP : Includes P Decoder.xmssTabsC.costDeps) :
    machineCost P Decoder.xmssTabsC.costIdx [] ≤ 4043 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := xTabs_ok
  have t1 := tabA_cost P (by includes) xFirst 64 fun r hr ↦ (h1 r hr).1
  have t2 := tabA_cost P (by includes) xRest 64 fun r hr ↦ (h2 r hr).1
  have t3 := tabA_cost P (by includes) xLast 64 fun r hr ↦ (h3 r hr).1
  have := Nat.mul_le_mul_left (64 + 15) h4
  have := Nat.mul_le_mul_left (64 + 15) h5
  have := Nat.mul_le_mul_left (64 + 15) h6
  rw [Decoder.xmssTabsC.costEq P hP, Decoder.gLanesC.costEq P (by includes),
    Decoder.xFirstC.costEq P (by includes), Decoder.xRestC.costEq P (by includes),
    Decoder.xLastC.costEq P (by includes), Decoder.xSel0C.costEq P (by includes),
    Decoder.xSel1C.costEq P (by includes), Decoder.xPath0C.costEq P (by includes),
    Decoder.xPath1C.costEq P (by includes),
    show xSel0.length = 20 from rfl, show xSel1.length = 20 from rfl,
    show xPath0.length = 16 from rfl, show xPath1.length = 16 from rfl]
  omega

/-- **leanSPHINCS's tables, built** (`sphincsTabsC`): at most `17072`. -/
theorem sphincsTabs_cost (hP : Includes P Decoder.sphincsTabsC.costDeps) :
    machineCost P Decoder.sphincsTabsC.costIdx [] ≤ 17072 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, -, -, hk, hkl⟩ := sTabs_ok
  have t1 := tabA_cost P (by includes) sFirst 64 fun r hr ↦ (h1 r hr).1
  have t2 := tabA_cost P (by includes) sRest 64 fun r hr ↦ (h2 r hr).1
  have t3 := tabA_cost P (by includes) sLast 64 fun r hr ↦ (h3 r hr).1
  have t4 := tabA_cost P (by includes) fkOff 6 fun r hr ↦ (hk r hr).1
  have := Nat.mul_le_mul_left (64 + 15) h4
  have := Nat.mul_le_mul_left (64 + 15) h5
  have := Nat.mul_le_mul_left (64 + 15) h6
  have := Nat.mul_le_mul_left (6 + 15) hkl
  rw [Decoder.sphincsTabsC.costEq P hP, Decoder.gLanesC.costEq P (by includes),
    Decoder.fkOffC.costEq P (by includes), Decoder.sCoordTabC.costEq P (by includes),
    Decoder.sSelC.costEq P (by includes), Decoder.sFirstC.costEq P (by includes),
    Decoder.sRestC.costEq P (by includes), Decoder.sLastC.costEq P (by includes),
    Decoder.sPathC.costEq P (by includes),
    show sCoordTab.length = 8 from rfl, show sSel.length = 22 from rfl,
    show sPath.length = 26 from rfl]
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

omit hσ hS in
theorem bitsN_lt (base : ℕ) : ∀ n, bitsN σ base n < 2 ^ n
  | 0 => by simp [bitsN]
  | n + 1 => by
    rw [bitsN, pow_succ]
    have := bitsN_lt base n
    have : (decide (σ (.n (base + n)) = 1)).toNat ≤ 1 := Bool.toNat_le _
    have := Nat.mul_le_mul_left (2 ^ n) this
    omega

/-- The integer of `n ≤ 32` bits (`bitsNC`): at most `(3·S + 85)·n + 5`. -/
theorem bitsN_cost (hP : Includes P Decoder.bitsNC.costDeps) (base : ℕ)
    (hbase : base < 2 ^ 32) : ∀ n, n ≤ 32 →
      machineCost P Decoder.bitsNC.costIdx [σV, encodeValue base, encodeValue n] ≤
        (3 * S + 85) * n + 5
  | 0, _ => by rw [Decoder.bitsNC.costEq_zero P hP σ σV hσ]; omega
  | n + 1, hn => by
    rw [Decoder.bitsNC.costEq_succ P hP σ σV hσ]
    have := bitsN_cost hP base hbase n (by omega)
    have hb := bitsN_lt (σ := σ) base n
    have h2 : 2 ^ n ≤ 2 ^ 32 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : 2 ^ n * (decide (σ (.n (base + n)) = 1)).toNat ≤ 2 ^ 32 := by
      have : (decide (σ (.n (base + n)) = 1)).toNat ≤ 1 := Bool.toNat_le _
      have := Nat.mul_le_mul_left (2 ^ n) this
      omega
    have h4 : (decide (σ (.n (base + n)) = 1)).toNat ≤ 1 := Bool.toNat_le _
    rw [limbs_of_lt (by omega : n + 1 < 2 ^ 64), limbs_of_lt (by omega : n < 2 ^ 64),
      limbs_of_lt (by omega : base < 2 ^ 64), Nat.one_shiftLeft, limbs_of_lt (by omega : 2 ^ n < 2 ^ 64),
      limbs_of_lt (by omega : (decide (σ (.n (base + n)) = 1)).toNat < 2 ^ 64),
      limbs_of_lt (by omega : bitsN σ base n < 2 ^ 64), limbs_of_lt (by omega : base + n < 2 ^ 64),
      limbs_of_lt (by omega : 2 ^ n * (decide (σ (.n (base + n)) = 1)).toNat < 2 ^ 64),
      limbs_of_lt (by omega : bitsN σ base n + 2 ^ n * (decide (σ (.n (base + n)) = 1)).toNat < 2 ^ 64)]
    have := hS (.n (base + n))
    simp only [max_self, Nat.mul_one, Bool.cond_decide, ite_self]
    split_ifs <;> nlinarith

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

/-! ## leanXMSS -/

/-- A layer's signature, off the tables `T` (`xPartNC`, `xPartA`), its selectors and path bases
below `2^20`: at most `181·S + 103735`. -/
theorem xPartA_cost (hP : Includes P Decoder.xPartNC.costDeps) (T : XmssTabs) (hT : XmssTabsOK T)
    (rho bitBase : ℕ) (sel path : Array ℕ) (hsel : ∀ k, sel.getD k 0 < 2 ^ 20)
    (hpath : ∀ k, path.getD k 0 < 2 ^ 20) (hb : bitBase < 2 ^ 20) :
    machineCost P Decoder.xPartNC.costIdx
      [encodeValue T, encodeValue rho, encodeValue bitBase, encodeValue sel, encodeValue path, σV] ≤
        181 * S + 103735 := by
  rw [Decoder.xPartNC.costEq P hP _ _ _ _ _ σ σV hσ, ofFnFrom_length, ofFnFrom_length]
  have hc := cellNat_cost P (by includes) (σ (.n rho))
  have := hS (.n rho)
  have m0 := ofFnFrom_cost P (by includes) (n := LeanXmss.chainCount) (by decide) _
    (.closure Decoder.xPartNC.lam0.costIdx [encodeValue T, encodeValue sel, σV])
    (fun i ↦ RunsApp.of_spec (Decoder.xPartNC.lam0.costSpec P (by includes) T sel σ σV hσ i))
    (2 * S + 1580) (fun i ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.nil_append,
        Decoder.xPartNC.lam0.costEq P (by includes) T sel σ σV hσ, List.length_cons, List.length_cons, List.length_cons, List.length_nil]
      have := cwCellA_cost P hσ hS (by includes) T.lanes hT.lanes 19 sel T.first T.rest T.last hsel
        hT.first hT.rest hT.last (by norm_num) i.val
        (by have := i.isLt; simp only [LeanXmss.chainCount] at this; omega)
      have := cellNat_cost P (by includes)
        (σ (.n (cwCellA T.lanes 19 sel T.first T.rest T.last σ i.val)))
      have := hS (.n (cwCellA T.lanes 19 sel T.first T.rest T.last σ i.val))
      omega) 0 (Nat.zero_le _)
  have m1 := ofFnFrom_cost P (by includes) (n := LeanXmss.layerHeight) (by decide) _
    (.closure Decoder.xPartNC.lam1.costIdx [encodeValue bitBase, encodeValue path, σV])
    (fun l ↦ RunsApp.of_spec (Decoder.xPartNC.lam1.costSpec P (by includes) bitBase path σ σV hσ l))
    (4 * S + 96) (fun l ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.nil_append,
        Decoder.xPartNC.lam1.costEq P (by includes) bitBase path σ σV hσ, List.length_cons, List.length_cons, List.length_cons, List.length_nil]
      have hl := l.isLt
      simp only [LeanXmss.layerHeight] at hl
      have := hpath l.val
      have := sibN_cost P hσ hS (by includes) (bitBase + l.val) (path.getD l.val 0) (by omega)
      have := cellNat_cost P (by includes) (sibN σ (bitBase + l.val) (path.getD l.val 0))
      rw [limbs_of_lt (by omega : bitBase < 2 ^ 64), limbs_of_lt (by omega : l.val < 2 ^ 64),
        limbs_of_lt (by omega : bitBase + l.val < 2 ^ 64)]
      omega) 0 (Nat.zero_le _)
  simp only [LeanXmss.chainCount, LeanXmss.layerHeight, Nat.sub_zero] at m0 m1 ⊢
  omega

/-- **A leanXMSS signature, off the tables `T`** (`xmssSigOfNC`, `xmssSigOfA`): at most
`458·S + 210280`. -/
theorem xmssSigOfN_cost (hP : Includes P Decoder.xmssSigOfNC.costDeps) (T : XmssTabs)
    (hT : XmssTabsOK T) :
    machineCost P Decoder.xmssSigOfNC.costIdx [encodeValue T, σV] ≤ 458 * S + 210280 := by
  rw [Decoder.xmssSigOfNC.costEq P hP T σ σV hσ, ofFnFrom_length]
  have hb := bitsN_cost P hσ hS (by includes) 2 (by norm_num) 32 le_rfl
  have m := ofFnFrom_cost P (by includes) (n := LeanXmss.layerCount) (by decide) _
    (.closure Decoder.xmssSigOfNC.lam0.costIdx [encodeValue T, σV])
    (fun l ↦ RunsApp.of_spec (Decoder.xmssSigOfNC.lam0.costSpec P (by includes) T σ σV hσ l))
    (181 * S + 103750) (fun l ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.nil_append,
        Decoder.xmssSigOfNC.lam0.costEq P (by includes) T σ σV hσ, List.length_cons, List.length_cons, List.length_nil]
      have hl := l.isLt
      simp only [LeanXmss.layerCount] at hl
      rw [limbs_of_lt (by omega : l.val < 2 ^ 64)]
      have := xPartA_cost P hσ hS (by includes) T hT 196 2 T.sel0 T.path0 hT.sel0 hT.path0
        (by norm_num)
      have := xPartA_cost P hσ hS (by includes) T hT 12604 18 T.sel1 T.path1 hT.sel1 hT.path1
        (by norm_num)
      split_ifs <;> omega) 0 (Nat.zero_le _)
  simp only [LeanXmss.layerCount, Nat.sub_zero] at m ⊢
  omega

/-! ## leanSPHINCS -/

omit hσ hS in
theorem foldPos_cost (hP : Includes P Decoder.foldPosC.costDeps)
    (first rest b a : ℕ) (hf : first < 2 ^ 20) (hr : rest < 2 ^ 20) (hb : b < 2 ^ 20)
    (ha : a < 2 ^ 20) :
    machineCost P Decoder.foldPosC.costIdx
      [encodeValue first, encodeValue rest, encodeValue b, encodeValue a] ≤ 13 := by
  rw [Decoder.foldPosC.costEq P hP]
  have : rest * (a - 1) < 2 ^ 40 := by
    calc rest * (a - 1) < 2 ^ 20 * 2 ^ 20 := Nat.mul_lt_mul_of_lt_of_le hr (by omega) (by norm_num)
      _ = 2 ^ 40 := by norm_num
  split_ifs
  · rw [limbs_of_lt (by omega : a < 2 ^ 64)]; omega
  · rw [limbs_of_lt (by omega : a < 2 ^ 64), limbs_of_lt (by omega : b < 2 ^ 64),
      limbs_of_lt (by omega : first < 2 ^ 64), limbs_of_lt (by omega : rest < 2 ^ 64),
      limbs_of_lt (by omega : a - 1 < 2 ^ 64), limbs_of_lt (by omega : b + first < 2 ^ 64),
      limbs_of_lt (by omega : rest * (a - 1) < 2 ^ 64),
      limbs_of_lt (by omega : b + first + rest * (a - 1) < 2 ^ 64)]
    omega

omit hσ hS in
theorem foldPos_lt (first rest b a : ℕ) (hf : first < 2 ^ 20) (hr : rest < 2 ^ 20)
    (hb : b < 2 ^ 20) (ha : a < 2 ^ 20) : foldPos first rest b a < 2 ^ 42 := by
  unfold foldPos
  have : rest * (a - 1) < 2 ^ 40 := by
    calc rest * (a - 1) < 2 ^ 20 * 2 ^ 20 := Nat.mul_lt_mul_of_lt_of_le hr (by omega) (by norm_num)
      _ = 2 ^ 40 := by norm_num
  split_ifs <;> omega

/-- A sub-tree's opening, its key `t` and arm `a` given (`subOpeningAtC`), its cells below `2^20`
and `a < 2^20`: at most `9·S + 596`. -/
theorem subOpeningAt_cost (hP : Includes P Decoder.subOpeningAtC.costDeps) (fk : Array (Array ℕ))
    (hfk : ∀ r k, offAtA fk r k < 2 ^ 20) (b fold p0 p1 t a : ℕ) (hb : b < 2 ^ 20)
    (hfold : fold < 2 ^ 20) (ha : a < 2 ^ 20) :
    machineCost P Decoder.subOpeningAtC.costIdx
      [encodeValue fk, σV, encodeValue b, encodeValue fold, encodeValue p0, encodeValue p1,
        encodeValue t, encodeValue a] ≤ 9 * S + 596 := by
  rw [Decoder.subOpeningAtC.costEq P hP fk σ σV hσ, ofFnFrom_length, ofFnFrom_length]
  have m0 := ofFnFrom_cost P (by includes) (n := Sphincs.forestChainCount) (by decide) _
    (.closure Decoder.subOpeningAtC.lam0.costIdx [encodeValue fk, σV, encodeValue b, encodeValue t])
    (fun i ↦ RunsApp.of_spec (Decoder.subOpeningAtC.lam0.costSpec P (by includes) fk σ σV hσ b t i))
    (S + 41) (fun i ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.cons_append,
        List.nil_append, Decoder.subOpeningAtC.lam0.costEq P (by includes) fk σ σV hσ,
        Decoder.offAtAC.costEq P (by includes), List.length_cons, List.length_cons, List.length_cons, List.length_cons, List.length_nil]
      have := hfk t i.val
      have := hS (.n (b + 12 + offAtA fk t i.val))
      have := cellNat_cost P (by includes) (σ (.n (b + 12 + offAtA fk t i.val)))
      rw [limbs_of_lt (by omega : b < 2 ^ 64), limbs_of_lt (by omega : b + 12 < 2 ^ 64),
        limbs_of_lt (by omega : offAtA fk t i.val < 2 ^ 64),
        limbs_of_lt (by omega : b + 12 + offAtA fk t i.val < 2 ^ 64)]
      omega) 0 (Nat.zero_le _)
  have m1 := ofFnFrom_cost P (by includes) (n := Sphincs.forestSubtreeHeight) (by decide) _
    (.closure Decoder.subOpeningAtC.lam1.costIdx
      [σV, encodeValue fold, encodeValue p0, encodeValue p1, encodeValue a])
    (fun l ↦ RunsApp.of_spec (Decoder.subOpeningAtC.lam1.costSpec P (by includes) σ σV hσ fold p0
      p1 a l))
    (S + 52) (fun l ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.cons_append,
        List.cons_append, List.nil_append,
        Decoder.subOpeningAtC.lam1.costEq P (by includes) σ σV hσ, List.length_cons, List.length_cons, List.length_cons, List.length_cons, List.length_cons, List.length_nil]
      have hl := l.isLt
      simp only [Sphincs.forestSubtreeHeight] at hl
      have := foldPos_cost P (by includes) 35 32 fold a (by norm_num) (by norm_num) hfold ha
      have := foldPos_lt 35 32 fold a (by norm_num) (by norm_num) hfold ha
      have := hS (.n (foldPos 35 32 fold a + 16 * l.val))
      have := hS (.n (if a / 4 = 0 then p0 else p1))
      have := cellNat_cost P (by includes)
        (if l.val < 2 then σ (.n (foldPos 35 32 fold a + 16 * l.val))
          else σ (.n (if a / 4 = 0 then p0 else p1)))
      rw [limbs_of_lt (by omega : l.val < 2 ^ 64)]
      split_ifs <;> limbs_one <;> cost_facts [cellNat_cost P, hS] <;> omega) 0 (Nat.zero_le _)
  simp only [Sphincs.forestChainCount, Sphincs.forestSubtreeHeight, Nat.sub_zero] at m0 m1 ⊢
  omega

/-- A sub-tree's opening, off the tables (`subOpeningNC`, `subOpeningA`): its key and arm read
once, its cells below `2^20`: at most `11·S + 6751`. -/
theorem subOpeningA_cost (hP : Includes P Decoder.subOpeningNC.costDeps) (lanes : List ℕ)
    (hlanes : ∀ x ∈ lanes, x < 2 ^ 64) (fk : Array (Array ℕ)) (hfk : ∀ r k, offAtA fk r k < 2 ^ 20)
    (b fold p0 p1 : ℕ) (hb : b < 2 ^ 20) (hfold : fold < 2 ^ 20) :
    machineCost P Decoder.subOpeningNC.costIdx
      [encodeValue lanes, encodeValue fk, σV, encodeValue b, encodeValue fold, encodeValue p0,
        encodeValue p1] ≤ 11 * S + 6751 := by
  rw [Decoder.subOpeningNC.costEq P hP lanes fk σ σV hσ, limbs_of_lt (by omega : b < 2 ^ 64),
    limbs_of_lt (by omega : b + 6 < 2 ^ 64)]
  have := hS (.n (b + 6)); have := hS (.n b)
  have := logGTWith_cost P (by includes) lanes hlanes (σ (.n (b + 6))) 256 (by norm_num)
  have := logGTWith_cost P (by includes) lanes hlanes (σ (.n b)) 8 (by norm_num)
  have := logGTWith_le lanes (σ (.n b)) 8
  have := subOpeningAt_cost P hσ hS (by includes) fk hfk b fold p0 p1
    (logGTWith lanes (σ (.n (b + 6))) 256) (logGTWith lanes (σ (.n b)) 8) hb hfold (by omega)
  omega

/-- A coordinate's opening at its positions `r`, its arm `s` given (`coordOpeningAtC`), `s < 2^20`:
at most `26·S + 13889`. -/
theorem coordOpeningAt_cost (hP : Includes P Decoder.coordOpeningAtC.costDeps) (lanes : List ℕ)
    (hlanes : ∀ x ∈ lanes, x < 2 ^ 64) (fk : Array (Array ℕ)) (hfk : ∀ r k, offAtA fk r k < 2 ^ 20)
    (r : SCoord)
    (hr : r.b < 2 ^ 19 ∧ r.f0 < 2 ^ 20 ∧ r.s1 < 2 ^ 20 ∧ r.f1 < 2 ^ 20 ∧ r.top < 2 ^ 20)
    (s : ℕ) (hs : s < 2 ^ 20) :
    machineCost P Decoder.coordOpeningAtC.costIdx
      [encodeValue lanes, encodeValue fk, σV, encodeValue r, encodeValue s] ≤ 26 * S + 13889 := by
  obtain ⟨hb, hf0, hs1, hf1, htop⟩ := hr
  rw [Decoder.coordOpeningAtC.costEq P hP lanes fk σ σV hσ, ofFnFrom_length, ofFnFrom_length]
  have m0 := ofFnFrom_cost P (by includes) (n := 2) (by norm_num) _
    (.closure Decoder.coordOpeningAtC.lam0.costIdx
      [encodeValue lanes, encodeValue fk, σV, encodeValue r])
    (fun j ↦ RunsApp.of_spec (Decoder.coordOpeningAtC.lam0.costSpec P (by includes) lanes fk σ σV
      hσ r j))
    (11 * S + 6773) (fun j ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.cons_append,
        List.nil_append, Decoder.coordOpeningAtC.lam0.costEq P (by includes) lanes fk σ σV hσ, List.length_cons, List.length_cons, List.length_cons, List.length_cons, List.length_nil]
      have := j.isLt
      have := subOpeningA_cost P hσ hS (by includes) lanes hlanes fk hfk (r.b + 10) r.f0 r.p00
        r.p01 (by omega) hf0
      have := subOpeningA_cost P hσ hS (by includes) lanes hlanes fk hfk r.s1 r.f1 r.p10 r.p11
        hs1 hf1
      rw [limbs_of_lt (by omega : j.val < 2 ^ 64)]
      split_ifs
      · rw [limbs_of_lt (by omega : r.b < 2 ^ 64), limbs_of_lt (by omega : r.b + 10 < 2 ^ 64)]; omega
      · omega) 0 (Nat.zero_le _)
  have m1 := ofFnFrom_cost P (by includes) (n := Sphincs.topTreeHeight) (by decide) _
    (.closure Decoder.coordOpeningAtC.lam1.costIdx [σV, encodeValue r, encodeValue s])
    (fun l ↦ RunsApp.of_spec (Decoder.coordOpeningAtC.lam1.costSpec P (by includes) σ σV hσ r s l))
    (S + 51) (fun l ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.nil_append,
        Decoder.coordOpeningAtC.lam1.costEq P (by includes) σ σV hσ, List.length_cons, List.length_cons, List.length_cons, List.length_nil]
      have hl := l.isLt
      simp only [Sphincs.topTreeHeight] at hl
      have := foldPos_cost P (by includes) 54 51 r.top s (by norm_num) (by norm_num) htop hs
      have := foldPos_lt 54 51 r.top s (by norm_num) (by norm_num) htop hs
      have := hS (.n (foldPos 54 51 r.top s + 17 * l.val))
      have := hS (.n (if s / 8 = 0 then r.q0 else r.q1))
      have := cellNat_cost P (by includes)
        (if l.val < 3 then σ (.n (foldPos 54 51 r.top s + 17 * l.val))
          else σ (.n (if s / 8 = 0 then r.q0 else r.q1)))
      rw [limbs_of_lt (by omega : l.val < 2 ^ 64)]
      split_ifs <;> limbs_one <;> cost_facts [cellNat_cost P, hS] <;> omega) 0 (Nat.zero_le _)
  simp only [Sphincs.topTreeHeight, Nat.sub_zero] at m0 m1 ⊢
  omega

/-- A coordinate's opening, off the tables (`coordOpeningNC`, `coordOpeningA`): its arm read once:
at most `27·S + 14300`. -/
theorem coordOpeningA_cost (hP : Includes P Decoder.coordOpeningNC.costDeps) (lanes : List ℕ)
    (hlanes : ∀ x ∈ lanes, x < 2 ^ 64) (fk : Array (Array ℕ)) (hfk : ∀ r k, offAtA fk r k < 2 ^ 20)
    (r : SCoord)
    (hr : r.b < 2 ^ 19 ∧ r.f0 < 2 ^ 20 ∧ r.s1 < 2 ^ 20 ∧ r.f1 < 2 ^ 20 ∧ r.top < 2 ^ 20) :
    machineCost P Decoder.coordOpeningNC.costIdx
      [encodeValue lanes, encodeValue fk, σV, encodeValue r] ≤ 27 * S + 14300 := by
  rw [Decoder.coordOpeningNC.costEq P hP lanes fk σ σV hσ]
  have := hS (.n r.b)
  have := logGTWith_cost P (by includes) lanes hlanes (σ (.n r.b)) 16 (by norm_num)
  have := logGTWith_le lanes (σ (.n r.b)) 16
  have := coordOpeningAt_cost P hσ hS (by includes) lanes hlanes fk hfk r hr
    (logGTWith lanes (σ (.n r.b)) 16) (by omega)
  omega

/-- **A leanSPHINCS signature, off the tables `T`** (`sphincsSigOfNC`, `sphincsSigOfA`): at most
`450·S + 220065`. -/
theorem sphincsSigOfN_cost (hP : Includes P Decoder.sphincsSigOfNC.costDeps) (T : SphincsTabs)
    (hT : SphincsTabsOK T) :
    machineCost P Decoder.sphincsSigOfNC.costIdx [encodeValue T, σV] ≤ 450 * S + 220065 := by
  rw [Decoder.sphincsSigOfNC.costEq P hP T σ σV hσ, ofFnFrom_length, ofFnFrom_length,
    ofFnFrom_length]
  have := hS (.n 3); have := hS (.n 412448)
  have := cellNat_cost P (by includes) (σ (.n 3))
  have := cellNat_cost P (by includes) (σ (.n 412448))
  have hl1 := limbs_le_of_lt (x := Sig.cellNat (σ (.n 412448))) (k := 2) (by norm_num)
    (Decoder.cellNat_lt _)
  rw [limbs_of_lt (by norm_num : 2 ^ 32 - 1 < 2 ^ 64)]
  have m0 := ofFnFrom_cost P (by includes) (n := Sphincs.forestCoordinateCount) (by decide) _
    (.closure Decoder.sphincsSigOfNC.lam0.costIdx [encodeValue T, σV])
    (fun c ↦ RunsApp.of_spec (Decoder.sphincsSigOfNC.lam0.costSpec P (by includes) T σ σV hσ c))
    (27 * S + 14336) (fun c ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.nil_append,
        Decoder.sphincsSigOfNC.lam0.costEq P (by includes) T σ σV hσ,
        Decoder.sCoord0C.costEq P (by includes), List.length_cons, List.length_cons, List.length_nil]
      have := coordOpeningA_cost P hσ hS (by includes) T.lanes hT.lanes T.fkOff hT.fkOff
        (T.coords.getD c.val sCoord0) (hT.coords c.val)
      omega) 0 (Nat.zero_le _)
  have m1 := ofFnFrom_cost P (by includes) (n := Sphincs.chainCount) (by decide) _
    (.closure Decoder.sphincsSigOfNC.lam1.costIdx [encodeValue T, σV])
    (fun i ↦ RunsApp.of_spec (Decoder.sphincsSigOfNC.lam1.costSpec P (by includes) T σ σV hσ i))
    (2 * S + 1580) (fun i ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.nil_append,
        Decoder.sphincsSigOfNC.lam1.costEq P (by includes) T σ σV hσ, List.length_cons, List.length_cons, List.length_nil]
      have := cwCellA_cost P hσ hS (by includes) T.lanes hT.lanes 21 T.sel T.first T.rest T.last
        hT.sel hT.first hT.rest hT.last (by norm_num) i.val
        (by have := i.isLt; simp only [Sphincs.chainCount] at this; omega)
      have := cellNat_cost P (by includes)
        (σ (.n (cwCellA T.lanes 21 T.sel T.first T.rest T.last σ i.val)))
      have := hS (.n (cwCellA T.lanes 21 T.sel T.first T.rest T.last σ i.val))
      omega) 0 (Nat.zero_le _)
  have m2 := ofFnFrom_cost P (by includes) (n := Sphincs.treeHeight) (by decide) _
    (.closure Decoder.sphincsSigOfNC.lam2.costIdx [encodeValue T, σV])
    (fun l ↦ RunsApp.of_spec (Decoder.sphincsSigOfNC.lam2.costSpec P (by includes) T σ σV hσ l))
    (4 * S + 96) (fun l ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.nil_append,
        Decoder.sphincsSigOfNC.lam2.costEq P (by includes) T σ σV hσ, List.length_cons, List.length_cons, List.length_nil]
      have hl := l.isLt
      simp only [Sphincs.treeHeight] at hl
      have := hT.path l.val
      have := sibN_cost P hσ hS (by includes) (30 + l.val) (T.path.getD l.val 0) (by omega)
      have := cellNat_cost P (by includes) (sibN σ (30 + l.val) (T.path.getD l.val 0))
      rw [limbs_of_lt (by omega : l.val < 2 ^ 64), limbs_of_lt (by omega : 30 + l.val < 2 ^ 64)]
      omega) 0 (Nat.zero_le _)
  have hnc : Sphincs.chainCount = 64 := rfl
  rw [hnc] at m1 ⊢
  simp only [Sphincs.forestCoordinateCount, Sphincs.treeHeight, Nat.sub_zero] at m0 m1 m2 ⊢
  omega

end Val

end

end LeanVM.Cost.Bounds.Guest
