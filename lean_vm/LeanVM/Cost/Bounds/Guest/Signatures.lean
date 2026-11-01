module

public import LeanVM.Cost.Bounds.Guest.Readers
public import LeanVM.Cost.Decoder.Signatures

/-!
# Bounds on the guest decoder's prices: the signatures

The readers of a leanXMSS and a leanSPHINCS signature off their checks' valuations
(`Cost/Decoder/Signatures.lean`, `Guest/Fast/{Xmss,Sphincs}.lean`), in the price `S` of an
application of the valuation: a signature has a fixed shape, so its price is `a·S + b`:

* the tables' facts (`gLanes_ok`, `xTabs_ok`, `sTabs_ok`, … by kernel evaluation of the literals);
* an exponent off the lanes of `g^k` (`idxBelow_cost`, `logGT_cost`: `25·bound + 1200`), a
  sibling (`sibN_cost`), the bits of a leaf index (`bitsN_cost`), a chain's start cell
  (`cwCell_cost`: `S + 4210`);
* **`xmssSigOfN_cost`**: `458·S + 714422`;
* `subOpeningN_cost`, `coordOpeningN_cost`, **`sphincsSigOfN_cost`**: `450·S + 1660929`.
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

/-! ## The exponent off the lanes -/

theorem idxBelow_le (w : ℕ) : ∀ (l : List ℕ) (i m : ℕ), idxBelow w l i m ≤ i + m
  | [], _, _ => by simp [idxBelow]
  | _ :: _, _, 0 => by simp [idxBelow]
  | t :: ts, i, m + 1 => by
    rw [idxBelow]
    split_ifs
    · omega
    · have := idxBelow_le w ts (i + 1) m; omega

theorem logGT_le (x : E) (b : ℕ) : logGT x b ≤ b := by
  unfold logGT; split_ifs
  · have := idxBelow_le (x.limb 0).lane.toNat gLanes 0 b; omega
  · omega

/-- The search among the lanes (`idxBelow.c593`), `m` entries: at most `25·m + 8`. -/
theorem idxBelow_cost (hP : Includes P Auto.LeanVM.Guest.Fast.idxBelow.c593.costDeps) (w : ℕ)
    (hw : w < 2 ^ 64) : ∀ (l : List ℕ) (i m : ℕ), (∀ x ∈ l, x < 2 ^ 64) → i + m < 2 ^ 64 →
      machineCost P Auto.LeanVM.Guest.Fast.idxBelow.c593.costIdx
        [encodeValue w, encodeValue l, encodeValue i, encodeValue m] ≤ 25 * m + 8
  | [], i, m, _, _ => by rw [Auto.LeanVM.Guest.Fast.idxBelow.c593.costEq_nil P hP]; omega
  | t :: ts, i, m, hl, him => by
    rw [Auto.LeanVM.Guest.Fast.idxBelow.c593.costEq_cons P hP, limbs_of_lt (by omega : m < 2 ^ 64)]
    cases m with
    | zero => simp
    | succ k =>
      have ht := hl t (by simp)
      have := idxBelow_cost hP w hw ts (i + 1) k (fun x hx ↦ hl x (by simp [hx])) (by omega)
      dsimp only
      rw [limbs_of_lt hw, limbs_of_lt ht, limbs_of_lt (by omega : i < 2 ^ 64)]
      split_ifs <;> omega

/-- **An exponent off the lanes** (`logGTC`), `bound < 2^32`: at most `25·bound + 1200`. -/
theorem logGT_cost (hP : Includes P Decoder.logGTC.costDeps) (x : E) (b : ℕ) (hb : b < 2 ^ 32) :
    machineCost P Decoder.logGTC.costIdx [encodeValue x, encodeValue b] ≤ 25 * b + 1200 := by
  rw [Decoder.logGTC.costEq P hP]
  have := idxBelow_cost P (by includes) (x.limb 0).lane.toNat (UInt64.toNat_lt _) gLanes 0 b
    gLanes_ok.2 (by omega)
  rw [Auto.LeanVM.Guest.Fast.gLanes.c594.costEq P (by includes)]
  split_ifs <;> omega

section Val

variable {σ : Val} {σV : MachineValue}
  (hσ : ∀ v : V, RunsApp P σV [encodeValue v] (encodeValue (σ v)))
  {S : ℕ} (hS : ∀ v : V, appCost P σV [encodeValue v] ≤ S)
include hσ hS

/-- A path level's sibling (`sibN.c602`): at most `4·S + 73`. -/
theorem sibN_cost (hP : Includes P Auto.LeanVM.Guest.Fast.sibN.c602.costDeps) (bit b : ℕ)
    (hb : b < 2 ^ 64) :
    machineCost P Auto.LeanVM.Guest.Fast.sibN.c602.costIdx [σV, encodeValue bit, encodeValue b] ≤
      4 * S + 73 := by
  rw [Auto.LeanVM.Guest.Fast.sibN.c602.costEq P hP σ σV hσ, limbs_of_lt hb]
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

/-- The integer of `n ≤ 32` bits (`bitsN.c604`): at most `(3·S + 93)·n + 6`. -/
theorem bitsN_cost (hP : Includes P Auto.LeanVM.Guest.Fast.bitsN.c604.costDeps) (base : ℕ)
    (hbase : base < 2 ^ 32) : ∀ n, n ≤ 32 →
      machineCost P Auto.LeanVM.Guest.Fast.bitsN.c604.costIdx [σV, encodeValue base, encodeValue n] ≤
        (3 * S + 93) * n + 6
  | 0, _ => by rw [Auto.LeanVM.Guest.Fast.bitsN.c604.costEq_zero P hP σ σV hσ]; omega
  | n + 1, hn => by
    rw [Auto.LeanVM.Guest.Fast.bitsN.c604.costEq_succ P hP σ σV hσ]
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
      limbs_of_lt (by omega : bitsN σ base n < 2 ^ 64), limbs_of_lt (by omega)]
    have := hS (.n (base + n))
    simp only [max_self, Nat.mul_one, Bool.cond_decide, ite_self]
    split_ifs <;> nlinarith

/-- **A chain's start cell** (`cwCellC`), its tables' rows at most `64` entries below `2^20`, at
most `3` rows, at most `22` selector cells: at most `S + 4210`. -/
theorem cwCell_cost (hP : Includes P Decoder.cwCellC.costDeps) (G : ℕ) (sel : List ℕ)
    (first rest last : List (List ℕ)) (hsel : ListOK 22 sel) (hf : RowsOK 64 first)
    (hr : RowsOK 64 rest) (hl : RowsOK 64 last) (hfl : first.length ≤ 3) (hrl : rest.length ≤ 3)
    (hll : last.length ≤ 3) (hG : G < 2 ^ 20) (i : ℕ) (hi : i < 2 ^ 20) :
    machineCost P Decoder.cwCellC.costIdx [encodeValue G, encodeValue sel, encodeValue first,
      encodeValue rest, encodeValue last, σV, encodeValue i] ≤ S + 4210 := by
  rw [Decoder.cwCellC.costEq P hP _ _ _ _ _ σ σV hσ]
  have hs := getD_cost P (by includes) sel (i / 3) 0 (by omega)
  have hsl := getD_lt_of hsel.2 (by norm_num) (i / 3)
  rw [limbs_of_lt (by omega : i < 2 ^ 64), limbs_of_lt (by omega : i / 3 < 2 ^ 64),
    limbs_of_lt (by omega : G < 2 ^ 64), limbs_of_lt (by omega : sel.getD (i / 3) 0 < 2 ^ 64)]
  have := hS (.n (sel.getD (i / 3) 0))
  split_ifs with h1 h2
  · have := getD_cost P (by includes) first (i % 3) [] (by omega)
    have := logGT_cost P (by includes) (σ (.n (sel.getD (i / 3) 0))) 64 (by norm_num)
    have := logGT_le (σ (.n (sel.getD (i / 3) 0))) 64
    have hrow := getD_row hf (i % 3)
    have := getD_cost P (by includes) (first.getD (i % 3) [])
      (logGT (σ (.n (sel.getD (i / 3) 0))) 64) 0 (by omega)
    have ho := offAt_lt hf (i % 3) (logGT (σ (.n (sel.getD (i / 3) 0))) 64)
    rw [limbs_of_lt (lt_trans ho (by norm_num))]
    have := hsel.1; have := hrow.1
    omega
  · have := getD_cost P (by includes) rest (i % 3) [] (by omega)
    have := logGT_cost P (by includes) (σ (.n (sel.getD (i / 3) 0))) 64 (by norm_num)
    have := logGT_le (σ (.n (sel.getD (i / 3) 0))) 64
    have hrow := getD_row hr (i % 3)
    have := getD_cost P (by includes) (rest.getD (i % 3) [])
      (logGT (σ (.n (sel.getD (i / 3) 0))) 64) 0 (by omega)
    have ho := offAt_lt hr (i % 3) (logGT (σ (.n (sel.getD (i / 3) 0))) 64)
    rw [limbs_of_lt (lt_trans ho (by norm_num))]
    have := hsel.1; have := hrow.1
    omega
  · have := getD_cost P (by includes) last (i % 3) [] (by omega)
    have := logGT_cost P (by includes) (σ (.n (sel.getD (i / 3) 0))) 4 (by norm_num)
    have := logGT_le (σ (.n (sel.getD (i / 3) 0))) 4
    have hrow := getD_row hl (i % 3)
    have := getD_cost P (by includes) (last.getD (i % 3) [])
      (logGT (σ (.n (sel.getD (i / 3) 0))) 4) 0 (by omega)
    have ho := offAt_lt hl (i % 3) (logGT (σ (.n (sel.getD (i / 3) 0))) 4)
    rw [limbs_of_lt (lt_trans ho (by norm_num))]
    have := hsel.1; have := hrow.1
    omega

/-! ## leanXMSS -/

/-- A layer's signature (`xPartNC`), its selectors and path a table's: at most
`181·S + 355534`. -/
theorem xPartN_cost (hP : Includes P Decoder.xPartNC.costDeps) (rho bitBase : ℕ)
    (sel path : List ℕ) (hsel : ListOK 22 sel) (hpath : ListOK 16 path) (hb : bitBase < 2 ^ 20) :
    machineCost P Decoder.xPartNC.costIdx
      [encodeValue rho, encodeValue bitBase, encodeValue sel, encodeValue path, σV] ≤
        181 * S + 355534 := by
  rw [Decoder.xPartNC.costEq P hP _ _ _ _ σ σV hσ, ofFnFrom_length, ofFnFrom_length]
  have hc := cellNat_cost P (by includes) (σ (.n rho))
  have := hS (.n rho)
  obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := xTabs_ok
  have m0 := ofFnFrom_cost P (by includes) (n := LeanXmss.numChains) (by decide) _
    (.closure Decoder.xPartNC.lam0.costIdx [encodeValue sel, σV])
    (fun i ↦ RunsApp.of_spec (Decoder.xPartNC.lam0.costSpec P (by includes) sel σ σV hσ i))
    (2 * S + 6008) (fun i ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.nil_append,
        Decoder.xPartNC.lam0.costEq P (by includes) sel σ σV hσ,
        Auto.LeanVM.Guest.Fast.xFirst.c598.costEq P (by includes),
        Auto.LeanVM.Guest.Fast.xRest.c599.costEq P (by includes),
        Auto.LeanVM.Guest.Fast.xLast.c600.costEq P (by includes)]
      have := cwCell_cost P hσ hS (by includes) 19 sel xFirst xRest xLast hsel h1 h2 h3 h4 h5 h6
        (by norm_num) i.val (by have := i.isLt; simp only [LeanXmss.numChains] at this; omega)
      have := cellNat_cost P (by includes) (σ (.n (cwCell 19 sel xFirst xRest xLast σ i.val)))
      have := hS (.n (cwCell 19 sel xFirst xRest xLast σ i.val))
      omega) 0 (Nat.zero_le _)
  have m1 := ofFnFrom_cost P (by includes) (n := LeanXmss.layerHeight) (by decide) _
    (.closure Decoder.xPartNC.lam1.costIdx [encodeValue bitBase, encodeValue path, σV])
    (fun l ↦ RunsApp.of_spec (Decoder.xPartNC.lam1.costSpec P (by includes) bitBase path σ σV hσ l))
    (4 * S + 350) (fun l ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.nil_append,
        Decoder.xPartNC.lam1.costEq P (by includes) bitBase path σ σV hσ]
      have hl := l.isLt
      simp only [LeanXmss.layerHeight] at hl
      have := getD_cost P (by includes) path l.val 0 (by omega)
      have := getD_lt_of hpath.2 (by norm_num) l.val
      have := sibN_cost P hσ hS (by includes) (bitBase + l.val) (path.getD l.val 0) (by omega)
      have := cellNat_cost P (by includes) (sibN σ (bitBase + l.val) (path.getD l.val 0))
      rw [limbs_of_lt (by omega : bitBase < 2 ^ 64), limbs_of_lt (by omega : l.val < 2 ^ 64)]
      have := hpath.1
      omega) 0 (Nat.zero_le _)
  simp only [LeanXmss.numChains, LeanXmss.layerHeight, Nat.sub_zero] at m0 m1 ⊢
  omega

/-- **A leanXMSS signature** (`xmssSigOfNC`): at most `458·S + 714422`. -/
theorem xmssSigOfN_cost (hP : Includes P Decoder.xmssSigOfNC.costDeps) :
    machineCost P Decoder.xmssSigOfNC.costIdx [σV] ≤ 458 * S + 714422 := by
  rw [Decoder.xmssSigOfNC.costEq P hP σ σV hσ, ofFnFrom_length]
  have hb := bitsN_cost P hσ hS (by includes) 2 (by norm_num) 32 le_rfl
  obtain ⟨-, -, -, -, -, -, s0, s1, p0, p1⟩ := xTabs_ok
  have m := ofFnFrom_cost P (by includes) (n := LeanXmss.numLayers) (by decide) _
    (.closure Decoder.xmssSigOfNC.lam0.costIdx [σV])
    (fun l ↦ RunsApp.of_spec (Decoder.xmssSigOfNC.lam0.costSpec P (by includes) σ σV hσ l))
    (181 * S + 355691) (fun l ↦ by
      rw [appCost_fn, List.cons_append, List.nil_append,
        Decoder.xmssSigOfNC.lam0.costEq P (by includes) σ σV hσ]
      have hl := l.isLt
      simp only [LeanXmss.numLayers] at hl
      rw [limbs_of_lt (by omega : l.val < 2 ^ 64),
        Auto.LeanVM.Guest.Fast.xSel0.c606.costEq P (by includes),
        Auto.LeanVM.Guest.Fast.xPath0.c607.costEq P (by includes),
        Auto.LeanVM.Guest.Fast.xSel1.c608.costEq P (by includes),
        Auto.LeanVM.Guest.Fast.xPath1.c609.costEq P (by includes)]
      have := xPartN_cost P hσ hS (by includes) 196 2 xSel0 xPath0 s0 p0 (by norm_num)
      have := xPartN_cost P hσ hS (by includes) 12604 18 xSel1 xPath1 s1 p1 (by norm_num)
      split_ifs <;> omega) 0 (Nat.zero_le _)
  simp only [LeanXmss.numLayers, Nat.sub_zero] at m ⊢
  omega

/-! ## leanSPHINCS -/

omit hσ hS in
theorem foldPos_cost (hP : Includes P Auto.LeanVM.Guest.Fast.foldPos.c614.costDeps)
    (first rest b a : ℕ) (hf : first < 2 ^ 20) (hr : rest < 2 ^ 20) (hb : b < 2 ^ 20)
    (ha : a < 2 ^ 20) :
    machineCost P Auto.LeanVM.Guest.Fast.foldPos.c614.costIdx
      [encodeValue first, encodeValue rest, encodeValue b, encodeValue a] ≤ 18 := by
  rw [Auto.LeanVM.Guest.Fast.foldPos.c614.costEq P hP]
  have : rest * (a - 1) < 2 ^ 40 := by
    calc rest * (a - 1) < 2 ^ 20 * 2 ^ 20 := Nat.mul_lt_mul_of_lt_of_le hr (by omega) (by norm_num)
      _ = 2 ^ 40 := by norm_num
  split_ifs
  · rw [limbs_of_lt (by omega : a < 2 ^ 64)]; omega
  · rw [limbs_of_lt (by omega : a < 2 ^ 64), limbs_of_lt (by omega : b < 2 ^ 64),
      limbs_of_lt (by omega : first < 2 ^ 64), limbs_of_lt (by omega : rest < 2 ^ 64),
      limbs_of_lt (by omega : a - 1 < 2 ^ 64), limbs_of_lt (by omega : b + first < 2 ^ 64),
      limbs_of_lt (by omega : rest * (a - 1) < 2 ^ 64)]
    omega

omit hσ hS in
theorem foldPos_lt (first rest b a : ℕ) (hf : first < 2 ^ 20) (hr : rest < 2 ^ 20)
    (hb : b < 2 ^ 20) (ha : a < 2 ^ 20) : foldPos first rest b a < 2 ^ 42 := by
  unfold foldPos
  have : rest * (a - 1) < 2 ^ 40 := by
    calc rest * (a - 1) < 2 ^ 20 * 2 ^ 20 := Nat.mul_lt_mul_of_lt_of_le hr (by omega) (by norm_num)
      _ = 2 ^ 40 := by norm_num
  split_ifs <;> omega

/-- A sub-tree's opening (`subOpeningNC`), its cells below `2^20`: at most `11·S + 77108`. -/
theorem subOpeningN_cost (hP : Includes P Decoder.subOpeningNC.costDeps) (b fold p0 p1 : ℕ)
    (hb : b < 2 ^ 20) (hfold : fold < 2 ^ 20) :
    machineCost P Decoder.subOpeningNC.costIdx
      [σV, encodeValue b, encodeValue fold, encodeValue p0, encodeValue p1] ≤ 11 * S + 77108 := by
  rw [Decoder.subOpeningNC.costEq P hP σ σV hσ, ofFnFrom_length, ofFnFrom_length,
    limbs_of_lt (by omega : b < 2 ^ 64)]
  have := hS (.n (b + 6)); have := hS (.n b)
  have := logGT_cost P (by includes) (σ (.n (b + 6))) 256 (by norm_num)
  have := logGT_cost P (by includes) (σ (.n b)) 8 (by norm_num)
  obtain ⟨-, -, -, -, -, -, -, -, hk, hkl⟩ := sTabs_ok
  have m0 := ofFnFrom_cost P (by includes) (n := Sphincs.childChains) (by decide) _
    (.closure Decoder.subOpeningNC.lam0.costIdx
      [σV, encodeValue b, encodeValue (logGT (σ (.n (b + 6))) 256)])
    (fun i ↦ RunsApp.of_spec (Decoder.subOpeningNC.lam0.costSpec P (by includes) σ σV hσ b _ i))
    (S + 11281) (fun i ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.nil_append,
        Decoder.subOpeningNC.lam0.costEq P (by includes) σ σV hσ,
        Auto.LeanVM.Guest.Fast.fkOff.c612.costEq P (by includes)]
      have hi := i.isLt
      simp only [Sphincs.childChains] at hi
      have := logGT_le (σ (.n (b + 6))) 256
      have := getD_cost P (by includes) fkOff (logGT (σ (.n (b + 6))) 256) [] (by omega)
      have hrow := getD_row hk (logGT (σ (.n (b + 6))) 256)
      have := getD_cost P (by includes) (fkOff.getD (logGT (σ (.n (b + 6))) 256) []) i.val 0
        (by omega)
      have := offAt_lt hk (logGT (σ (.n (b + 6))) 256) i.val
      have := hS (.n (b + 12 + offAt fkOff (logGT (σ (.n (b + 6))) 256) i.val))
      have := cellNat_cost P (by includes)
        (σ (.n (b + 12 + offAt fkOff (logGT (σ (.n (b + 6))) 256) i.val)))
      rw [limbs_of_lt (by omega : b < 2 ^ 64), limbs_of_lt (by omega : b + 12 < 2 ^ 64),
        limbs_of_lt (by unfold offAt at *; omega)]
      omega) 0 (Nat.zero_le _)
  have m1 := ofFnFrom_cost P (by includes) (n := Sphincs.subHeight) (by decide) _
    (.closure Decoder.subOpeningNC.lam1.costIdx
      [σV, encodeValue fold, encodeValue p0, encodeValue p1,
        encodeValue (logGT (σ (.n b)) 8)])
    (fun l ↦ RunsApp.of_spec (Decoder.subOpeningNC.lam1.costSpec P (by includes) σ σV hσ fold p0
      p1 _ l))
    (S + 61) (fun l ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.cons_append,
        List.cons_append, List.nil_append,
        Decoder.subOpeningNC.lam1.costEq P (by includes) σ σV hσ]
      have hl := l.isLt
      simp only [Sphincs.subHeight] at hl
      have := logGT_le (σ (.n b)) 8
      have := foldPos_cost P (by includes) 35 32 fold (logGT (σ (.n b)) 8) (by norm_num)
        (by norm_num) hfold (by omega)
      have := foldPos_lt 35 32 fold (logGT (σ (.n b)) 8) (by norm_num) (by norm_num) hfold (by omega)
      have := hS (.n (foldPos 35 32 fold (logGT (σ (.n b)) 8) + 16 * l.val))
      have := hS (.n (if logGT (σ (.n b)) 8 / 4 = 0 then p0 else p1))
      have := cellNat_cost P (by includes)
        (if l.val < 2 then σ (.n (foldPos 35 32 fold (logGT (σ (.n b)) 8) + 16 * l.val))
          else σ (.n (if logGT (σ (.n b)) 8 / 4 = 0 then p0 else p1)))
      rw [limbs_of_lt (by omega : l.val < 2 ^ 64)]
      split_ifs <;> limbs_one <;> cost_facts [cellNat_cost P, hS] <;> omega) 0 (Nat.zero_le _)
  simp only [Sphincs.childChains, Sphincs.subHeight, Nat.sub_zero] at m0 m1 ⊢
  omega

/-- A coordinate's opening (`coordOpeningNC`), its positions below `2^20`: at most
`27·S + 156262`. -/
theorem coordOpeningN_cost (hP : Includes P Decoder.coordOpeningNC.costDeps) (r : SCoord)
    (hr : r.b < 2 ^ 19 ∧ r.f0 < 2 ^ 20 ∧ r.s1 < 2 ^ 20 ∧ r.f1 < 2 ^ 20 ∧ r.top < 2 ^ 20) :
    machineCost P Decoder.coordOpeningNC.costIdx [σV, encodeValue r] ≤ 27 * S + 156262 := by
  obtain ⟨hb, hf0, hs1, hf1, htop⟩ := hr
  rw [Decoder.coordOpeningNC.costEq P hP σ σV hσ, ofFnFrom_length, ofFnFrom_length]
  have := hS (.n r.b)
  have := logGT_cost P (by includes) (σ (.n r.b)) 16 (by norm_num)
  have m0 := ofFnFrom_cost P (by includes) (n := 2) (by norm_num) _
    (.closure Decoder.coordOpeningNC.lam0.costIdx [σV, encodeValue r])
    (fun j ↦ RunsApp.of_spec (Decoder.coordOpeningNC.lam0.costSpec P (by includes) σ σV hσ r j))
    (11 * S + 77126) (fun j ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.nil_append,
        Decoder.coordOpeningNC.lam0.costEq P (by includes) σ σV hσ]
      have := j.isLt
      have := subOpeningN_cost P hσ hS (by includes) (r.b + 10) r.f0 r.p00 r.p01 (by omega) hf0
      have := subOpeningN_cost P hσ hS (by includes) r.s1 r.f1 r.p10 r.p11 hs1 hf1
      rw [limbs_of_lt (by omega : j.val < 2 ^ 64)]
      split_ifs
      · rw [limbs_of_lt (by omega : r.b < 2 ^ 64)]; omega
      · omega) 0 (Nat.zero_le _)
  have m1 := ofFnFrom_cost P (by includes) (n := Sphincs.topHeight) (by decide) _
    (.closure Decoder.coordOpeningNC.lam1.costIdx
      [σV, encodeValue r, encodeValue (logGT (σ (.n r.b)) 16)])
    (fun l ↦ RunsApp.of_spec (Decoder.coordOpeningNC.lam1.costSpec P (by includes) σ σV hσ r _ l))
    (S + 62) (fun l ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.nil_append,
        Decoder.coordOpeningNC.lam1.costEq P (by includes) σ σV hσ]
      have hl := l.isLt
      simp only [Sphincs.topHeight] at hl
      have := logGT_le (σ (.n r.b)) 16
      have := foldPos_cost P (by includes) 54 51 r.top (logGT (σ (.n r.b)) 16) (by norm_num)
        (by norm_num) htop (by omega)
      have := foldPos_lt 54 51 r.top (logGT (σ (.n r.b)) 16) (by norm_num) (by norm_num) htop
        (by omega)
      have := hS (.n (foldPos 54 51 r.top (logGT (σ (.n r.b)) 16) + 17 * l.val))
      have := hS (.n (if logGT (σ (.n r.b)) 16 / 8 = 0 then r.q0 else r.q1))
      have := cellNat_cost P (by includes)
        (if l.val < 3 then σ (.n (foldPos 54 51 r.top (logGT (σ (.n r.b)) 16) + 17 * l.val))
          else σ (.n (if logGT (σ (.n r.b)) 16 / 8 = 0 then r.q0 else r.q1)))
      rw [limbs_of_lt (by omega : l.val < 2 ^ 64)]
      split_ifs <;> limbs_one <;> cost_facts [cellNat_cost P, hS] <;> omega) 0 (Nat.zero_le _)
  simp only [Sphincs.topHeight, Nat.sub_zero] at m0 m1 ⊢
  omega

/-- **A leanSPHINCS signature** (`sphincsSigOfNC`): at most `450·S + 1660929`. -/
theorem sphincsSigOfN_cost (hP : Includes P Decoder.sphincsSigOfNC.costDeps) :
    machineCost P Decoder.sphincsSigOfNC.costIdx [σV] ≤ 450 * S + 1660929 := by
  rw [Decoder.sphincsSigOfNC.costEq P hP σ σV hσ, ofFnFrom_length, ofFnFrom_length,
    ofFnFrom_length]
  have := hS (.n 3); have := hS (.n 412448)
  have := cellNat_cost P (by includes) (σ (.n 3))
  have := cellNat_cost P (by includes) (σ (.n 412448))
  have hl1 := limbs_le_of_lt (x := Sig.cellNat (σ (.n 412448))) (k := 2) (by norm_num)
    (Decoder.cellNat_lt _)
  rw [limbs_two_pow (by norm_num)]
  obtain ⟨h1, h2, h3, h4, h5, h6, hsel, hpath, -, -⟩ := sTabs_ok
  obtain ⟨hcl, hc⟩ := sCoordTab_ok
  have m0 := ofFnFrom_cost P (by includes) (n := Sphincs.forestCoords) (by decide) _
    (.closure Decoder.sphincsSigOfNC.lam0.costIdx [σV])
    (fun c ↦ RunsApp.of_spec (Decoder.sphincsSigOfNC.lam0.costSpec P (by includes) σ σV hσ c))
    (27 * S + 156628) (fun c ↦ by
      rw [appCost_fn, List.cons_append, List.nil_append,
        Decoder.sphincsSigOfNC.lam0.costEq P (by includes) σ σV hσ,
        Auto.LeanVM.Guest.Fast.sCoordTab.c620.costEq P (by includes),
        Auto.LeanVM.Guest.Fast.sCoord0.c621.costEq P (by includes)]
      have hc' := c.isLt
      simp only [Sphincs.forestCoords] at hc'
      have := getD_cost P (by includes) sCoordTab c.val sCoord0 (by omega)
      have := coordOpeningN_cost P hσ hS (by includes) (sCoordTab.getD c.val sCoord0) (sCoord_getD_ok c.val)
      omega) 0 (Nat.zero_le _)
  have m1 := ofFnFrom_cost P (by includes) (n := Sphincs.numChains) (by decide) _
    (.closure Decoder.sphincsSigOfNC.lam1.costIdx [σV])
    (fun i ↦ RunsApp.of_spec (Decoder.sphincsSigOfNC.lam1.costSpec P (by includes) σ σV hσ i))
    (2 * S + 6097) (fun i ↦ by
      rw [appCost_fn, List.cons_append, List.nil_append,
        Decoder.sphincsSigOfNC.lam1.costEq P (by includes) σ σV hσ,
        Auto.LeanVM.Guest.Fast.sSel.c623.costEq P (by includes),
        Auto.LeanVM.Guest.Fast.sFirst.c624.costEq P (by includes),
        Auto.LeanVM.Guest.Fast.sRest.c625.costEq P (by includes),
        Auto.LeanVM.Guest.Fast.sLast.c626.costEq P (by includes)]
      have := cwCell_cost P hσ hS (by includes) 21 sSel sFirst sRest sLast hsel h1 h2 h3 h4 h5 h6
        (by norm_num) i.val (by have := i.isLt; simp only [Sphincs.numChains] at this; omega)
      have := cellNat_cost P (by includes) (σ (.n (cwCell 21 sSel sFirst sRest sLast σ i.val)))
      have := hS (.n (cwCell 21 sSel sFirst sRest sLast σ i.val))
      omega) 0 (Nat.zero_le _)
  have m2 := ofFnFrom_cost P (by includes) (n := Sphincs.totalHeight) (by decide) _
    (.closure Decoder.sphincsSigOfNC.lam2.costIdx [σV])
    (fun l ↦ RunsApp.of_spec (Decoder.sphincsSigOfNC.lam2.costSpec P (by includes) σ σV hσ l))
    (4 * S + 605) (fun l ↦ by
      rw [appCost_fn, List.cons_append, List.nil_append,
        Decoder.sphincsSigOfNC.lam2.costEq P (by includes) σ σV hσ,
        Auto.LeanVM.Guest.Fast.sPath.c628.costEq P (by includes)]
      have hl := l.isLt
      simp only [Sphincs.totalHeight] at hl
      have := getD_cost P (by includes) sPath l.val 0 (by omega)
      have := getD_lt_of hpath.2 (by norm_num) l.val
      have := sibN_cost P hσ hS (by includes) (30 + l.val) (sPath.getD l.val 0) (by omega)
      have := cellNat_cost P (by includes) (sibN σ (30 + l.val) (sPath.getD l.val 0))
      rw [limbs_of_lt (by omega : l.val < 2 ^ 64)]
      have := hpath.1
      omega) 0 (Nat.zero_le _)
  have hnc : Sphincs.numChains = 64 := rfl
  rw [hnc] at m1 ⊢
  simp only [Sphincs.forestCoords, Sphincs.totalHeight, Nat.sub_zero] at m0 m1 m2 ⊢
  omega

end Val

end

end LeanVM.Cost.Bounds.Guest
