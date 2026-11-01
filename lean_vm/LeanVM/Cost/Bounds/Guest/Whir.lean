module

public import LeanVM.Cost.Bounds.Guest.Signatures

/-!
# Bounds on the guest decoder's prices: a child's proof

`verify_sub`'s witness, the child proof (`Cost/Decoder/Signatures.lean`, `Guest/Fast/Whir.lean`):
its stream words and, per level of the opening's candidate (`osCallsTab`), the queries of
`opening_queries` and their openings, in the price `R` of a memory read, `S` of the valuation, `F`
of the frame map, the cursor's length at most `L` and its price at most `C`:

* the levels' shapes (`OqOK`, `callOK_osCallsTab`: the table's every call, by kernel evaluation),
  the shape's numbers (`Oq.R`, `Oq.D`, …: constants);
* a query's position (`posOf_cost`), row (`oqRow_cost`) and siblings (`oqSibsOf_cost`), a query
  (`oqQueryW_cost`), an iteration (`oqIterOf_cost`), the queries (`oqsOfN_cost`), a query's
  opening (`toOpening_cost`, `capSibsOf_cost`), a level (`levelOsN_cost`);
* **`vsPiOfN_cost`**: a child's proof.
-/

namespace LeanVM.Cost.Bounds.Guest

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.Library LeanVM.Parameters
open LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.Fast

public section

variable (P : MachineProgram)

theorem listCasesOn_le {α : Type} (l : List α) (a : ℕ) (f : α → List α → ℕ)
    (hf : ∀ x y, f x y ≤ a) : (List.casesOn (motive := fun _ ↦ ℕ) l a f) ≤ a := by
  cases l
  · exact le_rfl
  · exact hf _ _

/-! ## The levels' shapes -/

/-- A level's shape and its numbers, all small. -/
@[expose] def OqOK (s : Oq) : Prop :=
  s.base ≤ 1 ∧ s.I ≤ 64 ∧ s.pd ≤ 20 ∧ s.cd ≤ 8 ∧ s.R ≤ 192 ∧ s.lo ≤ 64 ∧ s.I / s.lo ≤ 64 ∧
    s.I / 8 ≤ 8 ∧ s.tsz ≤ 3 ∧ s.G < 2 ^ 20 ∧ s.D < 2 ^ 20 ∧ s.ncells ≤ 96 ∧
    16 * s.ncells / LeanVM.Protocol.KeccakHash.rate < 2 ^ 20 ∧ s.B < 2 ^ 20 ∧ s.chainLen < 2 ^ 20 ∧
    (s.lo - 1) * (3 + s.tsz) < 2 ^ 20 ∧ (s.I / s.lo - 1) * (s.G + 1) < 2 ^ 20 ∧
    (s.B - 2) * 22 < 2 ^ 20 ∧ oqE1 s < 2 ^ 20

instance (s : Oq) : Decidable (OqOK s) := by unfold OqOK; infer_instance

/-- An `opening_queries` call of the table: its shape's, its loop's and its words' bounds. -/
@[expose] def CallOK (c : OsCall) : Prop :=
  OqOK ⟨c.base, c.I, c.pd, c.cd⟩ ∧ c.odd ≤ 1 ∧ c.N ≤ 112 ∧ c.fn < 2 ^ 20 ∧ c.loop < 2 ^ 20 ∧
    c.depth ≤ 26 ∧ c.args.length ≤ 7 ∧ c.rets.length ≤ 1

instance (c : OsCall) : Decidable (CallOK c) := by unfold CallOK; infer_instance

theorem callOK_osCallsTab : osCallsTab.length = 28 ∧ (∀ cs ∈ osCallsTab, cs.length ≤ 6) ∧
    ∀ cs ∈ osCallsTab, ∀ c ∈ cs, CallOK c := by decide +kernel

theorem osWordsTab_ok : osWordsTab.length = 28 ∧ ∀ x ∈ osWordsTab, x ≤ 121 := by decide +kernel

theorem callOK_getD (m : ℕ) :
    (osCallsTab.getD m []).length ≤ 6 ∧ ∀ c ∈ osCallsTab.getD m [], CallOK c := by
  rw [List.getD_eq_getElem?_getD]
  cases hk : osCallsTab[m]? with
  | none => simp
  | some cs =>
    have := List.mem_of_getElem? hk
    exact ⟨callOK_osCallsTab.2.1 cs this, callOK_osCallsTab.2.2 cs this⟩

/-! ## The shape's numbers -/

section Shape

variable {s : Oq} (hs : OqOK s)
include hs

theorem Oq_R_cost (hP : Includes P Auto.LeanVM.Guest.B1.Oq.R.c681.costDeps) :
    machineCost P Auto.LeanVM.Guest.B1.Oq.R.c681.costIdx [encodeValue s] ≤ 11 := by
  obtain ⟨h1, h2, -⟩ := hs
  rw [Auto.LeanVM.Guest.B1.Oq.R.c681.costEq P hP]
  limbs_one; split_ifs <;> omega

theorem Oq_tsz_cost (hP : Includes P Auto.LeanVM.Guest.B1.Oq.tsz.c689.costDeps) :
    machineCost P Auto.LeanVM.Guest.B1.Oq.tsz.c689.costIdx [encodeValue s] ≤ 7 := by
  obtain ⟨h1, -⟩ := hs
  rw [Auto.LeanVM.Guest.B1.Oq.tsz.c689.costEq P hP]
  limbs_one; split_ifs <;> omega

theorem rowLo_cost (hP : Includes P Auto.LeanVM.Guest.B1.rowLo.c690.costDeps) :
    machineCost P Auto.LeanVM.Guest.B1.rowLo.c690.costIdx [encodeValue s.I] ≤ 9 := by
  obtain ⟨-, h2, -⟩ := hs
  rw [Auto.LeanVM.Guest.B1.rowLo.c690.costEq P hP]
  limbs_one; split_ifs <;> omega

theorem Oq_G_cost (hP : Includes P Auto.LeanVM.Guest.B1.Oq.G.c688.costDeps) :
    machineCost P Auto.LeanVM.Guest.B1.Oq.G.c688.costIdx [encodeValue s] ≤ 46 := by
  have ht := Oq_tsz_cost P hs (by includes)
  have hl := rowLo_cost P hs (by includes)
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, -⟩ := hs
  rw [Auto.LeanVM.Guest.B1.Oq.G.c688.costEq P hP]
  limbs_one; omega

theorem Oq_D_cost (hP : Includes P Auto.LeanVM.Guest.B1.Oq.D.c687.costDeps) :
    machineCost P Auto.LeanVM.Guest.B1.Oq.D.c687.costIdx [encodeValue s] ≤ 122 := by
  have hg := Oq_G_cost P hs (by includes)
  have hl := rowLo_cost P hs (by includes)
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, -⟩ := hs
  rw [Auto.LeanVM.Guest.B1.Oq.D.c687.costEq P hP]
  limbs_one; omega

theorem Oq_B_cost (hP : Includes P Auto.LeanVM.Guest.B1.Oq.B.c692.costDeps) :
    machineCost P Auto.LeanVM.Guest.B1.Oq.B.c692.costIdx [encodeValue s] ≤ 25 := by
  have hr := Oq_R_cost P hs (by includes)
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, -⟩ := hs
  rw [Auto.LeanVM.Guest.B1.Oq.B.c692.costEq P hP]
  have : LeanVM.Protocol.KeccakHash.rate < 2 ^ 64 := by decide
  limbs_one; omega

theorem Oq_chainLen_cost (hP : Includes P Auto.LeanVM.Guest.B1.Oq.chainLen.c691.costDeps) :
    machineCost P Auto.LeanVM.Guest.B1.Oq.chainLen.c691.costIdx [encodeValue s] ≤ 39 := by
  have hb := Oq_B_cost P hs (by includes)
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, -⟩ := hs
  rw [Auto.LeanVM.Guest.B1.Oq.chainLen.c691.costEq P hP]
  limbs_one; omega

theorem oqK1_cost (hP : Includes P Auto.LeanVM.Guest.B1.oqK1.c686.costDeps) (b : ℕ)
    (hb : b < 2 ^ 21) :
    machineCost P Auto.LeanVM.Guest.B1.oqK1.c686.costIdx [encodeValue b, encodeValue s.R] ≤ 13 := by
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := hs
  rw [Auto.LeanVM.Guest.B1.oqK1.c686.costEq P hP]
  limbs_one; omega

theorem oqKL_lt (b : ℕ) (hb : b < 2 ^ 21) (emit : Bool) : oqKL s b emit < 2 ^ 23 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, -⟩ := hs
  unfold oqKL oqK1; split_ifs <;> omega

theorem oqCh_lt (b : ℕ) (hb : b < 2 ^ 21) (emit : Bool) : oqCh s b emit < 2 ^ 24 := by
  have := oqKL_lt hs b hb emit
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, -⟩ := hs
  unfold oqCh; omega

theorem oqKL_cost (hP : Includes P Auto.LeanVM.Guest.B1.oqKL.c685.costDeps) (b : ℕ)
    (hb : b < 2 ^ 21) (emit : Bool) :
    machineCost P Auto.LeanVM.Guest.B1.oqKL.c685.costIdx
      [encodeValue s, encodeValue b, encodeValue emit] ≤ 159 := by
  have hr := Oq_R_cost P hs (by includes)
  have hk := oqK1_cost P hs (by includes) b hb
  have hd := Oq_D_cost P hs (by includes)
  have hkl := oqKL_lt hs b hb emit
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, -⟩ := hs
  rw [Auto.LeanVM.Guest.B1.oqKL.c685.costEq P hP]
  have : oqK1 b s.R < 2 ^ 22 := by unfold oqK1; omega
  limbs_one; split_ifs <;> limbs_one <;> omega

theorem oqCq_cost (hP : Includes P Auto.LeanVM.Guest.B1.oqCq.c696.costDeps) (ch : ℕ)
    (hch : ch < 2 ^ 24) :
    machineCost P Auto.LeanVM.Guest.B1.oqCq.c696.costIdx [encodeValue s, encodeValue ch] ≤ 11 := by
  obtain ⟨h1, h2, h3, -⟩ := hs
  rw [Auto.LeanVM.Guest.B1.oqCq.c696.costEq P hP]
  have : oqL0 ch < 2 ^ 25 := by unfold oqL0; omega
  limbs_one; omega

theorem oqEnd_cost (hP : Includes P Auto.LeanVM.Guest.B1.oqEnd.c695.costDeps) (b : ℕ)
    (hb : b < 2 ^ 21) (emit : Bool) :
    machineCost P Auto.LeanVM.Guest.B1.oqEnd.c695.costIdx
      [encodeValue s, encodeValue b, encodeValue emit] ≤ 232 := by
  have hkl := oqKL_cost P hs (by includes) b hb emit
  have hc := Oq_chainLen_cost P hs (by includes)
  have hch := oqCh_lt hs b hb emit
  have hq := oqCq_cost P hs (by includes) (oqCh s b emit) hch
  have hkl' := oqKL_lt hs b hb emit
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, -⟩ := hs
  rw [Auto.LeanVM.Guest.B1.oqEnd.c695.costEq P hP]
  have : oqCq s (oqCh s b emit) < 2 ^ 25 := by unfold oqCq oqL0; omega
  limbs_one; omega

end Shape

/-! ## A query -/

section Reader

variable {rd : Reader} {rdV : MachineValue}
  (hrd : ∀ a : K, RunsApp P rdV [encodeValue a] (encodeValue (rd a)))
  {R : ℕ} (hR : ∀ a : K, appCost P rdV [encodeValue a] ≤ R)
include hrd hR

/-- A cell (`memRead.c678`), as `cellAt`. -/
theorem memRead_cost (hP : Includes P Auto.LeanVM.Guest.B1.memRead.c678.costDeps) (p : E)
    (k : ℕ) (hk : k < 2 ^ 40) :
    machineCost P Auto.LeanVM.Guest.B1.memRead.c678.costIdx
      [rdV, encodeValue p, encodeValue k] ≤ R + 21678 := by
  rw [Auto.LeanVM.Guest.B1.memRead.c678.costEq P hP rd rdV hrd]
  have := powSqK_cost_lt P (by includes) g k 40 (by norm_num) (by norm_num) hk
  have := hR (p.limb 0 * gpow k)
  cases rd (p.limb 0 * gpow k) <;> dsimp only <;> omega

omit hrd hR in
/-- The integer of `D ≤ 62` bits read by a closure (`bitsVal.c676`): `(B + 27)·D + 6`. -/
theorem bitsVal_cost (hP : Includes P Auto.LeanVM.Guest.Value.bitsVal.c676.costDeps)
    (f : ℕ → Bool) (fV : MachineValue) (hf : ∀ a, RunsApp P fV [encodeValue a] (encodeValue (f a)))
    (B : ℕ) (hB : ∀ a, a < 62 → appCost P fV [encodeValue a] ≤ B) : ∀ D, D ≤ 62 →
      machineCost P Auto.LeanVM.Guest.Value.bitsVal.c676.costIdx [fV, encodeValue D] ≤
        (B + 27) * D + 6
  | 0, _ => by rw [Auto.LeanVM.Guest.Value.bitsVal.c676.costEq_zero P hP f fV hf]; omega
  | n + 1, hn => by
    rw [Auto.LeanVM.Guest.Value.bitsVal.c676.costEq_succ P hP f fV hf]
    have := bitsVal_cost hP f fV hf B hB n (by omega)
    have := hB n (by omega)
    have hb := LeanVM.Guest.Value.bitsVal_lt f n
    have h2 : 2 ^ n ≤ 2 ^ 62 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h4 : (f n).toNat ≤ 1 := Bool.toNat_le _
    have h3 : 2 ^ n * (f n).toNat ≤ 2 ^ 62 := by
      have := Nat.mul_le_mul_left (2 ^ n) h4; omega
    rw [Nat.one_shiftLeft]
    simp only [Bool.cond_self]
    limbs_one
    nlinarith

/-- A query's position (`posOf.c675`), `D ≤ 28` bits: `(3·R + 65105)·D + 13`. -/
theorem posOf_cost (hP : Includes P Auto.LeanVM.Guest.B1.posOf.c675.costDeps) (bp : E) (D : ℕ)
    (hD : D ≤ 28) :
    machineCost P Auto.LeanVM.Guest.B1.posOf.c675.costIdx [rdV, encodeValue bp, encodeValue D] ≤
      (3 * R + 65078 + 27) * D + 13 := by
  rw [Auto.LeanVM.Guest.B1.posOf.c675.costEq P hP rd rdV hrd]
  have hf : ∀ l, RunsApp P (.closure Auto.LeanVM.Guest.B1.posOf.c675.lam0.costIdx [rdV, encodeValue bp])
      [encodeValue l] (encodeValue (decide (memRead rd bp l = 1))) := fun l ↦
    RunsApp.of_spec (Auto.LeanVM.Guest.B1.posOf.c675.lam0.costSpec P (by includes) rd rdV hrd bp l)
  have := bitsVal_cost P (by includes) _ _ hf (3 * R + 65078) (fun l hl ↦ by
    rw [appCost_fn, List.cons_append, List.cons_append, List.nil_append,
      Auto.LeanVM.Guest.B1.posOf.c675.lam0.costEq P (by includes) rd rdV hrd]
    have := memRead_cost P hrd hR (by includes) bp l (by omega)
    split_ifs <;> omega) D (by omega)
  omega

omit hrd hR in
/-- The digest of two cells (`digestOfCells.c684`): at most `58`. -/
theorem digestOfCells640_cost (hP : Includes P Auto.LeanVM.Guest.B1.digestOfCells.c684.costDeps)
    (a b : E) :
    machineCost P Auto.LeanVM.Guest.B1.digestOfCells.c684.costIdx [encodeValue a, encodeValue b] ≤
      58 := by
  rw [Auto.LeanVM.Guest.B1.digestOfCells.c684.costEq P hP,
    Extractor.digestOfScalarsC.costEq P (by includes)]
  cases LeanVM.Protocol.KeccakHash.digestOfScalars (a, b) <;> dsimp only <;> split_ifs <;> omega

omit hrd hR in
/-- A bit (`testBit.c225`), of a word: at most `13`. -/
theorem testBit_cost (hP : Includes P Auto.Nat.testBit.c225.costDeps) (q l : ℕ) (hq : q < 2 ^ 64)
    (hl : l < 2 ^ 64) :
    machineCost P Auto.Nat.testBit.c225.costIdx [encodeValue q, encodeValue l] ≤ 13 := by
  rw [Auto.Nat.testBit.c225.costEq P hP]
  have h1 : q >>> l ≤ q := Nat.shiftRight_le q l
  have h2 : 1 &&& q >>> l ≤ 1 := Nat.and_le_left
  limbs_one
  omega

section Val

variable {σ : Val} {σV : MachineValue}
  (hσ : ∀ v : V, RunsApp P σV [encodeValue v] (encodeValue (σ v)))
  {S : ℕ} (hS : ∀ v : V, appCost P σV [encodeValue v] ≤ S)
include hσ hS

omit hrd hR in
/-- A query's row (`oqRow.c679`), `R ≤ 192` words: `(S + 41)·192 + 18`. -/
theorem oqRow_cost (hP : Includes P Auto.LeanVM.Guest.B1.oqRow.c679.costDeps) (b Rw : ℕ)
    (hb : b < 2 ^ 21) (hRw : Rw ≤ 192) :
    machineCost P Auto.LeanVM.Guest.B1.oqRow.c679.costIdx [encodeValue b, encodeValue Rw, σV] ≤
      (S + 13 + 28) * 192 + 18 := by
  rw [Auto.LeanVM.Guest.B1.oqRow.c679.costEq P hP b Rw σ σV hσ]
  have := rangeMap_le P (by includes) (by includes) _
    (.closure Auto.LeanVM.Guest.B1.oqRow.c679.lam0.costIdx [encodeValue b, σV])
    (fun i ↦ RunsApp.of_spec (Auto.LeanVM.Guest.B1.oqRow.c679.lam0.costSpec P (by includes) b σ σV
      hσ i))
    (S + 13) Rw 192 hRw (by norm_num) (fun i hi ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.nil_append,
        Auto.LeanVM.Guest.B1.oqRow.c679.lam0.costEq P (by includes) b σ σV hσ]
      have := hS (.n (b + i))
      limbs_one
      omega)
  omega

omit hrd hR in
/-- A query's siblings (`oqSibsOf.c682`), `pd ≤ 20` levels: `(2·S + 140 + 28)·20 + 20`. -/
theorem oqSibsOf_cost (hP : Includes P Auto.LeanVM.Guest.B1.oqSibsOf.c682.costDeps) (pd ch q : ℕ)
    (hpd : pd ≤ 20) (hch : ch < 2 ^ 24) (hq : q < 2 ^ 64) :
    machineCost P Auto.LeanVM.Guest.B1.oqSibsOf.c682.costIdx
      [encodeValue pd, encodeValue ch, encodeValue q, σV] ≤ (2 * S + 140 + 28) * 20 + 20 := by
  rw [Auto.LeanVM.Guest.B1.oqSibsOf.c682.costEq P hP pd ch q σ σV hσ]
  have := rangeMap_le P (by includes) (by includes) _
    (.closure Auto.LeanVM.Guest.B1.oqSibsOf.c682.lam0.costIdx [encodeValue ch, encodeValue q, σV])
    (fun l ↦ RunsApp.of_spec (Auto.LeanVM.Guest.B1.oqSibsOf.c682.lam0.costSpec P (by includes) ch q
      σ σV hσ l))
    (2 * S + 140) pd 20 hpd (by norm_num) (fun l hl ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.nil_append,
        Auto.LeanVM.Guest.B1.oqSibsOf.c682.lam0.costEq P (by includes) ch q σ σV hσ]
      have := testBit_cost P (by includes) q l hq (by omega)
      split_ifs <;> limbs_one <;> cost_facts [digestOfCells640_cost P, hS] <;> omega)
  omega

/-- A query's price. -/
@[expose] def queryPrice (R S : ℕ) : ℕ :=
  2 * ((3 * R + 65078 + 27) * 28 + 13) + ((S + 13 + 28) * 192 + 18) +
    ((2 * S + 140 + 28) * 20 + 20) + 251

/-- **A query** (`oqQueryW.c674`), of a level's shape, from a value below `2^21`: at most
`queryPrice R S`. -/
theorem oqQueryW_cost (hP : Includes P Auto.LeanVM.Guest.B1.oqQueryW.c674.costDeps) (s : Oq)
    (hs : OqOK s) (bp : E) (b : ℕ) (hb : b < 2 ^ 21) (emit : Bool) :
    machineCost P Auto.LeanVM.Guest.B1.oqQueryW.c674.costIdx
      [encodeValue s, rdV, encodeValue bp, encodeValue b, encodeValue emit, σV] ≤
        queryPrice R S := by
  rw [Auto.LeanVM.Guest.B1.oqQueryW.c674.costEq P hP s rd rdV hrd bp b emit σ σV hσ]
  have hR' := Oq_R_cost P hs (by includes)
  have hkl := oqKL_cost P hs (by includes) b hb emit
  have hc := Oq_chainLen_cost P hs (by includes)
  have hch := oqCh_lt hs b hb emit
  have hkl' := oqKL_lt hs b hb emit
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, -⟩ := hs
  have hp := posOf_cost P hrd hR (by includes) bp (s.pd + s.cd) (by omega)
  have := Nat.mul_le_mul_left (3 * R + 65078 + 27) (by omega : s.pd + s.cd ≤ 28)
  have hq := LeanVM.Guest.Value.bitsVal_lt (fun l ↦ decide (memRead rd bp l = 1)) (s.pd + s.cd)
  have hq' : 2 ^ (s.pd + s.cd) ≤ 2 ^ 28 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hrow := oqRow_cost P hσ hS (by includes) b s.R hb h5
  have hsib := oqSibsOf_cost P hσ hS (by includes) s.pd (oqCh s b emit)
    (posOf rd bp (s.pd + s.cd)) h3 hch (by unfold posOf; omega)
  unfold queryPrice
  limbs_one
  omega

/-- An iteration's price. -/
@[expose] def iterPrice (R S : ℕ) : ℕ := 2 * queryPrice R S + 2 * S + 516

/-- **A loop iteration's queries** (`oqIterOf.c694`): at most `iterPrice R S`. -/
theorem oqIterOf_cost (hP : Includes P Auto.LeanVM.Guest.B1.oqIterOf.c694.costDeps) (s : Oq)
    (hs : OqOK s) :
    machineCost P Auto.LeanVM.Guest.B1.oqIterOf.c694.costIdx [encodeValue s, rdV, σV] ≤
      iterPrice R S := by
  rw [Auto.LeanVM.Guest.B1.oqIterOf.c694.costEq P hP s rd rdV hrd σ σV hσ]
  have hE := hs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have q1 := oqQueryW_cost P hrd hR hσ hS (by includes) s hs (σ (.n 10)) 11 (by norm_num) true
  have q2 := oqQueryW_cost P hrd hR hσ hS (by includes) s hs (σ (.n (oqE1 s))) (oqE1 s + 1)
    (by omega) false
  have q3 := oqQueryW_cost P hrd hR hσ hS (by includes) s hs (σ (.n 9)) 10 (by norm_num) true
  have e1 := oqEnd_cost P hs (by includes) 11 (by norm_num) true
  have := hS (.n 10); have := hS (.n 9); have := hS (.n (oqE1 s))
  have hb := hs.1
  unfold iterPrice
  limbs_one
  split_ifs <;> omega

omit hrd hR in
/-- The loop's arguments (`oqLoopArgs.c698`): `7·S + 85`. -/
theorem oqLoopArgs_cost (hP : Includes P Auto.LeanVM.Guest.B1.oqLoopArgs.c698.costDeps) :
    machineCost P Auto.LeanVM.Guest.B1.oqLoopArgs.c698.costIdx [σV] ≤ 7 * S + 85 := by
  rw [Auto.LeanVM.Guest.B1.oqLoopArgs.c698.costEq P hP σ σV hσ]
  have := hS (.n 6); have := hS (.n 4); have := hS (.n 0); have := hS (.n 1); have := hS (.n 5)
  have := hS (.n 11); have := hS (.n 8)
  omega

omit hrd hR hσ hS in
theorem length_oqIterOf (s : Oq) (rd : Reader) (σ : Val) : (oqIterOf s rd σ).length ≤ 2 := by
  unfold oqIterOf; split_ifs <;> simp

section Frames

variable {Vn : NFrames} {VnV : MachineValue}
  (hVn : ∀ (k : ℕ) (a r : List E) (v : V),
    RunsApp P VnV [encodeValue k, encodeValue a, encodeValue r, encodeValue v]
      (encodeValue (Vn k a r v)))
  {F : ℕ} (hF : ∀ (k : ℕ) (a r : List E) (v : V),
    appCost P VnV [encodeValue k, encodeValue a, encodeValue r, encodeValue v] ≤ F)
include hVn hF

/-- The queries' price. -/
@[expose] def oqsPrice (R S F : ℕ) : ℕ :=
  S + queryPrice R S + 20 +
    ((33136 + (7 * S + 85) + iterPrice R (F + 6) + 26 + 28) * 112 + 9) + (27 * 112 + 3) + 12 + 21

/-- **The queries of `opening_queries`** (`oqsOfNC`), its odd query and `N ≤ 112` iterations:
at most `oqsPrice R S F`. -/
theorem oqsOfN_cost (hP : Includes P Decoder.oqsOfNC.costDeps) (s : Oq) (hs : OqOK s)
    (odd loop N : ℕ) (hodd : odd ≤ 1) (hN : N ≤ 112) :
    machineCost P Decoder.oqsOfNC.costIdx [encodeValue s, encodeValue odd, encodeValue loop,
      encodeValue N, rdV, σV, VnV] ≤ oqsPrice R S F := by
  rw [Decoder.oqsOfNC.costEq P hP s odd loop N rd rdV hrd σ σV hσ Vn VnV hVn]
  have q := oqQueryW_cost P hrd hR hσ hS (by includes) s hs (σ (.n 12)) 13 (by norm_num) true
  have := hS (.n 12)
  have m := rangeMap_le P (by includes) (by includes) _
    (.closure Decoder.oqsOfNC.lam0.costIdx [encodeValue s, encodeValue loop, rdV, σV, VnV])
    (fun j ↦ RunsApp.of_spec (Decoder.oqsOfNC.lam0.costSpec P (by includes) s loop rd rdV hrd σ σV hσ
      Vn VnV hVn j))
    (33136 + (7 * S + 85) + iterPrice R (F + 6) + 26) N 112 hN (by norm_num) (fun j hj ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.cons_append,
        List.cons_append, List.nil_append,
        Decoder.oqsOfNC.lam0.costEq P (by includes) s loop rd rdV hrd σ σV hσ Vn VnV hVn]
      have := powSqE_cost_lt P (by includes) LeanVM.Protocol.Verifier.gen j 7 (by norm_num)
        (by norm_num) (by omega)
      have := oqLoopArgs_cost P hσ hS (by includes)
      have hσ' : ∀ v : V, RunsApp P (.closure Decoder.oqsOfNC.lam0.lam0.costIdx
          [encodeValue loop, VnV, encodeValue (LeanVM.Protocol.Verifier.gen ^ j :: oqLoopArgs σ),
            encodeValue ([] : List E)]) [encodeValue v]
          (encodeValue (Vn loop (LeanVM.Protocol.Verifier.gen ^ j :: oqLoopArgs σ) [] v)) :=
        fun v ↦ RunsApp.of_spec (Decoder.oqsOfNC.lam0.lam0.costSpec P (by includes) loop Vn VnV hVn
          _ _ v)
      have hS' : ∀ v : V, appCost P (.closure Decoder.oqsOfNC.lam0.lam0.costIdx
          [encodeValue loop, VnV, encodeValue (LeanVM.Protocol.Verifier.gen ^ j :: oqLoopArgs σ),
            encodeValue ([] : List E)]) [encodeValue v] ≤ F + 6 := fun v ↦ by
        rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.cons_append,
          List.nil_append, Decoder.oqsOfNC.lam0.lam0.costEq P (by includes) loop Vn VnV hVn]
        have := hF loop (LeanVM.Protocol.Verifier.gen ^ j :: oqLoopArgs σ) [] v
        omega
      have := oqIterOf_cost P hrd hR hσ' hS' (by includes) s hs
      omega)
  have hf := flatten_map_cost P (by includes) 2
    (fun j ↦ oqIterOf s rd (Vn loop (LeanVM.Protocol.Verifier.gen ^ j :: oqLoopArgs σ) []))
    (List.range N) (fun j _ ↦ length_oqIterOf _ _ _)
  simp only [List.length_range] at hf
  have := Nat.mul_le_mul_left (9 * 2 + 9) hN
  unfold oqsPrice
  rw [limbs_of_lt (by omega : odd < 2 ^ 64)]
  split_ifs
  · have ha := append_cost P (by includes) [oqQueryW s rd (σ (.n 12)) 13 true σ]
      ((List.range N).flatMap fun j ↦
        oqIterOf s rd (Vn loop (LeanVM.Protocol.Verifier.gen ^ j :: oqLoopArgs σ) []))
    simp only [List.length_cons, List.length_nil] at ha
    omega
  · have ha := append_cost P (by includes) ([] : List QW)
      ((List.range N).flatMap fun j ↦
        oqIterOf s rd (Vn loop (LeanVM.Protocol.Verifier.gen ^ j :: oqLoopArgs σ) []))
    simp only [List.length_nil] at ha
    omega

end Frames

end Val

/-! ## The queries' values -/

omit hrd hR in
theorem oqQueryW_facts (s : Oq) (bp : E) (b : ℕ) (emit : Bool) (σ : Val) :
    (oqQueryW s rd bp b emit σ).1 < 2 ^ (s.pd + s.cd) ∧
      (oqQueryW s rd bp b emit σ).2.2.length = s.pd := by
  unfold oqQueryW posOf oqSibsOf
  exact ⟨LeanVM.Guest.Value.bitsVal_lt _ _, by simp⟩

omit hrd hR in
theorem mem_oqsOfN {s : Oq} {odd loop N : ℕ} {σ : Val} {Vn : NFrames} {w : QW}
    (h : w ∈ oqsOfN s odd loop N rd σ Vn) : w.1 < 2 ^ (s.pd + s.cd) ∧ w.2.2.length = s.pd := by
  unfold oqsOfN at h
  rcases List.mem_append.1 h with h | h
  · split_ifs at h
    · rw [List.mem_singleton] at h; subst h; exact oqQueryW_facts _ _ _ _ _
    · simp at h
  · obtain ⟨j, -, hj⟩ := List.mem_flatMap.1 h
    unfold oqIterOf at hj
    split_ifs at hj
    · rcases List.mem_pair.1 hj with rfl | rfl <;> exact oqQueryW_facts _ _ _ _ _
    · rw [List.mem_singleton] at hj; subst hj; exact oqQueryW_facts _ _ _ _ _

omit hrd hR in
theorem length_flatMap_le {α β : Type} (f : α → List β) (M : ℕ) (hf : ∀ a, (f a).length ≤ M) :
    ∀ l : List α, (l.flatMap f).length ≤ M * l.length
  | [] => by simp
  | a :: l => by
    rw [List.flatMap_cons, List.length_append, List.length_cons, Nat.mul_succ]
    have := length_flatMap_le f M hf l
    have := hf a
    omega

omit hrd hR in
theorem length_oqsOfN (s : Oq) (odd loop N : ℕ) (σ : Val) (Vn : NFrames) :
    (oqsOfN s odd loop N rd σ Vn).length ≤ 1 + 2 * N := by
  unfold oqsOfN
  rw [List.length_append]
  have := length_flatMap_le
    (fun j ↦ oqIterOf s rd (Vn loop (LeanVM.Protocol.Verifier.gen ^ j :: oqLoopArgs σ) [])) 2
    (fun _ ↦ length_oqIterOf _ _ _) (List.range N)
  rw [List.length_range] at this
  split_ifs <;> simp only [List.length_cons, List.length_nil] <;> omega

/-! ## A query's opening -/

omit hrd hR in
theorem capSib_le (D p j : ℕ) (hD : D ≤ 8) : Whir.capSib D p j ≤ 2 ^ 8 + p + 1 := by
  unfold Whir.capSib
  have : 2 ^ (D - j) ≤ 2 ^ 8 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have : p / 2 ^ j ≤ p := Nat.div_le_self _ _
  split_ifs <;> omega

omit hrd hR in
/-- A cap sibling's index (`capSib.c705`), `D ≤ 8`, `p < 2^28`: at most `37`. -/
theorem capSib_cost (hP : Includes P Auto.LeanVM.Guest.B1.Whir.capSib.c705.costDeps) (D p j : ℕ)
    (hD : D ≤ 8) (hj : j < 8) (hp : p < 2 ^ 28) :
    machineCost P Auto.LeanVM.Guest.B1.Whir.capSib.c705.costIdx
      [encodeValue D, encodeValue p, encodeValue j] ≤ 37 := by
  rw [Auto.LeanVM.Guest.B1.Whir.capSib.c705.costEq P hP]
  simp only [Nat.one_shiftLeft]
  have : 2 ^ (D - j) ≤ 2 ^ 8 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have : 2 ^ j ≤ 2 ^ 8 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have : p / 2 ^ j ≤ p := Nat.div_le_self _ _
  limbs_one
  split_ifs <;> omega

/-- The cap's siblings (`capSibsOf.c703`), `D ≤ 8` levels, `p < 2^28`: `(2·R + 43540)·8 + 22`. -/
theorem capSibsOf_cost (hP : Includes P Auto.LeanVM.Guest.B1.Whir.capSibsOf.c703.costDeps) (cap : E)
    (D p : ℕ) (hD : D ≤ 8) (hp : p < 2 ^ 28) :
    machineCost P Auto.LeanVM.Guest.B1.Whir.capSibsOf.c703.costIdx
      [rdV, encodeValue cap, encodeValue D, encodeValue p] ≤ (2 * R + 43512 + 28) * 8 + 22 := by
  rw [Auto.LeanVM.Guest.B1.Whir.capSibsOf.c703.costEq P hP rd rdV hrd]
  have := rangeMap_le P (by includes) (by includes) _
    (.closure Auto.LeanVM.Guest.B1.Whir.capSibsOf.c703.lam0.costIdx
      [rdV, encodeValue cap, encodeValue D, encodeValue p])
    (fun j ↦ RunsApp.of_spec (Auto.LeanVM.Guest.B1.Whir.capSibsOf.c703.lam0.costSpec P
      (by includes) rd rdV hrd cap D p j))
    (2 * R + 43512) D 8 hD (by norm_num) (fun j hj ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.cons_append,
        List.nil_append,
        Auto.LeanVM.Guest.B1.Whir.capSibsOf.c703.lam0.costEq P (by includes) rd rdV hrd]
      have := capSib_cost P (by includes) D p j hD (by omega) hp
      have := capSib_le D p j hD
      have := memRead_cost P hrd hR (by includes) cap (2 * Whir.capSib D p j) (by omega)
      have := memRead_cost P hrd hR (by includes) cap (2 * Whir.capSib D p j + 1) (by omega)
      have := digestOfCells640_cost P (by includes) (memRead rd cap (2 * Whir.capSib D p j))
        (memRead rd cap (2 * Whir.capSib D p j + 1))
      limbs_one
      omega)
  omega

/-- A query's opening's price. -/
@[expose] def openingPrice (R : ℕ) : ℕ := (2 * R + 43512 + 28) * 8 + 22 + 209

/-- **A query's opening** (`toOpening.c702`), of a level of depth at most `26`, cap depth at most
`8`, the query's position below `2^28` and its siblings at most `20`: `openingPrice R`. -/
theorem toOpening_cost (hP : Includes P Auto.LeanVM.Guest.B1.Whir.toOpening.c702.costDeps) (cap : E)
    (cd depth : ℕ) (w : QW) (hcd : cd ≤ 8) (hdepth : depth ≤ 26) (hw : w.1 < 2 ^ 28)
    (hw2 : w.2.2.length ≤ 20) :
    machineCost P Auto.LeanVM.Guest.B1.Whir.toOpening.c702.costIdx
      [rdV, encodeValue cap, encodeValue cd, encodeValue depth, encodeValue w] ≤ openingPrice R := by
  rw [Auto.LeanVM.Guest.B1.Whir.toOpening.c702.costEq P hP rd rdV hrd]
  simp only [Nat.one_shiftLeft]
  have : 2 ^ (depth - cd) ≤ 2 ^ 26 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hd : w.1 / 2 ^ (depth - cd) ≤ w.1 := Nat.div_le_self _ _
  have := capSibsOf_cost P hrd hR (by includes) cap cd (w.1 / 2 ^ (depth - cd)) hcd (by omega)
  have := append_cost P (by includes) w.2.2 (Whir.capSibsOf rd cap cd (w.1 / 2 ^ (depth - cd)))
  unfold openingPrice
  limbs_one
  omega

section Val2

variable {σ : Val} {σV : MachineValue}
  (hσ : ∀ v : V, RunsApp P σV [encodeValue v] (encodeValue (σ v)))
  {S : ℕ} (hS : ∀ v : V, appCost P σV [encodeValue v] ≤ S)
  {Vn : NFrames} {VnV : MachineValue}
  (hVn : ∀ (k : ℕ) (a r : List E) (v : V),
    RunsApp P VnV [encodeValue k, encodeValue a, encodeValue r, encodeValue v]
      (encodeValue (Vn k a r v)))
  {F : ℕ} (hF : ∀ (k : ℕ) (a r : List E) (v : V),
    appCost P VnV [encodeValue k, encodeValue a, encodeValue r, encodeValue v] ≤ F)
include hσ hS hVn hF

/-- A level's price. -/
@[expose] def levelPrice (R S F : ℕ) : ℕ :=
  ((S + 9 + 11) * 7 + 3) + 7 + ((S + 9 + 11) * 1 + 3) + oqsPrice R (F + 6) F +
    ((openingPrice R + 6 + 11) * 225 + 3) + 59

/-- **A level's openings** (`levelOsNC`), from a call of the table: at most `levelPrice R S F`. -/
theorem levelOsN_cost (hP : Includes P Decoder.levelOsNC.costDeps) (c : OsCall) (hc : CallOK c) :
    machineCost P Decoder.levelOsNC.costIdx [rdV, σV, VnV, encodeValue c] ≤ levelPrice R S F := by
  obtain ⟨hs, hodd, hN, hfn, hloop, hdepth, hargs, hrets⟩ := hc
  rw [Decoder.levelOsNC.costEq P hP rd rdV hrd σ σV hσ Vn VnV hVn]
  have hl0 : ∀ k : ℕ, appCost P (.closure Decoder.levelOsNC.lam0.costIdx [σV]) [encodeValue k] ≤
      S + 9 := fun k ↦ by
    rw [appCost_fn, List.cons_append, List.nil_append,
      Decoder.levelOsNC.lam0.costEq P (by includes) σ σV hσ]
    have := hS (.n k); omega
  have hr0 : ∀ k : ℕ, RunsApp P (.closure Decoder.levelOsNC.lam0.costIdx [σV]) [encodeValue k]
      (encodeValue (σ (.n k))) :=
    fun k ↦ RunsApp.of_spec (Decoder.levelOsNC.lam0.costSpec P (by includes) σ σV hσ k)
  have m1 := map_cost P (by includes) _ _ hr0 (S + 9) c.args (fun k _ ↦ hl0 k)
  have m2 := map_cost P (by includes) _ _ hr0 (S + 9) c.rets (fun k _ ↦ hl0 k)
  have := Nat.mul_le_mul_left (S + 9 + 11) hargs
  have := Nat.mul_le_mul_left (S + 9 + 11) hrets
  have hσ'' : ∀ v : V, RunsApp P (.closure Decoder.levelOsNC.lam2.costIdx
      [VnV, encodeValue (c.rets.map fun k ↦ σ (.n k)), encodeValue (c.args.map fun k ↦ σ (.n k)),
        encodeValue c.fn]) [encodeValue v]
      (encodeValue (Vn c.fn (c.args.map fun k ↦ σ (.n k)) (c.rets.map fun k ↦ σ (.n k)) v)) :=
    fun v ↦ RunsApp.of_spec (Decoder.levelOsNC.lam2.costSpec P (by includes) Vn VnV hVn _ _ _ v)
  have hS'' : ∀ v : V, appCost P (.closure Decoder.levelOsNC.lam2.costIdx
      [VnV, encodeValue (c.rets.map fun k ↦ σ (.n k)), encodeValue (c.args.map fun k ↦ σ (.n k)),
        encodeValue c.fn]) [encodeValue v] ≤ F + 6 := fun v ↦ by
    rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.cons_append,
      List.nil_append, Decoder.levelOsNC.lam2.costEq P (by includes) Vn VnV hVn]
    have := hF c.fn (c.args.map fun k ↦ σ (.n k)) (c.rets.map fun k ↦ σ (.n k)) v
    omega
  have ho := oqsOfN_cost P hrd hR hσ'' hS'' hVn hF (by includes) _ hs c.odd c.loop c.N hodd hN
  have hlen := length_oqsOfN (rd := rd) ⟨c.base, c.I, c.pd, c.cd⟩ c.odd c.loop c.N
    (Vn c.fn (c.args.map fun k ↦ σ (.n k)) (c.rets.map fun k ↦ σ (.n k))) Vn
  have m3 := map_cost P (by includes) _
    (.closure Decoder.levelOsNC.lam1.costIdx [rdV,
      encodeValue ((c.args.map fun k ↦ σ (.n k)).headD 0),
      encodeValue (c.args.map fun k ↦ σ (.n k)), encodeValue c.depth, encodeValue c.cd])
    (fun w ↦ RunsApp.of_spec (Decoder.levelOsNC.lam1.costSpec P (by includes) rd rdV hrd _ _ _ _ w))
    (openingPrice R + 6) (oqsOfN ⟨c.base, c.I, c.pd, c.cd⟩ c.odd c.loop c.N rd
      (Vn c.fn (c.args.map fun k ↦ σ (.n k)) (c.rets.map fun k ↦ σ (.n k))) Vn) (fun w hw ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.cons_append,
        List.cons_append, List.nil_append,
        Decoder.levelOsNC.lam1.costEq P (by includes) rd rdV hrd]
      obtain ⟨hw1, hw2⟩ := mem_oqsOfN hw
      have h4 : c.cd ≤ 8 := hs.2.2.2.1
      have h3 : c.pd ≤ 20 := hs.2.2.1
      have : 2 ^ (c.pd + c.cd) ≤ 2 ^ 28 := Nat.pow_le_pow_right (by norm_num) (by omega)
      have := toOpening_cost P hrd hR (by includes) ((c.args.map fun k ↦ σ (.n k)).headD 0) c.cd
        c.depth w h4 hdepth (lt_of_lt_of_le hw1 this) (by rw [hw2]; exact h3)
      omega)
  have := Nat.mul_le_mul_left (openingPrice R + 6 + 11) (hlen.trans (by omega : 1 + 2 * c.N ≤ 225))
  unfold levelPrice
  have := listCasesOn_le (c.args.map fun k ↦ σ (.n k)) 7 (fun _ _ ↦ 1) (by intros; omega)
  omega

end Val2

omit hrd hR in
theorem length_levelOsN (σ : Val) (Vn : NFrames) (c : OsCall) (hc : CallOK c) :
    (levelOsN rd σ Vn c).length ≤ 225 := by
  unfold levelOsN
  rw [List.length_map]
  have := length_oqsOfN (rd := rd) ⟨c.base, c.I, c.pd, c.cd⟩ c.odd c.loop c.N
    (Vn c.fn (c.args.map fun k ↦ σ (.n k)) (c.rets.map fun k ↦ σ (.n k))) Vn
  have := hc.2.2.1
  omega

/-- A stream's `n ≤ L` words (`wordsAt.c708`), `L ≤ 2^32`: `(R + 17398 + 28)·L + 18`. -/
theorem wordsAt_cost (hP : Includes P Auto.LeanVM.Guest.B1.VerifySub.wordsAt.c708.costDeps) (p : E)
    (n L : ℕ) (hn : n ≤ L) (hL : L ≤ 2 ^ 32) :
    machineCost P Auto.LeanVM.Guest.B1.VerifySub.wordsAt.c708.costIdx
      [rdV, encodeValue p, encodeValue n] ≤ (R + 17398 + 28) * L + 18 := by
  rw [Auto.LeanVM.Guest.B1.VerifySub.wordsAt.c708.costEq P hP rd rdV hrd]
  have := rangeMap_le P (by includes) (by includes) _
    (.closure Auto.LeanVM.Guest.B1.VerifySub.wordsAt.c708.lam0.costIdx [rdV, encodeValue p])
    (fun k ↦ RunsApp.of_spec (Auto.LeanVM.Guest.B1.VerifySub.wordsAt.c708.lam0.costSpec P
      (by includes) rd rdV hrd p k))
    (R + 17398) n L hn (by omega) (fun k hk ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.nil_append,
        Auto.LeanVM.Guest.B1.VerifySub.wordsAt.c708.lam0.costEq P (by includes) rd rdV hrd]
      have := powSqK_cost_lt P (by includes) g k 32 (by norm_num) (by norm_num) (by omega)
      have := hR (p.limb 0 * gpow k)
      cases rd (p.limb 0 * gpow k) <;> dsimp only <;> omega)
  omega

section Proof

variable {σ : Val} {σV : MachineValue}
  (hσ : ∀ v : V, RunsApp P σV [encodeValue v] (encodeValue (σ v)))
  {S : ℕ} (hS : ∀ v : V, appCost P σV [encodeValue v] ≤ S)
  {Vn : NFrames} {VnV : MachineValue}
  (hVn : ∀ (k : ℕ) (a r : List E) (v : V),
    RunsApp P VnV [encodeValue k, encodeValue a, encodeValue r, encodeValue v]
      (encodeValue (Vn k a r v)))
  {F : ℕ} (hF : ∀ (k : ℕ) (a r : List E) (v : V),
    appCost P VnV [encodeValue k, encodeValue a, encodeValue r, encodeValue v] ≤ F)
  {cl : E → E → ℕ} {clV : MachineValue}
  (hcl : ∀ a b : E, RunsApp P clV [encodeValue a, encodeValue b] (encodeValue (cl a b)))
  {C : ℕ} (hC : ∀ a b : E, appCost P clV [encodeValue a, encodeValue b] ≤ C)
  {L : ℕ} (hL : ∀ a b : E, cl a b ≤ L) (hL32 : L ≤ 2 ^ 32)
include hσ hS hVn hF hcl hC hL hL32

omit hrd hR hVn hF hcl hC hL hL32 in
theorem vsOsArgs_cost (hP : Includes P Auto.LeanVM.Guest.B1.VerifySub.vsOsArgs.c711.costDeps) :
    machineCost P Auto.LeanVM.Guest.B1.VerifySub.vsOsArgs.c711.costIdx [σV] ≤ 9 * S + 109 := by
  rw [Auto.LeanVM.Guest.B1.VerifySub.vsOsArgs.c711.costEq P hP σ σV hσ]
  cost_facts [hS]
  omega

omit hrd hR hVn hF hcl hC hL hL32 in
theorem vsOsRets_cost (hP : Includes P Auto.LeanVM.Guest.B1.VerifySub.vsOsRets.c712.costDeps) :
    machineCost P Auto.LeanVM.Guest.B1.VerifySub.vsOsRets.c712.costIdx [σV] ≤ 5 * S + 61 := by
  rw [Auto.LeanVM.Guest.B1.VerifySub.vsOsRets.c712.costEq P hP σ σV hσ]
  cost_facts [hS]
  omega

/-- A child proof's price. -/
@[expose] def vsPiPrice (R S F C L : ℕ) : ℕ :=
  4 * S + 1900 + C + ((R + 17398 + 28) * L + 18) + 1 + (9 * S + 109) + (5 * S + 61) + F + 113 +
    428 + ((R + 21682 + 28) * 121 + 9) + (9 * L + 3) + 8001 + 428 +
    (((5 * S + 61) + 1 + (9 * S + 109) + levelPrice R (F + 6) F + 17 + 11) * 6 + 3) +
    ((9 * 225 + 9) * 6 + 3) + 91

/-- **A child's proof** (`vsPiOfNC`) at `verify_sub`'s valuation: its stream (the cursor's length
at most `L`), the opening's words, the candidate's levels' openings: at most
`vsPiPrice R S F C L`. -/
theorem vsPiOfN_cost (hP : Includes P Decoder.vsPiOfNC.costDeps) :
    machineCost P Decoder.vsPiOfNC.costIdx [rdV, σV, VnV, clV] ≤ vsPiPrice R S F C L := by
  rw [Decoder.vsPiOfNC.costEq P hP rd rdV hrd σ σV hσ Vn VnV hVn cl clV hcl]
  have hm := logGT_le (σ (.n 1901)) 28
  have := logGT_cost P (by includes) (σ (.n 1901)) 28 (by norm_num)
  have := hS (.n 1901); have := hS (.n 27); have := hS (.n 868)
  have := hC (σ (.n 27)) (σ (.n 868))
  have hw := wordsAt_cost P hrd hR (by includes) (σ (.n 27)) (cl (σ (.n 27)) (σ (.n 868))) L
    (hL _ _) hL32
  have := vsOsArgs_cost P hσ hS (by includes)
  have := vsOsRets_cost P hσ hS (by includes)
  have := hF (openStackedIdx (logGT (σ (.n 1901)) 28)) (VerifySub.vsOsArgs σ)
    (VerifySub.vsOsRets σ) (.n 8)
  rw [Auto.LeanVM.Guest.Fast.osWordsTab.c713.costEq P (by includes),
    Auto.LeanVM.Guest.Fast.osCallsTab.c716.costEq P (by includes)]
  obtain ⟨hwl, hwt⟩ := osWordsTab_ok
  obtain ⟨hcl', -, -⟩ := callOK_osCallsTab
  have := getD_cost P (by includes) osWordsTab (logGT (σ (.n 1901)) 28) 0 (by omega)
  have := getD_cost P (by includes) osCallsTab (logGT (σ (.n 1901)) 28) [] (by omega)
  have hn : osWordsTab.getD (logGT (σ (.n 1901)) 28) 0 ≤ 121 := by
    rw [List.getD_eq_getElem?_getD]
    cases hk : osWordsTab[logGT (σ (.n 1901)) 28]? with
    | none => simp
    | some x => exact hwt x (List.mem_of_getElem? hk)
  have hr := rangeMap_le P (by includes) (by includes) _
    (.closure Decoder.vsPiOfNC.lam0.costIdx [rdV,
      encodeValue (Vn (openStackedIdx (logGT (σ (.n 1901)) 28)) (VerifySub.vsOsArgs σ)
        (VerifySub.vsOsRets σ) (.n 8)), encodeValue (logGT (σ (.n 1901)) 28)])
    (fun off ↦ RunsApp.of_spec (Decoder.vsPiOfNC.lam0.costSpec P (by includes) rd rdV hrd _ _ off))
    (R + 21682) _ 121 hn (by norm_num) (fun off hoff ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.nil_append,
        Decoder.vsPiOfNC.lam0.costEq P (by includes) rd rdV hrd]
      have := memRead_cost P hrd hR (by includes)
        (Vn (openStackedIdx (logGT (σ (.n 1901)) 28)) (VerifySub.vsOsArgs σ)
          (VerifySub.vsOsRets σ) (.n 8)) off (by omega)
      omega)
  have hlw : (VerifySub.wordsAt rd (σ (.n 27)) (cl (σ (.n 27)) (σ (.n 868)))).length ≤ L := by
    unfold VerifySub.wordsAt; rw [List.length_map, List.length_range]; exact hL _ _
  have ha := append_cost P (by includes)
    (VerifySub.wordsAt rd (σ (.n 27)) (cl (σ (.n 27)) (σ (.n 868))))
    (readN rd (Vn (openStackedIdx (logGT (σ (.n 1901)) 28)) (VerifySub.vsOsArgs σ)
      (VerifySub.vsOsRets σ) (.n 8)) (osWordsTab.getD (logGT (σ (.n 1901)) 28) 0))
  obtain ⟨hcl6, hcok⟩ := callOK_getD (logGT (σ (.n 1901)) 28)
  have hm1 := map_cost P (by includes) _
    (.closure Decoder.vsPiOfNC.lam1.costIdx [rdV, σV, VnV, encodeValue (logGT (σ (.n 1901)) 28)])
    (fun c ↦ RunsApp.of_spec (Decoder.vsPiOfNC.lam1.costSpec P (by includes) rd rdV hrd σ σV hσ Vn
      VnV hVn _ c))
    ((5 * S + 61) + 1 + (9 * S + 109) + levelPrice R (F + 6) F + 17)
    (osCallsTab.getD (logGT (σ (.n 1901)) 28) []) (fun c hc ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.cons_append,
        List.nil_append, Decoder.vsPiOfNC.lam1.costEq P (by includes) rd rdV hrd σ σV hσ Vn VnV hVn]
      have := vsOsArgs_cost P hσ hS (by includes)
      have := vsOsRets_cost P hσ hS (by includes)
      have hσ' : ∀ v : V, RunsApp P (.closure Decoder.vsPiOfNC.lam1.lam0.costIdx
          [VnV, encodeValue (VerifySub.vsOsRets σ),
            encodeValue (openStackedIdx (logGT (σ (.n 1901)) 28)),
            encodeValue (VerifySub.vsOsArgs σ)]) [encodeValue v]
          (encodeValue (Vn (openStackedIdx (logGT (σ (.n 1901)) 28)) (VerifySub.vsOsArgs σ)
            (VerifySub.vsOsRets σ) v)) :=
        fun v ↦ RunsApp.of_spec (Decoder.vsPiOfNC.lam1.lam0.costSpec P (by includes) Vn VnV hVn
          _ _ _ v)
      have hS' : ∀ v : V, appCost P (.closure Decoder.vsPiOfNC.lam1.lam0.costIdx
          [VnV, encodeValue (VerifySub.vsOsRets σ),
            encodeValue (openStackedIdx (logGT (σ (.n 1901)) 28)),
            encodeValue (VerifySub.vsOsArgs σ)]) [encodeValue v] ≤ F + 6 := fun v ↦ by
        rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.cons_append,
          List.nil_append, Decoder.vsPiOfNC.lam1.lam0.costEq P (by includes) Vn VnV hVn]
        have := hF (openStackedIdx (logGT (σ (.n 1901)) 28)) (VerifySub.vsOsArgs σ)
          (VerifySub.vsOsRets σ) v
        omega
      have := levelOsN_cost P hrd hR hσ' hS' hVn hF (by includes) c (hcok c hc)
      rw [limbs_of_lt (by omega : logGT (σ (.n 1901)) 28 < 2 ^ 64)]
      omega)
  have := Nat.mul_le_mul_left ((5 * S + 61) + 1 + (9 * S + 109) + levelPrice R (F + 6) F + 17 + 11)
    hcl6
  have hf := flatten_map_cost P (by includes) 225
    (levelOsN rd (Vn (openStackedIdx (logGT (σ (.n 1901)) 28)) (VerifySub.vsOsArgs σ)
      (VerifySub.vsOsRets σ)) Vn) (osCallsTab.getD (logGT (σ (.n 1901)) 28) [])
    (fun c hc ↦ length_levelOsN _ _ c (hcok c hc))
  have := Nat.mul_le_mul_left (9 * 225 + 9) hcl6
  have := Nat.mul_le_mul_left 9 hlw
  have hcl28 : osCallsTab.length = 28 := hcl'
  rw [hwl] at *
  rw [hcl28] at *
  unfold vsPiPrice
  rw [limbs_of_lt (by omega : logGT (σ (.n 1901)) 28 < 2 ^ 64)]
  omega

end Proof

end Reader

end

end LeanVM.Cost.Bounds.Guest
