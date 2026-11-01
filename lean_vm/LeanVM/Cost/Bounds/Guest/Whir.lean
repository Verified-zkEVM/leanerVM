module

public import LeanVM.Cost.Bounds.Guest.Signatures

/-!
# Bounds on the guest decoder's prices: a child's proof

`verify_sub`'s witness, the child proof, off `open_stacked`'s tables as arrays
(`Cost/Decoder/Signatures.lean`: `vsPiOfNC` is `vsPiOfA`, `Guest/Fast/Whir.lean`): its stream words
and, per level of the opening's candidate (`WhirTabs.calls`), the queries of `opening_queries` and
their openings, in the price `R` of a memory read, `S` of the valuation, `F` of the frame map, the
cursor's length at most `L` and its price at most `C`:

* the levels' shapes (`OqOK`, `callOK_osCallsTab`: the table's every call, by kernel evaluation),
  the tables as arrays (`WhirTabsOK`, `whirTabs_ok`), the shape's numbers (`Oq.R`, `Oq.D`, …:
  constants);
* consecutive words, the address stepped by `g` (`wordsFrom_cost`: `R + 286` a word, against
  `R + 17398` by `g^k` before), a query's position (`bitsW_cost`, `posOfW_cost`), row
  (`oqRow_cost`) and siblings (`oqSibsOf_cost`), a query, its position read once
  (`oqQueryAt_cost`, `oqQueryA_cost`), an iteration (`oqIterA_cost`), the loop, its frames at the
  next power of `g` (`oqItersFrom_cost`), the queries (`oqsOfA_cost`), a query's opening
  (`toOpening_cost`, `capSibsOf_cost`), a level (`levelOsAt_cost`, `levelOsA_cost`);
* **`vsPiOfN_cost`**: a child's proof (`vsPiOfAt_cost`, `vsPiOfM_cost`), at most
  `vsPiPrice R S F C L`.
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

/-- `open_stacked`'s tables as arrays: the lanes below `2^64`, each candidate's words at most
`121`, its calls at most `6`, each of the table's shapes (`whirTabs_ok`). -/
structure WhirTabsOK (T : WhirTabs) : Prop where
  lanes : ∀ x ∈ T.lanes, x < 2 ^ 64
  words : ∀ m, T.words.getD m 0 ≤ 121
  calls : ∀ m, (T.calls.getD m []).length ≤ 6 ∧ ∀ c ∈ T.calls.getD m [], CallOK c

theorem callOK_getD (m : ℕ) :
    (osCallsTab.getD m []).length ≤ 6 ∧ ∀ c ∈ osCallsTab.getD m [], CallOK c := by
  rw [List.getD_eq_getElem?_getD]
  cases hk : osCallsTab[m]? with
  | none => simp
  | some cs =>
    have := List.mem_of_getElem? hk
    exact ⟨callOK_osCallsTab.2.1 cs this, callOK_osCallsTab.2.2 cs this⟩

theorem whirTabs_ok : WhirTabsOK whirTabs := by
  refine ⟨gLanes_ok.2, fun m ↦ ?_, fun m ↦ ?_⟩
  · show osWordsTab.toArray.getD m 0 ≤ 121
    rw [getD_toArray, List.getD_eq_getElem?_getD]
    cases hk : osWordsTab[m]? with
    | none => simp
    | some x => exact osWordsTab_ok.2 x (List.mem_of_getElem? hk)
  · show (osCallsTab.toArray.getD m []).length ≤ 6 ∧ ∀ c ∈ osCallsTab.toArray.getD m [], CallOK c
    rw [getD_toArray]
    exact callOK_getD m

/-- **`open_stacked`'s tables, built** (`whirTabsC`): at most `9330`. -/
theorem whirTabs_cost (hP : Includes P Decoder.whirTabsC.costDeps) :
    machineCost P Decoder.whirTabsC.costIdx [] ≤ 9330 := by
  rw [Decoder.whirTabsC.costEq P hP, Decoder.gLanesC.costEq P (by includes),
    Decoder.osWordsTabC.costEq P (by includes), Decoder.osCallsTabC.costEq P (by includes),
    osWordsTab_ok.1, callOK_osCallsTab.1]

/-! ## The shape's numbers -/

section Shape

variable {s : Oq} (hs : OqOK s)
include hs

theorem Oq_R_cost (hP : Includes P Decoder.OqRC.costDeps) :
    machineCost P Decoder.OqRC.costIdx [encodeValue s] ≤ 11 := by
  obtain ⟨h1, h2, -⟩ := hs
  rw [Decoder.OqRC.costEq P hP]
  limbs_one; split_ifs <;> omega

theorem Oq_tsz_cost (hP : Includes P Decoder.OqTszC.costDeps) :
    machineCost P Decoder.OqTszC.costIdx [encodeValue s] ≤ 7 := by
  obtain ⟨h1, -⟩ := hs
  rw [Decoder.OqTszC.costEq P hP]
  limbs_one; split_ifs <;> omega

theorem rowLo_cost (hP : Includes P Decoder.rowLoC.costDeps) :
    machineCost P Decoder.rowLoC.costIdx [encodeValue s.I] ≤ 9 := by
  obtain ⟨-, h2, -⟩ := hs
  rw [Decoder.rowLoC.costEq P hP]
  limbs_one; split_ifs <;> omega

theorem Oq_G_cost (hP : Includes P Decoder.OqGC.costDeps) :
    machineCost P Decoder.OqGC.costIdx [encodeValue s] ≤ 46 := by
  have ht := Oq_tsz_cost P hs (by includes)
  have hl := rowLo_cost P hs (by includes)
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, -⟩ := hs
  rw [Decoder.OqGC.costEq P hP]
  limbs_one; omega

theorem Oq_D_cost (hP : Includes P Decoder.OqDC.costDeps) :
    machineCost P Decoder.OqDC.costIdx [encodeValue s] ≤ 122 := by
  have hg := Oq_G_cost P hs (by includes)
  have hl := rowLo_cost P hs (by includes)
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, -⟩ := hs
  rw [Decoder.OqDC.costEq P hP]
  limbs_one; omega

theorem Oq_B_cost (hP : Includes P Decoder.OqBC.costDeps) :
    machineCost P Decoder.OqBC.costIdx [encodeValue s] ≤ 25 := by
  have hr := Oq_R_cost P hs (by includes)
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, -⟩ := hs
  rw [Decoder.OqBC.costEq P hP]
  have : LeanVM.Protocol.KeccakHash.rate < 2 ^ 64 := by decide
  limbs_one; omega

theorem Oq_chainLen_cost (hP : Includes P Decoder.OqChainLenC.costDeps) :
    machineCost P Decoder.OqChainLenC.costIdx [encodeValue s] ≤ 39 := by
  have hb := Oq_B_cost P hs (by includes)
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, -⟩ := hs
  rw [Decoder.OqChainLenC.costEq P hP]
  limbs_one; omega

theorem oqK1_cost (hP : Includes P Decoder.oqK1C.costDeps) (b : ℕ)
    (hb : b < 2 ^ 21) :
    machineCost P Decoder.oqK1C.costIdx [encodeValue b, encodeValue s.R] ≤ 13 := by
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := hs
  rw [Decoder.oqK1C.costEq P hP]
  limbs_one; omega

theorem oqKL_lt (b : ℕ) (hb : b < 2 ^ 21) (emit : Bool) : oqKL s b emit < 2 ^ 23 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, -⟩ := hs
  unfold oqKL oqK1; split_ifs <;> omega

theorem oqCh_lt (b : ℕ) (hb : b < 2 ^ 21) (emit : Bool) : oqCh s b emit < 2 ^ 24 := by
  have := oqKL_lt hs b hb emit
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, -⟩ := hs
  unfold oqCh; omega

theorem oqKL_cost (hP : Includes P Decoder.oqKLC.costDeps) (b : ℕ)
    (hb : b < 2 ^ 21) (emit : Bool) :
    machineCost P Decoder.oqKLC.costIdx
      [encodeValue s, encodeValue b, encodeValue emit] ≤ 159 := by
  have hr := Oq_R_cost P hs (by includes)
  have hk := oqK1_cost P hs (by includes) b hb
  have hd := Oq_D_cost P hs (by includes)
  have hkl := oqKL_lt hs b hb emit
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, -⟩ := hs
  rw [Decoder.oqKLC.costEq P hP]
  have : oqK1 b s.R < 2 ^ 22 := by unfold oqK1; omega
  limbs_one; split_ifs <;> limbs_one <;> omega

theorem oqCh_cost (hP : Includes P Decoder.oqChC.costDeps) (b : ℕ)
    (hb : b < 2 ^ 21) (emit : Bool) :
    machineCost P Decoder.oqChC.costIdx
      [encodeValue s, encodeValue b, encodeValue emit] ≤ 220 := by
  have hkl := oqKL_cost P hs (by includes) b hb emit
  have hc := Oq_chainLen_cost P hs (by includes)
  have hkl' := oqKL_lt hs b hb emit
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, -⟩ := hs
  rw [Decoder.oqChC.costEq P hP]
  limbs_one; omega

theorem oqCq_cost (hP : Includes P Decoder.oqCqC.costDeps) (ch : ℕ)
    (hch : ch < 2 ^ 24) :
    machineCost P Decoder.oqCqC.costIdx [encodeValue s, encodeValue ch] ≤ 11 := by
  obtain ⟨h1, h2, h3, -⟩ := hs
  rw [Decoder.oqCqC.costEq P hP]
  have : oqL0 ch < 2 ^ 25 := by unfold oqL0; omega
  limbs_one; omega

theorem oqEnd_cost (hP : Includes P Decoder.oqEndC.costDeps) (b : ℕ)
    (hb : b < 2 ^ 21) (emit : Bool) :
    machineCost P Decoder.oqEndC.costIdx
      [encodeValue s, encodeValue b, encodeValue emit] ≤ 260 := by
  have hkl := oqCh_cost P hs (by includes) b hb emit
  have hch := oqCh_lt hs b hb emit
  have hq := oqCq_cost P hs (by includes) (oqCh s b emit) hch
  have hkl' := oqKL_lt hs b hb emit
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, -⟩ := hs
  rw [Decoder.oqEndC.costEq P hP]
  have : oqCq s (oqCh s b emit) < 2 ^ 25 := by unfold oqCq oqL0; omega
  limbs_one; omega

theorem oqE1_lt : oqE1 s < 2 ^ 20 := hs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

theorem oqE1_cost (hP : Includes P Decoder.oqE1C.costDeps) :
    machineCost P Decoder.oqE1C.costIdx [encodeValue s] ≤ 270 := by
  have := oqEnd_cost P hs (by includes) 11 (by norm_num) true
  rw [Decoder.oqE1C.costEq P hP]
  omega

end Shape

/-! ## Consecutive words -/

section Reader

variable {rd : Reader} {rdV : MachineValue}
  (hrd : ∀ a : K, RunsApp P rdV [encodeValue a] (encodeValue (rd a)))
  {R : ℕ} (hR : ∀ a : K, appCost P rdV [encodeValue a] ≤ R)
include hrd hR

/-- A cell (`memReadC`), as `cellAt`. -/
theorem memRead_cost (hP : Includes P Decoder.memReadC.costDeps) (p : E)
    (k : ℕ) (hk : k < 2 ^ 40) :
    machineCost P Decoder.memReadC.costIdx
      [rdV, encodeValue p, encodeValue k] ≤ R + 21678 := by
  rw [Decoder.memReadC.costEq P hP rd rdV hrd]
  have := powSqK_cost_lt P (by includes) g k 40 (by norm_num) (by norm_num) hk
  have := hR (p.limb 0 * gpow k)
  cases rd (p.limb 0 * gpow k) <;> dsimp only <;> omega

/-- **`n` consecutive words** (`wordsFromC`), the address stepped by `g`: `(R + 286)·n + 6`. -/
theorem wordsFrom_cost (hP : Includes P Decoder.wordsFromC.costDeps) :
    ∀ (n : ℕ) (a : K), n < 2 ^ 64 →
      machineCost P Decoder.wordsFromC.costIdx [rdV, encodeValue a, encodeValue n] ≤
        (R + 286) * n + 6
  | 0, a, _ => by rw [Decoder.wordsFromC.costEq_zero P hP rd rdV hrd]; omega
  | n + 1, a, hn => by
    rw [Decoder.wordsFromC.costEq_succ P hP rd rdV hrd, limbs_of_lt hn]
    have := wordsFrom_cost hP n (a * Parameters.g) (by omega)
    have := hR a
    have : (Option.casesOn (motive := fun _ ↦ ℕ) (rd a) 7 fun _ ↦ 1) ≤ 7 := by
      cases rd a <;> simp
    rw [Nat.mul_succ]
    omega

omit hrd hR in
theorem length_wordsFrom (a : K) : ∀ n, (wordsFrom rd a n).length = n
  | 0 => rfl
  | n + 1 => by rw [wordsFrom, List.length_cons, length_wordsFrom (a * Parameters.g) n]

omit hrd hR in
theorem bitsW_lt : ∀ l : List E, bitsW l < 2 ^ l.length
  | [] => by simp [bitsW]
  | w :: l => by
    have := bitsW_lt l
    rw [bitsW, List.length_cons, pow_succ]
    split_ifs <;> omega

omit hrd hR in
/-- The number of `n ≤ 62` bit words (`bitsWC`): `46·n + 3`. -/
theorem bitsW_cost (hP : Includes P Decoder.bitsWC.costDeps) :
    ∀ l : List E, l.length ≤ 62 →
      machineCost P Decoder.bitsWC.costIdx [encodeValue l] ≤ 46 * l.length + 3
  | [], _ => by rw [Decoder.bitsWC.costEq_nil P hP]; simp
  | w :: l, hl => by
    rw [Decoder.bitsWC.costEq_cons P hP]
    have := bitsW_cost hP l (by simp at hl; omega)
    have hb := bitsW_lt l
    have h62 : 2 ^ l.length ≤ 2 ^ 62 := Nat.pow_le_pow_right (by norm_num) (by simp at hl; omega)
    rw [limbs_of_lt (by omega : bitsW l < 2 ^ 64), limbs_of_lt (by omega : 2 * bitsW l < 2 ^ 64),
      List.length_cons]
    split_ifs <;> limbs_one <;> omega

/-- The position price: `D ≤ 28` words read in a row and their bits. -/
@[expose] def posPrice (R : ℕ) : ℕ := (R + 286) * 28 + 46 * 28 + 15

/-- **A query's position** (`posOfWC`), `D ≤ 28` bits read in a row: at most `posPrice R`. -/
theorem posOfW_cost (hP : Includes P Decoder.posOfWC.costDeps) (bp : E) (D : ℕ) (hD : D ≤ 28) :
    machineCost P Decoder.posOfWC.costIdx [rdV, encodeValue bp, encodeValue D] ≤ posPrice R := by
  rw [Decoder.posOfWC.costEq P hP rd rdV hrd]
  have := wordsFrom_cost P hrd hR (by includes) D (bp.limb 0) (by omega)
  have := bitsW_cost P (by includes) (wordsFrom rd (bp.limb 0) D)
    (by rw [length_wordsFrom]; omega)
  rw [length_wordsFrom] at this
  have := Nat.mul_le_mul_left (R + 286) hD
  unfold posPrice
  omega

omit hrd hR in
theorem posOfW_lt (bp : E) (D : ℕ) : posOfW rd bp D < 2 ^ D := by
  have := bitsW_lt (wordsFrom rd (bp.limb 0) D)
  rwa [length_wordsFrom] at this

omit hrd hR in
/-- The digest of two cells (`digestOfCellsC`): at most `58`. -/
theorem digestOfCells640_cost (hP : Includes P Decoder.digestOfCellsWC.costDeps)
    (a b : E) :
    machineCost P Decoder.digestOfCellsWC.costIdx [encodeValue a, encodeValue b] ≤
      58 := by
  rw [Decoder.digestOfCellsWC.costEq P hP,
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

/-! ## A query -/

section Val

variable {σ : Val} {σV : MachineValue}
  (hσ : ∀ v : V, RunsApp P σV [encodeValue v] (encodeValue (σ v)))
  {S : ℕ} (hS : ∀ v : V, appCost P σV [encodeValue v] ≤ S)
include hσ hS

omit hrd hR in
/-- A query's row (`oqRowC`), `R ≤ 192` words: `(S + 41)·192 + 18`. -/
theorem oqRow_cost (hP : Includes P Decoder.oqRowC.costDeps) (b Rw : ℕ)
    (hb : b < 2 ^ 21) (hRw : Rw ≤ 192) :
    machineCost P Decoder.oqRowC.costIdx [encodeValue b, encodeValue Rw, σV] ≤
      (S + 13 + 28) * 192 + 18 := by
  rw [Decoder.oqRowC.costEq P hP b Rw σ σV hσ]
  have := rangeMap_le P (by includes) (by includes) _
    (.closure Decoder.oqRowC.lam0.costIdx [encodeValue b, σV])
    (fun i ↦ RunsApp.of_spec (Decoder.oqRowC.lam0.costSpec P (by includes) b σ σV
      hσ i))
    (S + 13) Rw 192 hRw (by norm_num) (fun i hi ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.nil_append,
        Decoder.oqRowC.lam0.costEq P (by includes) b σ σV hσ]
      have := hS (.n (b + i))
      limbs_one
      omega)
  omega

omit hrd hR in
/-- A query's siblings (`oqSibsOfC`), `pd ≤ 20` levels: `(2·S + 140 + 28)·20 + 20`. -/
theorem oqSibsOf_cost (hP : Includes P Decoder.oqSibsOfC.costDeps) (pd ch q : ℕ)
    (hpd : pd ≤ 20) (hch : ch < 2 ^ 24) (hq : q < 2 ^ 64) :
    machineCost P Decoder.oqSibsOfC.costIdx
      [encodeValue pd, encodeValue ch, encodeValue q, σV] ≤ (2 * S + 140 + 28) * 20 + 20 := by
  rw [Decoder.oqSibsOfC.costEq P hP pd ch q σ σV hσ]
  have := rangeMap_le P (by includes) (by includes) _
    (.closure Decoder.oqSibsOfC.lam0.costIdx [encodeValue ch, encodeValue q, σV])
    (fun l ↦ RunsApp.of_spec (Decoder.oqSibsOfC.lam0.costSpec P (by includes) ch q
      σ σV hσ l))
    (2 * S + 140) pd 20 hpd (by norm_num) (fun l hl ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.nil_append,
        Decoder.oqSibsOfC.lam0.costEq P (by includes) ch q σ σV hσ]
      have := testBit_cost P (by includes) q l hq (by omega)
      split_ifs <;> limbs_one <;> cost_facts [digestOfCells640_cost P, hS] <;> omega)
  omega

/-- A query's price, its position given. -/
@[expose] def queryAtPrice (S : ℕ) : ℕ :=
  11 + ((S + 13 + 28) * 192 + 18) + 220 + ((2 * S + 140 + 28) * 20 + 20) + 21

omit hrd hR in
/-- **A query, its position `pos < 2^28` given** (`oqQueryAtC`), of a level's shape, from a value
below `2^21`: at most `queryAtPrice S`. -/
theorem oqQueryAt_cost (hP : Includes P Decoder.oqQueryAtC.costDeps) (s : Oq) (hs : OqOK s)
    (b : ℕ) (hb : b < 2 ^ 21) (emit : Bool) (pos : ℕ) (hpos : pos < 2 ^ 28) :
    machineCost P Decoder.oqQueryAtC.costIdx
      [encodeValue s, σV, encodeValue b, encodeValue emit, encodeValue pos] ≤ queryAtPrice S := by
  rw [Decoder.oqQueryAtC.costEq P hP s σ σV hσ]
  have hR' := Oq_R_cost P hs (by includes)
  have hch := oqCh_cost P hs (by includes) b hb emit
  have hch' := oqCh_lt hs b hb emit
  have hrow := oqRow_cost P hσ hS (by includes) b s.R hb hs.2.2.2.2.1
  have hsib := oqSibsOf_cost P hσ hS (by includes) s.pd (oqCh s b emit) pos hs.2.2.1 hch'
    (by omega)
  unfold queryAtPrice
  omega

/-- A query's price. -/
@[expose] def queryPrice (R S : ℕ) : ℕ := posPrice R + queryAtPrice S + 14

/-- **A query** (`oqQueryAC`), its position read once: at most `queryPrice R S`. -/
theorem oqQueryA_cost (hP : Includes P Decoder.oqQueryAC.costDeps) (s : Oq) (hs : OqOK s)
    (bp : E) (b : ℕ) (hb : b < 2 ^ 21) (emit : Bool) :
    machineCost P Decoder.oqQueryAC.costIdx
      [encodeValue s, rdV, encodeValue bp, encodeValue b, encodeValue emit, σV] ≤
        queryPrice R S := by
  rw [Decoder.oqQueryAC.costEq P hP s rd rdV hrd bp b emit σ σV hσ]
  have h3 : s.pd ≤ 20 := hs.2.2.1
  have h4 : s.cd ≤ 8 := hs.2.2.2.1
  have hp := posOfW_cost P hrd hR (by includes) bp (s.pd + s.cd) (by omega)
  have hlt := posOfW_lt (rd := rd) bp (s.pd + s.cd)
  have : 2 ^ (s.pd + s.cd) ≤ 2 ^ 28 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hq := oqQueryAt_cost P hσ hS (by includes) s hs b hb emit (posOfW rd bp (s.pd + s.cd))
    (by omega)
  rw [limbs_of_lt (by omega : s.pd < 2 ^ 64), limbs_of_lt (by omega : s.cd < 2 ^ 64)]
  unfold queryPrice
  omega

/-- An iteration's price. -/
@[expose] def iterPrice (R S : ℕ) : ℕ := 2 * queryPrice R S + 2 * S + 590

/-- **A loop iteration's queries** (`oqIterAC`): at most `iterPrice R S`. -/
theorem oqIterA_cost (hP : Includes P Decoder.oqIterAC.costDeps) (s : Oq) (hs : OqOK s) :
    machineCost P Decoder.oqIterAC.costIdx [encodeValue s, rdV, σV] ≤ iterPrice R S := by
  rw [Decoder.oqIterAC.costEq P hP s rd rdV hrd σ σV hσ]
  have hE := oqE1_lt hs
  have q1 := oqQueryA_cost P hrd hR hσ hS (by includes) s hs (σ (.n 10)) 11 (by norm_num) true
  have q2 := oqQueryA_cost P hrd hR hσ hS (by includes) s hs (σ (.n (oqE1 s))) (oqE1 s + 1)
    (by omega) false
  have q3 := oqQueryA_cost P hrd hR hσ hS (by includes) s hs (σ (.n 9)) 10 (by norm_num) true
  have e1 := oqE1_cost P hs (by includes)
  have := hS (.n 10); have := hS (.n 9); have := hS (.n (oqE1 s))
  have hb := hs.1
  unfold iterPrice
  limbs_one
  split_ifs <;> omega

omit hrd hR in
/-- The loop's arguments (`oqLoopArgsC`): `7·S + 85`. -/
theorem oqLoopArgs_cost (hP : Includes P Decoder.oqLoopArgsC.costDeps) :
    machineCost P Decoder.oqLoopArgsC.costIdx [σV] ≤ 7 * S + 85 := by
  rw [Decoder.oqLoopArgsC.costEq P hP σ σV hσ]
  have := hS (.n 6); have := hS (.n 4); have := hS (.n 0); have := hS (.n 1); have := hS (.n 5)
  have := hS (.n 11); have := hS (.n 8)
  omega

end Val

omit hrd hR in
theorem length_oqIterOf (s : Oq) (rd : Reader) (σ : Val) : (oqIterOf s rd σ).length ≤ 2 := by
  unfold oqIterOf; split_ifs <;> simp

omit hrd hR in
theorem length_oqIterA (s : Oq) (rd : Reader) (σ : Val) : (oqIterA s rd σ).length ≤ 2 := by
  unfold oqIterA; split_ifs <;> simp

section Frames

variable {Vn : NFrames} {VnV : MachineValue}
  (hVn : ∀ (k : ℕ) (a r : List E) (v : V),
    RunsApp P VnV [encodeValue k, encodeValue a, encodeValue r, encodeValue v]
      (encodeValue (Vn k a r v)))
  {F : ℕ} (hF : ∀ (k : ℕ) (a r : List E) (v : V), k < 2 ^ 64 → a.length + r.length ≤ 16 →
    appCost P VnV [encodeValue k, encodeValue a, encodeValue r, encodeValue v] ≤ F)
include hVn hF

/-- An iteration of the loop, its frame stepped: its price. -/
@[expose] def stepPrice (R F : ℕ) : ℕ := iterPrice R (F + 6) + 2434

/-- **The loop's `N` iterations from the frame at `x`** (`oqItersFromC`), each the next at
`x·g`: at most `stepPrice R F · N + 6`. -/
theorem oqItersFrom_cost (hP : Includes P Decoder.oqItersFromC.costDeps) (s : Oq) (hs : OqOK s)
    (loop : ℕ) (hloop : loop < 2 ^ 64) (la : List E) (hla : la.length ≤ 15) :
    ∀ (N : ℕ) (x : E), N < 2 ^ 64 →
      machineCost P Decoder.oqItersFromC.costIdx [encodeValue s, encodeValue loop, rdV, VnV,
        encodeValue la, encodeValue N, encodeValue x] ≤ stepPrice R F * N + 6
  | 0, x, _ => by rw [Decoder.oqItersFromC.costEq_zero P hP s loop rd rdV hrd Vn VnV hVn]; omega
  | N + 1, x, hN => by
    rw [Decoder.oqItersFromC.costEq_succ P hP s loop rd rdV hrd Vn VnV hVn, limbs_of_lt hN]
    have hσ' : ∀ v : V, RunsApp P (.closure Decoder.oqItersFromC.lam0.costIdx
        [encodeValue loop, VnV, encodeValue (x :: la), encodeValue ([] : List E)]) [encodeValue v]
        (encodeValue (Vn loop (x :: la) [] v)) :=
      fun v ↦ RunsApp.of_spec (Decoder.oqItersFromC.lam0.costSpec P (by includes) loop Vn VnV hVn
        _ _ v)
    have hS' : ∀ v : V, appCost P (.closure Decoder.oqItersFromC.lam0.costIdx
        [encodeValue loop, VnV, encodeValue (x :: la), encodeValue ([] : List E)]) [encodeValue v] ≤
          F + 6 := fun v ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.cons_append,
        List.nil_append, Decoder.oqItersFromC.lam0.costEq P (by includes) loop Vn VnV hVn]
      have := hF loop (x :: la) [] v hloop (by simp; omega)
      omega
    have hi := oqIterA_cost P hrd hR hσ' hS' (by includes) s hs
    have := oqItersFrom_cost hP s hs loop hloop la hla N (x * LeanVM.Protocol.Verifier.gen) (by omega)
    have ha := append_cost P (by includes) (oqIterA s rd (Vn loop (x :: la) []))
      (oqItersFrom s loop rd Vn la N (x * LeanVM.Protocol.Verifier.gen))
    have := length_oqIterA s rd (Vn loop (x :: la) [])
    unfold stepPrice at *
    rw [Nat.mul_succ]
    omega

section Val

variable {σ : Val} {σV : MachineValue}
  (hσ : ∀ v : V, RunsApp P σV [encodeValue v] (encodeValue (σ v)))
  {S : ℕ} (hS : ∀ v : V, appCost P σV [encodeValue v] ≤ S)
include hσ hS

/-- The queries' price. -/
@[expose] def oqsPrice (R S F : ℕ) : ℕ :=
  1 + (S + queryPrice R S + 19) + (7 * S + 85) + (stepPrice R F * 112 + 6) + 12 + 20

/-- **The queries of `opening_queries`** (`oqsOfNC`, `oqsOfA`), its odd query and `N ≤ 112`
iterations: at most `oqsPrice R S F`. -/
theorem oqsOfA_cost (hP : Includes P Decoder.oqsOfNC.costDeps) (s : Oq) (hs : OqOK s)
    (odd loop N : ℕ) (hodd : odd ≤ 1) (hN : N ≤ 112) (hloop : loop < 2 ^ 64) :
    machineCost P Decoder.oqsOfNC.costIdx [encodeValue s, encodeValue odd, encodeValue loop,
      encodeValue N, rdV, σV, VnV] ≤ oqsPrice R S F := by
  rw [Decoder.oqsOfNC.costEq P hP s odd loop N rd rdV hrd σ σV hσ Vn VnV hVn]
  have q := oqQueryA_cost P hrd hR hσ hS (by includes) s hs (σ (.n 12)) 13 (by norm_num) true
  have := hS (.n 12)
  have := oqLoopArgs_cost P hσ hS (by includes)
  have hi := oqItersFrom_cost P hrd hR hVn hF (by includes) s hs loop hloop (oqLoopArgs σ)
    (by simp [oqLoopArgs]) N 1
    (by omega)
  have := Nat.mul_le_mul_left (stepPrice R F) hN
  unfold oqsPrice
  rw [limbs_of_lt (by omega : odd < 2 ^ 64)]
  split_ifs
  · have ha := append_cost P (by includes) [oqQueryA s rd (σ (.n 12)) 13 true σ]
      (oqItersFrom s loop rd Vn (oqLoopArgs σ) N 1)
    simp only [List.length_cons, List.length_nil] at ha
    omega
  · have ha := append_cost P (by includes) ([] : List QW)
      (oqItersFrom s loop rd Vn (oqLoopArgs σ) N 1)
    simp only [List.length_nil] at ha
    omega

end Val

end Frames

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
/-- A cap sibling's index (`capSibC`), `D ≤ 8`, `p < 2^28`: at most `37`. -/
theorem capSib_cost (hP : Includes P Decoder.capSibC.costDeps) (D p j : ℕ)
    (hD : D ≤ 8) (hj : j < 8) (hp : p < 2 ^ 28) :
    machineCost P Decoder.capSibC.costIdx
      [encodeValue D, encodeValue p, encodeValue j] ≤ 37 := by
  rw [Decoder.capSibC.costEq P hP]
  simp only [Nat.one_shiftLeft]
  have : 2 ^ (D - j) ≤ 2 ^ 8 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have : 2 ^ j ≤ 2 ^ 8 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have : p / 2 ^ j ≤ p := Nat.div_le_self _ _
  limbs_one
  split_ifs <;> omega

/-- The cap's siblings (`capSibsOfC`), `D ≤ 8` levels, `p < 2^28`: `(2·R + 43540)·8 + 22`. -/
theorem capSibsOf_cost (hP : Includes P Decoder.capSibsOfC.costDeps) (cap : E)
    (D p : ℕ) (hD : D ≤ 8) (hp : p < 2 ^ 28) :
    machineCost P Decoder.capSibsOfC.costIdx
      [rdV, encodeValue cap, encodeValue D, encodeValue p] ≤ (2 * R + 43512 + 28) * 8 + 22 := by
  rw [Decoder.capSibsOfC.costEq P hP rd rdV hrd]
  have := rangeMap_le P (by includes) (by includes) _
    (.closure Decoder.capSibsOfC.lam0.costIdx
      [rdV, encodeValue cap, encodeValue D, encodeValue p])
    (fun j ↦ RunsApp.of_spec (Decoder.capSibsOfC.lam0.costSpec P
      (by includes) rd rdV hrd cap D p j))
    (2 * R + 43512) D 8 hD (by norm_num) (fun j hj ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.cons_append,
        List.nil_append,
        Decoder.capSibsOfC.lam0.costEq P (by includes) rd rdV hrd]
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

/-- **A query's opening** (`toOpeningC`), of a level of depth at most `26`, cap depth at most
`8`, the query's position below `2^28` and its siblings at most `20`: `openingPrice R`. -/
theorem toOpening_cost (hP : Includes P Decoder.toOpeningC.costDeps) (cap : E)
    (cd depth : ℕ) (w : QW) (hcd : cd ≤ 8) (hdepth : depth ≤ 26) (hw : w.1 < 2 ^ 28)
    (hw2 : w.2.2.length ≤ 20) :
    machineCost P Decoder.toOpeningC.costIdx
      [rdV, encodeValue cap, encodeValue cd, encodeValue depth, encodeValue w] ≤ openingPrice R := by
  rw [Decoder.toOpeningC.costEq P hP rd rdV hrd]
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
  {F : ℕ} (hF : ∀ (k : ℕ) (a r : List E) (v : V), k < 2 ^ 64 → a.length + r.length ≤ 16 →
    appCost P VnV [encodeValue k, encodeValue a, encodeValue r, encodeValue v] ≤ F)
include hσ hS hVn hF

/-- A level's price, its call's argument words given. -/
@[expose] def levelAtPrice (R S F : ℕ) : ℕ :=
  7 + ((S + 9 + 11) * 1 + 3) + oqsPrice R (F + 6) F + ((openingPrice R + 6 + 11) * 225 + 3) + 50

/-- **A level's openings, its call's words `a` given** (`levelOsAtC`), from a call of the table:
at most `levelAtPrice R S F`. -/
theorem levelOsAt_cost (hP : Includes P Decoder.levelOsAtC.costDeps) (c : OsCall) (hc : CallOK c)
    (a : List E) (ha : a.length ≤ 15) :
    machineCost P Decoder.levelOsAtC.costIdx [rdV, σV, VnV, encodeValue c, encodeValue a] ≤
      levelAtPrice R S F := by
  obtain ⟨hs, hodd, hN, hfn, hloop, hdepth, hargs, hrets⟩ := hc
  rw [Decoder.levelOsAtC.costEq P hP rd rdV hrd σ σV hσ Vn VnV hVn]
  have hl2 : ∀ k : ℕ, appCost P (.closure Decoder.levelOsAtC.lam2.costIdx [σV]) [encodeValue k] ≤
      S + 9 := fun k ↦ by
    rw [appCost_fn, List.cons_append, List.nil_append,
      Decoder.levelOsAtC.lam2.costEq P (by includes) σ σV hσ]
    have := hS (.n k); omega
  have hr2 : ∀ k : ℕ, RunsApp P (.closure Decoder.levelOsAtC.lam2.costIdx [σV]) [encodeValue k]
      (encodeValue (σ (.n k))) :=
    fun k ↦ RunsApp.of_spec (Decoder.levelOsAtC.lam2.costSpec P (by includes) σ σV hσ k)
  have m2 := map_cost P (by includes) _ _ hr2 (S + 9) c.rets (fun k _ ↦ hl2 k)
  have := Nat.mul_le_mul_left (S + 9 + 11) hrets
  have hσ'' : ∀ v : V, RunsApp P (.closure Decoder.levelOsAtC.lam1.costIdx
      [VnV, encodeValue a, encodeValue (c.rets.map fun k ↦ σ (.n k)), encodeValue c.fn])
      [encodeValue v] (encodeValue (Vn c.fn a (c.rets.map fun k ↦ σ (.n k)) v)) :=
    fun v ↦ RunsApp.of_spec (Decoder.levelOsAtC.lam1.costSpec P (by includes) Vn VnV hVn _ _ _ v)
  have hS'' : ∀ v : V, appCost P (.closure Decoder.levelOsAtC.lam1.costIdx
      [VnV, encodeValue a, encodeValue (c.rets.map fun k ↦ σ (.n k)), encodeValue c.fn])
      [encodeValue v] ≤ F + 6 := fun v ↦ by
    rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.cons_append,
      List.nil_append, Decoder.levelOsAtC.lam1.costEq P (by includes) Vn VnV hVn]
    have := hF c.fn a (c.rets.map fun k ↦ σ (.n k)) v (by omega)
      (by rw [List.length_map]; omega)
    omega
  have ho := oqsOfA_cost P hrd hR hVn hF hσ'' hS'' (by includes) _ hs c.odd c.loop c.N hodd hN
    (by omega)
  have hlen := length_oqsOfN (rd := rd) ⟨c.base, c.I, c.pd, c.cd⟩ c.odd c.loop c.N
    (Vn c.fn a (c.rets.map fun k ↦ σ (.n k))) Vn
  rw [← oqsOfA_eq] at hlen
  have m3 := map_cost P (by includes) _
    (.closure Decoder.levelOsAtC.lam0.costIdx [rdV, encodeValue (a.headD 0), encodeValue c.depth,
      encodeValue c.cd])
    (fun w ↦ RunsApp.of_spec (Decoder.levelOsAtC.lam0.costSpec P (by includes) rd rdV hrd _ _ _ w))
    (openingPrice R + 6) (oqsOfA ⟨c.base, c.I, c.pd, c.cd⟩ c.odd c.loop c.N rd
      (Vn c.fn a (c.rets.map fun k ↦ σ (.n k))) Vn) (fun w hw ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.cons_append,
        List.nil_append, Decoder.levelOsAtC.lam0.costEq P (by includes) rd rdV hrd]
      rw [oqsOfA_eq] at hw
      obtain ⟨hw1, hw2⟩ := mem_oqsOfN hw
      have h4 : c.cd ≤ 8 := hs.2.2.2.1
      have h3 : c.pd ≤ 20 := hs.2.2.1
      have : 2 ^ (c.pd + c.cd) ≤ 2 ^ 28 := Nat.pow_le_pow_right (by norm_num) (by omega)
      have := toOpening_cost P hrd hR (by includes) (a.headD 0) c.cd c.depth w h4 hdepth
        (lt_of_lt_of_le hw1 this) (by rw [hw2]; exact h3)
      omega)
  have := Nat.mul_le_mul_left (openingPrice R + 6 + 11) (hlen.trans (by omega : 1 + 2 * c.N ≤ 225))
  unfold levelAtPrice
  have := listCasesOn_le a 7 (fun _ _ ↦ 1) (by intros; omega)
  omega

/-- A level's price. -/
@[expose] def levelPrice (R S F : ℕ) : ℕ := ((S + 9 + 11) * 7 + 3) + levelAtPrice R S F + 11

/-- **A level's openings** (`levelOsNC`, `levelOsA`), its call's words read once: at most
`levelPrice R S F`. -/
theorem levelOsA_cost (hP : Includes P Decoder.levelOsNC.costDeps) (c : OsCall) (hc : CallOK c) :
    machineCost P Decoder.levelOsNC.costIdx [rdV, σV, VnV, encodeValue c] ≤ levelPrice R S F := by
  rw [Decoder.levelOsNC.costEq P hP rd rdV hrd σ σV hσ Vn VnV hVn]
  have hl2 : ∀ k : ℕ, appCost P (.closure Decoder.levelOsAtC.lam2.costIdx [σV]) [encodeValue k] ≤
      S + 9 := fun k ↦ by
    rw [appCost_fn, List.cons_append, List.nil_append,
      Decoder.levelOsAtC.lam2.costEq P (by includes) σ σV hσ]
    have := hS (.n k); omega
  have hr2 : ∀ k : ℕ, RunsApp P (.closure Decoder.levelOsAtC.lam2.costIdx [σV]) [encodeValue k]
      (encodeValue (σ (.n k))) :=
    fun k ↦ RunsApp.of_spec (Decoder.levelOsAtC.lam2.costSpec P (by includes) σ σV hσ k)
  have m1 := map_cost P (by includes) _ _ hr2 (S + 9) c.args (fun k _ ↦ hl2 k)
  have := Nat.mul_le_mul_left (S + 9 + 11) hc.2.2.2.2.2.2.1
  have := levelOsAt_cost P hrd hR hσ hS hVn hF (by includes) c hc (c.args.map fun k ↦ σ (.n k))
    (by rw [List.length_map]; have := hc.2.2.2.2.2.2.1; omega)
  unfold levelPrice
  omega

end Val2

omit hrd hR in
theorem length_levelOsA (σ : Val) (Vn : NFrames) (c : OsCall) (hc : CallOK c) :
    (levelOsA rd σ Vn c).length ≤ 225 := by
  rw [levelOsA_eq]
  unfold levelOsN
  rw [List.length_map]
  have := length_oqsOfN (rd := rd) ⟨c.base, c.I, c.pd, c.cd⟩ c.odd c.loop c.N
    (Vn c.fn (c.args.map fun k ↦ σ (.n k)) (c.rets.map fun k ↦ σ (.n k))) Vn
  have := hc.2.2.1
  omega

section Proof

variable {σ : Val} {σV : MachineValue}
  (hσ : ∀ v : V, RunsApp P σV [encodeValue v] (encodeValue (σ v)))
  {S : ℕ} (hS : ∀ v : V, appCost P σV [encodeValue v] ≤ S)
  {Vn : NFrames} {VnV : MachineValue}
  (hVn : ∀ (k : ℕ) (a r : List E) (v : V),
    RunsApp P VnV [encodeValue k, encodeValue a, encodeValue r, encodeValue v]
      (encodeValue (Vn k a r v)))
  {F : ℕ} (hF : ∀ (k : ℕ) (a r : List E) (v : V), k < 2 ^ 64 → a.length + r.length ≤ 16 →
    appCost P VnV [encodeValue k, encodeValue a, encodeValue r, encodeValue v] ≤ F)
  {cl : E → E → ℕ} {clV : MachineValue}
  (hcl : ∀ a b : E, RunsApp P clV [encodeValue a, encodeValue b] (encodeValue (cl a b)))
  {C : ℕ} (hC : ∀ a b : E, appCost P clV [encodeValue a, encodeValue b] ≤ C)
  {L : ℕ} (hL : ∀ a b : E, cl a b ≤ L) (hL32 : L ≤ 2 ^ 32)
include hσ hS hVn hF hcl hC hL hL32

omit hrd hR hVn hF hcl hC hL hL32 in
theorem vsOsArgs_cost (hP : Includes P Decoder.vsOsArgsC.costDeps) :
    machineCost P Decoder.vsOsArgsC.costIdx [σV] ≤ 9 * S + 109 := by
  rw [Decoder.vsOsArgsC.costEq P hP σ σV hσ]
  cost_facts [hS]
  omega

omit hrd hR hVn hF hcl hC hL hL32 in
theorem vsOsRets_cost (hP : Includes P Decoder.vsOsRetsC.costDeps) :
    machineCost P Decoder.vsOsRetsC.costIdx [σV] ≤ 5 * S + 61 := by
  rw [Decoder.vsOsRetsC.costEq P hP σ σV hσ]
  cost_facts [hS]
  omega

/-- A child proof's price, its candidate and `open_stacked`'s frame given. -/
@[expose] def vsAtPrice (R S F C L : ℕ) : ℕ :=
  3 * S + C + ((R + 286) * L + 6) + (F + 6) + ((R + 286) * 121 + 6) + (9 * L + 3) +
    ((levelPrice R (F + 6) F + 30 + 11) * 6 + 3) + ((9 * 225 + 9) * 6 + 3) + 67

/-- **A child's proof, its candidate `m` and the frame `fr` of its `open_stacked` call given**
(`vsPiOfAtC`), the frame of price at most `F + 6`: at most `vsAtPrice R S F C L`. -/
theorem vsPiOfAt_cost (hP : Includes P Decoder.vsPiOfAtC.costDeps) (T : WhirTabs)
    (hT : WhirTabsOK T) (m : ℕ) {fr : Val} {frV : MachineValue}
    (hfr : ∀ v : V, RunsApp P frV [encodeValue v] (encodeValue (fr v)))
    (hfrS : ∀ v : V, appCost P frV [encodeValue v] ≤ F + 6) :
    machineCost P Decoder.vsPiOfAtC.costIdx
      [encodeValue T, rdV, σV, VnV, clV, encodeValue m, frV] ≤ vsAtPrice R S F C L := by
  rw [Decoder.vsPiOfAtC.costEq P hP T rd rdV hrd σ σV hσ Vn VnV hVn cl clV hcl m fr frV hfr]
  have := hS (.n 27); have := hS (.n 868); have := hfrS (.n 8)
  have := hC (σ (.n 27)) (σ (.n 868))
  have hl := hL (σ (.n 27)) (σ (.n 868))
  have hw1 := wordsFrom_cost P hrd hR (by includes) (cl (σ (.n 27)) (σ (.n 868)))
    ((σ (.n 27)).limb 0) (by omega)
  have := Nat.mul_le_mul_left (R + 286) hl
  have hwd := hT.words m
  have hw2 := wordsFrom_cost P hrd hR (by includes) (T.words.getD m 0) ((fr (.n 8)).limb 0)
    (by omega)
  have := Nat.mul_le_mul_left (R + 286) hwd
  have ha := append_cost P (by includes)
    (wordsFrom rd ((σ (.n 27)).limb 0) (cl (σ (.n 27)) (σ (.n 868))))
    (wordsFrom rd ((fr (.n 8)).limb 0) (T.words.getD m 0))
  rw [length_wordsFrom] at ha
  obtain ⟨hcl6, hcok⟩ := hT.calls m
  have hm := map_cost P (by includes) _ (.closure Decoder.vsPiOfAtC.lam0.costIdx [rdV, VnV, frV])
    (fun c ↦ RunsApp.of_spec (Decoder.vsPiOfAtC.lam0.costSpec P (by includes) rd rdV hrd Vn VnV hVn
      fr frV hfr c))
    (levelPrice R (F + 6) F + 30) (T.calls.getD m []) (fun c hc ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.nil_append,
        Decoder.vsPiOfAtC.lam0.costEq P (by includes) rd rdV hrd Vn VnV hVn fr frV hfr]
      have := levelOsA_cost P hrd hR hfr hfrS hVn hF (by includes) c (hcok c hc)
      omega)
  have := Nat.mul_le_mul_left (levelPrice R (F + 6) F + 30 + 11) hcl6
  have hf := flatten_map_cost P (by includes) 225 (levelOsA rd fr Vn) (T.calls.getD m [])
    (fun c hc ↦ length_levelOsA _ _ c (hcok c hc))
  have := Nat.mul_le_mul_left (9 * 225 + 9) hcl6
  unfold vsAtPrice
  omega

/-- A child proof's price, its candidate given. -/
@[expose] def vsMPrice (R S F C L : ℕ) : ℕ :=
  (5 * S + 61) + 1 + (9 * S + 109) + vsAtPrice R S F C L + 20

/-- **A child's proof, its candidate `m` given** (`vsPiOfMC`): the frame of
`open_stacked__L{m}`'s call read once: at most `vsMPrice R S F C L`. -/
theorem vsPiOfM_cost (hP : Includes P Decoder.vsPiOfMC.costDeps) (T : WhirTabs)
    (hT : WhirTabsOK T) (m : ℕ) (hm : m < 2 ^ 32) :
    machineCost P Decoder.vsPiOfMC.costIdx [encodeValue T, rdV, σV, VnV, clV, encodeValue m] ≤
      vsMPrice R S F C L := by
  rw [Decoder.vsPiOfMC.costEq P hP T rd rdV hrd σ σV hσ Vn VnV hVn cl clV hcl m,
    limbs_of_lt (by omega : m < 2 ^ 64)]
  have hfr : ∀ v : V, RunsApp P (.closure Decoder.vsPiOfMC.lam0.costIdx
      [VnV, encodeValue (VerifySub.vsOsRets σ), encodeValue (openStackedIdx m),
        encodeValue (VerifySub.vsOsArgs σ)]) [encodeValue v]
      (encodeValue (Vn (openStackedIdx m) (VerifySub.vsOsArgs σ) (VerifySub.vsOsRets σ) v)) :=
    fun v ↦ RunsApp.of_spec (Decoder.vsPiOfMC.lam0.costSpec P (by includes) Vn VnV hVn _ _ _ v)
  have hfrS : ∀ v : V, appCost P (.closure Decoder.vsPiOfMC.lam0.costIdx
      [VnV, encodeValue (VerifySub.vsOsRets σ), encodeValue (openStackedIdx m),
        encodeValue (VerifySub.vsOsArgs σ)]) [encodeValue v] ≤ F + 6 := fun v ↦ by
    rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.cons_append,
      List.nil_append, Decoder.vsPiOfMC.lam0.costEq P (by includes) Vn VnV hVn]
    have := hF (openStackedIdx m) (VerifySub.vsOsArgs σ) (VerifySub.vsOsRets σ) v
      (by unfold openStackedIdx; omega) (by simp [VerifySub.vsOsArgs, VerifySub.vsOsRets])
    omega
  have := vsPiOfAt_cost P hrd hR hσ hS hVn hF hcl hC hL hL32 (by includes) T hT m hfr hfrS
  have := vsOsArgs_cost P hσ hS (by includes)
  have := vsOsRets_cost P hσ hS (by includes)
  unfold vsMPrice
  omega

/-- A child proof's price. -/
@[expose] def vsPiPrice (R S F C L : ℕ) : ℕ := S + 725 + vsMPrice R S F C L + 19

/-- **A child's proof** (`vsPiOfNC`, `vsPiOfA`) at `verify_sub`'s valuation, off `open_stacked`'s
tables `T`: its stream (the cursor's length at most `L`), the opening's words, the candidate's
levels' openings: at most `vsPiPrice R S F C L`. -/
theorem vsPiOfN_cost (hP : Includes P Decoder.vsPiOfNC.costDeps) (T : WhirTabs)
    (hT : WhirTabsOK T) :
    machineCost P Decoder.vsPiOfNC.costIdx [encodeValue T, rdV, σV, VnV, clV] ≤
      vsPiPrice R S F C L := by
  rw [Decoder.vsPiOfNC.costEq P hP T rd rdV hrd σ σV hσ Vn VnV hVn cl clV hcl]
  have := hS (.n 1901)
  have := logGTWith_cost P (by includes) T.lanes hT.lanes (σ (.n 1901)) 28 (by norm_num)
  have := logGTWith_le T.lanes (σ (.n 1901)) 28
  have := vsPiOfM_cost P hrd hR hσ hS hVn hF hcl hC hL hL32 (by includes) T hT
    (logGTWith T.lanes (σ (.n 1901)) 28) (by omega)
  unfold vsPiPrice
  omega

end Proof

end Reader

end

end LeanVM.Cost.Bounds.Guest
