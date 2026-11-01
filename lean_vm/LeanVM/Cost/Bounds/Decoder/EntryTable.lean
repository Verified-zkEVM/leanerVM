module

public import LeanVM.Cost.Bounds.Decoder.EntryMaps
public import LeanVM.Cost.Bounds.Decoder.PreTest
public import LeanVM.Cost.Bounds.Decoder.GuestTablesBounds

/-!
# Bound: the replayed frame map, compiled

The prices of `Cost/Decoder/EntryTable.lean`'s functions, the entry table's map amortized
(`Bounds/Decoder/EntryMaps.lean`). Parameters: `R` a memory read (the reader closure), `Pr` the
precondition's test (`preTestAt D T Pw rd`, `preTestAt_cost_deployed`), `Gpc` a lookup in the pc
table and `M` the functions entered at one pc (for `pcTableT`: `pcTableT_get_cost`, `8339`, and
`pcTableT_getD_length`, `2`), the entry table below `2^D ≤ 2^62` insertions.

* `wordsWith_cost`, `callKey_cost`, **`entryKeyT_cost`**: a state's key, its `22 + 10` words read
  (`guestArgCounts`, `guestRetCounts`, `GuestTablesBounds.lean`), at most `32R + 113685`;
* **`fileOne_amortized`**: one function filed, `fileOnePrice Pr R D` amortized
  (`Pr + 32R + insertKeyPrice 22 D + 113699`);
* **`fileStateT_amortized`**: a state filed under each function entered at its pc,
  `fileStatePrice Gpc M Pr R D = Gpc + (fileOnePrice Pr R D + 15)·M + 25` amortized;
* **`entryTableT_cost`**: the entry table of `n` states, `M·n < 2^D`:
  **`(fileStatePrice Gpc M Pr R D + 15)·n + 15`**, and the table a good map of keys of at most `22`
  codes, below `2^D` insertions (`EntryGood`);
* **`frameAt_cost`**: the frame map's closure on a call of `a` argument and `r` return words, the
  table below `2^D` insertions: at most
  `D·(17 + (67·(a + r) + 98)·(D + 2)) + 28·(a + r) + R + 11070`: one lookup (`D` levels, a binary
  search each), two frame reads;
* **`pcTableT_cost`**: the pc table, built once: at most `17036451`; a lookup in it at most `8339`
  (`pcTableT_get_cost`), at most two functions per pc (`pcTableT_getD_length`);
* **`cursorLength_cost`**: the cursor's length (`cursorLengthC`), the logarithm at most `Lg`: at
  most `Lg + 2·invK + …` (see the statement), its value at most `2^32` (`cursorLenWith_le`).
-/

namespace LeanVM.Cost.Bounds

open LeanVM.Cost LeanVM.Cost.Decoder LeanVM.Cost.Library LeanVM.Parameters LeanVM.Semantics
open LeanVM.Extraction LeanVM.Extraction.Fast LeanVM.Guest.Core LeanVM.Guest.Located
open LeanVM.Guest.Fast

public section

attribute [local instance] lexOrd

variable (P : MachineProgram)

/-! ## A fold, amortized, its final potential kept -/

/-- **`List.foldl`, amortized**, the final potential and invariant kept (`listFoldl_amortized`). -/
theorem listFoldl_amortized' {α β : Type} [MachineEncoding α] [MachineEncoding β]
    (hP : Includes P listFoldl.costDeps) (f : α → β → α) (fVal : MachineValue)
    (hf : ∀ a b, RunsApp P fVal [encodeValue a, encodeValue b] (encodeValue (f a b))) (A : ℕ)
    (Φ : α → ℕ) (I : α → ℕ → Prop) :
    ∀ (l : List β) (init : α), I init l.length →
      (∀ acc r, I acc (r + 1) → ∀ b ∈ l, I (f acc b) r ∧
        appCost P fVal [encodeValue acc, encodeValue b] + Φ (f acc b) ≤ Φ acc + A) →
      I (l.foldl f init) 0 ∧
        machineCost P listFoldl.costIdx [fVal, encodeValue init, encodeValue l] +
          Φ (l.foldl f init) ≤ Φ init + (A + 9) * l.length + 3 := by
  intro l
  induction l with
  | nil =>
    intro init hI _
    rw [listFoldl.costEq_nil P hP f fVal hf]
    refine ⟨hI, ?_⟩
    simp only [List.foldl_nil, List.length_nil]
    omega
  | cons b l ih =>
    intro init hI hB
    rw [listFoldl.costEq_cons P hP f fVal hf, List.foldl_cons]
    obtain ⟨hI', h2⟩ := hB init l.length (by simpa using hI) b (by simp)
    obtain ⟨hF, h1⟩ := ih (f init b) hI' (fun acc r hacc b' hb ↦ hB acc r hacc b' (by simp [hb]))
    refine ⟨hF, ?_⟩
    simp only [List.length_cons]
    nlinarith

/-! ## The guest's tables -/

theorem toArray_getD_le_of_all {l : List ℕ} {B : ℕ} (h : l.all (· ≤ B) = true) (j : ℕ) :
    l.toArray.getD j 0 ≤ B := by
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray]
  rw [List.all_eq_true] at h
  cases hj : l[j]? with
  | none => simp
  | some x =>
    simp only [Option.getD_some]
    exact of_decide_eq_true (h x (List.mem_of_getElem? hj))

theorem argCount_le (j : ℕ) : guestArgCounts.getD j 0 ≤ 22 :=
  toArray_getD_le_of_all guestArgCountsList_le j

theorem retCount_le (j : ℕ) : guestRetCounts.getD j 0 ≤ 10 :=
  toArray_getD_le_of_all guestRetCountsList_le j

theorem getD_getD_lt (A : Array (Array ℕ)) (B : ℕ) (hB : 0 < B)
    (h : ∀ a ∈ A, ∀ x ∈ a, x < B) (j i : ℕ) : (A.getD j #[]).getD i 0 < B := by
  by_cases h1 : j < A.size
  · have e : A.getD j #[] = A[j] := by simp [Array.getD, h1]
    rw [e]
    by_cases h2 : i < A[j].size
    · have e2 : A[j].getD i 0 = A[j][i] := by simp [Array.getD, h2]
      rw [e2]
      exact h _ (Array.getElem_mem h1) _ (Array.getElem_mem h2)
    · have e2 : A[j].getD i 0 = 0 := by simp [Array.getD, h2]
      rw [e2]
      exact hB
  · have e : A.getD j #[] = #[] := by simp [Array.getD, h1]
    rw [e]
    simpa using hB

theorem loc_lt (j i : ℕ) : (guestLocs.getD j #[]).getD i 0 < 2 ^ 20 := by
  refine getD_getD_lt _ _ (by norm_num) (fun a ha x hx ↦ ?_) j i
  have h := guestLocsList_lt
  rw [List.all_eq_true] at h
  rw [show guestLocs = (guestLocsList.map List.toArray).toArray from rfl, List.mem_toArray,
    List.mem_map] at ha
  obtain ⟨l, hl, rfl⟩ := ha
  have hl' := h l hl
  rw [List.all_eq_true] at hl'
  exact of_decide_eq_true (hl' x (by simpa using hx))

/-! ## A state's key -/

/-- A word's code (`wordCodeC`): `15`. -/
theorem wordCode_cost (hP : Includes P wordCodeC.costDeps) (x : E) :
    machineCost P wordCodeC.costIdx [encodeValue x] = 15 := by
  rw [wordCodeC.costEq P hP]

/-- A call's key (`callKeyC`): `28` per word, `19`. -/
theorem callKey_cost (hP : Includes P callKeyC.costDeps) (j : ℕ) (args rets : List E) :
    machineCost P callKeyC.costIdx [encodeValue j, encodeValue args, encodeValue rets] ≤
      28 * (args.length + rets.length) + 19 := by
  rw [callKeyC.costEq P hP]
  have hlam : ∀ x : E, appCost P (.closure callKeyC.lam0.costIdx []) [encodeValue x] ≤ 17 := by
    intro x
    rw [appCost_fn, List.nil_append, callKeyC.lam0.costEq P (by includes),
      wordCode_cost P (by includes)]
  have h1 := map_cost P (by includes) _ (.closure callKeyC.lam0.costIdx [])
    (fun x ↦ RunsApp.of_spec (callKeyC.lam0.costSpec P (by includes) x)) 17 args
    (fun x _ ↦ hlam x)
  have h2 := map_cost P (by includes) _ (.closure callKeyC.lam0.costIdx [])
    (fun x ↦ RunsApp.of_spec (callKeyC.lam0.costSpec P (by includes) x)) 17 rets
    (fun x _ ↦ hlam x)
  omega

/-- The code of a word: word-sized. -/
theorem wordCode_ok (x : E) : TripleOK (wordCode x) :=
  ⟨UInt64.toNat_lt _, UInt64.toNat_lt _, UInt64.toNat_lt _⟩

/-- A call's key, its callee word-sized, its lists at most `L`: of at most `L` codes. -/
theorem callKey_ok {L j : ℕ} {args rets : List E} (hj : j < 2 ^ 64) (ha : args.length ≤ L)
    (hr : rets.length ≤ L) : KeyOK L (callKey j args rets) := by
  refine ⟨hj, by simpa [callKey] using ha, by simpa [callKey] using hr, ?_, ?_⟩ <;>
  · intro x hx
    simp only [callKey, List.mem_map] at hx
    obtain ⟨y, -, rfl⟩ := hx
    exact wordCode_ok y

theorem length_wordsWith (rd : Reader) (fp : K) (o n : ℕ) : (wordsWith rd fp o n).length = n := by
  simp [wordsWith]

section Reads

variable (rd : Reader) (rdVal : MachineValue)
  (hrd : ∀ a : K, RunsApp P rdVal [encodeValue a] (encodeValue (rd a)))
  (R : ℕ) (hR : ∀ a : K, appCost P rdVal [encodeValue a] ≤ R)

include hrd hR in
/-- `n` words of a frame from cell `o` (`wordsWithC`), `o + n ≤ 2^W`: at most
`(psAt W + R + 306)·n + 20`. -/
theorem wordsWith_cost (hP : Includes P wordsWithC.costDeps) {W : ℕ} (hW : 0 < W) (hW64 : W < 64)
    (fp : K) (o n : ℕ) (hon : o + n ≤ 2 ^ W) :
    machineCost P wordsWithC.costIdx [rdVal, encodeValue fp, encodeValue o, encodeValue n] ≤
      (psAt W + R + 306) * n + 20 := by
  have h64 : 2 ^ W < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) hW64
  rw [wordsWithC.costEq P hP rd rdVal hrd]
  have hr := rangeLoop_cost P (by includes) n [] (by omega)
  have hm := map_cost P (by includes) _
    (.closure wordsWithC.lam0.costIdx [rdVal, encodeValue fp, encodeValue o])
    (fun i ↦ RunsApp.of_spec (wordsWithC.lam0.costSpec P (by includes) rd rdVal hrd fp o i))
    (psAt W + R + 278) (List.range n) (fun i hi ↦ by
      have hi' := List.mem_range.mp hi
      simp only [appCost_fn, List.cons_append, List.nil_append]
      rw [wordsWithC.lam0.costEq P (by includes) rd rdVal hrd, limbs_of_lt (by omega : o < 2 ^ 64),
        limbs_of_lt (by omega : i < 2 ^ 64)]
      have := wordWith_cost P rd rdVal hrd R hR hW hW64 (by includes) fp (o + i) (by omega)
      simp only [max_self]
      omega)
  rw [List.length_range] at hm
  nlinarith

include hrd hR in
/-- **A state's key** (`entryKeyTC`): its `≤ 22` argument and `≤ 10` return words read, at most
`32R + 113685`. -/
theorem entryKeyT_cost (hP : Includes P entryKeyTC.costDeps) (s : Registers K) (j : ℕ) :
    machineCost P entryKeyTC.costIdx [rdVal, encodeValue s, encodeValue j] ≤ 32 * R + 113685 := by
  have ha := argCount_le j
  have hr := retCount_le j
  rw [entryKeyTC.costEq P hP rd rdVal hrd, limbs_of_lt (by omega : guestArgCounts.getD j 0 < 2 ^ 64)]
  have h1 := wordsWith_cost P rd rdVal hrd R hR (by includes) (W := 6) (by norm_num) (by norm_num)
    s.fp 2 (guestArgCounts.getD j 0) (show 2 + guestArgCounts.getD j 0 ≤ 2 ^ 6 by omega)
  have h2 := wordsWith_cost P rd rdVal hrd R hR (by includes) (W := 6) (by norm_num) (by norm_num)
    s.fp (2 + guestArgCounts.getD j 0) (guestRetCounts.getD j 0)
    (show 2 + guestArgCounts.getD j 0 + guestRetCounts.getD j 0 ≤ 2 ^ 6 by omega)
  have h3 := callKey_cost P (by includes) j (wordsWith rd s.fp 2 (guestArgCounts.getD j 0))
    (wordsWith rd s.fp (2 + guestArgCounts.getD j 0) (guestRetCounts.getD j 0))
  rw [length_wordsWith, length_wordsWith] at h3
  unfold psAt at h1 h2
  generalize guestArgCounts.getD j 0 = a at *
  generalize guestRetCounts.getD j 0 = b at *
  nlinarith

/-- A state's key: of at most `22` codes per list. -/
theorem entryKeyT_ok (s : Registers K) {j : ℕ} (hj : j < 2 ^ 64) : KeyOK 22 (entryKeyT rd s j) :=
  callKey_ok hj (by rw [length_wordsWith]; exact argCount_le j)
    (by rw [length_wordsWith]; have := retCount_le j; omega)

/-! ## Filing the states -/

/-- The amortized price of filing one function's entry. -/
@[expose] def fileOnePrice (Pr R D : ℕ) : ℕ := Pr + 32 * R + insertKeyPrice 22 D + 113699

/-- The amortized price of filing a state, `M` functions per pc, a pc lookup at most `Gpc`. -/
@[expose] def fileStatePrice (Gpc M Pr R D : ℕ) : ℕ := Gpc + (fileOnePrice Pr R D + 15) * M + 25

section File

variable (pre : ℕ → K → Bool) (preVal : MachineValue)
  (hpre : ∀ (a : ℕ) (b : K), RunsApp P preVal [encodeValue a, encodeValue b] (encodeValue (pre a b)))
  (Pr : ℕ) (hPr : ∀ (j : ℕ) (fp : K), j < 2 ^ 64 → appCost P preVal [encodeValue j, encodeValue fp] ≤ Pr)
  (D : ℕ) (hD : D ≤ 62)

include hrd hR hpre hPr hD in
/-- **One function filed, amortized** (`fileOneC`): the precondition's test, the state's key and
an insertion if new. -/
theorem fileOne_amortized (hP : Includes P fileOneC.costDeps) (s : Registers K)
    (m : SortedMap CallKey K) (r : ℕ) (hm : KeyInv 22 D m (r + 1)) (j : ℕ) (hj : j < 2 ^ 64) :
    KeyInv 22 D (fileOne pre rd s m j) r ∧
      machineCost P fileOneC.costIdx [preVal, rdVal, encodeValue s, encodeValue m, encodeValue j] +
          (134 * 22 + 71) * potential D (fileOne pre rd s m j).levels ≤
        (134 * 22 + 71) * potential D m.levels + fileOnePrice Pr R D := by
  rw [fileOneC.costEq P hP pre preVal hpre rd rdVal hrd]
  have h1 := hPr j s.fp hj
  unfold fileOnePrice
  by_cases hp : pre j s.fp = true
  · simp only [hp, ↓reduceIte, fileOne]
    have h2 := entryKeyT_cost P rd rdVal hrd R hR (by includes) s j
    obtain ⟨hI, h3⟩ := insertIfNewKey_amortized P (by includes) 22 D hD m r hm (entryKeyT rd s j)
      (entryKeyT_ok rd s hj) s.fp
    refine ⟨hI, ?_⟩
    omega
  · simp only [hp, Bool.false_eq_true, ↓reduceIte, fileOne]
    obtain ⟨hg, hQ, hw⟩ := hm
    refine ⟨⟨hg, hQ, by omega⟩, ?_⟩
    omega

include hrd hR hpre hPr hD in
/-- **A state filed, amortized** (`fileStateTC`): the pc table's lookup (at most `Gpc`), then the
functions entered there (at most `M`), each filed: `fileStatePrice Gpc M Pr R D`. -/
theorem fileStateT_amortized (hP : Includes P fileStateTC.costDeps) (pcT : SortedMap ℕ (List ℕ))
    (M Gpc : ℕ) (hpc : ∀ k, ∀ j ∈ pcT.getD k [], j < 2 ^ 64) (hM : ∀ k, (pcT.getD k []).length ≤ M)
    (hG : ∀ k, NatKey k → machineCost P getPcC.costIdx [encodeValue pcT, encodeValue k] ≤ Gpc)
    (c : ℕ) (m : SortedMap CallKey K) (r : ℕ) (hm : KeyInv 22 D m (M * (r + 1) + c))
    (s : Registers K) :
    KeyInv 22 D (fileStateT pcT pre rd m s) (M * r + c) ∧
      machineCost P fileStateTC.costIdx [encodeValue pcT, preVal, rdVal, encodeValue m,
          encodeValue s] + (134 * 22 + 71) * potential D (fileStateT pcT pre rd m s).levels ≤
        (134 * 22 + 71) * potential D m.levels + fileStatePrice Gpc M Pr R D := by
  rw [fileStateTC.costEq P hP pcT pre preVal hpre rd rdVal hrd]
  have hg := hG (laneCode s.pc) (UInt64.toNat_lt _)
  have hjs := hM (laneCode s.pc)
  obtain ⟨hI, hF⟩ := listFoldl_amortized' P (by includes) _
    (.closure fileStateTC.lam0.costIdx [preVal, rdVal, encodeValue s])
    (fun acc j ↦ RunsApp.of_spec (fileStateTC.lam0.costSpec P (by includes) pre preVal hpre rd
      rdVal hrd s acc j))
    (fileOnePrice Pr R D + 6) (fun m ↦ (134 * 22 + 71) * potential D m.levels)
    (fun acc r' ↦ KeyInv 22 D acc (r' + (M * r + c))) (pcT.getD (laneCode s.pc) []) m
    (by obtain ⟨h1, h2, h3⟩ := hm; exact ⟨h1, h2, by nlinarith⟩)
    (fun acc r' hacc j hj ↦ by
      obtain ⟨h1, h2⟩ := fileOne_amortized P rd rdVal hrd R hR pre preVal hpre Pr hPr D hD
        (by includes) s acc (r' + (M * r + c)) (by simpa [Nat.add_right_comm] using hacc) j
        (hpc _ j hj)
      refine ⟨h1, ?_⟩
      rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.nil_append,
        fileStateTC.lam0.costEq P (by includes) pre preVal hpre rd rdVal hrd]
      omega)
  refine ⟨by simpa [fileStateT] using hI, ?_⟩
  have hjM := Nat.mul_le_mul_left (fileOnePrice Pr R D + 6 + 9) hjs
  unfold fileStatePrice
  simp only [fileStateT] at hF ⊢
  generalize pcT.get? (laneCode s.pc) = o
  cases o <;> dsimp only <;> nlinarith

/-- **The entry table is good**: a good map of keys of at most `22` codes, below `2^D`
insertions. -/
@[expose] def EntryGood (D : ℕ) (m : SortedMap CallKey K) : Prop :=
  smGood m ∧ KeysIn (KeyOK 22) m.levels ∧ smWeightSum m < 2 ^ D

include hrd hR hpre hPr hD in
/-- **The entry table of the states** (`entryTableTC`), `M·|states| < 2^D`: at most
`(fileStatePrice Gpc M Pr R D + 15)·|states| + 15`, and the table good. -/
theorem entryTableT_cost (hP : Includes P entryTableTC.costDeps) (pcT : SortedMap ℕ (List ℕ))
    (M Gpc : ℕ) (hpc : ∀ k, ∀ j ∈ pcT.getD k [], j < 2 ^ 64) (hM : ∀ k, (pcT.getD k []).length ≤ M)
    (hG : ∀ k, NatKey k → machineCost P getPcC.costIdx [encodeValue pcT, encodeValue k] ≤ Gpc)
    (states : List (Registers K)) (hn : M * states.length < 2 ^ D) :
    EntryGood D (entryTableT pcT pre states rd) ∧
      machineCost P entryTableTC.costIdx [encodeValue pcT, preVal, encodeValue states, rdVal] ≤
        (fileStatePrice Gpc M Pr R D + 15) * states.length + 15 := by
  rw [entryTableTC.costEq P hP pcT pre preVal hpre states rd rdVal hrd]
  obtain ⟨hI, hF⟩ := listFoldl_amortized' P (by includes) _
    (.closure entryTableTC.lam0.costIdx [encodeValue pcT, preVal, rdVal])
    (fun acc s ↦ RunsApp.of_spec (entryTableTC.lam0.costSpec P (by includes) pcT pre preVal hpre
      rd rdVal hrd acc s))
    (fileStatePrice Gpc M Pr R D + 6) (fun m ↦ (134 * 22 + 71) * potential D m.levels)
    (fun acc r ↦ KeyInv 22 D acc (M * r + 1)) states SortedMap.empty
    ⟨smGood_empty, fun _ h ↦ by simp [SortedMap.empty] at h, by simp [smWeightSum_empty]; omega⟩
    (fun acc r hacc s _ ↦ by
      obtain ⟨h1, h2⟩ := fileStateT_amortized P rd rdVal hrd R hR pre preVal hpre Pr hPr D hD
        (by includes) pcT M Gpc hpc hM hG 1 acc r hacc s
      refine ⟨h1, ?_⟩
      rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.nil_append,
        entryTableTC.lam0.costEq P (by includes) pcT pre preVal hpre rd rdVal hrd]
      omega)
  have he : entryTableT pcT pre states rd = states.foldl (fileStateT pcT pre rd) .empty := rfl
  obtain ⟨hg, hQ, hw⟩ := hI
  refine ⟨by rw [he]; exact ⟨hg, hQ, by omega⟩, ?_⟩
  have h0 : potential D (SortedMap.empty : SortedMap CallKey K).levels = 0 := rfl
  rw [h0, Nat.mul_zero, Nat.zero_add] at hF
  nlinarith

end File

/-! ## The frame map -/

/-- Whether `j` is a function's index (`isFunctionIndexC`), `j` word-sized: at most `9`. -/
theorem isFunctionIndex_cost (hP : Includes P isFunctionIndexC.costDeps) (j : ℕ) (hj : j < 2 ^ 64) :
    machineCost P isFunctionIndexC.costIdx [encodeValue j] ≤ 9 := by
  rw [isFunctionIndexC.costEq P hP, limbs_of_lt hj]
  split_ifs <;> omega

include hrd hR in
/-- A frame's word (`frameWordAtC`): the table of frame cells (`guestLocsTableC`, a literal), a
read, at most `R + 11010`. -/
theorem frameWordAt_cost (hP : Includes P frameWordAtC.costDeps) (fp : K) (j : ℕ)
    (hj : j < 2 ^ 64) (v : V) :
    machineCost P frameWordAtC.costIdx [rdVal, encodeValue fp, encodeValue j, encodeValue v] ≤
      R + 11010 := by
  rw [frameWordAtC.costEq P hP rd rdVal hrd]
  have h0 := guestLocsTableC.costEq P (by includes)
  have h1 := isFunctionIndex_cost P (by includes) j hj
  have h2 := wordWith_cost P rd rdVal hrd R hR (W := 20) (by norm_num) (by norm_num) (by includes)
    fp _ (loc_lt (canonIndex j) v.idx)
  unfold psAt at h2
  split_ifs <;> omega

theorem canonIndex_lt64 (j : ℕ) : canonIndex j < 2 ^ 64 := by
  unfold canonIndex isFunctionIndex
  split_ifs with h
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h; omega
  · norm_num

include hrd hR in
/-- **The frame map's closure** (`frameAtC`, `frameAt table rd`): a call of `|args| + |rets|`
words, the table good below `2^D ≤ 2^62` insertions: one lookup, two reads, at most
`D·(17 + (67·(|args| + |rets|) + 98)·(D + 2)) + 28·(|args| + |rets|) + R + 11070`. -/
theorem frameAt_cost (hP : Includes P frameAtC.costDeps) (D : ℕ) (hD : D ≤ 62)
    (table : SortedMap CallKey K) (ht : EntryGood D table) (j : ℕ) (hj : j < 2 ^ 64)
    (args rets : List E) (v : V) :
    machineCost P frameAtC.costIdx [encodeValue table, rdVal, encodeValue j, encodeValue args,
        encodeValue rets, encodeValue v] ≤
      D * (17 + (67 * (args.length + rets.length) + 98) * (D + 2)) +
        28 * (args.length + rets.length) + R + 11070 := by
  obtain ⟨hg, hQ, hw⟩ := ht
  obtain ⟨hlev, hsz⟩ := smGood_levels_le hg hw
  rw [frameAtC.costEq P hP table rd rdVal hrd]
  have h1 := isFunctionIndex_cost P (by includes) j hj
  have h2 := callKey_cost P (by includes) (canonIndex j) args rets
  have hk : KeyOK (args.length + rets.length) (callKey (canonIndex j) args rets) :=
    callKey_ok (canonIndex_lt64 j) (by omega) (by omega)
  have h3 := getKey_cost P (by includes) 22 D hD table hQ hlev
    (fun l hl ↦ (hsz l hl).1.trans (hsz l hl).2) _ hk
  have hkc : keyCmpPrice (callKey (canonIndex j) args rets) =
      67 * (args.length + rets.length) + 38 := by
    simp [keyCmpPrice, callKey]
  rw [hkc, show 67 * (args.length + rets.length) + 38 + 60 =
    67 * (args.length + rets.length) + 98 by omega] at h3
  generalize D * (17 + (67 * (args.length + rets.length) + 98) * (D + 2)) = X at h3 ⊢
  generalize table.get? (callKey (canonIndex j) args rets) = o
  cases o with
  | none => dsimp only; split_ifs <;> omega
  | some fp =>
    have h4 := frameWordAt_cost P rd rdVal hrd R hR (by includes) fp j hj v
    dsimp only; split_ifs <;> omega

end Reads

end

end LeanVM.Cost.Bounds
