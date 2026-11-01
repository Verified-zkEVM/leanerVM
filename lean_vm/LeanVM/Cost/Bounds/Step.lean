module

public import LeanVM.Cost.Bounds.FastPath

/-!
# Bounds: one step of the candidate runner

The price of one step of the halting loop (`stepVec.c390`): the code table's lookup, the
instruction (`executeWithShared.c392`, `executeWith` as compiled), its memory reads, each a binary
search in the memory table (`gLogTable.c445`, `findLane.c446`), and Keccak-f for `KECCAK`.

* **`keccakRound_cost`**: one Keccak round (`keccakRoundShared.c413`) at most `13859` (measured
  `13848`: the bound takes every rotation at its nonzero price); **`keccakF_cost`**: Keccak-f[1600],
  `24` rounds, at most `332907` (≈ `2^18.35`);
* `readCells_cost`: thirteen reads and offsets, `13·(O + R) + 9367`;
* `executeXor_cost` … `executeKeccak_cost`, **`executeWith_cost`**: one instruction with reads of
  price at most `R`, at most `26R + 408358` (`KECCAK` the worst; `MUL` `3R + 8196`);
* `findLane_cost` (`32 + 42·(log₂(hi − lo) + 1)`), `gLogTable_cost` (`94 + 42·log₂|t|`),
  `memRead_cost` (`123 + 42·log₂|memT|`), on tables of word-sized pairs (`WordTable`);
* **`stepVec_cost`**: one step at most `411697 + 42·log₂|codeT| + 1092·log₂|memT|`; at
  `|memT| = |codeT| = 2^32`, `447985 ≈ 2^18.77`.

Library: `listFoldl_le_sum` (a closure's price depending on the element), `getD_cost_idx`,
`bind_cost`, `optionMap_cost`, `listAll_cost`, `finRangeFrom_cost`, `powSq_cost` (`535` per bit).
-/

namespace LeanVM.Cost.Bounds

open LeanVM.Cost LeanVM.Cost.Extractor LeanVM.Cost.Library LeanVM.Parameters LeanVM.Semantics
open LeanVM.Extraction.Fast

public section

variable (P : LeanVM.Cost.MachineProgram)

/-- `List.foldl`, the closure's price depending on the element. -/
theorem listFoldl_le_sum {α β : Type} [MachineEncoding α] [MachineEncoding β] (hP : Includes P listFoldl.costDeps)
    (f : α → β → α) (fVal : MachineValue)
    (hf : ∀ a b, RunsApp P fVal [encodeValue a, encodeValue b] (encodeValue (f a b))) (B : β → ℕ) :
    ∀ (l : List β) (init : α), (∀ acc : α, ∀ b ∈ l, appCost P fVal [encodeValue acc, encodeValue b] ≤ B b) →
      machineCost P listFoldl.costIdx [fVal, encodeValue init, encodeValue l] ≤ (l.map fun b ↦ B b + 9).sum + 3 := by
  intro l
  induction l with
  | nil => intro init _; rw [listFoldl.costEq_nil P hP f fVal hf]; simp
  | cons b l ih =>
    intro init hB
    rw [listFoldl.costEq_cons P hP f fVal hf]
    have h1 := ih (f init b) (fun acc b' hb ↦ hB acc b' (by simp [hb]))
    have h2 := hB init b (by simp)
    simp only [List.map_cons, List.sum_cons]
    omega

/-- `List.get?` at index `k`: `15·k + 10` at most. -/
theorem getInternal_cost_idx (hP : Includes P Auto.List.«get?Internal».c275.costDeps) {α : Type} [MachineEncoding α] :
    ∀ (l : List α) (k : ℕ), k < 2 ^ 64 →
      machineCost P Auto.List.«get?Internal».c275.costIdx [encodeValue l, encodeValue k] ≤ 15 * k + 10 := by
  intro l
  induction l with
  | nil => intro k _; rw [Auto.List.«get?Internal».c275.costEq_nil P hP]; omega
  | cons x l ih =>
    intro k hk
    rw [Auto.List.«get?Internal».c275.costEq_cons P hP, limbs_of_lt hk]
    cases k with
    | zero => simp only [Nat.rec_zero]; omega
    | succ k =>
      have := ih k (by omega)
      simp only
      omega

/-- `List.getD` at index `k`: `15·k + 15` at most. -/
theorem getD_cost_idx (hP : Includes P Auto.List.getD.c274.costDeps) {α : Type} [MachineEncoding α]
    (l : List α) (k : ℕ) (hk : k < 2 ^ 64) (d : α) :
    machineCost P Auto.List.getD.c274.costIdx [encodeValue l, encodeValue k, encodeValue d] ≤ 15 * k + 15 := by
  rw [Auto.List.getD.c274.costEq P hP]
  have := getInternal_cost_idx P (by includes) l k hk
  generalize l[k]? = o
  cases o <;> dsimp only <;> omega

/-- `rot` (`rot.c416`): `17` at most on a word-sized rotation. -/
theorem rot_cost (hP : Includes P Auto.LeanVM.Semantics.Keccak.rot.c416.costDeps) (x : UInt64) (n : ℕ)
    (hn : n < 2 ^ 64) : machineCost P Auto.LeanVM.Semantics.Keccak.rot.c416.costIdx [encodeValue x, encodeValue n] ≤ 17 := by
  rw [Auto.LeanVM.Semantics.Keccak.rot.c416.costEq P hP, limbs_of_lt hn]
  split_ifs <;> omega

theorem keccakRho_getD_le (i : ℕ) : keccakRho.getD i 0 ≤ 62 := by
  rw [List.getD_eq_getElem?_getD]
  cases h : keccakRho[i]? with
  | none => simp
  | some x =>
    simp only [Option.getD_some]
    exact (by decide : ∀ x ∈ keccakRho, x ≤ 62) x (List.mem_of_getElem? h)

theorem keccakPi_cost (hP : Includes P Auto.LeanVM.Parameters.keccakPi.c419.costDeps) (i : ℕ) (hi : i < 25) :
    machineCost P Auto.LeanVM.Parameters.keccakPi.c419.costIdx [encodeValue i] = 28 := by
  rw [Auto.LeanVM.Parameters.keccakPi.c419.costEq P hP]
  cost_simp

theorem setIfInBounds_cost (hP : Includes P Auto.Vector.setIfInBounds.c418.costDeps) {α : Type} [MachineEncoding α]
    {n : ℕ} (xs : Vector α n) (i : ℕ) (x : α) :
    machineCost P Auto.Vector.setIfInBounds.c418.costIdx [encodeValue n, encodeValue xs, encodeValue i, encodeValue x] = n + 4 := by
  rw [Auto.Vector.setIfInBounds.c418.costEq P hP, Vector.size_toArray]


section Round
open Auto.LeanVM.Cost.Extractor

/-- θ's column parities: `5` entries of `36`. -/
theorem roundParity_cost (hP : Includes P keccakRoundShared.c413.costDeps) (a : KeccakState) :
    machineCost P Auto.LeanVM.Cost.Rewrite.ofFnFrom.c117.costIdx
      [encodeValue 5, .closure keccakRoundShared.c413.lam0.costIdx [encodeValue a], encodeValue 0] ≤ 276 := by
  have := ofFnFrom_cost P (by includes) (by norm_num) _ (.closure keccakRoundShared.c413.lam0.costIdx [encodeValue a])
    (fun x ↦ RunsApp.of_spec (keccakRoundShared.c413.lam0.costSpec P (by includes) a x)) 36
    (fun x ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append]
      rw [keccakRoundShared.c413.lam0.costEq P (by includes), limbs_of_lt (by omega)]) 0 (by omega)
  simpa using this

/-- θ: `25` entries of `45`. -/
theorem roundTheta_cost (hP : Includes P keccakRoundShared.c413.costDeps) (a : KeccakState)
    (c : Vector UInt64 5) :
    machineCost P Auto.LeanVM.Cost.Rewrite.ofFnFrom.c117.costIdx
      [encodeValue 25, .closure keccakRoundShared.c413.lam1.costIdx [encodeValue a, encodeValue c], encodeValue 0] ≤ 1581 := by
  have := ofFnFrom_cost P (by includes) (by norm_num) _
    (.closure keccakRoundShared.c413.lam1.costIdx [encodeValue a, encodeValue c])
    (fun x ↦ RunsApp.of_spec (keccakRoundShared.c413.lam1.costSpec P (by includes) a c x)) 45
    (fun x ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append]
      rw [keccakRoundShared.c413.lam1.costEq P (by includes)]
      have := rot_cost P (by includes) (c.toArray.getD ((↑x + 1) % 5) 0) 1 (by norm_num)
      have := x.isLt
      cost_simp
      omega) 0 (by omega)
  simpa using this

/-- ρ and π: `25` steps, step `i` at most `204 + 15·i` (the rotation read from a list). -/
theorem roundRhoPi_cost (hP : Includes P keccakRoundShared.c413.costDeps) (t : KeccakState)
    (c : Vector UInt64 5) (b : KeccakState) :
    machineCost P listFoldl.costIdx
      [.closure keccakRoundShared.c413.lam2.costIdx [encodeValue t, encodeValue c], encodeValue b, encodeValue (List.range 25)] ≤ 9828 := by
  have := listFoldl_le_sum P (by includes) _ (.closure keccakRoundShared.c413.lam2.costIdx [encodeValue t, encodeValue c])
    (fun x y ↦ RunsApp.of_spec (keccakRoundShared.c413.lam2.costSpec P (by includes) t c x y))
    (fun i ↦ 204 + 15 * i) (List.range 25) b
    (fun acc i hi ↦ by
      have hi := List.mem_range.1 hi
      simp only [appCost_fn, List.cons_append, List.nil_append]
      rw [keccakRoundShared.c413.lam2.costEq P (by includes), keccakPi_cost P (by includes) i hi,
        setIfInBounds_cost P (by includes),
        Auto.LeanVM.Parameters.keccakRho.c420.costEq P (by includes)]
      have := getD_cost_idx P (by includes) keccakRho i (by omega) 0
      have := rot_cost P (by includes) (Keccak.lane t i) (keccakRho.getD i 0)
        (by have := keccakRho_getD_le i; omega)
      omega)
  exact this.trans (by decide)

/-- χ: `25` entries of `45`. -/
theorem roundChi_cost (hP : Includes P keccakRoundShared.c413.costDeps) (b t : KeccakState)
    (c : Vector UInt64 5) :
    machineCost P Auto.LeanVM.Cost.Rewrite.ofFnFrom.c117.costIdx
      [encodeValue 25, .closure keccakRoundShared.c413.lam3.costIdx [encodeValue b, encodeValue t, encodeValue c], encodeValue 0] ≤ 1581 := by
  have := ofFnFrom_cost P (by includes) (by norm_num) _
    (.closure keccakRoundShared.c413.lam3.costIdx [encodeValue b, encodeValue t, encodeValue c])
    (fun x ↦ RunsApp.of_spec (keccakRoundShared.c413.lam3.costSpec P (by includes) b t c x)) 45
    (fun x ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append]
      rw [keccakRoundShared.c413.lam3.costEq P (by includes)]
      have := x.isLt
      cost_simp
      omega) 0 (by omega)
  simpa using this

/-- **One Keccak round** (`keccakRoundShared.c413`): at most `13859` (measured `13848`). -/
theorem keccakRound_cost (hP : Includes P keccakRoundShared.c413.costDeps) (a : KeccakState)
    (rc : UInt64) : machineCost P keccakRoundShared.c413.costIdx [encodeValue a, encodeValue rc] ≤ 13859 := by
  have hS : Includes P Auto.Vector.setIfInBounds.c418.costDeps := by includes
  rw [keccakRoundShared.c413.costEq P hP, setIfInBounds_cost P hS]
  simp only [ofFnFrom_length]
  have := rangeLoop_cost P (by includes) 25 [] (by norm_num)
  cost_facts [roundParity_cost P hP, roundTheta_cost P hP, roundRhoPi_cost P hP, roundChi_cost P hP]
  omega

end Round

/-- A table of word-sized pairs, below `2^63` entries. -/
@[expose] def WordTable (t : Array (ℕ × ℕ)) : Prop :=
  t.size < 2 ^ 63 ∧ ∀ e ∈ t.toList, e.1 < 2 ^ 64 ∧ e.2 < 2 ^ 64

theorem WordTable.getD_fst {t : Array (ℕ × ℕ)} (ht : WordTable t) (i : ℕ) :
    (t.getD i (0, 0)).1 < 2 ^ 64 := by
  by_cases hi : i < t.size
  · have : t.getD i (0, 0) = t[i] := by
      simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi]
    rw [this]
    exact (ht.2 _ (Array.getElem_mem_toList hi)).1
  · have : t.getD i (0, 0) = (0, 0) := by
      simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega : t.size ≤ i)]
    rw [this]; norm_num

/-- **The binary search** (`findLane.c446`) over `[lo, hi)`: `42` per halving, `32` at most at
the end. -/
theorem findLane_cost (hP : Includes P Auto.LeanVM.Extraction.Fast.findLane.c446.costDeps)
    (t : Array (ℕ × ℕ)) (ht : WordTable t) (key : ℕ) (hkey : key < 2 ^ 64) (lo hi : ℕ)
    (hlo : lo ≤ hi) (hhi : hi ≤ t.size) :
    machineCost P Auto.LeanVM.Extraction.Fast.findLane.c446.costIdx [encodeValue t, encodeValue key, encodeValue lo, encodeValue hi] ≤
      32 + 42 * (Nat.log2 (hi - lo) + 1) := by
  have hs := ht.1
  have := le_of_halving (fun x : ℕ × ℕ ↦ x.1 ≤ x.2 ∧ x.2 ≤ t.size) (fun x ↦ x.2 - x.1)
    (fun x ↦ machineCost P Auto.LeanVM.Extraction.Fast.findLane.c446.costIdx
      [encodeValue t, encodeValue key, encodeValue x.1, encodeValue x.2]) 42 32
    (fun x hx h0 ↦ by
      try dsimp only at hx h0 ⊢
      rw [Auto.LeanVM.Extraction.Fast.findLane.c446.costEq P hP, limbs_of_lt (by omega : x.1 < 2 ^ 64),
        limbs_of_lt (by omega : x.2 < 2 ^ 64)]
      simp only [show ¬ x.1 < x.2 by omega, ↓reduceDIte]
      omega)
    (fun x hx hpos ↦ by
      try dsimp only at hx hpos ⊢
      rw [Auto.LeanVM.Extraction.Fast.findLane.c446.costEq P hP, limbs_of_lt (by omega : x.1 < 2 ^ 64),
        limbs_of_lt (by omega : x.2 < 2 ^ 64), limbs_of_lt (by omega : x.1 + x.2 < 2 ^ 64),
        limbs_of_lt (ht.getD_fst _), limbs_of_lt hkey,
        limbs_of_lt (by omega : (x.1 + x.2) / 2 < 2 ^ 64)]
      simp only [show x.1 < x.2 by omega, ↓reduceDIte, max_self]
      split_ifs with h1 h2
      · left; omega
      · right
        exact ⟨((x.1 + x.2) / 2 + 1, x.2), by dsimp only; omega, by dsimp only; omega, by simp only; omega⟩
      · right
        exact ⟨(x.1, (x.1 + x.2) / 2), by dsimp only; omega, by dsimp only; omega, by simp only; omega⟩)
    (lo, hi) ⟨hlo, hhi⟩
  simpa using this


section Generic
variable {α β : Type} [MachineEncoding α] [MachineEncoding β]

/-- `Option.bind` (`bind.c323`): the closure's price and `5` at most. -/
theorem bind_cost (hP : Includes P Auto.Option.bind.c323.costDeps) (f : α → Option β) (fVal : MachineValue)
    (hf : ∀ a : α, RunsApp P fVal [encodeValue a] (encodeValue (f a))) (B : ℕ) (hB : ∀ a : α, appCost P fVal [encodeValue a] ≤ B)
    (o : Option α) : machineCost P Auto.Option.bind.c323.costIdx [encodeValue o, fVal] ≤ B + 5 := by
  cases o with
  | none => rw [Auto.Option.bind.c323.costEq_none P hP f fVal hf]; omega
  | some a => rw [Auto.Option.bind.c323.costEq_some P hP a f fVal hf]; have := hB a; omega

/-- `Option.map` (`map.c106`): the closure's price and `7` at most. -/
theorem optionMap_cost (hP : Includes P Auto.Option.map.c106.costDeps) (f : α → β) (fVal : MachineValue)
    (hf : ∀ a : α, RunsApp P fVal [encodeValue a] (encodeValue (f a))) (B : ℕ) (hB : ∀ a : α, appCost P fVal [encodeValue a] ≤ B)
    (o : Option α) : machineCost P Auto.Option.map.c106.costIdx [fVal, encodeValue o] ≤ B + 7 := by
  cases o with
  | none => rw [Auto.Option.map.c106.costEq_none P hP f fVal hf]; omega
  | some a => rw [Auto.Option.map.c106.costEq_some P hP f fVal hf a]; have := hB a; omega

/-- `List.all` (`all.c240`): `9` per element and the predicate's price, `3` at the end. -/
theorem listAll_cost (hP : Includes P Auto.List.all.c240.costDeps) (p : α → Bool) (pVal : MachineValue)
    (hp : ∀ a : α, RunsApp P pVal [encodeValue a] (encodeValue (p a))) (B : ℕ) (hB : ∀ a : α, appCost P pVal [encodeValue a] ≤ B) :
    ∀ l : List α, machineCost P Auto.List.all.c240.costIdx [encodeValue l, pVal] ≤ (B + 9) * l.length + 3 := by
  intro l
  induction l with
  | nil => rw [Auto.List.all.c240.costEq_nil P hP p pVal hp]; omega
  | cons x l ih =>
    rw [Auto.List.all.c240.costEq_cons P hP x l p pVal hp]
    have := hB x
    simp only [List.length_cons]
    split_ifs <;> nlinarith

/-- `List.finRange` from `i` (`finRangeFrom.c425`): `15` per element, `6` at the end. -/
theorem finRangeFrom_cost (hP : Includes P Auto.LeanVM.Cost.Rewrite.finRangeFrom.c425.costDeps)
    (n : ℕ) (hn : n < 2 ^ 64) : ∀ i, i ≤ n →
      machineCost P Auto.LeanVM.Cost.Rewrite.finRangeFrom.c425.costIdx [encodeValue n, encodeValue i] ≤
        15 * (n - i) + 6 := by
  intro i hi
  induction hk : n - i generalizing i with
  | zero =>
    rw [Auto.LeanVM.Cost.Rewrite.finRangeFrom.c425.costEq P hP, limbs_of_lt (by omega : i < 2 ^ 64),
      limbs_of_lt hn]
    simp only [show ¬i < n by omega, ↓reduceDIte]
    omega
  | succ k ih =>
    rw [Auto.LeanVM.Cost.Rewrite.finRangeFrom.c425.costEq P hP, limbs_of_lt (by omega : i < 2 ^ 64),
      limbs_of_lt hn]
    simp only [show i < n by omega, ↓reduceDIte]
    have := ih (i + 1) (by omega) (by omega)
    omega

end Generic

theorem log2_lt_of {n k : ℕ} (hk : 0 < k) (h : n < 2 ^ k) : Nat.log2 n < k := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Nat.log2_zero]; omega
  · exact (Nat.log2_lt (by omega)).2 h

/-- `a^n` by squaring (`powSq.c198`): `535` per bit, `6` at the end. -/
theorem powSq_cost (hP : Includes P Auto.LeanVM.Cost.Rewrite.powSq.c198.costDeps) (a : K) (n : ℕ)
    (hn : n < 2 ^ 64) :
    machineCost P Auto.LeanVM.Cost.Rewrite.powSq.c198.costIdx [encodeValue a, encodeValue n] ≤
      6 + 535 * (Nat.log2 n + 1) := by
  have := le_of_halving (fun x : K × ℕ ↦ x.2 < 2 ^ 64) (fun x ↦ x.2)
    (fun x ↦ machineCost P Auto.LeanVM.Cost.Rewrite.powSq.c198.costIdx [encodeValue x.1, encodeValue x.2]) 535 6
    (fun x hx h0 ↦ by
      try dsimp only at hx h0 ⊢
      rw [Auto.LeanVM.Cost.Rewrite.powSq.c198.costEq P hP, h0]
      simp)
    (fun x hx hpos ↦ by
      try dsimp only at hx hpos ⊢
      right
      refine ⟨(x.1 * x.1, x.2 / 2), by dsimp only; omega, le_refl _, ?_⟩
      rw [Auto.LeanVM.Cost.Rewrite.powSq.c198.costEq P hP, limbs_of_lt hx,
        limbs_of_lt (by omega : x.2 % 2 < 2 ^ 64)]
      simp only [show x.2 ≠ 0 by omega, ↓reduceIte]
      split_ifs <;> omega)
    (a, n) hn
  simpa using this

theorem powSq_cost_le (hP : Includes P Auto.LeanVM.Cost.Rewrite.powSq.c198.costDeps) (a : K) (n : ℕ)
    (hn : n ≤ 3) : machineCost P Auto.LeanVM.Cost.Rewrite.powSq.c198.costIdx [encodeValue a, encodeValue n] ≤ 1076 := by
  refine (powSq_cost P hP a n (by omega)).trans ?_
  have := log2_lt_of (k := 2) (by norm_num) (by omega : n < 2 ^ 2)
  omega

theorem powSq_cost_le' (hP : Includes P Auto.LeanVM.Cost.Rewrite.powSq.c198.costDeps) (a : K) (n : ℕ)
    (hn : n ≤ 15) : machineCost P Auto.LeanVM.Cost.Rewrite.powSq.c198.costIdx [encodeValue a, encodeValue n] ≤ 2146 := by
  refine (powSq_cost P hP a n (by omega)).trans ?_
  have := log2_lt_of (k := 4) (by norm_num) (by omega : n < 2 ^ 4)
  omega

/-! ## Reading thirteen cells -/

section ReadCells
open Auto.LeanVM.Semantics

variable (read : K → Option E) (readVal : MachineValue) (hread : ∀ a, RunsApp P readVal [encodeValue a] (encodeValue (read a)))
  (R : ℕ) (hR : ∀ a : K, appCost P readVal [encodeValue a] ≤ R)

include hread hR in
/-- **`readCells`** (`readCells.c432`): thirteen reads and offsets (at most `R`, `O` each), the
cells' function rebuilt per cell: at most `13·(O + R) + 9367`. -/
theorem readCells_cost (hP : Includes P readCells.c432.costDeps) (fp : K) (offset : Fin 13 → K)
    (offsetVal : MachineValue) (hoff : ∀ a, RunsApp P offsetVal [encodeValue a] (encodeValue (offset a))) (O : ℕ)
    (hO : ∀ a : Fin 13, appCost P offsetVal [encodeValue a] ≤ O) :
    machineCost P readCells.c432.costIdx [readVal, encodeValue fp, offsetVal] ≤ 13 * (O + R) + 9367 := by
  rw [readCells.c432.costEq P hP read readVal hread fp offset offsetVal hoff]
  have h1 := ofFnFrom_cost P (by includes) (by norm_num) _ (.closure readCells.c432.lam1.costIdx [])
    (fun x ↦ RunsApp.of_spec (readCells.c432.lam1.costSpec P (by includes) x)) 7
    (fun x ↦ by
      simp only [appCost_fn, List.nil_append]
      rw [readCells.c432.lam1.costEq P (by includes)]) 0 (by omega)
  have h2 := finRangeFrom_cost P (by includes) 13 (by norm_num) 0 (by omega)
  -- one cell: the inner function rebuilt
  have hin : ∀ (c : Fin 13) (v : E) (rest : Fin 13 → E),
      appCost P (.closure readCells.c432.lam0.lam0.lam0.costIdx [encodeValue c, encodeValue v]) [encodeValue rest] ≤ 383 := by
    intro c v rest
    simp only [appCost_fn, List.cons_append, List.nil_append]
    rw [readCells.c432.lam0.lam0.lam0.costEq P (by includes), ofFnFrom_length]
    have := ofFnFrom_cost P (by includes) (by norm_num) _
      (.closure readCells.c432.lam0.lam0.lam0.lam0.costIdx [encodeValue c, encodeValue v, encodeValue rest])
      (fun x ↦ RunsApp.of_spec (readCells.c432.lam0.lam0.lam0.lam0.costSpec P (by includes) c v rest x))
      9 (fun x ↦ by
        simp only [appCost_fn, List.cons_append, List.nil_append]
        rw [readCells.c432.lam0.lam0.lam0.lam0.costEq P (by includes),
          limbs_of_lt (by have := x.isLt; omega), limbs_of_lt (by have := c.isLt; omega)]
        split_ifs <;> omega) 0 (by omega)
    omega
  have hmid : ∀ (c : Fin 13) (acc : Option (Fin 13 → E)) (v : E),
      appCost P (.closure readCells.c432.lam0.lam0.costIdx [encodeValue c, encodeValue acc]) [encodeValue v] ≤ 395 := by
    intro c acc v
    simp only [appCost_fn, List.cons_append, List.nil_append]
    rw [readCells.c432.lam0.lam0.costEq P (by includes)]
    have := bind_cost P (by includes) _ (.closure readCells.c432.lam0.lam0.lam0.costIdx [encodeValue c, encodeValue v])
      (fun x ↦ RunsApp.of_spec (readCells.c432.lam0.lam0.lam0.costSpec P (by includes) c v x)) 383
      (hin c v) acc
    omega
  have h3 := foldr_cost P (by includes) _ (.closure readCells.c432.lam0.costIdx [readVal, encodeValue fp, offsetVal])
    (fun x y ↦ RunsApp.of_spec (readCells.c432.lam0.costSpec P (by includes) read readVal hread fp offset
      offsetVal hoff x y)) (O + R + 668) (some fun _ ↦ 0) (List.finRange 13)
    (fun c _ acc ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append]
      rw [readCells.c432.lam0.costEq P (by includes) read readVal hread fp offset offsetVal hoff]
      have := bind_cost P (by includes) _ (.closure readCells.c432.lam0.lam0.costIdx [encodeValue c, encodeValue acc])
        (fun x ↦ RunsApp.of_spec (readCells.c432.lam0.lam0.costSpec P (by includes) c acc x)) 395
        (hmid c acc) (read (fp * offset c))
      have := hO c
      have := hR (fp * offset c)
      omega)
  rw [ofFnFrom_length]
  simp only [List.length_finRange] at h3
  omega

end ReadCells

/-! ## The Keccak relation -/

section KeccakCells
open Auto.LeanVM.Semantics

/-- The lanes of cell `c < 13` (`cellLanes.c424`): at most `37`. -/
theorem cellLanes_cost (hP : Includes P cellLanes.c424.costDeps) (odd : Bool) (c : ℕ) (hc : c < 13) :
    machineCost P cellLanes.c424.costIdx [encodeValue odd, encodeValue c] ≤ 37 := by
  rw [cellLanes.c424.costEq P hP]
  cost_simp
  split_ifs <;> omega

/-- A cell of a state (`cellsOfState.c431`): at most `97`. -/
theorem cellsOfState_cost (hP : Includes P cellsOfState.c431.costDeps) (s : KeccakState) (odd : Bool)
    (c : Fin 13) : machineCost P cellsOfState.c431.costIdx [encodeValue s, encodeValue odd, encodeValue c] ≤ 97 := by
  rw [cellsOfState.c431.costEq P hP]
  have := cellLanes_cost P (by includes) odd c c.isLt
  generalize (cellLanes odd ↑c).1 = o1
  generalize (cellLanes odd ↑c).2 = o2
  cases o1 <;> cases o2 <;> dsimp only <;> omega

/-- The state of thirteen cells (`stateOfCells.c422`), each cell's price at most `B`: at most
`13·(2B + 132) + 243`. -/
theorem stateOfCells_cost (hP : Includes P stateOfCells.c422.costDeps) (cells : Fin 13 → E)
    (cellsVal : MachineValue) (hcells : ∀ a, RunsApp P cellsVal [encodeValue a] (encodeValue (cells a))) (B : ℕ)
    (hB : ∀ a : Fin 13, appCost P cellsVal [encodeValue a] ≤ B) (odd : Bool) :
    machineCost P stateOfCells.c422.costIdx [cellsVal, encodeValue odd] ≤ 13 * (2 * B + 132) + 243 := by
  rw [stateOfCells.c422.costEq P hP cells cellsVal hcells]
  have h1 := finRangeFrom_cost P (by includes) 13 (by norm_num) 0 (by omega)
  have hS : Includes P Auto.Vector.setIfInBounds.c418.costDeps := by includes
  have h2 := listFoldl_le P (by includes) _ (.closure stateOfCells.c422.lam0.costIdx [cellsVal, encodeValue odd])
    (fun x y ↦ RunsApp.of_spec (stateOfCells.c422.lam0.costSpec P (by includes) cells cellsVal hcells
      odd x y)) (2 * B + 123) (fun _ ↦ True) (List.finRange 13) (Vector.replicate 25 0) trivial
    (fun acc _ c _ ↦ ⟨trivial, by
      simp only [appCost_fn, List.cons_append, List.nil_append]
      rw [stateOfCells.c422.lam0.costEq P (by includes) cells cellsVal hcells]
      have := cellLanes_cost P (by includes) odd c c.isLt
      have := hB c
      generalize cellLanes odd ↑c = cl
      obtain ⟨o1, o2⟩ := cl
      cases o1 <;> cases o2 <;> dsimp only <;> (try simp only [setIfInBounds_cost P hS]) <;> omega⟩)
  simp only [List.length_finRange] at h2
  omega

/-- **Keccak-f[1600]** (`keccakF1600`: the fold of `24` rounds over `keccakRC`, through
`lam5.lam0.lam0`): at most `24·13871 + 3 = 332907`. -/
theorem keccakF_cost (hP : Includes P Auto.LeanVM.Cost.Extractor.executeWithShared.c392.lam5.lam0.lam0.costDeps)
    (hF : Includes P listFoldl.costDeps) (a : KeccakState) :
    machineCost P listFoldl.costIdx
      [.closure Auto.LeanVM.Cost.Extractor.executeWithShared.c392.lam5.lam0.lam0.costIdx [], encodeValue a,
        encodeValue keccakRC] ≤ 332907 := by
  have := listFoldl_le P hF _ (.closure Auto.LeanVM.Cost.Extractor.executeWithShared.c392.lam5.lam0.lam0.costIdx [])
    (fun x y ↦ RunsApp.of_spec
      (Auto.LeanVM.Cost.Extractor.executeWithShared.c392.lam5.lam0.lam0.costSpec P hP x y))
    13862 (fun _ ↦ True) keccakRC a trivial
    (fun acc _ rc _ ↦ ⟨trivial, by
      simp only [appCost_fn, List.nil_append]
      rw [Auto.LeanVM.Cost.Extractor.executeWithShared.c392.lam5.lam0.lam0.costEq P hP]
      have := keccakRound_cost P (by includes) acc rc
      omega⟩)
  have hl : keccakRC.length = 24 := rfl
  rw [hl] at this
  omega

end KeccakCells

/-! ## One instruction -/

section Execute
open Auto.LeanVM.Cost.Extractor Auto.LeanVM.Semantics

variable (read : K → Option E) (readVal : MachineValue) (hread : ∀ a, RunsApp P readVal [encodeValue a] (encodeValue (read a)))
  (R : ℕ) (hR : ∀ a : K, appCost P readVal [encodeValue a] ≤ R)

/-- The last step of every instruction, `pure r.next` after a check: `272` at most. -/
theorem guardNext_cost (hP : Includes P executeWithShared.c392.costDeps) (r : Registers K)
    (o : Option Unit) :
    machineCost P Auto.Option.bind.c323.costIdx
      [encodeValue o, .closure executeWithShared.c392.lam0.lam0.lam0.lam0.costIdx [encodeValue r]] ≤
      272 :=
  bind_cost P (by includes) _ _
    (fun u ↦ RunsApp.of_spec (executeWithShared.c392.lam0.lam0.lam0.lam0.costSpec P (by includes) r u))
    267 (fun u ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append]
      rw [executeWithShared.c392.lam0.lam0.lam0.lam0.costEq P (by includes)]) _

include hread hR in
/-- `XOR`: three reads, at most `3R + 1179`. -/
theorem executeXor_cost (hP : Includes P executeWithShared.c392.costDeps) (r : Registers K)
    (oA oB oC : K) :
    machineCost P executeWithShared.c392.costIdx [readVal, encodeValue r, encodeValue (Instr.xor oA oB oC)] ≤
      3 * R + 1179 := by
  rw [executeWithShared.c392.costEq_xor P hP read readVal hread]
  have h3 : ∀ vA vB vC : E, appCost P (.closure executeWithShared.c392.lam0.lam0.lam0.costIdx
      [encodeValue r, encodeValue vA, encodeValue vB]) [encodeValue vC] ≤ 351 := by
    intro vA vB vC
    simp only [appCost_fn, List.cons_append, List.nil_append]
    rw [executeWithShared.c392.lam0.lam0.lam0.costEq P (by includes)]
    cost_facts [guardNext_cost P hP r]
    split_ifs <;> omega
  have h2 : ∀ vA vB : E, appCost P (.closure executeWithShared.c392.lam0.lam0.costIdx
      [encodeValue oC, readVal, encodeValue r, encodeValue vA]) [encodeValue vB] ≤ R + 625 := by
    intro vA vB
    simp only [appCost_fn, List.cons_append, List.nil_append]
    rw [executeWithShared.c392.lam0.lam0.costEq P (by includes) oC read readVal hread]
    have := bind_cost P (by includes) _ _ (fun vC ↦ RunsApp.of_spec
      (executeWithShared.c392.lam0.lam0.lam0.costSpec P (by includes) r vA vB vC)) 351 (h3 vA vB)
      (read (r.fp * oC))
    have := hR (r.fp * oC)
    omega
  have h1 : ∀ vA : E, appCost P (.closure executeWithShared.c392.lam0.costIdx
      [encodeValue oB, encodeValue oC, readVal, encodeValue r]) [encodeValue vA] ≤ 2 * R + 901 := by
    intro vA
    simp only [appCost_fn, List.cons_append, List.nil_append]
    rw [executeWithShared.c392.lam0.costEq P (by includes) oB oC read readVal hread]
    have := bind_cost P (by includes) _ _ (fun vB ↦ RunsApp.of_spec
      (executeWithShared.c392.lam0.lam0.costSpec P (by includes) oC read readVal hread r vA vB))
      (R + 625) (h2 vA) (read (r.fp * oB))
    have := hR (r.fp * oB)
    omega
  have := bind_cost P (by includes) _ _ (fun vA ↦ RunsApp.of_spec
    (executeWithShared.c392.lam0.costSpec P (by includes) oB oC read readVal hread r vA))
    (2 * R + 901) h1 (read (r.fp * oA))
  have := hR (r.fp * oA)
  omega

include hread hR in
/-- `MUL`: three reads and one product in `E`, at most `3R + 8196`. -/
theorem executeMul_cost (hP : Includes P executeWithShared.c392.costDeps) (r : Registers K)
    (oA oB oC : K) :
    machineCost P executeWithShared.c392.costIdx [readVal, encodeValue r, encodeValue (Instr.mulNative oA oB oC)] ≤
      3 * R + 8196 := by
  rw [executeWithShared.c392.costEq_mulNative P hP read readVal hread]
  have h3 : ∀ vA vB vC : E, appCost P (.closure executeWithShared.c392.lam1.lam0.lam0.costIdx
      [encodeValue r, encodeValue vA, encodeValue vB]) [encodeValue vC] ≤ 7368 := by
    intro vA vB vC
    simp only [appCost_fn, List.cons_append, List.nil_append]
    rw [executeWithShared.c392.lam1.lam0.lam0.costEq P (by includes)]
    cost_facts [guardNext_cost P hP r]
    split_ifs <;> omega
  have h2 : ∀ vA vB : E, appCost P (.closure executeWithShared.c392.lam1.lam0.costIdx
      [encodeValue oC, readVal, encodeValue r, encodeValue vA]) [encodeValue vB] ≤ R + 7642 := by
    intro vA vB
    simp only [appCost_fn, List.cons_append, List.nil_append]
    rw [executeWithShared.c392.lam1.lam0.costEq P (by includes) oC read readVal hread]
    have := bind_cost P (by includes) _ _ (fun vC ↦ RunsApp.of_spec
      (executeWithShared.c392.lam1.lam0.lam0.costSpec P (by includes) r vA vB vC)) 7368 (h3 vA vB)
      (read (r.fp * oC))
    have := hR (r.fp * oC)
    omega
  have h1 : ∀ vA : E, appCost P (.closure executeWithShared.c392.lam1.costIdx
      [encodeValue oB, encodeValue oC, readVal, encodeValue r]) [encodeValue vA] ≤ 2 * R + 7918 := by
    intro vA
    simp only [appCost_fn, List.cons_append, List.nil_append]
    rw [executeWithShared.c392.lam1.costEq P (by includes) oB oC read readVal hread]
    have := bind_cost P (by includes) _ _ (fun vB ↦ RunsApp.of_spec
      (executeWithShared.c392.lam1.lam0.costSpec P (by includes) oC read readVal hread r vA vB))
      (R + 7642) (h2 vA) (read (r.fp * oB))
    have := hR (r.fp * oB)
    omega
  have := bind_cost P (by includes) _ _ (fun vA ↦ RunsApp.of_spec
    (executeWithShared.c392.lam1.costSpec P (by includes) oB oC read readVal hread r vA))
    (2 * R + 7918) h1 (read (r.fp * oA))
  have := hR (r.fp * oA)
  omega

include hread hR in
/-- `SET`: one read, at most `R + 571`. -/
theorem executeSet_cost (hP : Includes P executeWithShared.c392.costDeps) (r : Registers K)
    (o : K) (k : E) :
    machineCost P executeWithShared.c392.costIdx [readVal, encodeValue r, encodeValue (Instr.setConstant o k)] ≤
      R + 571 := by
  rw [executeWithShared.c392.costEq_setConstant P hP read readVal hread]
  have h1 : ∀ v : E, appCost P (.closure executeWithShared.c392.lam2.costIdx [encodeValue k, encodeValue r]) [encodeValue v] ≤ 297 := by
    intro v
    simp only [appCost_fn, List.cons_append, List.nil_append]
    rw [executeWithShared.c392.lam2.costEq P (by includes)]
    cost_facts [guardNext_cost P hP r]
    split_ifs <;> omega
  have := bind_cost P (by includes) _ _ (fun v ↦ RunsApp.of_spec
    (executeWithShared.c392.lam2.costSpec P (by includes) k r v)) 297 h1 (read (r.fp * o))
  have := hR (r.fp * o)
  omega

/-- `derefSource` (`derefSource.c405`): at most `1346`. -/
theorem derefSource_cost (hP : Includes P derefSource.c405.costDeps) (mode : DerefMode) (r : Registers K)
    (v : E) : machineCost P derefSource.c405.costIdx [encodeValue mode, encodeValue r, encodeValue v] ≤ 1346 := by
  have := powSq_cost_le P (by includes) g 2 (by omega)
  cases mode
  · rw [derefSource.c405.costEq_cell P hP]; omega
  · rw [derefSource.c405.costEq_pc P hP]; omega
  · rw [derefSource.c405.costEq_fp P hP]; omega

include hread hR in
/-- `DEREF`: three reads, at most `3R + 5717`. -/
theorem executeDeref_cost (hP : Includes P executeWithShared.c392.costDeps) (r : Registers K)
    (o1 o2 o3 : K) (mode : DerefMode) :
    machineCost P executeWithShared.c392.costIdx [readVal, encodeValue r, encodeValue (Instr.deref o1 o2 o3 mode)] ≤
      3 * R + 5717 := by
  rw [executeWithShared.c392.costEq_deref P hP read readVal hread]
  have h4 : ∀ (p v3 v2 : E), appCost P (.closure executeWithShared.c392.lam3.lam0.lam0.lam0.costIdx
      [encodeValue mode, encodeValue r, encodeValue v3]) [encodeValue v2] ≤ 4361 := by
    intro p v3 v2
    simp only [appCost_fn, List.cons_append, List.nil_append]
    rw [executeWithShared.c392.lam3.lam0.lam0.lam0.costEq P (by includes)]
    cost_facts [guardNext_cost P hP r]
    have := derefSource_cost P (by includes) mode r v3
    split_ifs <;> omega
  have h3 : ∀ (p v3 : E), appCost P (.closure executeWithShared.c392.lam3.lam0.lam0.costIdx
      [encodeValue o2, encodeValue mode, readVal, encodeValue r, encodeValue p]) [encodeValue v3] ≤ R + 4635 := by
    intro p v3
    simp only [appCost_fn, List.cons_append, List.nil_append]
    rw [executeWithShared.c392.lam3.lam0.lam0.costEq P (by includes) o2 mode read readVal hread]
    have := bind_cost P (by includes) _ _ (fun v2 ↦ RunsApp.of_spec
      (executeWithShared.c392.lam3.lam0.lam0.lam0.costSpec P (by includes) mode r v3 v2)) 4361
      (h4 p v3) (read (p.limb 0 * o2))
    have := hR (p.limb 0 * o2)
    omega
  have h2 : ∀ (p : E) (u : Unit), appCost P (.closure executeWithShared.c392.lam3.lam0.costIdx
      [encodeValue o2, encodeValue o3, encodeValue mode, readVal, encodeValue r, encodeValue p]) [encodeValue u] ≤ 2 * R + 4913 := by
    intro p u
    simp only [appCost_fn, List.cons_append, List.nil_append]
    rw [executeWithShared.c392.lam3.lam0.costEq P (by includes) o2 o3 mode read readVal hread]
    have := bind_cost P (by includes) _ _ (fun v3 ↦ RunsApp.of_spec
      (executeWithShared.c392.lam3.lam0.lam0.costSpec P (by includes) o2 mode read readVal hread r p
        v3)) (R + 4635) (h3 p) (read (r.fp * o3))
    have := hR (r.fp * o3)
    omega
  have h1 : ∀ p : E, appCost P (.closure executeWithShared.c392.lam3.costIdx
      [encodeValue o2, encodeValue o3, encodeValue mode, readVal, encodeValue r]) [encodeValue p] ≤ 2 * R + 4945 := by
    intro p
    simp only [appCost_fn, List.cons_append, List.nil_append]
    rw [executeWithShared.c392.lam3.costEq P (by includes) o2 o3 mode read readVal hread]
    have := bind_cost P (by includes) _ _ (fun u ↦ RunsApp.of_spec
      (executeWithShared.c392.lam3.lam0.costSpec P (by includes) o2 o3 mode read readVal hread r p
        u)) (2 * R + 4913) (h2 p) (guard (IsInK p))
    split_ifs <;> omega
  have := bind_cost P (by includes) _ _ (fun p ↦ RunsApp.of_spec
    (executeWithShared.c392.lam3.costSpec P (by includes) o2 o3 mode read readVal hread r p))
    (2 * R + 4945) h1 (read (r.fp * o1))
  have := hR (r.fp * o1)
  omega

include hread hR in
/-- `JUMP`: three reads, at most `3R + 1181`. -/
theorem executeJump_cost (hP : Includes P executeWithShared.c392.costDeps) (r : Registers K)
    (oc od of : K) :
    machineCost P executeWithShared.c392.costIdx [readVal, encodeValue r, encodeValue (Instr.jump oc od of)] ≤
      3 * R + 1181 := by
  rw [executeWithShared.c392.costEq_jump P hP read readVal hread]
  have h4 : ∀ (c d f : E) (u : Unit), appCost P (.closure executeWithShared.c392.lam4.lam0.lam0.lam0.costIdx
      [encodeValue r, encodeValue c, encodeValue d, encodeValue f]) [encodeValue u] ≤ 303 := by
    intro c d f u
    simp only [appCost_fn, List.cons_append, List.nil_append]
    rw [executeWithShared.c392.lam4.lam0.lam0.lam0.costEq P (by includes)]
    split_ifs <;> omega
  have h3 : ∀ (c d f : E), appCost P (.closure executeWithShared.c392.lam4.lam0.lam0.costIdx
      [encodeValue r, encodeValue c, encodeValue d]) [encodeValue f] ≤ 353 := by
    intro c d f
    simp only [appCost_fn, List.cons_append, List.nil_append]
    rw [executeWithShared.c392.lam4.lam0.lam0.costEq P (by includes)]
    have := bind_cost P (by includes) _ _ (fun u ↦ RunsApp.of_spec
      (executeWithShared.c392.lam4.lam0.lam0.lam0.costSpec P (by includes) r c d f u)) 303
      (h4 c d f) (guard (IsInK c ∧ IsInK d ∧ IsInK f))
    split_ifs <;> omega
  have h2 : ∀ (c d : E), appCost P (.closure executeWithShared.c392.lam4.lam0.costIdx
      [encodeValue of, readVal, encodeValue r, encodeValue c]) [encodeValue d] ≤ R + 627 := by
    intro c d
    simp only [appCost_fn, List.cons_append, List.nil_append]
    rw [executeWithShared.c392.lam4.lam0.costEq P (by includes) of read readVal hread]
    have := bind_cost P (by includes) _ _ (fun f ↦ RunsApp.of_spec
      (executeWithShared.c392.lam4.lam0.lam0.costSpec P (by includes) r c d f)) 353 (h3 c d)
      (read (r.fp * of))
    have := hR (r.fp * of)
    omega
  have h1 : ∀ c : E, appCost P (.closure executeWithShared.c392.lam4.costIdx
      [encodeValue od, encodeValue of, readVal, encodeValue r]) [encodeValue c] ≤ 2 * R + 903 := by
    intro c
    simp only [appCost_fn, List.cons_append, List.nil_append]
    rw [executeWithShared.c392.lam4.costEq P (by includes) od of read readVal hread]
    have := bind_cost P (by includes) _ _ (fun d ↦ RunsApp.of_spec
      (executeWithShared.c392.lam4.lam0.costSpec P (by includes) of read readVal hread r c d))
      (R + 627) (h2 c) (read (r.fp * od))
    have := hR (r.fp * od)
    omega
  have := bind_cost P (by includes) _ _ (fun c ↦ RunsApp.of_spec
    (executeWithShared.c392.lam4.costSpec P (by includes) od of read readVal hread r c))
    (2 * R + 903) h1 (read (r.fp * oc))
  have := hR (r.fp * oc)
  omega

/-- The Keccak check after the reads (`lam5.lam0`): the state of the input cells, Keccak-f once,
the two `∀ c` over the thirteen cells: at most `340560`. -/
theorem keccakCheck_cost (hP : Includes P executeWithShared.c392.costDeps) (inOdd outOdd : Bool)
    (r : Registers K) (input output : Fin 13 → E) :
    machineCost P executeWithShared.c392.lam5.lam0.costIdx
      [encodeValue inOdd, encodeValue outOdd, encodeValue r, encodeValue input, encodeValue output] ≤ 340560 := by
  rw [executeWithShared.c392.lam5.lam0.costEq P (by includes)]
  have hst := stateOfCells_cost P (by includes) input
    (.closure executeWithShared.c392.lam5.lam0.lam1.costIdx [encodeValue input])
    (fun a ↦ RunsApp.of_spec (executeWithShared.c392.lam5.lam0.lam1.costSpec P (by includes) input a)) 4
    (fun a ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append]
      rw [executeWithShared.c392.lam5.lam0.lam1.costEq P (by includes)]) inOdd
  have hrc := Auto.LeanVM.Parameters.keccakRC.c427.costEq P (by includes)
  have hkf := keccakF_cost P (by includes) (by includes) (stateOfCells input inOdd)
  have hid := ofFnFrom_cost P (by includes) (by norm_num) _
    (.closure executeWithShared.c392.lam5.lam0.lam3.costIdx [])
    (fun a ↦ RunsApp.of_spec (executeWithShared.c392.lam5.lam0.lam3.costSpec P (by includes) a)) 1
    (fun a ↦ by
      simp only [appCost_fn, List.nil_append]
      rw [executeWithShared.c392.lam5.lam0.lam3.costEq P (by includes)]) 0 (by omega)
  have hlen : (Array.ofFn (id : Fin 13 → Fin 13)).toList.length = 13 := by simp
  have ha1 := listAll_cost P (by includes) _
    (.closure executeWithShared.c392.lam5.lam0.lam2.costIdx [encodeValue input])
    (fun a ↦ RunsApp.of_spec (executeWithShared.c392.lam5.lam0.lam2.costSpec P (by includes) input a)) 7
    (fun a ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append]
      rw [executeWithShared.c392.lam5.lam0.lam2.costEq P (by includes)])
    (Array.ofFn (id : Fin 13 → Fin 13)).toList
  have ha2 := listAll_cost P (by includes) _
    (.closure executeWithShared.c392.lam5.lam0.lam4.costIdx
      [encodeValue outOdd, encodeValue output, encodeValue (keccakF1600 (stateOfCells input inOdd))])
    (fun a ↦ RunsApp.of_spec (executeWithShared.c392.lam5.lam0.lam4.costSpec P (by includes) outOdd
      output _ a)) 326
    (fun a ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append]
      rw [executeWithShared.c392.lam5.lam0.lam4.costEq P (by includes)]
      have := cellsOfState_cost P (by includes) (keccakF1600 (stateOfCells input inOdd)) outOdd a
      split_ifs <;> omega)
    (Array.ofFn (id : Fin 13 → Fin 13)).toList
  rw [hlen] at ha1 ha2
  rw [ofFnFrom_length, Array.size_ofFn]
  cost_facts [guardNext_cost P hP r]
  simp only [Nat.sub_zero] at hid
  split_ifs <;> omega

include hread hR in
/-- After the input cells (`lam5`): the thirteen output cells read at offsets `g^c·o` (at most
`2407` each), then the check: at most `13R + 381240`. -/
theorem keccakOutput_cost (hP : Includes P executeWithShared.c392.costDeps) (oout : K)
    (inOdd outOdd : Bool) (r : Registers K) (input : Fin 13 → E) :
    machineCost P executeWithShared.c392.lam5.costIdx
      [encodeValue oout, encodeValue inOdd, encodeValue outOdd, readVal, encodeValue r, encodeValue input] ≤ 13 * R + 381240 := by
  rw [executeWithShared.c392.lam5.costEq P (by includes) oout inOdd outOdd read readVal hread]
  have h1 := readCells_cost P read readVal hread R hR (by includes) r.fp _
    (.closure executeWithShared.c392.lam5.lam1.costIdx [encodeValue oout])
    (fun c ↦ RunsApp.of_spec (executeWithShared.c392.lam5.lam1.costSpec P (by includes) oout c)) 2407
    (fun c ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append]
      rw [executeWithShared.c392.lam5.lam1.costEq P (by includes)]
      have := powSq_cost_le' P (by includes) LeanVM.Parameters.g c (by have := c.isLt; omega)
      omega)
  have h2 := bind_cost P (by includes) _
    (.closure executeWithShared.c392.lam5.lam0.costIdx [encodeValue inOdd, encodeValue outOdd, encodeValue r, encodeValue input])
    (fun output ↦ RunsApp.of_spec
    (executeWithShared.c392.lam5.lam0.costSpec P (by includes) inOdd outOdd r input output)) 340560
    (fun output ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append]
      exact keccakCheck_cost P hP inOdd outOdd r input output)
    (readCells read r.fp fun c ↦ LeanVM.Parameters.g ^ c.val * oout)
  omega

/-- The input cells' offsets (`keccakInOffset.c440` through `lam6`): at most `1363`. -/
theorem keccakInOffset_cost (hP : Includes P executeWithShared.c392.costDeps) (om : Fin 4 → K)
    (otail ob8 ocap : K) (c : Fin 13) :
    machineCost P executeWithShared.c392.lam6.costIdx [encodeValue om, encodeValue otail, encodeValue ob8, encodeValue ocap, encodeValue c] ≤
      1363 := by
  rw [executeWithShared.c392.lam6.costEq P (by includes),
    keccakInOffset.c440.costEq P (by includes) om _
      (fun a ↦ RunsApp.of_spec (executeWithShared.c392.lam6.lam0.costSpec P (by includes) om a))]
  have hc := c.isLt
  simp only [appCost_fn, List.cons_append, List.nil_append,
    executeWithShared.c392.lam6.lam0.costEq P (by includes)]
  rw [limbs_of_lt (by omega : (c : ℕ) < 2 ^ 64)]
  have := powSq_cost_le P (by includes) LeanVM.Parameters.g (c - 4)
  have := powSq_cost_le P (by includes) LeanVM.Parameters.g (c - 9)
  split_ifs <;> omega

include hread hR in
/-- `KECCAK`: twenty-six reads, Keccak-f once: at most `26R + 408358`. -/
theorem executeKeccak_cost (hP : Includes P executeWithShared.c392.costDeps) (r : Registers K)
    (om : Fin 4 → K) (otail ob8 ocap oout : K) (inOdd outOdd : Bool) :
    machineCost P executeWithShared.c392.costIdx
      [readVal, encodeValue r, encodeValue (Instr.keccak om otail ob8 ocap oout inOdd outOdd)] ≤ 26 * R + 408358 := by
  rw [executeWithShared.c392.costEq_keccak P hP read readVal hread]
  have h1 := readCells_cost P read readVal hread R hR (by includes) r.fp _
    (.closure executeWithShared.c392.lam6.costIdx [encodeValue om, encodeValue otail, encodeValue ob8, encodeValue ocap])
    (fun c ↦ RunsApp.of_spec (executeWithShared.c392.lam6.costSpec P (by includes) om otail ob8 ocap c))
    1363 (fun c ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append]
      exact keccakInOffset_cost P hP om otail ob8 ocap c)
  have h2 := bind_cost P (by includes) _
    (.closure executeWithShared.c392.lam5.costIdx [encodeValue oout, encodeValue inOdd, encodeValue outOdd, readVal, encodeValue r])
    (fun input ↦ RunsApp.of_spec
    (executeWithShared.c392.lam5.costSpec P (by includes) oout inOdd outOdd read readVal hread r input))
    (13 * R + 381240)
    (fun input ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append]
      exact keccakOutput_cost P read readVal hread R hR hP oout inOdd outOdd r input)
    (readCells read r.fp (keccakInOffset om otail ob8 ocap))
  omega

include hread hR in
/-- **One instruction** (`executeWithShared.c392`, `executeWith` as compiled), each read at most
`R`: at most `26R + 408358` (`KECCAK` the worst). -/
theorem executeWith_cost (hP : Includes P executeWithShared.c392.costDeps) (r : Registers K)
    (i : Instr) :
    machineCost P executeWithShared.c392.costIdx [readVal, encodeValue r, encodeValue i] ≤ 26 * R + 408358 := by
  cases i with
  | xor oA oB oC => have := executeXor_cost P read readVal hread R hR hP r oA oB oC; omega
  | mulNative oA oB oC => have := executeMul_cost P read readVal hread R hR hP r oA oB oC; omega
  | setConstant o k => have := executeSet_cost P read readVal hread R hR hP r o k; omega
  | deref o1 o2 o3 mode => have := executeDeref_cost P read readVal hread R hR hP r o1 o2 o3 mode; omega
  | jump oc od of => have := executeJump_cost P read readVal hread R hR hP r oc od of; omega
  | keccak om otail ob8 ocap oout inOdd outOdd =>
    exact executeKeccak_cost P read readVal hread R hR hP r om otail ob8 ocap oout inOdd outOdd

end Execute

/-! ## One step -/

section Step
open Auto.LeanVM.Extraction.Fast

/-- **An address lookup** (`gLogTable.c445`): a binary search over the table, at most
`94 + 42·log₂|t|`. -/
theorem gLogTable_cost (hP : Includes P gLogTable.c445.costDeps) (t : Array (ℕ × ℕ)) (ht : WordTable t)
    (κ : ℕ) (hκ : κ < 64) (a : K) :
    machineCost P gLogTable.c445.costIdx [encodeValue t, encodeValue κ, encodeValue a] ≤ 94 + 42 * Nat.log2 t.size := by
  rw [gLogTable.c445.costEq P hP]
  have hkey : a.lane.toNat < 2 ^ 64 := UInt64.toNat_lt _
  have := findLane_cost P (by includes) t ht _ hkey 0 t.size (by omega) le_rfl
  rw [Nat.sub_zero] at this
  rw [limbs_shift hκ, limbs_of_lt (by omega : κ < 2 ^ 64), limbs_two_pow hκ]
  generalize hf : findLane t a.lane.toNat 0 t.size = o
  cases o with
  | none => dsimp only; omega
  | some v =>
    have hv := (ht.2 _ (findLane_sound t _ _ 0 t.size rfl le_rfl hf)).2
    dsimp only
    rw [limbs_of_lt hv]
    split_ifs <;> simp only [max_self] <;> omega

/-- **A memory read** (the closure `stepVec.c390.lam0.lam0`): at most `123 + 42·log₂|memT|`. -/
theorem memRead_cost (hP : Includes P stepVec.c390.lam0.lam0.costDeps) (memT : Array (ℕ × ℕ))
    (ht : WordTable memT) {κ : ℕ} (hκ : κ < 64) (mem : Vector E (2 ^ κ)) (a : K) :
    machineCost P stepVec.c390.lam0.lam0.costIdx [encodeValue memT, encodeValue κ, encodeValue mem, encodeValue a] ≤
      123 + 42 * Nat.log2 memT.size := by
  rw [stepVec.c390.lam0.lam0.costEq P hP]
  have := gLogTable_cost P (by includes) memT ht κ hκ a
  have := optionMap_cost P (by includes) _ (.closure stepVec.c390.lam0.lam0.lam0.costIdx [encodeValue κ, encodeValue mem])
    (fun i ↦ RunsApp.of_spec (stepVec.c390.lam0.lam0.lam0.costSpec P (by includes) mem i)) 12
    (fun i ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append]
      rw [stepVec.c390.lam0.lam0.lam0.costEq P (by includes), limbs_shift hκ,
        limbs_of_lt (by omega : κ < 2 ^ 64), Auto.Vector.get.c444.costEq P (by includes)])
    (gLogTable memT κ a)
  omega

/-- **One step** (`stepVec.c390`): the code table's lookup, the instruction, its reads (each a
lookup in the memory table): at most `411697 + 42·log₂|codeT| + 1092·log₂|memT|`. -/
theorem stepVec_cost (hP : Includes P stepVec.c390.costDeps) (memT codeT : Array (ℕ × ℕ))
    (hm : WordTable memT) (hc : WordTable codeT) (prog : Semantics.Program) {κ : ℕ} (hκ : κ < 64)
    (mem : Vector E (2 ^ κ)) (r : Registers K) :
    machineCost P stepVec.c390.costIdx [encodeValue memT, encodeValue codeT, encodeValue prog, encodeValue κ, encodeValue mem, encodeValue r] ≤
      411697 + 42 * Nat.log2 codeT.size + 1092 * Nat.log2 memT.size := by
  rw [stepVec.c390.costEq P hP]
  have hls : prog.logSize < 64 := by have := prog.logSize_le; unfold maxLogBytecode at this; omega
  have h1 := gLogTable_cost P (by includes) codeT hc prog.logSize hls r.pc
  have h2 := optionMap_cost P (by includes) _ (.closure stepVec.c390.lam1.costIdx [encodeValue prog])
    (fun i ↦ RunsApp.of_spec (stepVec.c390.lam1.costSpec P (by includes) prog i)) 5
    (fun i ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append]
      rw [stepVec.c390.lam1.costEq P (by includes)])
    (gLogTable codeT prog.logSize r.pc)
  have h3 := bind_cost P (by includes) _ (.closure stepVec.c390.lam0.costIdx [encodeValue memT, encodeValue κ, encodeValue mem, encodeValue r])
    (fun i ↦ RunsApp.of_spec (stepVec.c390.lam0.costSpec P (by includes) memT mem r i))
    (26 * (123 + 42 * Nat.log2 memT.size) + 408368)
    (fun i ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append]
      rw [stepVec.c390.lam0.costEq P (by includes)]
      have := executeWith_cost P _ (.closure stepVec.c390.lam0.lam0.costIdx [encodeValue memT, encodeValue κ, encodeValue mem])
        (fun a ↦ RunsApp.of_spec (stepVec.c390.lam0.lam0.costSpec P (by includes) memT mem a))
        (123 + 42 * Nat.log2 memT.size)
        (fun a ↦ by
          simp only [appCost_fn, List.cons_append, List.nil_append]
          exact memRead_cost P (by includes) memT hm hκ mem a) (by includes) r i
      omega)
    (Option.map prog.code (gLogTable codeT prog.logSize r.pc))
  omega

end Step

end

end LeanVM.Cost.Bounds
