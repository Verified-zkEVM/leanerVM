module

public import LeanVM.Cost.Bounds.Decoder.Lane
public import LeanVM.Cost.Bounds.Sizes.Pruning
public import LeanVM.Cost.Extractor.Decode

/-!
# Bound: the lanes pruned against the word, compiled

The price of `pruneUpToDistinct κ R A W U` (`Fast/DecodeAdmissible.lean`, compiled in
`Cost/Extractor/Decode.lean`): the word's table (`laneTable`, each column reversed once), then for
each of the `U` lanes its candidates (`laneEncodedDistinctC`, a price `G` per lane, bounded in
`Bounds/Decoder/Lane.lean` up to its Guruswami–Sudan run) and the pruning step
(`pruneStep_cost` of `Bounds/FastPath.lean`, at most `Smax` survivors):
`pruneUpToDistinctC_cost ≤ pruneBound …`. The survivors are at most `2^18` at the admissible
shapes (`pruneUpToDistinct_length_le_johnson`).
-/

namespace LeanVM.Cost.Bounds.Decoder

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.Library
open LeanVM.Cost.Extractor LeanVM.Parameters CompPoly LeanVM.Extraction LeanVM.Extraction.Fast

public section

variable (P : MachineProgram)

/-- **`List.foldl` over `List.range' s n`, the closure's price bounded on the states the fold
reaches**: `9` per element and the closure's price, `3`. -/
theorem listFoldl_range'_le (hP : Includes P listFoldl.costDeps) {α : Type} [MachineEncoding α]
    (f : α → ℕ → α) (fVal : MachineValue) (hf : ∀ a b, RunsApp P fVal [encodeValue a, encodeValue b] (encodeValue (f a b)))
    (B : ℕ) :
    ∀ (n s : ℕ) (st : α),
      (∀ j, s ≤ j → j < s + n →
        appCost P fVal [encodeValue ((List.range' s (j - s)).foldl f st), encodeValue j] ≤ B) →
      machineCost P listFoldl.costIdx [fVal, encodeValue st, encodeValue (List.range' s n)] ≤ (B + 9) * n + 3 := by
  intro n
  induction n with
  | zero => intro s st _; rw [List.range'_zero, listFoldl.costEq_nil P hP f fVal hf]; omega
  | succ n ih =>
    intro s st hB
    rw [List.range'_succ, listFoldl.costEq_cons P hP f fVal hf]
    have h1 := hB s le_rfl (by omega)
    simp only [Nat.sub_self, List.range'_zero, List.foldl_nil] at h1
    have h2 := ih (s + 1) (f st s) (fun j hj1 hj2 ↦ by
      have := hB j (by omega) (by omega)
      have e : j - s = (j - (s + 1)) + 1 := by omega
      rw [e, List.range'_succ, List.foldl_cons] at this
      exact this)
    have e : (B + 9) * (n + 1) = (B + 9) * n + B + 9 := by ring
    omega

theorem laneTable_getD (n : ℕ) (W : ℕ → List K) (u v : ℕ) (hv : v < n) :
    tableSymbol (laneTable n W) u v = laneSymbol W u v := by
  simp [tableSymbol, laneTable, laneSymbol, Array.getD_eq_getD_getElem?, hv]

/-- **The lanes pruned** (`pruneUpToDistinct κ R A W U`): at most `pruneBound …`, the lanes'
candidates of price at most `G` and at most `Lc` each, the survivors at most `Smax` after every
lane. -/
theorem pruneUpToDistinctC_cost (hP : Includes P pruneUpToDistinctC.costDeps) (κ R A U : ℕ)
    (hκR : κ + R ≤ 60) (hU : U < 2 ^ 62) (hA : A < 2 ^ 128) (W : ℕ → List K) (WVal : MachineValue)
    (hW : ∀ a, RunsApp P WVal [encodeValue a] (encodeValue (W a))) {BW Lw G Lc Smax : ℕ}
    (hBW : ∀ v : ℕ, v < 2 ^ 64 → appCost P WVal [encodeValue v] ≤ BW) (hLw : ∀ v, (W v).length ≤ Lw)
    (hG : ∀ u < U, machineCost P laneEncodedDistinctC.costIdx
      [encodeValue κ, encodeValue R, encodeValue A, .closure pruneUpToDistinctC.lam1.lam0.costIdx
        [encodeValue (laneTable (2 ^ (κ + R)) W)], encodeValue u] ≤ G)
    (hLc : ∀ u, (laneEncodedDistinct κ R A (tableSymbol (laneTable (2 ^ (κ + R)) W)) u).length ≤ Lc)
    (hS : ∀ u < U, (pruneUpToDistinct κ R A W u).length ≤ Smax) :
    machineCost P pruneUpToDistinctC.costIdx [encodeValue κ, encodeValue R, encodeValue A, WVal, encodeValue U] ≤
      pruneBound κ R U BW Lw G Lc Smax := by
  rw [pruneUpToDistinctC.costEq P hP κ R A W WVal hW U]
  have hN : 2 ^ (κ + R) < 2 ^ 62 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hs : (1 <<< (κ + R) : ℕ) = 2 ^ (κ + R) := Nat.one_shiftLeft _
  rw [hs]
  -- the table
  have hf0 := fun v ↦ RunsApp.of_spec (us := [encodeValue κ, encodeValue R, WVal]) (vs := [encodeValue v])
    (pruneUpToDistinctC.lam0.costSpec P (by includes) κ R W WVal hW v)
  have hof := ofFnFrom_cost P (by includes) (n := 2 ^ (κ + R)) (by omega) _
    (.closure pruneUpToDistinctC.lam0.costIdx [encodeValue κ, encodeValue R, WVal]) hf0 (BW + 10 * Lw + 9)
    (fun v ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append]
      rw [pruneUpToDistinctC.lam0.costEq P (by includes) κ R W WVal hW]
      have := hBW v (by have := v.isLt; omega)
      have := reverseAux_cost P (by includes) (W v) []
      have := hLw v
      simp only [List.length_reverse]
      omega) 0 (Nat.zero_le _)
  have := rangeLoop_cost P (by includes) (2 ^ (κ + R)) [] (by omega)
  have := rangeLoop_cost P (by includes) U [] (by omega)
  -- the lanes
  have hf1 := fun st u ↦ RunsApp.of_spec
    (us := [encodeValue κ, encodeValue R, encodeValue A, encodeValue (laneTable (2 ^ (κ + R)) W)]) (vs := [encodeValue st, encodeValue u])
    (pruneUpToDistinctC.lam1.costSpec P (by includes) κ R A (laneTable (2 ^ (κ + R)) W) st u)
  have hfold := listFoldl_range'_le P (by includes) _
    (.closure pruneUpToDistinctC.lam1.costIdx [encodeValue κ, encodeValue R, encodeValue A, encodeValue (laneTable (2 ^ (κ + R)) W)])
    hf1 (G + Smax * (Lc * (41 * 2 ^ (κ + R) + 9 * U + 62) + 32) + 50) U 0
    [([], List.range (2 ^ (κ + R)))]
    (fun j _ hj ↦ by
      simp only [Nat.sub_zero, appCost_fn, List.cons_append, List.nil_append]
      have hst : (List.range' 0 j).foldl
          (fun st u ↦ if st.isEmpty = true then [] else pruneStep A
            (tableSymbol (laneTable (2 ^ (κ + R)) W) u)
            (laneEncodedDistinct κ R A (tableSymbol (laneTable (2 ^ (κ + R)) W)) u) st)
          [([], List.range (2 ^ (κ + R)))] = pruneUpToDistinct κ R A W j := by
        simp only [pruneUpToDistinct, List.range_eq_range']
      rw [hst]
      have hsm := (pruneUpToDistinct_bounds W hLc j).2
      generalize hS' : pruneUpToDistinct κ R A W j = st at hsm
      have hSl : st.length ≤ Smax := hS' ▸ hS j (by omega)
      cases st with
      | nil =>
        rw [pruneUpToDistinctC.lam1.costEq_nil P (by includes)]
        simp
      | cons s0 st =>
        rw [pruneUpToDistinctC.lam1.costEq_cons P (by includes)]
        simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
        have := hG j (by omega)
        have hsym := fun v ↦ RunsApp.of_spec
          (us := [encodeValue (laneTable (2 ^ (κ + R)) W), encodeValue j]) (vs := [encodeValue v])
          (pruneUpToDistinctC.lam1.lam0.costSpec P (by includes) (laneTable (2 ^ (κ + R)) W) j v)
        have hp := pruneStep_cost P (by includes) A hA _
          (.closure pruneUpToDistinctC.lam1.lam0.costIdx [encodeValue (laneTable (2 ^ (κ + R)) W), encodeValue j]) hsym
          12 (fun v ↦ by
            simp only [appCost_fn, List.cons_append, List.nil_append]
            rw [pruneUpToDistinctC.lam1.lam0.costEq P (by includes),
              Auto.LeanVM.Extraction.Fast.tableSymbol.c269.costEq P (by includes)])
          (laneEncodedDistinct κ R A (tableSymbol (laneTable (2 ^ (κ + R)) W)) j) (s0 :: st)
          (2 ^ (κ + R)) U (by omega) (fun s hs ↦ by
            obtain ⟨h1, -, h3⟩ := hsm s hs
            exact ⟨by have := h3.length_le; simpa using this, by omega⟩)
        have hl := hLc j
        simp only [Nat.reduceAdd] at hp
        have h1 : (s0 :: st).length *
            ((laneEncodedDistinct κ R A (tableSymbol (laneTable (2 ^ (κ + R)) W)) j).length *
              (41 * 2 ^ (κ + R) + 9 * U + 62) + 32) ≤
            Smax * (Lc * (41 * 2 ^ (κ + R) + 9 * U + 62) + 32) :=
          Nat.mul_le_mul hSl (by have := Nat.mul_le_mul_right (41 * 2 ^ (κ + R) + 9 * U + 62) hl; omega)
        omega)
  simp only [List.range_eq_range'] at hfold ⊢
  simp only [length_ofFnFrom, Nat.sub_zero] at *
  unfold pruneBound
  have e : (BW + 10 * Lw + 28) * 2 ^ (κ + R) = (BW + 10 * Lw + 9 + 18) * 2 ^ (κ + R) + 2 ^ (κ + R) := by
    ring
  have e2 : (G + Smax * (Lc * (41 * 2 ^ (κ + R) + 9 * U + 62) + 32) + 60) * U =
      (G + Smax * (Lc * (41 * 2 ^ (κ + R) + 9 * U + 62) + 32) + 50 + 9) * U + U := by ring
  cost_simp
  omega

end

end LeanVM.Cost.Bounds.Decoder
