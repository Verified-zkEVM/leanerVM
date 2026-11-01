module

public import LeanVM.Cost.Bounds.Decoder.GsRun
public import LeanVM.Cost.Bounds.FastPath
public import LeanVM.Cost.Bounds.Sizes.Lane
public import LeanVM.Cost.Extractor.Lane
import all LeanVM.Cost.InitLib

/-!
# Bound: one lane's candidates, compiled

The price of `laneEncodedDistinct κ R A S u` (`Fast/DecodeAdmissible.lean`, compiled in
`Cost/Extractor/Lane.lean`) beyond its Guruswami–Sudan run (`gsLaneDistinct`, bounded in
`Bounds/Decoder/Decode.lean`, `gsLaneDistinctC_cost`):

* the candidates in the novel basis (`toNovelFastC_cost`: `2^κ` Horner evaluations, then the
  inverse transform `novelInv_cost` of `Bounds/FastPath.lean`);
* their deduplication (`dedupC_cost`: each candidate compared with the kept ones, `O(n²·2^κ)`)
  and sort (`mergeSortList_cost_sq`, `coeffsLEC_cost`: at most `C·n² + 10`, a quadratic bound,
  enough at `n ≤ ℓ`);
* each candidate re-encoded (`novelFwd_cost` of `Bounds/FastPath.lean`);
* `laneEncodedDistinctC_cost`: the run's price plus `laneExtraBound κ R ℓ k`.
-/

namespace LeanVM.Cost.Bounds.Decoder

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.Library
open LeanVM.Cost.Extractor LeanVM.Parameters CompPoly LeanVM.Extraction.Fast

public section

variable (P : MachineProgram)

/-! ## Deduplication -/

/-- Array equality over `K` (`List.beq.c242` on the coefficient lists): at most `11·|a| + 6`. -/
theorem beqArrC_cost (hP : Includes P Auto.List.beq.c242.costDeps) :
    ∀ a b : List K, machineCost P Auto.List.beq.c242.costIdx [encodeValue a, encodeValue b] ≤ 11 * a.length + 6 := by
  intro a
  induction a with
  | nil => intro b; rw [Auto.List.beq.c242.costEq_nil P hP]; cases b <;> simp
  | cons x a ih =>
    intro b
    rw [Auto.List.beq.c242.costEq_cons P hP]
    cases b with
    | nil => simp
    | cons y b =>
      have := ih b
      simp only [List.length_cons]
      split_ifs <;> omega

theorem foldr_pw_length_le (l : List (Array K)) :
    (l.foldr (fun x IH ↦ if ∀ y ∈ IH, x ≠ y then x :: IH else IH) []).length ≤ l.length := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.foldr_cons]
    split_ifs <;> simp only [List.length_cons] <;> omega

/-- **The deduplication** (`List.dedup` of `n` arrays of `N` entries: each compared with the kept
ones): at most `((17·N + 22)·n + 30)·n + 9`. -/
theorem dedupC_cost (hP : Includes P Auto.List.dedup.c237.costDeps) (N : ℕ) :
    ∀ l : List (Array K), (∀ a ∈ l, a.size = N) →
      machineCost P Auto.List.dedup.c237.costIdx [encodeValue l] ≤ ((17 * N + 22) * l.length + 30) * l.length + 9 := by
  intro l hl
  rw [Auto.List.dedup.c237.costEq P hP, Auto.List.pwFilter.c238.costEq P (by includes)]
  have hf := fun x IH ↦ RunsApp.of_spec (us := []) (vs := [encodeValue x, encodeValue IH])
    (Auto.List.pwFilter.c238.lam0.costSpec P (by includes) x IH)
  suffices h : ∀ l' : List (Array K), (∀ a ∈ l', a.size = N) → l'.length ≤ l.length →
      machineCost P Auto.List.foldr.c86.costIdx [.closure Auto.List.pwFilter.c238.lam0.costIdx [],
        encodeValue ([] : List (Array K)), encodeValue l'] ≤ ((17 * N + 22) * l.length + 30) * l'.length + 3 by
    have := h l hl le_rfl
    omega
  intro l'
  induction l' with
  | nil =>
    intro _ _
    rw [Auto.List.foldr.c86.costEq_nil P (by includes) _ (.closure Auto.List.pwFilter.c238.lam0.costIdx []) hf]
    simp
  | cons x l' ih =>
    intro hl' hlen
    rw [Auto.List.foldr.c86.costEq_cons P (by includes) _
      (.closure Auto.List.pwFilter.c238.lam0.costIdx []) hf]
    simp only [List.length_cons] at hlen ⊢
    have := ih (fun a ha ↦ hl' a (by simp [ha])) (by omega)
    have hIH := foldr_pw_length_le l'
    simp only [appCost_fn, List.nil_append]
    rw [Auto.List.pwFilter.c238.lam0.costEq P (by includes)]
    have hq := fun y ↦ RunsApp.of_spec (us := [encodeValue x]) (vs := [encodeValue y])
      (Auto.List.pwFilter.c238.lam0.lam0.costSpec P (by includes) x y)
    have hall := all_cost P (by includes) _ (.closure Auto.List.pwFilter.c238.lam0.lam0.costIdx [encodeValue x])
      hq (17 * N + 13) (l'.foldr (fun x IH ↦ if ∀ y ∈ IH, x ≠ y then x :: IH else IH) [])
      (fun y hy ↦ by
        simp only [appCost_fn, List.cons_append, List.nil_append]
        rw [Auto.List.pwFilter.c238.lam0.lam0.costEq P (by includes)]
        have := beqArrC_cost P (by includes) x.toList y.toList
        have hx := hl' x (by simp)
        have hy' : y.size = N := by
          have : ∀ (l'' : List (Array K)), (∀ a ∈ l'', a.size = N) →
              ∀ y ∈ l''.foldr (fun x IH ↦ if ∀ y ∈ IH, x ≠ y then x :: IH else IH) [], y.size = N := by
            intro l'' h''
            induction l'' with
            | nil => simp
            | cons z l'' ih'' =>
              intro w hw
              rw [List.foldr_cons] at hw
              split_ifs at hw
              · rcases List.mem_cons.1 hw with rfl | hw
                · exact h'' w (by simp)
                · exact ih'' (fun a ha ↦ h'' a (by simp [ha])) w hw
              · exact ih'' (fun a ha ↦ h'' a (by simp [ha])) w hw
          exact this l' (fun a ha ↦ hl' a (by simp [ha])) y hy
        simp only [Array.length_toList] at *
        omega)
    have h3 : (17 * N + 13 + 9) * (l'.foldr (fun x IH ↦ if ∀ y ∈ IH, x ≠ y then x :: IH else IH)
        []).length ≤ (17 * N + 22) * l.length := Nat.mul_le_mul_left _ (by omega)
    have e : ((17 * N + 22) * l.length + 30) * (l'.length + 1) =
        ((17 * N + 22) * l.length + 30) * l'.length + (17 * N + 22) * l.length + 30 := by ring
    split_ifs <;> omega

/-! ## The order on coefficient arrays -/

/-- `lexLE` on word lists: at most `17·|a| + 3`. -/
theorem lexLEC_cost (hP : Includes P Auto.LeanVM.Extraction.lexLE.c235.costDeps) :
    ∀ a b : List ℕ, (∀ x ∈ a, x < 2 ^ 64) → (∀ x ∈ b, x < 2 ^ 64) →
      machineCost P Auto.LeanVM.Extraction.lexLE.c235.costIdx [encodeValue a, encodeValue b] ≤ 17 * a.length + 3 := by
  intro a
  induction a with
  | nil => intro b _ _; rw [Auto.LeanVM.Extraction.lexLE.c235.costEq_nil P hP]; simp
  | cons x a ih =>
    intro b ha hb
    rw [Auto.LeanVM.Extraction.lexLE.c235.costEq_cons P hP]
    cases b with
    | nil => simp; omega
    | cons y b =>
      have := ih b (fun z hz ↦ ha z (by simp [hz])) (fun z hz ↦ hb z (by simp [hz]))
      have := ha x (by simp)
      have := hb y (by simp)
      simp only [List.length_cons]
      cost_simp
      split_ifs <;> omega

/-- **The candidates' order** (`coeffsLE` on arrays of `N` entries): at most `50·N + 21`. -/
theorem coeffsLEC_cost (hP : Includes P Auto.LeanVM.Extraction.coeffsLE.c234.costDeps)
    (a b : Array K) {N : ℕ} (ha : a.size = N) (hb : b.size = N) :
    machineCost P Auto.LeanVM.Extraction.coeffsLE.c234.costIdx [encodeValue a, encodeValue b] ≤ 50 * N + 21 := by
  rw [Auto.LeanVM.Extraction.coeffsLE.c234.costEq P hP]
  have hf := fun x ↦ RunsApp.of_spec (us := []) (vs := [encodeValue x])
    (Auto.LeanVM.Extraction.coeffsLE.c234.lam0.costSpec P (by includes) x)
  have hm := fun (c : Array K) ↦ listMap_le P Auto.List.map.c12.costIdx
    (.closure Auto.LeanVM.Extraction.coeffsLE.c234.lam0.costIdx [])
    (Auto.List.map.c12.costEq_nil P (by includes) _ _ hf)
    (Auto.List.map.c12.costEq_cons P (by includes) _ _ hf) 2 c.toList
    (fun x _ ↦ by
      rw [appCost_fn, List.nil_append, Auto.LeanVM.Extraction.coeffsLE.c234.lam0.costEq P (by includes)])
  have h1 := hm a
  have h2 := hm b
  have hw : ∀ c : Array K, ∀ x ∈ c.toList.map (fun x ↦ x.lane.toNat), x < 2 ^ 64 := by
    intro c x hx
    obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
    exact UInt64.toNat_lt _
  have := lexLEC_cost P (by includes) (a.toList.map fun x ↦ x.lane.toNat)
    (b.toList.map fun x ↦ x.lane.toNat) (hw a) (hw b)
  simp only [Array.length_toList, List.length_map] at *
  omega

/-! ## The novel basis -/

/-- **A candidate in the novel basis** (`toNovelFast κ p`: `2^κ` Horner evaluations, then the
inverse transform): at most `(272·|p| + 33)·2^κ + κ·(760·2^κ + 19790) + 40`. -/
theorem toNovelFastC_cost (hP : Includes P Auto.LeanVM.Extraction.Fast.toNovelFast.c244.costDeps) (κ : ℕ) (hκ : κ ≤ 62)
    (p : CPolynomial K) :
    machineCost P Auto.LeanVM.Extraction.Fast.toNovelFast.c244.costIdx [encodeValue κ, encodeValue p] ≤
      (272 * p.val.size + 33) * 2 ^ κ + κ * (760 * 2 ^ κ + 19790) + 40 := by
  rw [Auto.LeanVM.Extraction.Fast.toNovelFast.c244.costEq P hP]
  have hN : 2 ^ κ < 2 ^ 63 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hs : (1 <<< κ : ℕ) = 2 ^ κ := Nat.one_shiftLeft κ
  rw [hs]
  have hf := fun v ↦ RunsApp.of_spec (us := [encodeValue κ, encodeValue p]) (vs := [encodeValue v])
    (Auto.LeanVM.Extraction.Fast.toNovelFast.c244.lam1.costSpec P (by includes) κ p v)
  have hof := ofFnFrom_cost P (by includes) (n := 2 ^ κ) (by omega) _
    (.closure Auto.LeanVM.Extraction.Fast.toNovelFast.c244.lam1.costIdx [encodeValue κ, encodeValue p]) hf (272 * p.val.size + 14) (fun v ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append]
      rw [Auto.LeanVM.Extraction.Fast.toNovelFast.c244.lam1.costEq P (by includes)]
      have := hornerEvalC_cost P (by includes) (K.ofBits v) p
      omega) 0 (Nat.zero_le _)
  have := rangeLoop_cost P (by includes) κ [] (by omega)
  have := novelInv_cost P (by includes) (by includes) κ hκ
    (Array.ofFn fun v : Fin (2 ^ κ) ↦ hornerEval (K.ofBits v.val) p)
  simp only [length_ofFnFrom, Nat.sub_zero] at *
  cost_simp
  have e : (272 * p.val.size + 33) * 2 ^ κ = (272 * p.val.size + 14 + 18) * 2 ^ κ + 2 ^ κ := by
    ring
  have e2 : κ * (760 * 2 ^ κ + 19790) = κ * (760 * 2 ^ κ + 19773) + 17 * κ := by ring
  omega


/-! ## The lane's candidates -/

theorem mem_dedup_toNovel_size {κ : ℕ} {l : List (CPolynomial K)} {c : Array K}
    (h : c ∈ (l.map (toNovelFast κ)).dedup) : c.size = 2 ^ κ := by
  rw [List.mem_dedup, List.mem_map] at h
  obtain ⟨p, -, rfl⟩ := h
  exact toNovelFast_size κ p

/-- **One lane's candidates** (`laneEncodedDistinct`: the Guruswami–Sudan run, its candidates in
the novel basis, deduplicated, sorted, each re-encoded): at most the run's price plus
`laneExtraBound κ R L k`, `L` bounding the candidates and `k` their sizes. -/
theorem laneEncodedDistinctC_cost (hP : Includes P laneEncodedDistinctC.costDeps) (κ R A : ℕ)
    (hκR : κ + R ≤ 62) (S : ℕ → ℕ → K) (SVal : MachineValue)
    (hS : ∀ a b, RunsApp P SVal [encodeValue a, encodeValue b] (encodeValue (S a b))) (u : ℕ) {L k : ℕ}
    (hL : (gsLaneDistinct κ R A S u).size ≤ L) (hL60 : L < 2 ^ 30)
    (hk : ∀ p ∈ gsLaneDistinct κ R A S u, p.val.size ≤ k) :
    machineCost P laneEncodedDistinctC.costIdx [encodeValue κ, encodeValue R, encodeValue A, SVal, encodeValue u] ≤
      machineCost P Auto.LeanVM.Extraction.Fast.gsLaneDistinct.c249.costIdx
        [encodeValue κ, encodeValue R, encodeValue A, SVal, encodeValue u] + laneExtraBound κ R L k := by
  rw [laneEncodedDistinctC.costEq P hP κ R A S SVal hS,
    Auto.LeanVM.Extraction.Fast.laneListDistinct.c227.costEq P (by includes) κ R A S SVal hS]
  generalize hC : gsLaneDistinct κ R A S u = cands at hL hk
  -- the novel basis
  have hf1 := fun p ↦ RunsApp.of_spec (us := [encodeValue κ]) (vs := [encodeValue p])
    (Auto.LeanVM.Extraction.Fast.laneListDistinct.c227.lam1.costSpec P (by includes) κ p)
  have hm1 := listMap_le P Auto.List.map.c12.costIdx
    (.closure Auto.LeanVM.Extraction.Fast.laneListDistinct.c227.lam1.costIdx [encodeValue κ])
    (Auto.List.map.c12.costEq_nil P (by includes) _ _ hf1)
    (Auto.List.map.c12.costEq_cons P (by includes) _ _ hf1)
    ((272 * k + 33) * 2 ^ κ + κ * (760 * 2 ^ κ + 19790) + 43) cands.toList
    (fun p hp ↦ by
      rw [appCost_fn, List.singleton_append,
        Auto.LeanVM.Extraction.Fast.laneListDistinct.c227.lam1.costEq P (by includes)]
      have := toNovelFastC_cost P (by includes) κ (by omega) p
      have := Nat.mul_le_mul_right (2 ^ κ) (show 272 * p.val.size + 33 ≤ 272 * k + 33 by
        have := hk p (by simpa using hp); omega)
      omega)
  -- the deduplication
  have hlen : (cands.toList.map (toNovelFast κ)).length ≤ L := by simpa using hL
  have hd := dedupC_cost P (by includes) (2 ^ κ) (cands.toList.map (toNovelFast κ))
    (fun c hc ↦ by
      obtain ⟨p, -, rfl⟩ := List.mem_map.1 hc
      exact toNovelFast_size κ p)
  have hd1 : ((17 * 2 ^ κ + 22) * (cands.toList.map (toNovelFast κ)).length + 30) *
      (cands.toList.map (toNovelFast κ)).length ≤ ((17 * 2 ^ κ + 22) * L + 30) * L :=
    Nat.mul_le_mul (by have := Nat.mul_le_mul_left (17 * 2 ^ κ + 22) hlen; omega) hlen
  -- the sort
  have hdl : (cands.toList.map (toNovelFast κ)).dedup.length ≤ L :=
    (List.dedup_sublist _).length_le.trans hlen
  have hl0 := fun a b ↦ RunsApp.of_spec (us := []) (vs := [encodeValue a, encodeValue b])
    (Auto.LeanVM.Extraction.Fast.laneListDistinct.c227.lam0.costSpec P (by includes) a b)
  have hs := mergeSortList_cost_sq P (by includes) _
    (.closure Auto.LeanVM.Extraction.Fast.laneListDistinct.c227.lam0.costIdx []) hl0
    (fun c : Array K ↦ c.size = 2 ^ κ) (50 * 2 ^ κ + 24)
    (fun a b ha hb ↦ by
      simp only [appCost_fn, List.nil_append]
      rw [Auto.LeanVM.Extraction.Fast.laneListDistinct.c227.lam0.costEq P (by includes)]
      have := coeffsLEC_cost P (by includes) a b ha hb
      omega)
    _ (cands.toList.map (toNovelFast κ)).dedup rfl (by omega)
    (fun c hc ↦ mem_dedup_toNovel_size hc)
  have hs1 : (50 * 2 ^ κ + 24 + 100) *
      ((cands.toList.map (toNovelFast κ)).dedup.length *
        (cands.toList.map (toNovelFast κ)).dedup.length) ≤ (50 * 2 ^ κ + 124) * (L * L) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul hdl hdl)
  -- the re-encoding
  have hlist : (laneListDistinct κ R A S u).length ≤ L := by
    rw [laneListDistinct, List.length_mergeSort, hC]; exact hdl
  have hf2 := fun c ↦ RunsApp.of_spec (us := [encodeValue κ, encodeValue R]) (vs := [encodeValue c])
    (laneEncodedDistinctC.lam0.costSpec P (by includes) κ R c)
  have hm2 := listMap_le P Auto.List.map.c12.costIdx (.closure laneEncodedDistinctC.lam0.costIdx [encodeValue κ, encodeValue R])
    (Auto.List.map.c12.costEq_nil P (by includes) _ _ hf2)
    (Auto.List.map.c12.costEq_cons P (by includes) _ _ hf2)
    (κ * (760 * 2 ^ (κ + R) + 19793) + 30 * 2 ^ (κ + R) + 50) (laneListDistinct κ R A S u)
    (fun c _ ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.nil_append,
        laneEncodedDistinctC.lam0.costEq P (by includes)]
      have := novelFwd_cost P (by includes) κ R hκR c
      omega)
  simp only [Array.length_toList, List.length_map] at hm1 hlen
  have h1 : ((272 * k + 33) * 2 ^ κ + κ * (760 * 2 ^ κ + 19790) + 43 + 11) * cands.size ≤
      ((272 * k + 33) * 2 ^ κ + κ * (760 * 2 ^ κ + 19790) + 43 + 11) * L :=
    Nat.mul_le_mul_left _ hL
  have e5 : ((272 * k + 33) * 2 ^ κ + κ * (760 * 2 ^ κ + 19790) + 57) * L =
      ((272 * k + 33) * 2 ^ κ + κ * (760 * 2 ^ κ + 19790) + 43 + 11) * L + 3 * L := by ring
  have h2 : (κ * (760 * 2 ^ (κ + R) + 19793) + 30 * 2 ^ (κ + R) + 50 + 11) *
      (laneListDistinct κ R A S u).length ≤
      (κ * (760 * 2 ^ (κ + R) + 19793) + 30 * 2 ^ (κ + R) + 61) * L := Nat.mul_le_mul_left _ hlist
  have h3 : 3 * cands.size ≤ 3 * L := by omega
  unfold laneExtraBound
  omega

end

end LeanVM.Cost.Bounds.Decoder
