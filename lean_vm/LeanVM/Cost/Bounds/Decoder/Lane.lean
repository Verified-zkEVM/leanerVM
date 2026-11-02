module

public import LeanVM.Cost.Bounds.Decoder.GsRun
public import LeanVM.Cost.Bounds.FastPath
public import LeanVM.Cost.Bounds.Sizes.Lane
public import LeanVM.Cost.Extractor.PMLane
import all LeanVM.Cost.InitLib

/-!
# Bound: one lane's candidates, the pieces, compiled

The pieces of a lane's price beyond its Guruswami–Sudan run (`laneEncodedWith pmSolver`, compiled
in `Cost/Extractor/PMLane.lean`; assembled in `Bounds/PMLane/Decode.lean`, `laneExtraBound`):

* the candidates in the novel basis (`toNovelFastC_cost`: `2^κ` Horner evaluations, then the
  inverse transform `novelInv_cost` of `Bounds/FastPath.lean`);
* their deduplication (`dedupC_cost`: each candidate compared with the kept ones, `O(n²·2^κ)`)
  and sort (`mergeSortList_cost_sq`, `coeffsLEC_cost`: at most `C·n² + 10`, a quadratic bound,
  enough at `n ≤ ℓ`);
* each candidate re-encoded (`novelFwd_cost` of `Bounds/FastPath.lean`).
-/

namespace LeanVM.Cost.Bounds.Decoder

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.Library
open LeanVM.Cost.Extractor LeanVM.Parameters CompPoly LeanVM.Extraction.Fast

public section

variable (P : MachineProgram)

/-! ## Deduplication -/

/-- Array equality over `K` (`List.beq.c662` on the coefficient lists): at most `11·|a| + 6`. -/
theorem beqArrC_cost (hP : Includes P Auto.List.beq.c662.costDeps) :
    ∀ a b : List K, machineCost P Auto.List.beq.c662.costIdx [encodeValue a, encodeValue b] ≤ 11 * a.length + 6 := by
  intro a
  induction a with
  | nil => intro b; rw [Auto.List.beq.c662.costEq_nil P hP]; cases b <;> simp
  | cons x a ih =>
    intro b
    rw [Auto.List.beq.c662.costEq_cons P hP]
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
theorem dedupC_cost (hP : Includes P Auto.List.dedup.c658.costDeps) (N : ℕ) :
    ∀ l : List (Array K), (∀ a ∈ l, a.size = N) →
      machineCost P Auto.List.dedup.c658.costIdx [encodeValue l] ≤ ((17 * N + 22) * l.length + 30) * l.length + 9 := by
  intro l hl
  rw [Auto.List.dedup.c658.costEq P hP, Auto.List.pwFilter.c659.costEq P (by includes)]
  have hf := fun x IH ↦ RunsApp.of_spec (us := []) (vs := [encodeValue x, encodeValue IH])
    (Auto.List.pwFilter.c659.lam0.costSpec P (by includes) x IH)
  suffices h : ∀ l' : List (Array K), (∀ a ∈ l', a.size = N) → l'.length ≤ l.length →
      machineCost P Auto.List.foldr.c22.costIdx [.closure Auto.List.pwFilter.c659.lam0.costIdx [],
        encodeValue ([] : List (Array K)), encodeValue l'] ≤ ((17 * N + 22) * l.length + 30) * l'.length + 3 by
    have := h l hl le_rfl
    omega
  intro l'
  induction l' with
  | nil =>
    intro _ _
    rw [Auto.List.foldr.c22.costEq_nil P (by includes) _ (.closure Auto.List.pwFilter.c659.lam0.costIdx []) hf]
    simp
  | cons x l' ih =>
    intro hl' hlen
    rw [Auto.List.foldr.c22.costEq_cons P (by includes) _
      (.closure Auto.List.pwFilter.c659.lam0.costIdx []) hf]
    simp only [List.length_cons] at hlen ⊢
    have := ih (fun a ha ↦ hl' a (by simp [ha])) (by omega)
    have hIH := foldr_pw_length_le l'
    simp only [appCost_fn, List.nil_append]
    rw [Auto.List.pwFilter.c659.lam0.costEq P (by includes)]
    have hq := fun y ↦ RunsApp.of_spec (us := [encodeValue x]) (vs := [encodeValue y])
      (Auto.List.pwFilter.c659.lam0.lam0.costSpec P (by includes) x y)
    have hall := all_cost P (by includes) _ (.closure Auto.List.pwFilter.c659.lam0.lam0.costIdx [encodeValue x])
      hq (17 * N + 13) (l'.foldr (fun x IH ↦ if ∀ y ∈ IH, x ≠ y then x :: IH else IH) [])
      (fun y hy ↦ by
        simp only [appCost_fn, List.cons_append, List.nil_append]
        rw [Auto.List.pwFilter.c659.lam0.lam0.costEq P (by includes)]
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
theorem lexLEC_cost (hP : Includes P Auto.LeanVM.Extraction.lexLE.c656.costDeps) :
    ∀ a b : List ℕ, (∀ x ∈ a, x < 2 ^ 64) → (∀ x ∈ b, x < 2 ^ 64) →
      machineCost P Auto.LeanVM.Extraction.lexLE.c656.costIdx [encodeValue a, encodeValue b] ≤ 17 * a.length + 3 := by
  intro a
  induction a with
  | nil => intro b _ _; rw [Auto.LeanVM.Extraction.lexLE.c656.costEq_nil P hP]; simp
  | cons x a ih =>
    intro b ha hb
    rw [Auto.LeanVM.Extraction.lexLE.c656.costEq_cons P hP]
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
theorem coeffsLEC_cost (hP : Includes P Auto.LeanVM.Extraction.coeffsLE.c655.costDeps)
    (a b : Array K) {N : ℕ} (ha : a.size = N) (hb : b.size = N) :
    machineCost P Auto.LeanVM.Extraction.coeffsLE.c655.costIdx [encodeValue a, encodeValue b] ≤ 50 * N + 21 := by
  rw [Auto.LeanVM.Extraction.coeffsLE.c655.costEq P hP]
  have hf := fun x ↦ RunsApp.of_spec (us := []) (vs := [encodeValue x])
    (Auto.LeanVM.Extraction.coeffsLE.c655.lam0.costSpec P (by includes) x)
  have hm := fun (c : Array K) ↦ listMap_le P Auto.List.map.c29.costIdx
    (.closure Auto.LeanVM.Extraction.coeffsLE.c655.lam0.costIdx [])
    (Auto.List.map.c29.costEq_nil P (by includes) _ _ hf)
    (Auto.List.map.c29.costEq_cons P (by includes) _ _ hf) 2 c.toList
    (fun x _ ↦ by
      rw [appCost_fn, List.nil_append, Auto.LeanVM.Extraction.coeffsLE.c655.lam0.costEq P (by includes)])
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
theorem toNovelFastC_cost (hP : Includes P Auto.LeanVM.Extraction.Fast.toNovelFast.c664.costDeps) (κ : ℕ) (hκ : κ ≤ 62)
    (p : CPolynomial K) :
    machineCost P Auto.LeanVM.Extraction.Fast.toNovelFast.c664.costIdx [encodeValue κ, encodeValue p] ≤
      (272 * p.val.size + 33) * 2 ^ κ + κ * (760 * 2 ^ κ + 19790) + 40 := by
  rw [Auto.LeanVM.Extraction.Fast.toNovelFast.c664.costEq P hP]
  have hN : 2 ^ κ < 2 ^ 63 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hs : (1 <<< κ : ℕ) = 2 ^ κ := Nat.one_shiftLeft κ
  rw [hs]
  have hf := fun v ↦ RunsApp.of_spec (us := [encodeValue κ, encodeValue p]) (vs := [encodeValue v])
    (Auto.LeanVM.Extraction.Fast.toNovelFast.c664.lam0.costSpec P (by includes) κ p v)
  have hof := ofFnFrom_cost P (by includes) (n := 2 ^ κ) (by omega) _
    (.closure Auto.LeanVM.Extraction.Fast.toNovelFast.c664.lam0.costIdx [encodeValue κ, encodeValue p]) hf (272 * p.val.size + 14) (fun v ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append]
      rw [Auto.LeanVM.Extraction.Fast.toNovelFast.c664.lam0.costEq P (by includes)]
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

end

end LeanVM.Cost.Bounds.Decoder
