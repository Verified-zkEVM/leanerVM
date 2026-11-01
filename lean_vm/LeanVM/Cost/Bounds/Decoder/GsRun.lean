module

public import LeanVM.Cost.Bounds.Decoder.Roots
public import LeanVM.Cost.Extractor.GsRun
import all CompPoly.Univariate.Raw.Core
import all CompPoly.Univariate.Raw.Ops
import all CompPoly.Univariate.Basic

/-!
# Bound: one node of Roth–Ruckenstein's search, compiled

The prices of the pieces of a node of `prefixesNF` (`Cost/Extractor/GsRun.lean`), on a node of at
most `Y` rows of at most `X` coefficients:

* the `X`-adic order (`xAdicOrderBC_cost`), the division by `X^s` (`divXPowerFastC_cost`), the
  initial coefficient polynomial (`initialCoeffFastC_cost`), its roots
  (`rootsNonzeroC_cost`, the root finder of `Bounds/Decoder/Roots.lean`);
* the substitution `Y := a + X·Y` (`substituteFastC_cost`: per row the Taylor coefficient
  `taylorCoeffC_cost`, with a binomial parity `chooseOddC_cost` and a power `powSq_cost` per
  term, then the shift `shiftXC_cost`), the truncation (`truncateXC_cost`), the prefix extended
  (`extendPrefixC_cost`);
* the lane filter's pieces: Horner's evaluation, the mismatch count (`mismatchCountC_cost`),
  `degreeLtBool`.

The recursion itself, and the run, are bounded in `Bounds/Decoder/Prefixes.lean`.

**Honest-cost note.** `taylorCoeff`'s step names `a^(y−t) • Q_y` three times through
`CPolynomial`'s sum (the `trim_eq` rewrite), so the power and the scaling are computed thrice.
-/

namespace LeanVM.Cost.Bounds.Decoder

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.Library
open LeanVM.Cost.Extractor LeanVM.Parameters CompPoly LeanVM.Extraction.Fast

/-! The functions compiled on demand, by their short names. -/
open LeanVM.Cost.Auto.LeanVM.Extraction.Fast

public section

variable (P : MachineProgram)

/-! ## Orders and divisions by powers of `X` -/

theorem cpoly_xAdicOrder?_lt {p : CPolynomial K} {v : ℕ} (h : CPolynomial.xAdicOrder? p = some v) :
    v < p.val.size := by
  unfold CPolynomial.xAdicOrder? at h
  have := List.mem_of_find?_eq_some h
  rw [List.mem_range'] at this
  omega

/-- The `X`-adic order of a polynomial over `K`: at most `38·|p| + 18`. -/
theorem xAdicOrderC_cost (hP : Includes P Auto.CompPoly.CPolynomial.xAdicOrder?.c182.costDeps)
    (p : CPolynomial K) (hp : p.val.size < 2 ^ 62) :
    machineCost P Auto.CompPoly.CPolynomial.xAdicOrder?.c182.costIdx [encodeValue p] ≤ 38 * p.val.size + 18 := by
  rw [Auto.CompPoly.CPolynomial.xAdicOrder?.c182.costEq P hP]
  have := rangeC_cost P (by includes) p.val.size 0 (by omega)
  have hf := fun i ↦ RunsApp.of_spec (us := [encodeValue p]) (vs := [encodeValue i])
    (Auto.CompPoly.CPolynomial.xAdicOrder?.c182.lam0.costSpec P (by includes) p i)
  have := findNat_cost P (by includes) _ (.closure Auto.CompPoly.CPolynomial.xAdicOrder?.c182.lam0.costIdx
    [encodeValue p]) hf 8 (List.range' 0 p.val.size) (fun i _ ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append]
      rw [Auto.CompPoly.CPolynomial.xAdicOrder?.c182.lam0.costEq P (by includes)])
  simp only [List.length_range'] at this
  omega

/-- **The `X`-adic order of a bivariate polynomial** (`xAdicOrder?`, the least over its rows):
at most `(38·X + 72)·|Q| + 22`, rows of at most `X` coefficients. -/
theorem xAdicOrderBC_cost (hP : Includes P Auto.CompPoly.CBivariate.xAdicOrder?.c180.costDeps)
    (Q : CBivariate K) {X : ℕ} (hX : X < 2 ^ 60) (hQ : InnerLe Q.val X) (hQs : Q.val.size < 2 ^ 60) :
    machineCost P Auto.CompPoly.CBivariate.xAdicOrder?.c180.costIdx [encodeValue Q] ≤
      (38 * X + 72) * Q.val.size + 22 := by
  rw [Auto.CompPoly.CBivariate.xAdicOrder?.c180.costEq P hP]
  have := rangeC_cost P (by includes) Q.val.size 0 (by omega)
  have hf := listFoldl_le P (by includes) _
    (.closure Auto.CompPoly.CBivariate.xAdicOrder?.c180.lam0.costIdx [encodeValue Q])
    (fun best y ↦ RunsApp.of_spec (us := [encodeValue Q]) (vs := [encodeValue best, encodeValue y])
      (Auto.CompPoly.CBivariate.xAdicOrder?.c180.lam0.costSpec P (by includes) Q best y))
    (38 * X + 42) (fun best ↦ ∀ v, best = some v → v < 2 ^ 60) (List.range' 0 Q.val.size) none
    (by simp)
    (fun best hb y _ ↦ by
      have hcs := coeff_size_le_of_innerLe hQ y
      refine ⟨?_, ?_⟩
      · intro v hv
        generalize ho : CPolynomial.xAdicOrder? (Q.val.coeff y) = o at hv
        cases o with
        | none => exact hb v hv
        | some w =>
          have := cpoly_xAdicOrder?_lt ho
          cases best with
          | none => simp only [Option.some.injEq] at hv; omega
          | some b =>
            have := hb b rfl
            simp only [Option.some.injEq] at hv
            omega
      · simp only [appCost_fn, List.cons_append, List.nil_append]
        rw [Auto.CompPoly.CBivariate.xAdicOrder?.c180.lam0.costEq P (by includes)]
        have := xAdicOrderC_cost P (by includes) (Q.val.coeff y) (by omega)
        generalize ho : CPolynomial.xAdicOrder? (Q.val.coeff y) = o
        cases o with
        | none => dsimp only; omega
        | some w =>
          have := cpoly_xAdicOrder?_lt ho
          cases best with
          | none => dsimp only; omega
          | some b =>
            have := hb b rfl
            dsimp only
            cost_simp
            split_ifs <;> omega)
  simp only [List.length_range'] at hf
  have e : (38 * X + 72) * Q.val.size = (38 * X + 42 + 9) * Q.val.size + 21 * Q.val.size := by
    ring
  omega

theorem dropXPowerFast_size_le (p : CPolynomial K) (n : ℕ) :
    (dropXPowerFast p n).val.size ≤ p.val.size :=
  (raw_trim_size_le _).trans (by simp)

/-- `p / X^n` (`dropXPowerFast`): at most `24·|p| + 22`. -/
theorem dropXPowerFastC_cost (hP : Includes P dropXPowerFast.c186.costDeps) (p : CPolynomial K)
    (n : ℕ) (hp : p.val.size < 2 ^ 60) :
    machineCost P dropXPowerFast.c186.costIdx [encodeValue p, encodeValue n] ≤ 24 * p.val.size + 22 := by
  rw [dropXPowerFast.c186.costEq P hP]
  have h1 : (Array.extract p.val n).size ≤ p.val.size := by simp
  have := ofArray_cost P (by includes) (Array.extract p.val n) (by omega)
  omega

/-- **`Q / X^n`** (`divXPowerFast`, each row): at most `(27·X + 81)·|Q| + 26`. -/
theorem divXPowerFastC_cost (hP : Includes P divXPowerFast.c184.costDeps) (Q : CBivariate K)
    (n : ℕ) {X : ℕ} (hX : X < 2 ^ 58) (hQ : InnerLe Q.val X) (hQs : Q.val.size < 2 ^ 58) :
    machineCost P divXPowerFast.c184.costIdx [encodeValue Q, encodeValue n] ≤ (27 * X + 81) * Q.val.size + 26 := by
  rw [divXPowerFast.c184.costEq P hP]
  have hf := fun c ↦ RunsApp.of_spec (us := [encodeValue n]) (vs := [encodeValue c])
    (divXPowerFast.c184.lam0.costSpec P (by includes) n c)
  have hm := listMap_le P Auto.List.map.c12.costIdx (.closure divXPowerFast.c184.lam0.costIdx [encodeValue n])
    (Auto.List.map.c12.costEq_nil P (by includes) _ _ hf)
    (Auto.List.map.c12.costEq_cons P (by includes) _ _ hf) (24 * X + 25) Q.val.toList
    (fun c hc ↦ by
      rw [appCost_fn, List.singleton_append, divXPowerFast.c184.lam0.costEq P (by includes)]
      have := hQ c (by simpa using hc)
      have := dropXPowerFastC_cost P (by includes) c n (by omega)
      omega)
  have := ofArrayB_cost P (by includes) (Q.val.map fun c ↦ dropXPowerFast c n) X
    (fun x hx ↦ by
      obtain ⟨c, hc, rfl⟩ := Array.mem_map.1 hx
      exact (dropXPowerFast_size_le c n).trans (hQ c hc))
    (by simp; omega)
  simp only [Array.length_toList, List.length_map, Array.size_map] at hm this ⊢
  have e : (27 * X + 81) * Q.val.size =
      (24 * X + 25 + 11) * Q.val.size + (3 * X + 41) * Q.val.size + 4 * Q.val.size := by ring
  omega

/-- **The initial coefficient polynomial** (`initialCoeffFast`: each row's constant term):
at most `42·|Q| + 25`. -/
theorem initialCoeffFastC_cost (hP : Includes P initialCoeffFast.c204.costDeps) (Q : CBivariate K)
    (hQs : Q.val.size < 2 ^ 60) :
    machineCost P initialCoeffFast.c204.costIdx [encodeValue Q] ≤ 42 * Q.val.size + 25 := by
  rw [initialCoeffFast.c204.costEq P hP]
  have hf := fun c ↦ RunsApp.of_spec (us := []) (vs := [encodeValue c])
    (initialCoeffFast.c204.lam0.costSpec P (by includes) c)
  have hm := listMap_le P Auto.List.map.c12.costIdx (.closure initialCoeffFast.c204.lam0.costIdx [])
    (Auto.List.map.c12.costEq_nil P (by includes) _ _ hf)
    (Auto.List.map.c12.costEq_cons P (by includes) _ _ hf) 4 Q.val.toList
    (fun c _ ↦ by rw [appCost_fn, List.nil_append, initialCoeffFast.c204.lam0.costEq P (by includes)])
  have := ofArray_cost P (by includes) (Q.val.map fun c ↦ c.coeff 0) (by simp; omega)
  simp only [Array.length_toList, List.length_map, Array.size_map] at hm this ⊢
  omega

theorem initialCoeffFast_size_le (Q : CBivariate K) :
    (initialCoeffFast Q).val.size ≤ Q.val.size :=
  (raw_trim_size_le _).trans (by simp)

/-- **The roots of the initial coefficient polynomial** (`rootsInFieldForNonzeroEquation`, the root
finder on a nonzero polynomial of at most `B` coefficients): at most `rootsBound B + 15·B + 16`. -/
theorem rootsNonzeroC_cost
    (hP : Includes P Auto.CompPoly.GuruswamiSudan.rootsInFieldForNonzeroEquation.c203.costDeps)
    {B : ℕ} (hB : B < 2 ^ 28) (hB2 : 2 ≤ B) (p : CPolynomial K) (hp : p.val.size ≤ B) :
    machineCost P Auto.CompPoly.GuruswamiSudan.rootsInFieldForNonzeroEquation.c203.costIdx [encodeValue p] ≤
      rootsBound B + 15 * B + 16 := by
  rw [Auto.CompPoly.GuruswamiSudan.rootsInFieldForNonzeroEquation.c203.costEq P hP]
  have := listBeqK_cost P (by includes) p.val.toList (↑(0 : CPolynomial K) : Array K).toList
  have := rootsInFieldC_cost P (by includes) hB hB2 p hp
  simp only [Array.length_toList, size_zero_val] at *
  split_ifs <;> omega

/-! ## The substitution `Y := a + X·Y` -/

/-- `chooseOdd n a` (the parity of `C(n, a)`, bit by bit): at most `40 + 40·(log₂ n + 1)`. -/
theorem chooseOddC_cost (hP : Includes P chooseOdd.c197.costDeps) (n a : ℕ) (hn : n < 2 ^ 64)
    (ha : a < 2 ^ 64) :
    machineCost P chooseOdd.c197.costIdx [encodeValue n, encodeValue a] ≤ 40 + 40 * (Nat.log2 n + 1) := by
  have key := le_of_halving (fun x : ℕ × ℕ ↦ x.1 < 2 ^ 64 ∧ x.2 < 2 ^ 64) (fun x ↦ x.1)
    (fun x ↦ machineCost P chooseOdd.c197.costIdx [encodeValue x.1, encodeValue x.2]) 40 40
    (fun x hI h0 ↦ by
      obtain ⟨n, a⟩ := x
      dsimp only at h0 hI ⊢
      subst h0
      rw [chooseOdd.c197.costEq_zero P hP]
      cost_simp
      omega)
    (fun x hI hpos ↦ by
      obtain ⟨n, a⟩ := x
      obtain ⟨hn, ha⟩ := hI
      dsimp only at hpos hn ha ⊢
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      rw [chooseOdd.c197.costEq_succ P hP]
      cost_simp
      by_cases hc : a % 2 ≤ (k + 1) % 2
      · right
        refine ⟨((k + 1) / 2, a / 2), ⟨by omega, by omega⟩, le_rfl, ?_⟩
        simp only [hc, decide_true, ↓reduceIte]
        cost_simp
        omega
      · left
        simp only [hc, decide_false, Bool.false_eq_true, ↓reduceIte]
        omega)
  exact key (n, a) ⟨hn, ha⟩

theorem cpoly_smul_size_le (r : K) (p : CPolynomial K) : (r • p).val.size ≤ p.val.size := by
  show (CPolynomial.Raw.smul r p.val).trim.size ≤ _
  exact (raw_trim_size_le _).trans (by rw [size_smul])

theorem taylorCoeff_size_le {Q : CBivariate K} {X : ℕ} (hQ : InnerLe Q.val X) (a : K) (t : ℕ) :
    (taylorCoeff Q a t).val.size ≤ X := by
  unfold taylorCoeff
  suffices ∀ (l : List ℕ) (acc : CPolynomial K), acc.val.size ≤ X →
      (l.foldl (fun acc y ↦ if chooseOdd y t then acc + a ^ (y - t) • Q.val.coeff y else acc)
        acc).val.size ≤ X from this _ 0 (by simp [size_zero_val])
  intro l
  induction l with
  | nil => intro acc h; exact h
  | cons y l ih =>
    intro acc h
    apply ih
    dsimp only
    split_ifs
    · have := cpoly_add_size_le acc (a ^ (y - t) • Q.val.coeff y)
      have := cpoly_smul_size_le (a ^ (y - t)) (Q.val.coeff y)
      have := coeff_size_le_of_innerLe hQ y
      omega
    · exact h

/-- **One Taylor coefficient** (`taylorCoeff Q a t`: per row `y ≥ t` a binomial parity and, when
odd, `a^(y−t)·Q_y` added): at most `taylorBound X Y (log₂ Y + 1)`. -/
theorem taylorCoeffC_cost (hP : Includes P taylorCoeff.c195.costDeps) (Q : CBivariate K) (a : K)
    (t : ℕ) {X Y : ℕ} (hX : X < 2 ^ 56) (hY : Y < 2 ^ 56) (hQ : InnerLe Q.val X)
    (hQs : Q.val.size ≤ Y) (ht : t < 2 ^ 56) :
    machineCost P taylorCoeff.c195.costIdx [encodeValue Q, encodeValue a, encodeValue t] ≤
      taylorBound X Y (Nat.log2 Y + 1) := by
  rw [taylorCoeff.c195.costEq P hP]
  have := rangeC_cost P (by includes) (Q.val.size - t) t (by omega)
  have hf := listFoldl_le P (by includes) _ (.closure taylorCoeff.c195.lam0.costIdx [encodeValue Q, encodeValue a, encodeValue t])
    (fun acc y ↦ RunsApp.of_spec (us := [encodeValue Q, encodeValue a, encodeValue t]) (vs := [encodeValue acc, encodeValue y])
      (taylorCoeff.c195.lam0.costSpec P (by includes) Q a t acc y))
    (1700 * (Nat.log2 Y + 1) + 960 * X + 320) (fun acc : CPolynomial K ↦ acc.val.size ≤ X)
    (List.range' t (Q.val.size - t)) 0 (by simp [size_zero_val])
    (fun acc hacc y hy ↦ by
      simp only [List.mem_range'_1] at hy
      have hcs := coeff_size_le_of_innerLe hQ y
      have hsm := cpoly_smul_size_le (a ^ (y - t)) (Q.val.coeff y)
      refine ⟨?_, ?_⟩
      · split_ifs
        · have := cpoly_add_size_le acc (a ^ (y - t) • Q.val.coeff y)
          omega
        · exact hacc
      · simp only [appCost_fn, List.cons_append, List.nil_append]
        rw [taylorCoeff.c195.lam0.costEq P (by includes)]
        have hlog : Nat.log2 y ≤ Nat.log2 Y := log2_mono (by omega)
        have := chooseOddC_cost P (by includes) y t (by omega) (by omega)
        have := powSq_cost P (by includes) a (y - t) (by omega)
        have hlog' : Nat.log2 (y - t) ≤ Nat.log2 Y := log2_mono (by omega)
        have := smulK_cost P (by includes) (a ^ (y - t)) (Q.val.coeff y).val
        have hss : (CPolynomial.Raw.smul (a ^ (y - t)) (Q.val.coeff y).val).size ≤ X := by
          rw [size_smul]; exact hcs
        have := trimLen_cost P (by includes) (CPolynomial.Raw.smul (a ^ (y - t)) (Q.val.coeff y).val)
          (CPolynomial.Raw.smul (a ^ (y - t)) (Q.val.coeff y).val).size (by omega)
        have hext : ∀ (arr : Array K) (n : ℕ), (arr.extract 0 n).size ≤ arr.size :=
          fun arr n ↦ by simp
        have := hext (CPolynomial.Raw.smul (a ^ (y - t)) (Q.val.coeff y).val)
          (CompPolyLib.trimLen (CPolynomial.Raw.smul (a ^ (y - t)) (Q.val.coeff y).val)
              (CPolynomial.Raw.smul (a ^ (y - t)) (Q.val.coeff y).val).size)
        have := addK_cost P (by includes) acc.val (a ^ (y - t) • Q.val.coeff y).val (by omega)
          (by omega)
        cost_simp
        split_ifs <;> omega)
  simp only [List.length_range'] at hf
  have h1 : (1700 * (Nat.log2 Y + 1) + 960 * X + 320 + 9) * (Q.val.size - t) ≤
      (1700 * (Nat.log2 Y + 1) + 960 * X + 329) * Y := Nat.mul_le_mul_left _ (by omega)
  unfold taylorBound
  cost_simp
  omega

/-- `X^t·p` (`shiftX`): at most `25·(t + |p|) + 22`. -/
theorem shiftXC_cost (hP : Includes P shiftX.c194.costDeps) (t : ℕ) (p : CPolynomial K)
    (h : t + p.val.size < 2 ^ 60) :
    machineCost P shiftX.c194.costIdx [encodeValue t, encodeValue p] ≤ 25 * (t + p.val.size) + 22 := by
  rw [shiftX.c194.costEq P hP]
  have := ofArray_cost P (by includes) (Array.replicate t 0 ++ p.val) (by simp; omega)
  simp only [Array.size_append, Array.size_replicate] at this ⊢
  omega

/-- **The substitution `Y := a + X·Y`** (`substituteFast`: per row its Taylor coefficient, shifted
by `X^t`): at most `substBound X Y`, its rows of at most `X + Y` coefficients. -/
theorem substituteFastC_cost (hP : Includes P substituteFast.c192.costDeps) (Q : CBivariate K)
    (a : K) {X Y : ℕ} (hX : X < 2 ^ 56) (hY : Y < 2 ^ 56) (hQ : InnerLe Q.val X)
    (hQs : Q.val.size ≤ Y) :
    machineCost P substituteFast.c192.costIdx [encodeValue Q, encodeValue a] ≤ substBound X Y := by
  rw [substituteFast.c192.costEq P hP]
  have hf := fun t ↦ RunsApp.of_spec (us := [encodeValue Q, encodeValue a]) (vs := [encodeValue t])
    (substituteFast.c192.lam0.costSpec P (by includes) Q a t)
  have := ofFnFrom_cost P (by includes) (n := Q.val.size) (by omega) _
    (.closure substituteFast.c192.lam0.costIdx [encodeValue Q, encodeValue a]) hf
    (taylorBound X Y (Nat.log2 Y + 1) + 25 * (X + Y) + 28) (fun t ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append]
      rw [substituteFast.c192.lam0.costEq P (by includes)]
      have ht := t.isLt
      have := taylorCoeffC_cost P (by includes) Q a t hX hY hQ hQs (by omega)
      have hts := taylorCoeff_size_le hQ a t
      have := shiftXC_cost P (by includes) t (taylorCoeff Q a t) (by omega)
      have : 25 * (↑t + (taylorCoeff Q a ↑t).val.size) ≤ 25 * (X + Y) := by omega
      omega) 0 (by omega)
  have := ofArrayB_cost P (by includes)
    (Array.ofFn fun t : Fin Q.val.size ↦ shiftX t.val (taylorCoeff Q a t.val)) (X + Y)
    (fun x hx ↦ by
      obtain ⟨t, rfl⟩ := Array.mem_ofFn.1 hx
      have := taylorCoeff_size_le hQ a t
      have h1 : (shiftX t.val (taylorCoeff Q a t.val)).val.size ≤ t.val + (taylorCoeff Q a t).val.size :=
        (raw_trim_size_le _).trans (by simp)
      have := t.isLt
      omega)
    (by simp; omega)
  simp only [length_ofFnFrom, Array.size_ofFn, Nat.sub_zero] at *
  have h1 : (taylorBound X Y (Nat.log2 Y + 1) + 25 * (X + Y) + 28 + 18) * Q.val.size ≤
      (taylorBound X Y (Nat.log2 Y + 1) + 25 * (X + Y) + 46) * Y := Nat.mul_le_mul_left _ hQs
  have h2 : (3 * (X + Y) + 41) * Q.val.size ≤ (3 * (X + Y) + 41) * Y := Nat.mul_le_mul_left _ hQs
  have e : (taylorBound X Y (Nat.log2 Y + 1) + 28 * (X + Y) + 100) * Y =
      (taylorBound X Y (Nat.log2 Y + 1) + 25 * (X + Y) + 46) * Y + (3 * (X + Y) + 41) * Y +
        13 * Y := by ring
  unfold substBound
  omega

theorem substituteFast_sizes {Q : CBivariate K} {X : ℕ} (hQ : InnerLe Q.val X) (a : K) :
    (substituteFast Q a).val.size ≤ Q.val.size ∧
      InnerLe (substituteFast Q a).val (X + Q.val.size) := by
  refine ⟨(raw_trim_size_le _).trans (by simp), ?_⟩
  refine InnerLe.trim (fun x hx ↦ ?_)
  obtain ⟨t, rfl⟩ := Array.mem_ofFn.1 hx
  have := taylorCoeff_size_le hQ a t
  have h1 : (shiftX t.val (taylorCoeff Q a t.val)).val.size ≤ t.val + (taylorCoeff Q a t).val.size :=
    (raw_trim_size_le _).trans (by simp)
  have := t.isLt
  omega

/-- `p mod X^n` (`truncate`): at most `24·|p| + 21`. -/
theorem truncateC_cost (hP : Includes P Auto.CompPoly.CPolynomial.truncate.c191.costDeps)
    (p : CPolynomial K) (n : ℕ) (hp : p.val.size < 2 ^ 60) :
    machineCost P Auto.CompPoly.CPolynomial.truncate.c191.costIdx [encodeValue p, encodeValue n] ≤
      24 * p.val.size + 21 := by
  rw [Auto.CompPoly.CPolynomial.truncate.c191.costEq P hP]
  have h1 : (Array.extract p.val 0 n).size ≤ p.val.size := by simp
  have := ofArray_cost P (by includes) (Array.extract p.val 0 n) (by omega)
  omega

/-- **`Q mod X^n`** (`truncateX`, each row): at most `(27·X + 80)·|Q| + 26`. -/
theorem truncateXC_cost (hP : Includes P Auto.CompPoly.CBivariate.truncateX.c189.costDeps)
    (Q : CBivariate K) (n : ℕ) {X : ℕ} (hX : X < 2 ^ 60) (hQ : InnerLe Q.val X)
    (hQs : Q.val.size < 2 ^ 58) :
    machineCost P Auto.CompPoly.CBivariate.truncateX.c189.costIdx [encodeValue Q, encodeValue n] ≤
      (27 * X + 80) * Q.val.size + 26 := by
  rw [Auto.CompPoly.CBivariate.truncateX.c189.costEq P hP]
  have hf := fun c ↦ RunsApp.of_spec (us := [encodeValue n]) (vs := [encodeValue c])
    (Auto.CompPoly.CBivariate.truncateX.c189.lam0.costSpec P (by includes) n c)
  have hm := listMap_le P Auto.List.map.c12.costIdx
    (.closure Auto.CompPoly.CBivariate.truncateX.c189.lam0.costIdx [encodeValue n])
    (Auto.List.map.c12.costEq_nil P (by includes) _ _ hf)
    (Auto.List.map.c12.costEq_cons P (by includes) _ _ hf) (24 * X + 24) Q.val.toList
    (fun c hc ↦ by
      rw [appCost_fn, List.singleton_append,
        Auto.CompPoly.CBivariate.truncateX.c189.lam0.costEq P (by includes)]
      have := hQ c (by simpa using hc)
      have := truncateC_cost P (by includes) c n (by omega)
      omega)
  have := ofArrayB_cost P (by includes) (Q.val.map fun c ↦ CPolynomial.truncate c n) X
    (fun x hx ↦ by
      obtain ⟨c, hc, rfl⟩ := Array.mem_map.1 hx
      have := hQ c hc
      have : (CPolynomial.truncate c n).val.size ≤ c.val.size :=
        (raw_trim_size_le _).trans (by simp)
      omega)
    (by simp; omega)
  simp only [Array.length_toList, List.length_map, Array.size_map] at hm this ⊢
  have e : (27 * X + 80) * Q.val.size =
      (24 * X + 24 + 11) * Q.val.size + (3 * X + 41) * Q.val.size + 4 * Q.val.size := by ring
  omega

/-- **The prefix extended** (`extendPrefix pref depth a = pref + a·X^depth`): at most
`110·(|pref| + depth + 1) + 2·depth + 200`. -/
theorem extendPrefixC_cost (hP : Includes P Auto.CompPoly.GuruswamiSudan.extendPrefix.c199.costDeps)
    (pref : CPolynomial K) (depth : ℕ) (a : K) (hp : pref.val.size < 2 ^ 58)
    (hd : depth < 2 ^ 58) :
    machineCost P Auto.CompPoly.GuruswamiSudan.extendPrefix.c199.costIdx
      [encodeValue pref, encodeValue depth, encodeValue a] ≤ 110 * (pref.val.size + depth + 1) + 2 * depth + 200 := by
  rw [Auto.CompPoly.GuruswamiSudan.extendPrefix.c199.costEq P hP,
    Auto.CompPoly.CPolynomial.monomial.c200.costEq P (by includes),
    Auto.CompPoly.CPolynomial.Raw.monomial.c201.costEq P (by includes)]
  have hm : (CPolynomial.monomial depth a).val.size ≤ depth + 1 := by
    show (CPolynomial.Raw.monomial depth a).size ≤ _
    unfold CPolynomial.Raw.monomial
    split <;> simp [CPolynomial.Raw.mk]
  have := addK_cost P (by includes) pref.val (CPolynomial.monomial depth a).val (by omega)
    (by omega)
  simp only [Array.size_replicate, List.size_toArray, List.length_cons, List.length_nil] at *
  split_ifs <;> omega


/-! ## The lane filter -/

/-- `p(x)` by Horner's rule (`hornerEval`): at most `272·|p| + 10`. -/
theorem hornerEvalC_cost (hP : Includes P hornerEval.c212.costDeps) (x : K) (p : CPolynomial K) :
    machineCost P hornerEval.c212.costIdx [encodeValue x, encodeValue p] ≤ 272 * p.val.size + 10 := by
  rw [hornerEval.c212.costEq P hP]
  have := foldr_cost P (by includes) _ (.closure hornerEval.c212.lam0.costIdx [encodeValue x])
    (fun a acc ↦ RunsApp.of_spec (us := [encodeValue x]) (vs := [encodeValue a, encodeValue acc])
      (hornerEval.c212.lam0.costSpec P (by includes) x a acc)) 260 (0 : K) p.val.toList
    (fun a _ acc ↦ by
      rw [appCost_fn, List.singleton_append, hornerEval.c212.lam0.costEq P (by includes)])
  simp only [Array.length_toList] at this
  omega

/-- **The mismatch count** (`mismatchCountFast`: `p` evaluated at each of `n` points): at most
`(272·|p| + 34)·n + 10`. -/
theorem mismatchCountC_cost (hP : Includes P mismatchCountFast.c210.costDeps)
    (points : Array (K × K)) (p : CPolynomial K) (hn : points.size < 2 ^ 63) :
    machineCost P mismatchCountFast.c210.costIdx [encodeValue points, encodeValue p] ≤
      (272 * p.val.size + 34) * points.size + 10 := by
  rw [mismatchCountFast.c210.costEq P hP]
  have := listFoldl_le_idx P (by includes) _ (.closure mismatchCountFast.c210.lam0.costIdx [encodeValue p])
    (fun c pt ↦ RunsApp.of_spec (us := [encodeValue p]) (vs := [encodeValue c, encodeValue pt])
      (mismatchCountFast.c210.lam0.costSpec P (by includes) p c pt)) (272 * p.val.size + 22)
    (fun k c ↦ c + k ≤ points.size) points.toList
    (fun k c hc pt _ ↦ by
      refine ⟨by split_ifs <;> omega, ?_⟩
      simp only [appCost_fn, List.cons_append, List.nil_append]
      rw [mismatchCountFast.c210.lam0.costEq P (by includes)]
      have := hornerEvalC_cost P (by includes) pt.1 p
      cost_simp
      split_ifs <;> omega)
    points.toList 0 (fun _ h ↦ h) (by simp)
  simp only [Array.length_toList] at this
  have e : (272 * p.val.size + 34) * points.size =
      (272 * p.val.size + 22 + 9) * points.size + 3 * points.size := by ring
  omega

theorem mismatchCountFast_le (points : Array (K × K)) (p : CPolynomial K) :
    mismatchCountFast points p ≤ points.size := by
  unfold mismatchCountFast
  rw [← Array.foldl_toList]
  suffices ∀ (l : List (K × K)) (c : ℕ), l.foldl (fun count point ↦
      if hornerEval point.1 p == point.2 then count else count + 1) c ≤ c + l.length by
    simpa using this points.toList 0
  intro l
  induction l with
  | nil => intro c; simp
  | cons x l ih =>
    intro c
    rw [List.foldl_cons]
    simp only [List.length_cons]
    by_cases h : (hornerEval x.1 p == x.2) = true
    · simp only [h, ↓reduceIte]; have := ih c; omega
    · simp only [h, Bool.false_eq_true, ↓reduceIte]; have := ih (c + 1); omega

/-- **The candidate filter** (`gsRunDistinctNF`'s test: degree below `k`, then at most `radius`
mismatches): at most `(272·|p| + 34)·n + 30`. -/
theorem gsRunFilterC_cost (hP : Includes P gsRunDistinctNFC.lam0.costDeps)
    (points : Array (K × K)) (params : GuruswamiSudan.GSInterpParams) (radius : ℕ)
    (p : CPolynomial K) (hn : points.size < 2 ^ 63) (hp : p.val.size < 2 ^ 64)
    (hk : params.messageDegree < 2 ^ 64) (hr : radius < 2 ^ 64) :
    machineCost P gsRunDistinctNFC.lam0.costIdx [encodeValue points, encodeValue params, encodeValue radius, encodeValue p] ≤
      (272 * p.val.size + 34) * points.size + 30 := by
  rw [gsRunDistinctNFC.lam0.costEq P hP,
    Auto.CompPoly.GuruswamiSudan.degreeLtBool.c208.costEq P (by includes)]
  cost_simp
  split_ifs
  · rw [passesDistanceFast.c209.costEq P (by includes)]
    have := mismatchCountC_cost P (by includes) points p hn
    have := mismatchCountFast_le points p
    cost_simp
    omega
  · omega


/-! ## Roth–Ruckenstein's prefixes: sizes -/

theorem mem_foldl_append {α β : Type} (g : α → Array β) :
    ∀ (l : List α) (init : Array β) (x : β), x ∈ l.foldl (fun out a ↦ out ++ g a) init →
      x ∈ init ∨ ∃ a ∈ l, x ∈ g a := by
  intro l
  induction l with
  | nil => intro init x h; exact Or.inl h
  | cons a l ih =>
    intro init x h
    rcases ih _ x h with h | ⟨b, hb, hx⟩
    · rcases Array.mem_append.1 h with h | h
      · exact Or.inl h
      · exact Or.inr ⟨a, by simp, h⟩
    · exact Or.inr ⟨b, by simp [hb], hx⟩

theorem extendPrefix_size_le (pref : CPolynomial K) (depth : ℕ) (a : K) :
    (GuruswamiSudan.extendPrefix pref depth a).val.size ≤ max pref.val.size (depth + 1) := by
  have hm : (CPolynomial.monomial depth a).val.size ≤ depth + 1 := by
    show (CPolynomial.Raw.monomial depth a).size ≤ _
    unfold CPolynomial.Raw.monomial
    split <;> simp [CPolynomial.Raw.mk]
  have := cpoly_add_size_le pref (CPolynomial.monomial depth a)
  show (pref + CPolynomial.monomial depth a).val.size ≤ _
  omega

/-- **Roth–Ruckenstein's prefixes have at most `depth + fuel` coefficients.** -/
theorem prefixesWithFuelFast_mem_size_le (fr : GuruswamiSudan.FieldRootContext K) (fuel : ℕ) :
    ∀ (Q : CBivariate K) (depth : ℕ) (pref : CPolynomial K), pref.val.size ≤ depth →
      ∀ p ∈ prefixesWithFuelFast fr fuel Q depth pref, p.val.size ≤ depth + fuel := by
  induction fuel with
  | zero =>
    intro Q depth pref hp p hmem
    simp only [prefixesWithFuelFast, Array.mem_singleton] at hmem
    subst hmem; omega
  | succ fuel ih =>
    intro Q depth pref hp p hmem
    rw [prefixesWithFuelFast] at hmem
    split at hmem
    · simp at hmem
    · rw [← Array.foldl_toList] at hmem
      rcases mem_foldl_append _ _ _ p hmem with h | ⟨a, -, ha⟩
      · simp at h
      · have := ih _ (depth + 1) _ (by have := extendPrefix_size_le pref depth a; omega) p ha
        omega

open CompPoly.GuruswamiSudan in
/-- **Roth–Ruckenstein's prefixes on an interpolated `Q`: at most `max 1 ℓ`** (`k > 1`). -/
theorem prefixesNF_size_le {points : Array (K × K)} (h : DistinctXCoordinates points)
    {params : GSInterpParams} {Q : CBivariate K} (hQ : interpolateDistinct points params = some Q)
    (hk : 1 < params.messageDegree) :
    (prefixesNF fieldRootCtxFast params.messageDegree
      (CBivariate.truncateX Q (params.weightedDegreeBound + 1)) (params.weightedDegreeBound + 1) 0
      default).size ≤ max 1 (interpolationYCap params) := by
  have hv := interpolateDistinct_valid h hQ
  rw [prefixesNF_eq_truncD hv, prefixesTruncD_eq,
    prefixesTrunc_eq fieldRootCtxFast _ Q _ (fun _ ↦ replayPath Q []) 0 default rfl]
  refine (prefixesWithFuelFast_size_le fieldRootCtxFast_nodup _ _ _ _).trans ?_
  have hd := rrDeg_le (lenLe_of_validInterpolation hv hk).1
  simp only [replayPath, List.foldl_nil, Nat.add_sub_cancel] at hd ⊢
  omega

end

end LeanVM.Cost.Bounds.Decoder
