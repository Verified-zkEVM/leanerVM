/-
  LeanVM.E2E.Vis.PerKey.Coll

  W-vis, P7d: the key coincidences of one key in key generation. Key `idx`'s parameter is another
  key's, or some parameter is zero, with probability at most `2n/2^128 + Q²/2^256`.
-/

module

public import LeanVM.E2E.Vis.PerKey.Defs
public import LeanVM.E2E.Vis.Engine
public import LeanVM.E2E.Reduction.GameW

/-!
# Key coincidences in key generation (W-vis, P7d)

Each key's parameter is the truncation of the answer at `kcParamIn S = 0^16 ‖ A_param ‖ S`, `S` the
answer at its seed input `a_i` (`"leanXMSS" ‖ S0` or `"leanSPHINCS" ‖ S0`). Key `idx` coincides
(`KeyCollAt`) when another key's parameter is its own or some parameter is zero.

**Seeds first** (`prEvent_keygenPhase_eq_seeds`). In the lazy random oracle a coin commutes past
every computation, so key generation draws all seeds first and then generates the keys from
them (`kcKeygenFrom`), a computation of hash queries only.

**The potential.** With the seeds fixed, a log `ℓ` *determines* key `i`'s parameter answer
`kcR a ℓ i` once it answers `a_i` and then `kcParamIn S_i`. The potential is
`kcPot = kcGlobPot + kcHidPot`:

* `kcGlobPot` charges the failure `KcGlob`: an answer equal to an earlier one, or naming the
  parameter input of an earlier input (`KcStep`), at most `2|ℓ|/2^256` per fresh query, paid in
  advance down to the cap `N`: `N(N-1)/2^256` in all;
* `kcHidPot` is `0` after a failure, and otherwise `kcCore`: the indicator of the bad event on the
  determined answers (`KcBad`: a zero parameter, or key `idx`'s equal to another one with another
  parameter input) plus `2^-128` per pending check (`kcPend`: a key not determined yet, and a pair
  with key `idx` not checked yet). A fresh answer at a parameter input settles the keys waiting on
  it: each check it settles fails with probability at most `2^-128` (`kc_sum_core_le`). A fresh
  answer at a seed input determines nothing new unless it fails (`KcStep`). Every other answer
  changes nothing.

So the potential does not rise in expectation (P1's engine, `kc_prEvent_le`), and starts at
`(2n - 1)/2^128 + Q(Q-1)/2^256` (`kcPot_nil_le`). At the end of key generation every key is
determined (`kcKeygenFrom_post`); a coincidence is then a failure, a bad event, or two keys with
the same seed input (`one_le_kcPot`), which the seeds avoid with probability at least
`1 - n/2^256` (`prEvent_kcColl_le`).

**The bound** (`prEvent_keygenPhase_keyCollAt_le`): `n/2^256 + (2n - 1)/2^128 + Q(Q-1)/2^256`,
at most `2n/2^128 + Q²/2^256` since `n ≤ Q` (every key generation makes a query). On the game
with V_I's trace (`prEvent_gameRec_keyCollAt_le`) the same: the rest keeps the keys.
-/

namespace LeanVM.E2E

open LeanVM.Parameters LeanVM.Semantics LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Rom
open OracleSpec OracleComp MeasureTheory
open scoped ENNReal

@[expose] public section

/- The enumeration of `Digest` must never be unfolded by unification. -/
attribute [local irreducible] instFintypeDigest

/-! ## Parameter inputs and parameters -/

/-- **The parameter derivation's input** at the scheme seed `S`: `0^16 ‖ A_param ‖ S`. -/
def kcParamIn (S : Digest) : Bytes := paramPrefix ++ LeanXmss.bytesLE 32 (digestBits S)

/-- **The parameter's bytes** from the parameter derivation's answer. -/
def kcParBytes (R : Digest) : Bytes :=
  LeanXmss.bytesLE 16 (LeanXmss.truncateHash (digestBits R))

theorem length_kcParamIn (S : Digest) : (kcParamIn S).length = 64 := by
  simp [kcParamIn, paramPrefix, LeanXmss.fieldBytes, LeanXmss.bytesLE]

theorem kcParamIn_injective : Function.Injective kcParamIn := fun _ _ h ↦
  digestBits_injective (Guest.Binding.bytesLE_inj (List.append_cancel_left h))

/-- A 256-bit vector is its two halves. -/
theorem bitVec256_ext {v w : BitVec 256} (h0 : v.extractLsb' 0 128 = w.extractLsb' 0 128)
    (h1 : v.extractLsb' 128 128 = w.extractLsb' 128 128) : v = w := by
  apply BitVec.eq_of_toNat_eq
  have e0 := congrArg BitVec.toNat h0
  have e1 := congrArg BitVec.toNat h1
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow] at e0 e1
  have hv := v.isLt
  have hw := w.isLt
  norm_num at e0 e1 hv hw ⊢
  omega

/-- An indicator sum is at most the size of a type it injects into. -/
theorem sum_ind_le_card_of_injOn {γ β : Type} [Fintype γ] [Fintype β] (p : γ → Prop) (f : γ → β)
    (hf : ∀ u u', p u → p u' → f u = f u' → u = u') :
    ∑ u, ind (p u) ≤ (Fintype.card β : ℝ≥0∞) := by
  classical
  have e : ∑ u, ind (p u) = ((Finset.univ.filter p).card : ℝ≥0∞) := by
    simp only [ind]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [e]
  have hc : (Finset.univ.filter p).card ≤ (Finset.univ : Finset β).card :=
    Finset.card_le_card_of_injOn f (fun _ _ ↦ Finset.mem_univ _) fun u hu u' hu' h ↦ by
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hu hu'
      exact hf u u' hu hu' h
  rw [Finset.card_univ] at hc
  exact_mod_cast hc

/-- **A parameter is hit by at most `2^128` answers.** -/
theorem kc_sum_parBytes_le (c : Bytes) : ∑ u : Digest, ind (kcParBytes u = c) ≤ 2 ^ 128 := by
  have h := sum_ind_le_card_of_injOn (fun u : Digest ↦ kcParBytes u = c)
    (fun u ↦ (digestBits u).extractLsb' 128 128) fun u u' hu hu' h ↦
      digestBits_injective (bitVec256_ext
        (Guest.Binding.bytesLE_inj (n := 16) (hu.trans hu'.symm)) h)
  have hcard : Fintype.card (BitVec 128) = 2 ^ 128 := by simp
  rw [hcard] at h
  exact_mod_cast h

/-! ## The bad event and the pending checks, on determined answers -/

section Core

variable {n : ℕ} (idx : Fin n)

/-- **The bad event** on determined parameter answers `r` (and parameter inputs `b`): a zero
parameter, or key `idx`'s parameter equal to another key's with another parameter input. -/
def KcBad (r : Fin n → Option Digest) (b : Fin n → Option Bytes) : Prop :=
  (∃ i R, r i = some R ∧ kcParBytes R = List.replicate 16 0) ∨
    ∃ i, i ≠ idx ∧ ∃ R R', r i = some R ∧ r idx = some R' ∧ b i ≠ b idx ∧
      kcParBytes R = kcParBytes R'

/-- **The pending checks**: a zero check per undetermined key, and a pair check per key other
than `idx` not checked against it yet (all `n - 1` while key `idx` is undetermined). -/
def kcPend (r : Fin n → Option Digest) : ℕ :=
  (Finset.univ.filter fun i ↦ r i = none).card +
    if r idx = none then n - 1 else (Finset.univ.filter fun i ↦ i ≠ idx ∧ r i = none).card

/-- **The potential before a failure**: the bad event, and `2^-128` per pending check. -/
noncomputable def kcCore (r : Fin n → Option Digest) (b : Fin n → Option Bytes) : ℝ≥0∞ :=
  ind (KcBad idx r b) + kcPend idx r * (2 ^ 128 : ℝ≥0∞)⁻¹

/-- The bad event reads the parameter inputs only of determined keys. -/
theorem kcBad_congr {r : Fin n → Option Digest} {b b' : Fin n → Option Bytes}
    (h : ∀ j, r j ≠ none → b' j = b j) : KcBad idx r b' ↔ KcBad idx r b := by
  unfold KcBad
  constructor
  · rintro (hz | ⟨i, hi, R, R', hR, hR', hb, hp⟩)
    · exact Or.inl hz
    · refine Or.inr ⟨i, hi, R, R', hR, hR', ?_, hp⟩
      rwa [← h i (by simp [hR]), ← h idx (by simp [hR'])]
  · rintro (hz | ⟨i, hi, R, R', hR, hR', hb, hp⟩)
    · exact Or.inl hz
    · refine Or.inr ⟨i, hi, R, R', hR, hR', ?_, hp⟩
      rwa [h i (by simp [hR]), h idx (by simp [hR'])]

theorem kcCore_congr {r : Fin n → Option Digest} {b b' : Fin n → Option Bytes}
    (h : ∀ j, r j ≠ none → b' j = b j) : kcCore idx r b' = kcCore idx r b := by
  unfold kcCore
  rw [show KcBad idx r b' = KcBad idx r b from propext (kcBad_congr idx h)]

/-- **Settling the keys at `x`**: after a fresh answer `u` at the input `x`, the keys whose
parameter input is `x` are determined, with answer `u`. -/
def kcSettle (r : Fin n → Option Digest) (b : Fin n → Option Bytes) (x : Bytes) (u : Digest) :
    Fin n → Option Digest :=
  fun j ↦ if b j = some x then some u else r j

variable {r : Fin n → Option Digest} {b : Fin n → Option Bytes} {x : Bytes}

/-- Settling keeps the determined answers. -/
theorem kcSettle_of_some (h : ∀ j, b j = some x → r j = none) (u : Digest) {j : Fin n}
    {R : Digest} (hR : r j = some R) : kcSettle r b x u j = some R := by
  have hb : b j ≠ some x := fun hb ↦ by simp [h j hb] at hR
  simp [kcSettle, hb, hR]

theorem kcSettle_eq_none_iff (u : Digest) (j : Fin n) :
    kcSettle r b x u j = none ↔ b j ≠ some x ∧ r j = none := by
  unfold kcSettle
  split <;> simp_all

/-- Settling keeps the bad event. -/
theorem kcBad_settle_of_kcBad (h : ∀ j, b j = some x → r j = none) (u : Digest)
    (hb : KcBad idx r b) : KcBad idx (kcSettle r b x u) b := by
  rcases hb with ⟨i, R, hR, hz⟩ | ⟨i, hi, R, R', hR, hR', hbne, hp⟩
  · exact Or.inl ⟨i, R, kcSettle_of_some h u hR, hz⟩
  · exact Or.inr ⟨i, hi, R, R', kcSettle_of_some h u hR, kcSettle_of_some h u hR', hbne, hp⟩

/-- The parameter of key `i` equals that of the answer `u`. -/
def KcHitAt (r : Fin n → Option Digest) (i : Fin n) (u : Digest) : Prop :=
  ∃ R, r i = some R ∧ kcParBytes u = kcParBytes R

/-- The keys other than `idx` determined before, not settled at `x`. -/
noncomputable def kcOld (r : Fin n → Option Digest) (b : Fin n → Option Bytes) (x : Bytes) :
    Finset (Fin n) :=
  Finset.univ.filter fun i ↦ i ≠ idx ∧ b i ≠ some x ∧ r i ≠ none

/-- **A new bad event at a settling answer**: a settled key's parameter is zero; key `idx` is
settled and its parameter is an old key's; or another key is settled and its parameter is key
`idx`'s. -/
theorem kcBad_settle (u : Digest) (hb : KcBad idx (kcSettle r b x u) b) :
    KcBad idx r b ∨ ((∃ j, b j = some x) ∧ kcParBytes u = List.replicate 16 0) ∨
      (b idx = some x ∧ ∃ i ∈ kcOld idx r b x, KcHitAt r i u) ∨
      (b idx ≠ some x ∧ (∃ j, b j = some x) ∧ KcHitAt r idx u) := by
  rcases hb with ⟨i, R, hR, hz⟩ | ⟨i, hi, R, R', hR, hR', hbne, hp⟩
  · by_cases hbi : b i = some x
    · simp only [kcSettle, hbi, ↓reduceIte, Option.some.injEq] at hR
      subst hR
      exact Or.inr (Or.inl ⟨⟨i, hbi⟩, hz⟩)
    · simp only [kcSettle, hbi, ↓reduceIte] at hR
      exact Or.inl (Or.inl ⟨i, R, hR, hz⟩)
  · by_cases hbi : b i = some x <;> by_cases hbx : b idx = some x
    · exact absurd (hbi.trans hbx.symm) hbne
    · simp only [kcSettle, hbi, hbx, ↓reduceIte, Option.some.injEq] at hR hR'
      subst hR
      exact Or.inr (Or.inr (Or.inr ⟨hbx, ⟨i, hbi⟩, R', hR', hp⟩))
    · simp only [kcSettle, hbi, hbx, ↓reduceIte, Option.some.injEq] at hR hR'
      subst hR'
      refine Or.inr (Or.inr (Or.inl ⟨hbx, i, ?_, R, hR, hp.symm⟩))
      simp [kcOld, hi, hbi, hR]
    · simp only [kcSettle, hbi, hbx, ↓reduceIte] at hR hR'
      exact Or.inl (Or.inr ⟨i, hi, R, R', hR, hR', hbne, hp⟩)

/-- A parameter hit has at most `2^128` answers. -/
theorem kc_sum_hitAt_le (i : Fin n) : ∑ u : Digest, ind (KcHitAt r i u) ≤ 2 ^ 128 := by
  rcases hr : r i with _ | R
  · simp [KcHitAt, hr, ind]
  · refine le_trans (le_of_eq ?_) (kc_sum_parBytes_le (kcParBytes R))
    refine Finset.sum_congr rfl fun u _ ↦ ?_
    simp [KcHitAt, hr]

/-- An indicator of a bounded existential is at most the sum of the indicators. -/
theorem ind_exists_finset_le {β : Type} (s : Finset β) (q : β → Prop) :
    ind (∃ i ∈ s, q i) ≤ ∑ i ∈ s, ind (q i) := by
  by_cases h : ∃ i ∈ s, q i
  · obtain ⟨i, hi, hq⟩ := h
    rw [ind_of ⟨i, hi, hq⟩]
    calc (1 : ℝ≥0∞) = ind (q i) := (ind_of hq).symm
      _ ≤ _ := Finset.single_le_sum (f := fun i ↦ ind (q i)) (fun _ _ ↦ bot_le) hi
  · rw [ind_of_not h]; exact bot_le

/-- The checks a settling answer pays for. -/
noncomputable def kcPaid (r : Fin n → Option Digest) (b : Fin n → Option Bytes) (x : Bytes) : ℕ :=
  (if ∃ j, b j = some x then 1 else 0) +
    if b idx = some x then (kcOld idx r b x).card
    else if (∃ j, b j = some x) ∧ r idx ≠ none then 1 else 0

open Classical in
/-- **The new bad events' answers** are at most `2^128` per paid check. -/
theorem kc_sum_newBad_le (r : Fin n → Option Digest) (b : Fin n → Option Bytes) (x : Bytes) :
    ∑ u : Digest, (ind ((∃ j, b j = some x) ∧ kcParBytes u = List.replicate 16 0) +
      ind (b idx = some x ∧ ∃ i ∈ kcOld idx r b x, KcHitAt r i u) +
      ind (b idx ≠ some x ∧ (∃ j, b j = some x) ∧ KcHitAt r idx u)) ≤
      kcPaid idx r b x * 2 ^ 128 := by
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have h1 : ∑ u : Digest, ind ((∃ j, b j = some x) ∧ kcParBytes u = List.replicate 16 0) ≤
      ((if ∃ j, b j = some x then 1 else 0 : ℕ) : ℝ≥0∞) * 2 ^ 128 := by
    by_cases hT : ∃ j, b j = some x
    · simpa [hT] using kc_sum_parBytes_le (List.replicate 16 0)
    · simp [hT, ind]
  have h2 : ∑ u : Digest, ind (b idx = some x ∧ ∃ i ∈ kcOld idx r b x, KcHitAt r i u) ≤
      ((if b idx = some x then (kcOld idx r b x).card else 0 : ℕ) : ℝ≥0∞) * 2 ^ 128 := by
    by_cases hx : b idx = some x
    · simp only [hx, true_and, ↓reduceIte]
      calc ∑ u : Digest, ind (∃ i ∈ kcOld idx r b x, KcHitAt r i u)
          ≤ ∑ u : Digest, ∑ i ∈ kcOld idx r b x, ind (KcHitAt r i u) :=
            Finset.sum_le_sum fun u _ ↦ ind_exists_finset_le _ _
        _ = ∑ i ∈ kcOld idx r b x, ∑ u : Digest, ind (KcHitAt r i u) := Finset.sum_comm
        _ ≤ ∑ i ∈ kcOld idx r b x, (2 ^ 128 : ℝ≥0∞) :=
            Finset.sum_le_sum fun i _ ↦ kc_sum_hitAt_le i
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
    · simp [hx, ind]
  have h3 : ∑ u : Digest, ind (b idx ≠ some x ∧ (∃ j, b j = some x) ∧ KcHitAt r idx u) ≤
      ((if b idx = some x then 0 else if (∃ j, b j = some x) ∧ r idx ≠ none then 1 else 0 : ℕ) :
        ℝ≥0∞) * 2 ^ 128 := by
    by_cases hx : b idx = some x
    · simp [hx, ind]
    by_cases hT : (∃ j, b j = some x) ∧ r idx ≠ none
    · rw [ite_eq_right hx, ite_eq_left hT, Nat.cast_one, one_mul]
      refine le_trans (Finset.sum_le_sum fun u _ ↦ ind_mono fun h ↦ h.2.2) (kc_sum_hitAt_le idx)
    · simp only [hx, ↓reduceIte, hT, Nat.cast_zero, zero_mul, nonpos_iff_eq_zero]
      refine Finset.sum_eq_zero fun u _ ↦ ind_of_not ?_
      rintro ⟨-, hj, R, hR, -⟩
      exact hT ⟨hj, by simp [hR]⟩
  calc _ ≤ _ := add_le_add (add_le_add h1 h2) h3
    _ = _ := by
      unfold kcPaid
      by_cases hx : b idx = some x <;> simp only [hx, ↓reduceIte] <;> push_cast <;> ring

/-- **The pending checks fall by the paid ones.** -/
theorem kcPend_settle_add_le (h : ∀ j, b j = some x → r j = none) (u : Digest) :
    kcPend idx (kcSettle r b x u) + kcPaid idx r b x ≤ kcPend idx r := by
  classical
  -- the zero checks
  have hz : (Finset.univ.filter fun i ↦ kcSettle r b x u i = none).card +
      (if ∃ j, b j = some x then 1 else 0) ≤ (Finset.univ.filter fun i ↦ r i = none).card := by
    have hsub : (Finset.univ.filter fun i ↦ kcSettle r b x u i = none) ⊆
        Finset.univ.filter fun i ↦ r i = none := by
      intro i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, kcSettle_eq_none_iff]
      exact And.right
    split
    · rename_i hT
      obtain ⟨j, hj⟩ := hT
      refine Finset.card_lt_card ⟨hsub, fun hs ↦ ?_⟩
      have := hs (Finset.mem_filter.mpr ⟨Finset.mem_univ j, h j hj⟩)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, kcSettle_eq_none_iff] at this
      exact this.1 hj
    · simpa using Finset.card_le_card hsub
  -- the pair checks
  have hp : (if kcSettle r b x u idx = none then n - 1 else
        (Finset.univ.filter fun i ↦ i ≠ idx ∧ kcSettle r b x u i = none).card) +
      (if b idx = some x then (kcOld idx r b x).card
        else if (∃ j, b j = some x) ∧ r idx ≠ none then 1 else 0) ≤
      (if r idx = none then n - 1 else
        (Finset.univ.filter fun i ↦ i ≠ idx ∧ r i = none).card) := by
    have hsub : (Finset.univ.filter fun i ↦ i ≠ idx ∧ kcSettle r b x u i = none) ⊆
        Finset.univ.filter fun i ↦ i ≠ idx ∧ r i = none := by
      intro i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, kcSettle_eq_none_iff]
      exact fun hi ↦ ⟨hi.1, hi.2.2⟩
    by_cases hx : b idx = some x
    · have hr : r idx = none := h idx hx
      have hs : kcSettle r b x u idx ≠ none := by simp [kcSettle, hx]
      simp only [hs, hr, hx, ↓reduceIte]
      have hdisj : Disjoint (Finset.univ.filter fun i ↦ i ≠ idx ∧ kcSettle r b x u i = none)
          (kcOld idx r b x) := by
        rw [Finset.disjoint_left]
        intro i hi hi'
        simp only [kcOld, Finset.mem_filter, Finset.mem_univ, true_and,
          kcSettle_eq_none_iff] at hi hi'
        exact hi'.2.2 hi.2.2
      rw [← Finset.card_union_of_disjoint hdisj]
      have hu : (Finset.univ.filter fun i ↦ i ≠ idx ∧ kcSettle r b x u i = none) ∪
          kcOld idx r b x ⊆ Finset.univ.erase idx := by
        intro i hi
        simp only [kcOld, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hi
        exact Finset.mem_erase.mpr ⟨by rcases hi with hi | hi <;> exact hi.1, Finset.mem_univ _⟩
      refine (Finset.card_le_card hu).trans (le_of_eq ?_)
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    · have hs : kcSettle r b x u idx = r idx := by simp [kcSettle, hx]
      rw [hs]
      simp only [hx, ↓reduceIte]
      by_cases hr : r idx = none
      · simp [hr]
      · simp only [hr, ↓reduceIte]
        split
        · rename_i hT
          obtain ⟨⟨j, hj⟩, -⟩ := hT
          refine Finset.card_lt_card ⟨hsub, fun hs' ↦ ?_⟩
          have hji : j ≠ idx := fun e ↦ hx (e ▸ hj)
          have := hs' (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hji, h j hj⟩)
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, kcSettle_eq_none_iff] at this
          exact this.2.1 hj
        · simpa using Finset.card_le_card hsub
  unfold kcPend kcPaid
  omega

/-- `2^256 · 2^-128 = 2^128`. -/
theorem two_pow_256_mul_inv : (2 ^ 256 : ℝ≥0∞) * (2 ^ 128 : ℝ≥0∞)⁻¹ = 2 ^ 128 := by
  rw [show (2 ^ 256 : ℝ≥0∞) = 2 ^ 128 * 2 ^ 128 by norm_num, mul_assoc,
    ENNReal.mul_inv_cancel (by simp) (by simp), mul_one]

/-- A sum over the digests of a constant. -/
theorem sum_digest_const (c : ℝ≥0∞) : ∑ _u : Digest, c = 2 ^ 256 * c := by
  rw [Finset.sum_const, Finset.card_univ, card_digest, nsmul_eq_mul]
  norm_num

/-- **The core is a supermartingale at a settling answer.** -/
theorem kc_sum_core_le (h : ∀ j, b j = some x → r j = none) :
    ∑ u : Digest, kcCore idx (kcSettle r b x u) b ≤ 2 ^ 256 * kcCore idx r b := by
  have hpend := kcPend_settle_add_le idx h
  by_cases hbad : KcBad idx r b
  · calc ∑ u : Digest, kcCore idx (kcSettle r b x u) b
        ≤ ∑ _u : Digest, kcCore idx r b := by
          refine Finset.sum_le_sum fun u _ ↦ ?_
          unfold kcCore
          rw [ind_of (kcBad_settle_of_kcBad idx h u hbad), ind_of hbad]
          gcongr
          exact (Nat.le_add_right _ _).trans (hpend u)
      _ = _ := sum_digest_const _
  · have hpt : ∀ u, kcCore idx (kcSettle r b x u) b ≤
        (ind ((∃ j, b j = some x) ∧ kcParBytes u = List.replicate 16 0) +
          ind (b idx = some x ∧ ∃ i ∈ kcOld idx r b x, KcHitAt r i u) +
          ind (b idx ≠ some x ∧ (∃ j, b j = some x) ∧ KcHitAt r idx u)) +
        ((kcPend idx r - kcPaid idx r b x : ℕ) : ℝ≥0∞) * (2 ^ 128 : ℝ≥0∞)⁻¹ := by
      intro u
      unfold kcCore
      gcongr
      · refine (ind_mono (kcBad_settle idx u)).trans ?_
        refine (ind_or_le _ _).trans ?_
        rw [ind_of_not hbad, zero_add]
        refine (ind_or_le _ _).trans ?_
        rw [add_assoc]
        exact add_le_add le_rfl (ind_or_le _ _)
      · have := hpend u
        omega
    calc ∑ u : Digest, kcCore idx (kcSettle r b x u) b
        ≤ ∑ u : Digest, ((ind ((∃ j, b j = some x) ∧ kcParBytes u = List.replicate 16 0) +
          ind (b idx = some x ∧ ∃ i ∈ kcOld idx r b x, KcHitAt r i u) +
          ind (b idx ≠ some x ∧ (∃ j, b j = some x) ∧ KcHitAt r idx u)) +
          ((kcPend idx r - kcPaid idx r b x : ℕ) : ℝ≥0∞) * (2 ^ 128 : ℝ≥0∞)⁻¹) :=
          Finset.sum_le_sum fun u _ ↦ hpt u
      _ ≤ kcPaid idx r b x * 2 ^ 128 +
          2 ^ 256 * (((kcPend idx r - kcPaid idx r b x : ℕ) : ℝ≥0∞) * (2 ^ 128 : ℝ≥0∞)⁻¹) := by
          rw [Finset.sum_add_distrib, sum_digest_const]
          exact add_le_add (kc_sum_newBad_le idx r b x) le_rfl
      _ = 2 ^ 256 * kcCore idx r b := by
          have hle : kcPaid idx r b x ≤ kcPend idx r := (Nat.le_add_left _ _).trans (hpend 0)
          unfold kcCore
          rw [ind_of_not hbad, zero_add,
            mul_left_comm (2 ^ 256 : ℝ≥0∞) ((kcPend idx r - kcPaid idx r b x : ℕ) : ℝ≥0∞),
            two_pow_256_mul_inv, mul_left_comm (2 ^ 256 : ℝ≥0∞) (kcPend idx r : ℝ≥0∞),
            two_pow_256_mul_inv, ← add_mul, ← Nat.cast_add, Nat.add_sub_cancel' hle]

end Core


/-! ## The failure -/

/-- **A failing fresh answer** `u` after the log `ℓ`: an earlier answer, or the parameter input it
names is an earlier input. -/
def KcStep (ℓ : Log) (u : Digest) : Prop := (∃ e ∈ ℓ, e.2 = u) ∨ ∃ e ∈ ℓ, e.1 = kcParamIn u

/-- **Some entry of the log failed** with respect to the entries before it. -/
def KcGlob (ℓ : Log) : Prop := ∃ (k : ℕ) (hk : k < ℓ.length), KcStep (ℓ.take k) ℓ[k].2

/-- The log with one more entry fails exactly if the log fails or the entry does. -/
theorem kcGlob_append (ℓ : Log) (t : Bytes) (u : Digest) :
    KcGlob (ℓ ++ [(t, u)]) ↔ KcGlob ℓ ∨ KcStep ℓ u := by
  constructor
  · rintro ⟨i, hi, h⟩
    rw [List.length_append, List.length_singleton] at hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
    · left
      refine ⟨i, hi', ?_⟩
      rwa [List.getElem_append_left hi', List.take_append_of_le_length hi'.le] at h
    · right
      simpa using h
  · rintro (⟨i, hi, h⟩ | h)
    · refine ⟨i, by simp; omega, ?_⟩
      rwa [List.getElem_append_left hi, List.take_append_of_le_length hi.le]
    · exact ⟨ℓ.length, by simp, by simpa using h⟩

theorem not_kcGlob_nil : ¬ KcGlob [] := fun ⟨_, hi, _⟩ ↦ by simp at hi

/-- **A fresh answer fails for at most `2|ℓ|` digests.** -/
theorem kc_sum_step_le (ℓ : Log) : ∑ u : Digest, ind (KcStep ℓ u) ≤ 2 * ℓ.length := by
  have hpt : ∀ u, ind (KcStep ℓ u) ≤
      (ℓ.map fun e ↦ ind (e.2 = u)).sum + (ℓ.map fun e ↦ ind (e.1 = kcParamIn u)).sum := fun u ↦
    (ind_or_le _ _).trans (add_le_add (ind_exists_le _ _) (ind_exists_le _ _))
  calc ∑ u : Digest, ind (KcStep ℓ u)
      ≤ ∑ u : Digest, ((ℓ.map fun e ↦ ind (e.2 = u)).sum +
          (ℓ.map fun e ↦ ind (e.1 = kcParamIn u)).sum) := Finset.sum_le_sum fun u _ ↦ hpt u
    _ = (ℓ.map fun e ↦ ∑ u : Digest, ind (e.2 = u)).sum +
          (ℓ.map fun e ↦ ∑ u : Digest, ind (e.1 = kcParamIn u)).sum := by
        rw [Finset.sum_add_distrib, sum_list_sum_comm, sum_list_sum_comm]
    _ ≤ ℓ.length * 1 + ℓ.length * 1 := by
        refine add_le_add (list_sum_le _ _ _ fun e _ ↦ ?_) (list_sum_le _ _ _ fun e _ ↦ ?_)
        · exact sum_ind_le_one fun u u' hu hu' ↦ hu.symm.trans hu'
        · exact sum_ind_le_one fun u u' hu hu' ↦ kcParamIn_injective (hu.symm.trans hu')
    _ = 2 * ℓ.length := by ring

/-- **Two inputs with one answer fail.** -/
theorem kcGlob_of_look {ℓ : Log} {y y' : Bytes} {S : Digest} (h : look ℓ y = some S)
    (h' : look ℓ y' = some S) (hne : y ≠ y') : KcGlob ℓ := by
  obtain ⟨i, hi, hei, -⟩ := (look_eq_some_iff ℓ y S).mp h
  obtain ⟨i', hi', hei', -⟩ := (look_eq_some_iff ℓ y' S).mp h'
  have key : ∀ (j j' : ℕ) (hj : j < ℓ.length) (hj' : j' < ℓ.length), j < j' →
      ℓ[j].2 = S → ℓ[j'].2 = S → KcGlob ℓ := by
    intro j j' hj hj' hlt e e'
    refine ⟨j', hj', Or.inl ⟨ℓ[j], ?_, e.trans e'.symm⟩⟩
    rw [List.mem_iff_getElem]
    exact ⟨j, by simp; omega, by simp⟩
  rcases lt_trichotomy i i' with hlt | rfl | hgt
  · exact key i i' hi hi' hlt (by rw [hei]) (by rw [hei'])
  · exact absurd (by rw [hei] at hei'; exact (Prod.mk.inj hei').1) hne
  · exact key i' i hi' hi hgt (by rw [hei']) (by rw [hei])

/-! ## The keys a log determines -/

section Log

variable {n : ℕ} (a : Fin n → Bytes) (idx : Fin n)

/-- **Key `i`'s parameter answer**, once the log answers its seed input `a i` with `S`, then
`kcParamIn S`. -/
def kcR (ℓ : Log) (i : Fin n) : Option Digest :=
  (look ℓ (a i)).bind fun S ↦ look ℓ (kcParamIn S)

/-- **Key `i`'s parameter input**, once the log answers its seed input. -/
def kcB (ℓ : Log) (i : Fin n) : Option Bytes := (look ℓ (a i)).map kcParamIn

open Classical in
/-- **The potential of the hidden part**: `0` after a failure, otherwise the core. -/
noncomputable def kcHidPot (ℓ : Log) : ℝ≥0∞ :=
  if KcGlob ℓ then 0 else kcCore idx (kcR a ℓ) (kcB a ℓ)

/-- **The potential of the failure**, its future rises paid in advance up to `N` entries. -/
noncomputable def kcGlobPot (N : ℕ) (ℓ : Log) : ℝ≥0∞ :=
  ind (KcGlob ℓ) + ((N * (N - 1) - ℓ.length * (ℓ.length - 1) : ℕ) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹

/-- **The potential.** -/
noncomputable def kcPot (N : ℕ) (ℓ : Log) : ℝ≥0∞ := kcGlobPot N ℓ + kcHidPot a idx ℓ

theorem two_pow_256_mul_inv_self : (2 ^ 256 : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹ = 1 :=
  ENNReal.mul_inv_cancel (by simp) (by simp)

/-- **The failure's potential does not rise** below the cap. -/
theorem kc_sum_globPot_le (N : ℕ) (ℓ : Log) (hN : ℓ.length < N) (x : Bytes) :
    ∑ u : Digest, kcGlobPot N (ℓ ++ [(x, u)]) ≤ 2 ^ 256 * kcGlobPot N ℓ := by
  set m := ℓ.length with hm
  have hl : ∀ u : Digest, (ℓ ++ [(x, u)]).length = m + 1 := fun u ↦ by simp [hm]
  have hc : N * (N - 1) - m * (m - 1) = 2 * m + (N * (N - 1) - (m + 1) * (m + 1 - 1)) := by
    have hB : (m + 1) * (m + 1 - 1) ≤ N * (N - 1) := Nat.mul_le_mul (by omega) (by omega)
    have hAB : (m + 1) * (m + 1 - 1) = m * (m - 1) + 2 * m := by
      rcases m with _ | m
      · simp
      · simp only [Nat.add_sub_cancel]; ring_nf
    omega
  calc ∑ u : Digest, kcGlobPot N (ℓ ++ [(x, u)])
      ≤ ∑ u : Digest, (ind (KcGlob ℓ) + ind (KcStep ℓ u) +
          ((N * (N - 1) - (m + 1) * (m + 1 - 1) : ℕ) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹) := by
        refine Finset.sum_le_sum fun u _ ↦ ?_
        unfold kcGlobPot
        rw [hl u]
        gcongr
        rw [show KcGlob (ℓ ++ [(x, u)]) = (KcGlob ℓ ∨ KcStep ℓ u) from
          propext (kcGlob_append ℓ x u)]
        exact ind_or_le _ _
    _ ≤ 2 ^ 256 * ind (KcGlob ℓ) + 2 * m +
          ((N * (N - 1) - (m + 1) * (m + 1 - 1) : ℕ) : ℝ≥0∞) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, sum_digest_const, sum_digest_const,
          mul_left_comm, two_pow_256_mul_inv_self, mul_one]
        gcongr
        exact kc_sum_step_le ℓ
    _ = 2 ^ 256 * kcGlobPot N ℓ := by
        unfold kcGlobPot
        rw [← hm, hc, mul_add, mul_left_comm, two_pow_256_mul_inv_self, mul_one, add_assoc]
        push_cast
        ring

variable {a}

/-- One entry more: a lookup elsewhere is unchanged. -/
theorem look_append_fresh_ne {ℓ : Log} {x y : Bytes} (u : Digest) (h : y ≠ x) :
    look (ℓ ++ [(x, u)]) y = look ℓ y :=
  look_append_single_of_ne h u

theorem look_append_fresh_self {ℓ : Log} {x : Bytes} (hx : look ℓ x = none) (u : Digest) :
    look (ℓ ++ [(x, u)]) x = some u :=
  look_append_single_self hx u

/-- **An answer elsewhere than a seed input settles the keys at it.** -/
theorem kcR_append_of_ne (ℓ : Log) {x : Bytes} (hx : look ℓ x = none) (hax : ∀ i, a i ≠ x)
    (u : Digest) :
    kcR a (ℓ ++ [(x, u)]) = kcSettle (kcR a ℓ) (kcB a ℓ) x u ∧
      kcB a (ℓ ++ [(x, u)]) = kcB a ℓ := by
  refine ⟨funext fun j ↦ ?_, funext fun j ↦ ?_⟩
  · unfold kcR kcSettle kcB
    rw [look_append_fresh_ne u (hax j)]
    rcases hS : look ℓ (a j) with _ | S
    · simp [hS]
    · simp only [hS, Option.bind_some, Option.map_some, Option.some.injEq]
      by_cases hSx : kcParamIn S = x
      · rw [ite_eq_left hSx, hSx, look_append_fresh_self hx]
      · rw [ite_eq_right hSx, look_append_fresh_ne u hSx]
  · unfold kcB
    rw [look_append_fresh_ne u (hax j)]

/-- **An answer at a seed input settles nothing**, unless it fails. -/
theorem kcR_append_of_eq (ha : ∀ i, (a i).length ≠ 64) (ℓ : Log) {x : Bytes}
    (hx : look ℓ x = none) (hax : ∃ i, a i = x) (u : Digest) (hs : ¬ KcStep ℓ u) :
    kcR a (ℓ ++ [(x, u)]) = kcR a ℓ ∧
      ∀ j, kcR a ℓ j ≠ none → kcB a (ℓ ++ [(x, u)]) j = kcB a ℓ j := by
  obtain ⟨i, rfl⟩ := hax
  have hne : ∀ S, kcParamIn S ≠ a i := fun S e ↦ ha i (e ▸ length_kcParamIn S)
  refine ⟨funext fun j ↦ ?_, fun j hj ↦ ?_⟩
  · unfold kcR
    by_cases hj : a j = a i
    · rw [hj, hx, look_append_fresh_self hx]
      simp only [Option.bind_some, Option.bind_none]
      rw [look_append_fresh_ne u (hne u), look, logLookup_eq_none_iff]
      intro hm
      obtain ⟨e, he, he1⟩ := List.mem_map.mp hm
      exact hs (Or.inr ⟨e, he, he1⟩)
    · rw [look_append_fresh_ne u hj]
      rcases look ℓ (a j) with _ | S
      · rfl
      · simp only [Option.bind_some]
        rw [look_append_fresh_ne u (hne S)]
  · have hj' : a j ≠ a i := by
      intro e
      apply hj
      unfold kcR
      rw [e, hx]
      rfl
    unfold kcB
    rw [look_append_fresh_ne u hj']

/-- **The hidden part's potential does not rise.** -/
theorem kc_sum_hidPot_le (ha : ∀ i, (a i).length ≠ 64) (ℓ : Log) {x : Bytes}
    (hx : look ℓ x = none) :
    ∑ u : Digest, kcHidPot a idx (ℓ ++ [(x, u)]) ≤ 2 ^ 256 * kcHidPot a idx ℓ := by
  by_cases hg : KcGlob ℓ
  · have h0 : ∀ u : Digest, kcHidPot a idx (ℓ ++ [(x, u)]) = 0 := fun u ↦ by
      unfold kcHidPot
      rw [ite_eq_left ((kcGlob_append ℓ x u).mpr (Or.inl hg))]
    simp [h0]
  · have hpot : kcHidPot a idx ℓ = kcCore idx (kcR a ℓ) (kcB a ℓ) := by
      unfold kcHidPot; rw [ite_eq_right hg]
    rw [hpot]
    by_cases hax : ∃ i, a i = x
    · calc ∑ u : Digest, kcHidPot a idx (ℓ ++ [(x, u)])
          ≤ ∑ _u : Digest, kcCore idx (kcR a ℓ) (kcB a ℓ) := by
            refine Finset.sum_le_sum fun u _ ↦ ?_
            unfold kcHidPot
            split
            · exact bot_le
            · rename_i hg'
              have hs : ¬ KcStep ℓ u := fun hs ↦ hg' ((kcGlob_append ℓ x u).mpr (Or.inr hs))
              obtain ⟨hR, hB⟩ := kcR_append_of_eq ha ℓ hx hax u hs
              rw [hR, kcCore_congr idx hB]
        _ = _ := sum_digest_const _
    · push Not at hax
      calc ∑ u : Digest, kcHidPot a idx (ℓ ++ [(x, u)])
          ≤ ∑ u : Digest, kcCore idx (kcSettle (kcR a ℓ) (kcB a ℓ) x u) (kcB a ℓ) := by
            refine Finset.sum_le_sum fun u _ ↦ ?_
            obtain ⟨hR, hB⟩ := kcR_append_of_ne ℓ hx hax u
            unfold kcHidPot
            split
            · exact bot_le
            · rw [hR, hB]
        _ ≤ _ := by
            refine kc_sum_core_le idx fun j hj ↦ ?_
            unfold kcR
            unfold kcB at hj
            rcases hS : look ℓ (a j) with _ | S
            · rfl
            · rw [hS, Option.map_some, Option.some.injEq] at hj
              simp only [Option.bind_some, hj, hx]

/-- **The potential at the empty log**: the failure's advance and the pending checks. -/
theorem kcPot_nil_le (N : ℕ) :
    kcPot a idx N [] ≤ ((2 * n - 1 : ℕ) : ℝ≥0∞) * (2 ^ 128 : ℝ≥0∞)⁻¹ +
      ((N * (N - 1) : ℕ) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  have hR : kcR a [] = fun _ ↦ none := funext fun _ ↦ rfl
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) idx.isLt
  unfold kcPot kcGlobPot kcHidPot
  rw [ind_of_not not_kcGlob_nil, ite_eq_right not_kcGlob_nil, hR]
  have hp : kcPend idx (fun _ : Fin n ↦ (none : Option Digest)) = 2 * n - 1 := by
    unfold kcPend; simp; omega
  unfold kcCore
  rw [hp]
  have hb : ¬ KcBad idx (fun _ : Fin n ↦ (none : Option Digest)) (kcB a []) := by
    rintro (⟨_, _, h, -⟩ | ⟨_, -, _, _, h, -⟩) <;> exact absurd h (by simp)
  rw [ind_of_not hb]
  simp only [List.length_nil, zero_mul, Nat.sub_zero, zero_add]
  rw [add_comm]

/-- **The event forces the potential**: when the log determines every key (`hdet`) and no two
keys share a seed input, a coincidence of key `idx`'s parameters `P` is a failure or a bad
event. -/
theorem one_le_kcPot (N : ℕ) {ℓ : Log} {P : Fin n → Bytes}
    (hdet : ∀ i, ∃ S R, look ℓ (a i) = some S ∧ look ℓ (kcParamIn S) = some R ∧
      P i = kcParBytes R)
    (hseed : ∀ i, i ≠ idx → a i ≠ a idx)
    (hev : (∃ i, i ≠ idx ∧ P i = P idx) ∨ ∃ i, P i = List.replicate 16 0) :
    1 ≤ kcPot a idx N ℓ := by
  by_cases hg : KcGlob ℓ
  · exact le_add_right (le_add_right (ind_of hg).ge)
  refine le_add_left ?_
  unfold kcHidPot
  rw [ite_eq_right hg]
  refine le_add_right (ind_of ?_).ge
  have hR : ∀ i, ∃ S R, kcR a ℓ i = some R ∧ kcB a ℓ i = some (kcParamIn S) ∧
      look ℓ (a i) = some S ∧ P i = kcParBytes R := by
    intro i
    obtain ⟨S, R, hS, hR, hP⟩ := hdet i
    exact ⟨S, R, by simp [kcR, hS, hR], by simp [kcB, hS], hS, hP⟩
  rcases hev with ⟨i, hi, hP⟩ | ⟨i, hz⟩
  · obtain ⟨S, R, hRi, hBi, hSi, hPi⟩ := hR i
    obtain ⟨S', R', hRx, hBx, hSx, hPx⟩ := hR idx
    refine Or.inr ⟨i, hi, R, R', hRi, hRx, ?_, by rw [← hPi, ← hPx, hP]⟩
    rw [hBi, hBx]
    intro he
    have hSS : S = S' := kcParamIn_injective (Option.some.inj he)
    subst hSS
    exact hg (kcGlob_of_look hSi hSx (hseed i hi))
  · obtain ⟨S, R, hRi, -, -, hPi⟩ := hR i
    exact Or.inl ⟨i, R, hRi, hPi ▸ hz⟩

/-- **The potential bound on a run from the empty log**: a computation of the game with at most
`Q` hash queries, an event forcing the potential at the end. -/
theorem kc_prEvent_le (ha : ∀ i, (a i).length ≠ 64) {α : Type} (oa : OracleComp GameSpec α)
    (Q : ℕ) (hQ : IsQueryBoundP oa IsHash Q) (ev : α → Log → Prop)
    (hev : ∀ z ∈ support ((simulateQ gameImpl oa).run []), ev z.1 z.2 → 1 ≤ kcPot a idx Q z.2) :
    Pr{let z ← (simulateQ gameImpl oa).run []}[ev z.1 z.2] ≤ kcPot a idx Q [] := by
  have h := prEvent_run_le_twoRate gameImpl_isLazySampler IsHash IsHash (fun _ h ↦ h)
    (Φ := kcPot a idx Q) (δp := 0) (δq := 0) List.length Q ?_ ?_ ?_ ?_ ?_ oa Q Q hQ hQ [] (by simp)
    ev hev
  · simpa using h
  · rintro ℓ (n | x) u hq _
    · exact absurd hq id
    · simp [gameRecord]
  · rintro ℓ (n | x) u hq _
    · simp [gameRecord]
    · exact absurd trivial hq
  · rintro ℓ (n | x) hN hp hn
    · exact absurd hp id
    · change (∑ u : Digest, kcPot a idx Q (ℓ ++ [(x, u)])) / Fintype.card Digest ≤ _ + 0
      rw [add_zero, card_digest]
      refine ENNReal.div_le_of_le_mul ?_
      have hx : look ℓ x = none := hn
      calc ∑ u : Digest, kcPot a idx Q (ℓ ++ [(x, u)])
          = ∑ u : Digest, kcGlobPot Q (ℓ ++ [(x, u)]) +
              ∑ u : Digest, kcHidPot a idx (ℓ ++ [(x, u)]) := Finset.sum_add_distrib
        _ ≤ 2 ^ 256 * kcGlobPot Q ℓ + 2 ^ 256 * kcHidPot a idx ℓ :=
            add_le_add (kc_sum_globPot_le Q ℓ hN x) (kc_sum_hidPot_le idx ha ℓ hx)
        _ = _ := by rw [← mul_add, mul_comm]; norm_num [kcPot]
  · rintro ℓ (n | x) _ hq hp _
    · exact absurd hq id
    · exact absurd trivial hp
  · rintro ℓ (n | x) hq _
    · exact (sum_gameRecord_coin _ ℓ n).le
    · exact absurd trivial hq

end Log


/-! ## What a run of key generation leaves in the log -/

section Runs

variable {nx ns : ℕ}

/-- **A run extends the log.** -/
theorem prefix_of_mem_support_run {α : Type} (oa : OracleComp GameSpec α) (ℓ : Log)
    {z : α × Log} (hz : z ∈ support ((simulateQ gameImpl oa).run ℓ)) : ℓ <+: z.2 := by
  induction oa using OracleComp.inductionOn generalizing ℓ with
  | pure x =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    rw [hz]
  | query_bind t k ih =>
    rw [simulateQ_query_bind, StateT.run_bind] at hz
    simp only [OracleQuery.input_query, monadLift_self] at hz
    change z ∈ support ((gameImpl t).run ℓ >>= fun p ↦ (simulateQ gameImpl (k p.1)).run p.2)
      at hz
    rw [gameImpl_isLazySampler t ℓ, mem_support_bind_iff] at hz
    obtain ⟨p, hp, hz⟩ := hz
    refine List.IsPrefix.trans ?_ (ih p.1 p.2 hz)
    split at hp
    · simp only [support_pure, Set.mem_singleton_iff] at hp
      rw [hp]
    · rw [mem_support_bind_iff] at hp
      obtain ⟨u, -, hp⟩ := hp
      simp only [support_pure, Set.mem_singleton_iff] at hp
      rw [hp]
      rcases t with n | x
      · exact List.prefix_rfl
      · exact List.prefix_append _ _

/-- A run of `pure`. -/
theorem mem_support_run_pure {α : Type} (a : α) (st : SignState nx ns) (ℓ : Log)
    {z : (α × SignState nx ns) × Log}
    (hz : z ∈ support ((simulateQ gameImpl ((pure a : GameM nx ns α).run st)).run ℓ)) :
    z = ((a, st), ℓ) := by
  simpa using hz

/-- **A hash query's answer is the log's.** -/
theorem look_of_mem_support_hashQuery (x : Bytes) (st : SignState nx ns) (ℓ : Log)
    {z : (Digest × SignState nx ns) × Log}
    (hz : z ∈ support ((simulateQ gameImpl ((hashQuery x : GameM nx ns Digest).run st)).run ℓ)) :
    look z.2 x = some z.1.1 := by
  unfold hashQuery at hz
  change z ∈ support ((simulateQ gameImpl ((liftM (liftM (GameSpec.query (.inr x)) :
    OracleComp GameSpec Digest) : GameM nx ns Digest).run st)).run ℓ) at hz
  rw [OracleComp.liftM_run_StateT, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨p, hp, hz⟩ := hz
  simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  subst hz
  rw [simulateQ_spec_query] at hp
  change p ∈ support ((gameImpl (.inr x)).run ℓ) at hp
  rw [gameImpl_isLazySampler] at hp
  simp only [gameLookup, gameRecord] at hp
  rcases h : look ℓ x with _ | v
  · rw [h] at hp
    rw [mem_support_bind_iff] at hp
    obtain ⟨u, -, hp⟩ := hp
    simp only [support_pure, Set.mem_singleton_iff] at hp
    subst hp
    exact look_append_single_self h u
  · rw [h] at hp
    simp only [support_pure, Set.mem_singleton_iff] at hp
    subst hp
    exact h

/-- The parameter derivation's input in leanXMSS. -/
theorem xmss_keygenHashInput_parameter (u : Digest) :
    LeanXmss.keygenHashInput 0 .parameter (digestBits u) = kcParamIn u := by
  have h0 : LeanXmss.bytesLE 16 (0 : LeanXmss.PublicParameter) = List.replicate 16 0 := by decide
  unfold LeanXmss.keygenHashInput kcParamIn paramPrefix
  simp only [h0]

/-- leanXMSS key generation, query by query. -/
theorem kc_xmss_keygenFromSeed_eq (s : LeanXmss.MasterSeed) :
    LeanXmss.Seeded.keygenFromSeed s =
      (liftM (LeanXmss.HashSpec.query (LeanXmss.seedHashInput s)) :
        OracleComp LeanXmss.HashSpec _) >>= fun S ↦
      (liftM (LeanXmss.HashSpec.query (LeanXmss.keygenHashInput 0 .parameter S)) :
        OracleComp LeanXmss.HashSpec _) >>= fun R ↦
      LeanXmss.Seeded.treeNode (LeanXmss.truncateHash R) LeanXmss.topLayer S
        LeanXmss.layerHeight 0 >>= fun root ↦
      pure (⟨root, LeanXmss.truncateHash R⟩, ⟨S, LeanXmss.truncateHash R, root⟩) := rfl

/-- leanSPHINCS key generation, query by query. -/
theorem kc_sphincs_keygenFromSeed_eq [Sphincs.Params] (s : Sphincs.MasterSeed) :
    Sphincs.Seeded.keygenFromSeed s =
      (liftM (Sphincs.HashSpec.query (Sphincs.schemeSeedInput s)) :
        OracleComp Sphincs.HashSpec _) >>= fun S ↦
      (liftM (Sphincs.HashSpec.query (Sphincs.keygenHashInput 0 .parameter S)) :
        OracleComp Sphincs.HashSpec _) >>= fun R ↦
      Sphincs.Seeded.treeRoot (Sphincs.truncateHash R) Sphincs.topLayer
        Sphincs.Concrete.rootTree S >>= fun root ↦
      pure (⟨root, Sphincs.truncateHash R⟩, ⟨S, Sphincs.truncateHash R, root⟩) := rfl

/-- A key generation makes a query. -/
theorem one_le_of_xmss_keygen {cxk : ℕ}
    (hxk : ∀ seed, IsTotalQueryBound (LeanXmss.Seeded.keygenFromSeed seed) cxk) : 1 ≤ cxk := by
  have h := hxk 0
  rw [kc_xmss_keygenFromSeed_eq] at h
  exact (isTotalQueryBound_query_bind_iff.mp h).1

theorem one_le_of_sphincs_keygen [Sphincs.Params] {csk : ℕ}
    (hsk : ∀ seed, IsTotalQueryBound (Sphincs.Seeded.keygenFromSeed seed) csk) : 1 ≤ csk := by
  have h := hsk 0
  rw [kc_sphincs_keygenFromSeed_eq] at h
  exact (isTotalQueryBound_query_bind_iff.mp h).1

/-- **leanXMSS key generation, run.** -/
theorem xmssRun_keygenFromSeed_eq (s : LeanXmss.MasterSeed) :
    (xmssRun (LeanXmss.Seeded.keygenFromSeed s) : GameM nx ns _) =
      (digestBits <$> hashQuery (LeanXmss.seedHashInput s)) >>= fun S ↦
        (digestBits <$> hashQuery (LeanXmss.keygenHashInput 0 .parameter S)) >>= fun R ↦
          xmssRun (LeanXmss.Seeded.treeNode (LeanXmss.truncateHash R)
            LeanXmss.topLayer S LeanXmss.layerHeight 0) >>= fun root ↦
            pure (⟨root, LeanXmss.truncateHash R⟩, ⟨S, LeanXmss.truncateHash R, root⟩) := by
  rw [kc_xmss_keygenFromSeed_eq]
  simp only [xmssRun, simulateQ_bind, simulateQ_pure, simulateQ_spec_query]
  rfl

theorem sphincs_keygenHashInput_parameter (u : Digest) :
    Sphincs.keygenHashInput 0 .parameter (digestBits u) = kcParamIn u := by
  have h0 : Sphincs.bytesLE 16 (0 : Sphincs.PublicParameter) = List.replicate 16 0 := by decide
  unfold Sphincs.keygenHashInput kcParamIn
  rw [paramPrefix_eq_sphincs]
  simp only [h0]
  rfl

/-- **leanSPHINCS key generation, run.** -/
theorem sphincsRun_keygenFromSeed_eq [Sphincs.Params] (s : Sphincs.MasterSeed) :
    (sphincsRun (Sphincs.Seeded.keygenFromSeed s) : GameM nx ns _) =
      (digestBits <$> hashQuery (Sphincs.schemeSeedInput s)) >>= fun S ↦
        (digestBits <$> hashQuery (Sphincs.keygenHashInput 0 .parameter S)) >>= fun R ↦
          sphincsRun (Sphincs.Seeded.treeRoot (Sphincs.truncateHash R)
            Sphincs.topLayer Sphincs.Concrete.rootTree S) >>= fun root ↦
            pure (⟨root, Sphincs.truncateHash R⟩, ⟨S, Sphincs.truncateHash R, root⟩) := by
  rw [kc_sphincs_keygenFromSeed_eq]
  simp only [sphincsRun, simulateQ_bind, simulateQ_pure, simulateQ_spec_query]
  rfl

/-- A run of a map. -/
theorem mem_support_run_map {α β : Type} (f : α → β) (x : GameM nx ns α)
    (st : SignState nx ns) (ℓ : Log) {z : (β × SignState nx ns) × Log}
    (hz : z ∈ support ((simulateQ gameImpl ((f <$> x).run st)).run ℓ)) :
    ∃ y ∈ support ((simulateQ gameImpl (x.run st)).run ℓ), z = ((f y.1.1, y.1.2), y.2) := by
  rw [map_eq_bind_pure_comp] at hz
  obtain ⟨y, hy, hz⟩ := mem_support_run_bind hz
  exact ⟨y, hy, mem_support_run_pure _ _ _ hz⟩

/-- A hash query read as bits: the log answers it. -/
theorem look_of_mem_support_bits {β : Type} (f : Digest → β) (x : Bytes) (st : SignState nx ns)
    (ℓ : Log) {z : (β × SignState nx ns) × Log}
    (hz : z ∈ support ((simulateQ gameImpl ((f <$> hashQuery x : GameM nx ns β).run st)).run ℓ)) :
    ∃ u, look z.2 x = some u ∧ z.1.1 = f u := by
  obtain ⟨y, hy, rfl⟩ := mem_support_run_map f _ st ℓ hz
  exact ⟨y.1.1, look_of_mem_support_hashQuery x st ℓ hy, rfl⟩

/-- **A key determined by the log**: the log answers the seed input `y` with `S`, then
`kcParamIn S` with `R`, and the parameter's bytes are `R`'s. -/
def KcDet (ℓ : Log) (y P : Bytes) : Prop :=
  ∃ S R, look ℓ y = some S ∧ look ℓ (kcParamIn S) = some R ∧ P = kcParBytes R

theorem KcDet.of_prefix {ℓ ℓ' : Log} {y P : Bytes} (h : KcDet ℓ y P) (hp : ℓ <+: ℓ') :
    KcDet ℓ' y P := by
  obtain ⟨S, R, hS, hR, hP⟩ := h
  exact ⟨S, R, look_of_prefix hp hS, look_of_prefix hp hR, hP⟩

/-- **A key generation of the schemes' shape determines its key**: the seed input `y` answered
with `S`, the parameter input `bIn S` with `R`, then anything `T S R`, and a key whose parameter's
bytes are `R`'s. -/
theorem kcDet_of_shape {K D : Type} {T : BitVec 256 → BitVec 256 → GameM nx ns D}
    {mk : BitVec 256 → BitVec 256 → D → K} {P : K → Bytes} {bIn : BitVec 256 → Bytes}
    (hP : ∀ S R root, P (mk S R root) = LeanXmss.bytesLE 16 (LeanXmss.truncateHash R))
    (hb : ∀ u, bIn (digestBits u) = kcParamIn u) (y : Bytes) (st : SignState nx ns) (ℓ : Log)
    {z : (K × SignState nx ns) × Log}
    (hz : z ∈ support ((simulateQ gameImpl (((digestBits <$> hashQuery y) >>= fun S ↦
      (digestBits <$> hashQuery (bIn S)) >>= fun R ↦ T S R >>= fun root ↦
        (pure (mk S R root) : GameM nx ns K)).run st)).run ℓ)) :
    KcDet z.2 y (P z.1.1) := by
  obtain ⟨y1, hy1, hz⟩ := mem_support_run_bind hz
  obtain ⟨u1, hl1, he1⟩ := look_of_mem_support_bits digestBits _ st ℓ hy1
  obtain ⟨y2, hy2, hz⟩ := mem_support_run_bind hz
  obtain ⟨u2, hl2, he2⟩ := look_of_mem_support_bits digestBits _ _ _ hy2
  obtain ⟨y3, hy3, hz⟩ := mem_support_run_bind hz
  have hz := mem_support_run_pure _ _ _ hz
  have p2 := prefix_of_mem_support_run _ _ hy2
  have p3 := prefix_of_mem_support_run _ _ hy3
  subst hz
  rw [he1, hb] at hl2
  refine ⟨u1, u2, look_of_prefix (p2.trans p3) hl1, look_of_prefix p3 hl2, ?_⟩
  rw [hP, he2]
  rfl

/-- **A leanXMSS key generation determines its key.** -/
theorem kcDet_xmssRun_keygen (s : LeanXmss.MasterSeed) (st : SignState nx ns) (ℓ : Log)
    {z : ((LeanXmss.PublicKey × LeanXmss.Seeded.SecretKey) × SignState nx ns) × Log}
    (hz : z ∈ support ((simulateQ gameImpl ((xmssRun (LeanXmss.Seeded.keygenFromSeed s) :
      GameM nx ns _).run st)).run ℓ)) :
    KcDet z.2 (LeanXmss.seedHashInput s) (LeanXmss.bytesLE 16 z.1.1.2.parameter) := by
  rw [xmssRun_keygenFromSeed_eq] at hz
  exact kcDet_of_shape (P := fun k ↦ LeanXmss.bytesLE 16 k.2.parameter) (fun _ _ _ ↦ rfl)
    xmss_keygenHashInput_parameter _ st ℓ hz

/-- **A leanSPHINCS key generation determines its key.** -/
theorem kcDet_sphincsRun_keygen [Sphincs.Params] (s : Sphincs.MasterSeed) (st : SignState nx ns)
    (ℓ : Log)
    {z : ((Sphincs.PublicKey × Sphincs.Seeded.SecretKey) × SignState nx ns) × Log}
    (hz : z ∈ support ((simulateQ gameImpl ((sphincsRun (Sphincs.Seeded.keygenFromSeed s) :
      GameM nx ns _).run st)).run ℓ)) :
    KcDet z.2 (Sphincs.schemeSeedInput s) (Sphincs.bytesLE 16 z.1.1.2.parameter) := by
  rw [sphincsRun_keygenFromSeed_eq] at hz
  exact kcDet_of_shape (P := fun k ↦ Sphincs.bytesLE 16 k.2.parameter) (fun _ _ _ ↦ rfl)
    sphincs_keygenHashInput_parameter _ st ℓ hz

/-- **A sequence's results each satisfy their post-condition**, monotone in the log. -/
theorem forall_of_mem_support_sequenceFin {β : Type} :
    ∀ {m : ℕ} (c : Fin m → GameM nx ns β) (P : Fin m → β → Log → Prop)
      (_hP : ∀ i st ℓ z, z ∈ support ((simulateQ gameImpl ((c i).run st)).run ℓ) →
        P i z.1.1 z.2)
      (_hmono : ∀ i b ℓ ℓ', ℓ <+: ℓ' → P i b ℓ → P i b ℓ') (st : SignState nx ns) (ℓ : Log)
      {z : ((Fin m → β) × SignState nx ns) × Log},
      z ∈ support ((simulateQ gameImpl ((LeanXmss.Concrete.sequenceFin c).run st)).run ℓ) →
      ∀ i, P i (z.1.1 i) z.2
  | 0, _, _, _, _, _, _, _, _, i => i.elim0
  | m + 1, c, P, hP, hmono, st, ℓ, z, hz, i => by
    simp only [LeanXmss.Concrete.sequenceFin] at hz
    obtain ⟨y1, hy1, hz⟩ := mem_support_run_bind hz
    obtain ⟨y2, hy2, hz⟩ := mem_support_run_bind hz
    have hz := mem_support_run_pure _ _ _ hz
    subst hz
    have p2 := prefix_of_mem_support_run _ _ hy2
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · exact hmono 0 _ _ _ p2 (hP 0 st ℓ y1 hy1)
    · exact forall_of_mem_support_sequenceFin (fun j ↦ c j.succ) (fun j ↦ P j.succ)
        (fun j ↦ hP j.succ) (fun j ↦ hmono j.succ) _ _ hy2 j

/-- A sequence costs its length times the cost of an entry. -/
theorem costs_sequenceFin {β : Type} {c : ℕ} :
    ∀ {m : ℕ} (f : Fin m → GameM nx ns β), (∀ i, Costs c (f i)) →
      Costs (m * c) (LeanXmss.Concrete.sequenceFin f)
  | 0, _, _ => by simpa [LeanXmss.Concrete.sequenceFin] using costs_pure (nx := nx) (ns := ns) _
  | m + 1, f, hf => by
    simp only [LeanXmss.Concrete.sequenceFin]
    rw [show (m + 1) * c = c + (m * c + 0) by ring]
    exact costs_bind (hf 0) fun _ ↦
      costs_bind (costs_sequenceFin (fun i ↦ f i.succ) fun i ↦ hf i.succ) fun _ ↦ costs_pure _

/-! ## Key generation from given seeds -/

section Seeds

/-- **The keys' seed inputs**: leanXMSS's `"leanXMSS" ‖ S0`, then leanSPHINCS's
`"leanSPHINCS" ‖ S0`. -/
def kcSeedIn (sx : Fin nx → LeanXmss.MasterSeed) (ss : Fin ns → Sphincs.MasterSeed) :
    Fin (nx + ns) → Bytes :=
  Fin.addCases (fun j ↦ LeanXmss.seedHashInput (sx j)) (fun j ↦ Sphincs.schemeSeedInput (ss j))

theorem length_kcSeedIn_ne (sx : Fin nx → LeanXmss.MasterSeed)
    (ss : Fin ns → Sphincs.MasterSeed) (i : Fin (nx + ns)) : (kcSeedIn sx ss i).length ≠ 64 := by
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
  · simp [kcSeedIn, LeanXmss.seedHashInput, LeanXmss.seedTag, LeanXmss.bytesLE]
  · simp [kcSeedIn, Sphincs.schemeSeedInput, Sphincs.seedTag, Sphincs.bytesLE]

variable [Sphincs.Params]

/-- **The keys' parameters' bytes**, leanXMSS then leanSPHINCS. -/
def kcKeyPar (keys : Keys nx ns) : Fin (nx + ns) → Bytes :=
  Fin.addCases (fun j ↦ LeanXmss.bytesLE 16 (keys.xmss j).2.parameter)
    (fun j ↦ Sphincs.bytesLE 16 (keys.sphincs j).2.parameter)

theorem keyParams_getElem? (keys : Keys nx ns) (i : Fin (nx + ns)) :
    (keyParams keys)[i]? = some (kcKeyPar keys i) := by
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
  · simp [keyParams, kcKeyPar, List.getElem?_append_left (by simp : j.val < (List.ofFn
      (fun j ↦ LeanXmss.bytesLE 16 (keys.xmss j).2.parameter)).length)]
  · simp [keyParams, kcKeyPar]

/-- **A key coincidence of key `idx`**, by the keys' parameters. -/
theorem kcKeyPar_of_keyCollAt {keys : Keys nx ns} {idx : Fin (nx + ns)}
    (h : KeyCollAt keys idx) :
    (∃ i, i ≠ idx ∧ kcKeyPar keys i = kcKeyPar keys idx) ∨
      ∃ i, kcKeyPar keys i = List.replicate 16 0 := by
  rcases h with ⟨i, hi, he⟩ | hm
  · rw [keyParams_getElem?, keyParams_getElem?] at he
    exact Or.inl ⟨i, hi, Option.some.inj he⟩
  · obtain ⟨i, hi, he⟩ := List.getElem_of_mem hm
    have hl : (keyParams keys).length = nx + ns := by simp [keyParams]
    refine Or.inr ⟨⟨i, hl ▸ hi⟩, ?_⟩
    have := keyParams_getElem? keys ⟨i, hl ▸ hi⟩
    rw [Fin.getElem?_fin, List.getElem?_eq_getElem hi, he] at this
    exact (Option.some.inj this).symm

/-- **Key generation from given seeds**: the keys in the game's order, each from its seed. -/
noncomputable def kcKeygenFrom (sx : Fin nx → LeanXmss.MasterSeed)
    (ss : Fin ns → Sphincs.MasterSeed) : GameM nx ns (Keys nx ns) := do
  let xs ← LeanXmss.Concrete.sequenceFin fun i ↦
    xmssRun (LeanXmss.Seeded.keygenFromSeed (sx i))
  let ks ← LeanXmss.Concrete.sequenceFin fun i ↦
    sphincsRun (Sphincs.Seeded.keygenFromSeed (ss i))
  pure ⟨xs, ks⟩

/-- **Key generation from given seeds determines every key.** -/
theorem kcKeygenFrom_post (sx : Fin nx → LeanXmss.MasterSeed) (ss : Fin ns → Sphincs.MasterSeed)
    (st : SignState nx ns) (ℓ : Log) {z : (Keys nx ns × SignState nx ns) × Log}
    (hz : z ∈ support ((simulateQ gameImpl ((kcKeygenFrom sx ss).run st)).run ℓ)) (i : Fin (nx + ns)) :
    KcDet z.2 (kcSeedIn sx ss i) (kcKeyPar z.1.1 i) := by
  unfold kcKeygenFrom at hz
  obtain ⟨y1, hy1, hz⟩ := mem_support_run_bind hz
  obtain ⟨y2, hy2, hz⟩ := mem_support_run_bind hz
  have hz := mem_support_run_pure _ _ _ hz
  have p2 := prefix_of_mem_support_run _ _ hy2
  subst hz
  have hx := forall_of_mem_support_sequenceFin
    (fun i ↦ (xmssRun (LeanXmss.Seeded.keygenFromSeed (sx i)) : GameM nx ns _))
    (fun j (k : LeanXmss.PublicKey × LeanXmss.Seeded.SecretKey) ℓ ↦
      KcDet ℓ (LeanXmss.seedHashInput (sx j)) (LeanXmss.bytesLE 16 k.2.parameter))
    (fun j st ℓ z hz ↦ kcDet_xmssRun_keygen (sx j) st ℓ hz) (fun _ _ _ _ hp h ↦ h.of_prefix hp)
    st ℓ hy1
  have hs := forall_of_mem_support_sequenceFin
    (fun i ↦ (sphincsRun (Sphincs.Seeded.keygenFromSeed (ss i)) : GameM nx ns _))
    (fun j (k : Sphincs.PublicKey × Sphincs.Seeded.SecretKey) ℓ ↦
      KcDet ℓ (Sphincs.schemeSeedInput (ss j)) (Sphincs.bytesLE 16 k.2.parameter))
    (fun j st ℓ z hz ↦ kcDet_sphincsRun_keygen (ss j) st ℓ hz) (fun _ _ _ _ hp h ↦ h.of_prefix hp)
    _ _ hy2
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
  · simp only [kcSeedIn, kcKeyPar, Fin.addCases_left]
    exact (hx j).of_prefix p2
  · simp only [kcSeedIn, kcKeyPar, Fin.addCases_right]
    exact hs j

/-- Key generation from given seeds costs the keys' generations. -/
theorem costs_kcKeygenFrom {cxk csk : ℕ}
    (hxk : ∀ seed, IsTotalQueryBound (LeanXmss.Seeded.keygenFromSeed seed) cxk)
    (hsk : ∀ seed, IsTotalQueryBound (Sphincs.Seeded.keygenFromSeed seed) csk)
    (sx : Fin nx → LeanXmss.MasterSeed) (ss : Fin ns → Sphincs.MasterSeed) :
    Costs (nx * cxk + ns * csk) (kcKeygenFrom sx ss) := by
  unfold kcKeygenFrom
  rw [show nx * cxk + ns * csk = nx * cxk + (ns * csk + 0) by ring]
  exact costs_bind (costs_sequenceFin _ fun i ↦ costs_xmssRun (hxk (sx i))) fun _ ↦
    costs_bind (costs_sequenceFin _ fun i ↦ costs_sphincsRun (hsk (ss i))) fun _ ↦ costs_pure _

/-- **The coincidence bound at given seeds** with distinct seed inputs. -/
theorem prEvent_kcKeygenFrom_le (idx : Fin (nx + ns)) {cxk csk : ℕ}
    (hxk : ∀ seed, IsTotalQueryBound (LeanXmss.Seeded.keygenFromSeed seed) cxk)
    (hsk : ∀ seed, IsTotalQueryBound (Sphincs.Seeded.keygenFromSeed seed) csk)
    (sx : Fin nx → LeanXmss.MasterSeed) (ss : Fin ns → Sphincs.MasterSeed)
    (hseed : ∀ i, i ≠ idx → kcSeedIn sx ss i ≠ kcSeedIn sx ss idx) :
    Pr{let z ← (simulateQ gameImpl ((kcKeygenFrom sx ss).run (SignState.init nx ns))).run []}[
        KeyCollAt z.1.1 idx] ≤
      ((2 * (nx + ns) - 1 : ℕ) : ℝ≥0∞) * (2 ^ 128 : ℝ≥0∞)⁻¹ +
        (((nx * cxk + ns * csk) * (nx * cxk + ns * csk - 1) : ℕ) : ℝ≥0∞) *
          (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  refine (kc_prEvent_le idx (length_kcSeedIn_ne sx ss) _ _
    (costs_kcKeygenFrom hxk hsk sx ss _) (fun k _ ↦ KeyCollAt k.1 idx) ?_).trans
    (kcPot_nil_le idx _)
  intro z hz hev
  exact one_le_kcPot idx _ (fun i ↦ kcKeygenFrom_post sx ss _ _ hz i) hseed
    (kcKeyPar_of_keyCollAt hev)

/-! ## Seeds first -/

/-- The game's key generation, translated. -/
theorem tw_keygen_eq (st : SignState nx ns) :
    tw (keygen : GameM nx ns (Keys nx ns)) st =
      LeanXmss.Concrete.sequenceFin (fun _ : Fin nx ↦ LeanXmss.MultiUser.keygen) >>= fun mk ↦
        LeanXmss.Concrete.sequenceFin (fun _ : Fin ns ↦ sKeygen) >>= fun ks ↦
          pure (⟨mk, ks⟩, st) := by
  unfold keygen
  simp only [tw_bind, tw_xKeygen, tw_sKeygen, bind_map_left, tw_pure, Fin.getElem_fin,
    Vector.getElem_ofFn, Fin.eta]

/-- Key generation from given seeds, translated. -/
theorem tw_kcKeygenFrom_eq (sx : Fin nx → LeanXmss.MasterSeed) (ss : Fin ns → Sphincs.MasterSeed)
    (st : SignState nx ns) :
    tw (kcKeygenFrom sx ss) st =
      LeanXmss.Concrete.sequenceFin (fun i ↦
          (liftM (LeanXmss.Seeded.keygenFromSeed (sx i)) : OracleComp OW _)) >>= fun mk ↦
        LeanXmss.Concrete.sequenceFin (fun i ↦ sLift (Sphincs.Seeded.keygenFromSeed (ss i))) >>=
          fun ks ↦ pure (⟨mk, ks⟩, st) := by
  unfold kcKeygenFrom
  rw [tw_bind, tw_sequenceFin st _ _ fun i ↦ tw_xmssRun _ st, bind_map_left]
  refine bind_congr fun mk ↦ ?_
  rw [tw_bind, tw_sequenceFin st _ _ fun i ↦ tw_sphincsRun _ st, bind_map_left]
  refine bind_congr fun ks ↦ ?_
  rw [tw_pure]

/-- **The leanSPHINCS seeds first**, past a computation, in the schemes' random oracle. -/
theorem romRun_sphincsSeeds_first {α γ : Type} (A : OracleComp OW α)
    (k : α → (Fin ns → Sphincs.PublicKey × Sphincs.Seeded.SecretKey) → OracleComp OW γ)
    (c : QueryCache LeanXmss.HashSpec) :
    romRun (A >>= fun a ↦ LeanXmss.Concrete.sequenceFin (fun _ : Fin ns ↦ sKeygen) >>= k a) c =ᵈ
      (LeanXmss.Concrete.sequenceFin fun _ : Fin ns ↦ Sphincs.sampleMasterSeed) >>= fun ss ↦
        romRun (A >>= fun a ↦ LeanXmss.Concrete.sequenceFin
          (fun i ↦ sLift (Sphincs.Seeded.keygenFromSeed (ss i))) >>= k a) c := by
  refine EvalDistEq.trans (m' := ProbComp) (m'' := ProbComp) ?_
    (EvalDistEq.trans (m' := ProbComp) (m'' := ProbComp) (romRun_bind_comm A
      (liftM (LeanXmss.Concrete.sequenceFin fun _ : Fin ns ↦ Sphincs.sampleMasterSeed) :
        OracleComp OW _)
      (fun a ss ↦ LeanXmss.Concrete.sequenceFin
        (fun i ↦ sLift (Sphincs.Seeded.keygenFromSeed (ss i))) >>= k a) c)
      (by rw [romRun_liftM_bind]))
  rw [romRun_bind, romRun_bind]
  exact EvalDistEq.bind_right _ fun r ↦ (romRun_seeds_first Sphincs.sampleMasterSeed
    (fun seed ↦ sLift (Sphincs.Seeded.keygenFromSeed seed)) ns (k r.1) r.2).symm

/-- **Key generation draws its seeds first**: the keys and the log (read as a cache) of the
key-generation phase are those of key generation from uniform seeds. -/
theorem keygenPhase_seedsFirst :
    Prod.map id logCache <$> (keygenPhase (nx := nx) (ns := ns)) =ᵈ
      (LeanXmss.Concrete.sequenceFin fun _ : Fin nx ↦ LeanXmss.sampleMasterSeed) >>= fun sx ↦
        (LeanXmss.Concrete.sequenceFin fun _ : Fin ns ↦ Sphincs.sampleMasterSeed) >>= fun ss ↦
          Prod.map id logCache <$>
            (simulateQ gameImpl ((kcKeygenFrom sx ss).run (SignState.init nx ns))).run [] := by
  refine EvalDistEq.trans (m' := ProbComp) (m'' := ProbComp)
    (evalDistEq_run_toW_nil (((keygen : GameM nx ns (Keys nx ns))).run (SignState.init nx ns))) ?_
  change romRun (tw keygen (SignState.init nx ns)) ∅ =ᵈ _
  rw [tw_keygen_eq]
  simp only [LeanXmss.MultiUser.keygen]
  refine EvalDistEq.trans (m' := ProbComp) (m'' := ProbComp)
    (romRun_seeds_first LeanXmss.sampleMasterSeed
      (fun seed ↦ (liftM (LeanXmss.Seeded.keygenFromSeed seed) : OracleComp OW _)) nx
      (fun mk ↦ LeanXmss.Concrete.sequenceFin (fun _ : Fin ns ↦ sKeygen) >>= fun ks ↦
        pure (({ xmss := mk, sphincs := ks } : Keys nx ns), SignState.init nx ns)) ∅).symm ?_
  rw [romRun_liftM_bind]
  refine EvalDistEq.bind_right _ fun sx ↦ ?_
  refine EvalDistEq.trans (m' := ProbComp) (m'' := ProbComp)
    (romRun_sphincsSeeds_first _ _ ∅) ?_
  refine EvalDistEq.bind_right _ fun ss ↦ ?_
  refine EvalDistEq.symm ?_
  refine EvalDistEq.trans (m' := ProbComp) (m'' := ProbComp)
    (evalDistEq_run_toW_nil ((kcKeygenFrom sx ss).run (SignState.init nx ns))) ?_
  change romRun (tw (kcKeygenFrom sx ss) (SignState.init nx ns)) ∅ =ᵈ _
  rw [tw_kcKeygenFrom_eq]

/-- **Key generation draws its seeds first**, for an event of the keys. -/
theorem prEvent_keygenPhase_eq_seeds (E : Keys nx ns → Prop) :
    Pr{let k ← keygenPhase (nx := nx) (ns := ns)}[E k.1.1] =
      Pr{let z ← (LeanXmss.Concrete.sequenceFin fun _ : Fin nx ↦ LeanXmss.sampleMasterSeed) >>=
          fun sx ↦ (LeanXmss.Concrete.sequenceFin fun _ : Fin ns ↦ Sphincs.sampleMasterSeed) >>=
            fun ss ↦
              (simulateQ gameImpl ((kcKeygenFrom sx ss).run (SignState.init nx ns))).run []}[
        E z.1.1] := by
  have h := (keygenPhase_seedsFirst (nx := nx) (ns := ns)).prEvent_eq (fun z ↦ E z.1.1)
  simp only [prEvent_map, map_bind] at h
  rw [← prEvent_map] at h
  simpa [prEvent_map] using h

/-! ## Seed coincidences -/

omit [Sphincs.Params] in
theorem sampleMasterSeed_xmss_eq : LeanXmss.sampleMasterSeed = Sphincs.sampleMasterSeed := rfl

omit [Sphincs.Params] in
/-- **Two of `m` uniform seeds coincide** with probability at most `2^-256`. -/
theorem prEvent_seeds_eq_le {m : ℕ} {i j : Fin m} (hij : i ≠ j) :
    Pr{let y ← LeanXmss.Concrete.sequenceFin fun _ : Fin m ↦ Sphincs.sampleMasterSeed}[
      y i = y j] ≤ (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  classical
  rw [← (evalDistEq_sampleSeeds m).prEvent_eq]
  unfold Sphincs.Security.Multi.sampleSeeds
  rw [@SampleableType.prEvent_uniformSample _ (SampleableType.ofFintype _) _ _ _]
  set s := Finset.univ.filter fun f : Fin m → Sphincs.MasterSeed ↦ f i = f j
  have hB : Fintype.card Sphincs.MasterSeed = 2 ^ 256 := by
    change Fintype.card (BitVec 256) = _; simp
  have hc : s.card * 2 ^ 256 ≤ Fintype.card (Fin m → Sphincs.MasterSeed) := by
    have h := Finset.card_le_card_of_injOn (s := s ×ˢ (Finset.univ : Finset Sphincs.MasterSeed))
      (t := (Finset.univ : Finset (Fin m → Sphincs.MasterSeed)))
      (fun p ↦ Function.update p.1 j p.2) (fun _ _ ↦ Finset.mem_univ _) ?_
    · rwa [Finset.card_product, Finset.card_univ, Finset.card_univ, hB] at h
    · rintro ⟨f, b⟩ hf ⟨f', b'⟩ hf' he
      simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, s, Finset.mem_filter,
        Finset.mem_univ, true_and, and_true] at hf hf'
      have hb : b = b' := by simpa using congrFun he j
      subst hb
      refine Prod.ext (funext fun k ↦ ?_) rfl
      by_cases hk : k = j
      · subst hk
        show f k = f' k
        rw [← hf, ← hf']
        simpa [Function.update_of_ne hij] using congrFun he i
      · simpa [Function.update_of_ne hk] using congrFun he k
  have hN0 : (Fintype.card (Fin m → Sphincs.MasterSeed) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [ENNReal.div_le_iff hN0 (ENNReal.natCast_ne_top _)]
  calc (s.card : ℝ≥0∞) = s.card * 2 ^ 256 * (2 ^ 256 : ℝ≥0∞)⁻¹ := by
        rw [mul_assoc, ENNReal.mul_inv_cancel (by simp) (by simp), mul_one]
    _ ≤ Fintype.card (Fin m → Sphincs.MasterSeed) * (2 ^ 256 : ℝ≥0∞)⁻¹ := by
        gcongr; exact_mod_cast hc
    _ = _ := mul_comm _ _

omit [Sphincs.Params] in
/-- **One of `m` uniform seeds is another's** with probability at most `m · 2^-256`. -/
theorem prEvent_seedColl_le {m : ℕ} (j : Fin m) :
    Pr{let y ← LeanXmss.Concrete.sequenceFin fun _ : Fin m ↦ Sphincs.sampleMasterSeed}[
      ∃ i, i ≠ j ∧ y i = y j] ≤ m * (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  refine (prEvent_exists_le _ _).trans ?_
  calc ∑ i, Pr{let y ← LeanXmss.Concrete.sequenceFin fun _ : Fin m ↦ Sphincs.sampleMasterSeed}[
        i ≠ j ∧ y i = y j]
      ≤ ∑ _i : Fin m, (2 ^ 256 : ℝ≥0∞)⁻¹ := by
        refine Finset.sum_le_sum fun i _ ↦ ?_
        by_cases hij : i = j
        · simp [hij]
        · exact (prEvent_mono _ _ _ fun y h ↦ h.2).trans (prEvent_seeds_eq_le hij)
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The leanXMSS seeds of key `idx`'s scheme coincide with its own. -/
def KcCollX (idx : Fin (nx + ns)) (sx : Fin nx → LeanXmss.MasterSeed) : Prop :=
  ∃ j, idx = Fin.castAdd ns j ∧ ∃ i, i ≠ j ∧ sx i = sx j

/-- The leanSPHINCS seeds of key `idx`'s scheme coincide with its own. -/
def KcCollS (idx : Fin (nx + ns)) (ss : Fin ns → Sphincs.MasterSeed) : Prop :=
  ∃ j, idx = Fin.natAdd nx j ∧ ∃ i, i ≠ j ∧ ss i = ss j

omit [Sphincs.Params] in
theorem prEvent_kcColl_le (idx : Fin (nx + ns)) :
    Pr{let sx ← LeanXmss.Concrete.sequenceFin fun _ : Fin nx ↦ LeanXmss.sampleMasterSeed}[
        KcCollX idx sx] +
      Pr{let ss ← LeanXmss.Concrete.sequenceFin fun _ : Fin ns ↦ Sphincs.sampleMasterSeed}[
        KcCollS idx ss] ≤ ((nx + ns : ℕ) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  rw [sampleMasterSeed_xmss_eq]
  induction idx using Fin.addCases with
  | left j =>
    have h1 : Pr{let sx ← LeanXmss.Concrete.sequenceFin fun _ : Fin nx ↦ Sphincs.sampleMasterSeed}[
        KcCollX (Fin.castAdd ns j) sx] ≤ nx * (2 ^ 256 : ℝ≥0∞)⁻¹ := by
      refine (prEvent_mono _ _ _ fun sx h ↦ ?_).trans (prEvent_seedColl_le j)
      obtain ⟨j', hj', h⟩ := h
      obtain rfl : j' = j := Fin.ext (by have := congrArg Fin.val hj'; simp at this; omega)
      exact h
    have h2 : Pr{let ss ← LeanXmss.Concrete.sequenceFin fun _ : Fin ns ↦ Sphincs.sampleMasterSeed}[
        KcCollS (Fin.castAdd ns j) ss] = 0 := by
      refine prEvent_eq_zero_of_forall_mem_support _ _ fun ss _ h ↦ ?_
      obtain ⟨j', hj', -⟩ := h
      exact absurd hj' (by simp [Fin.ext_iff]; omega)
    rw [h2, add_zero]
    refine h1.trans ?_
    gcongr
    exact_mod_cast Nat.le_add_right nx ns
  | right j =>
    have h1 : Pr{let sx ← LeanXmss.Concrete.sequenceFin fun _ : Fin nx ↦ Sphincs.sampleMasterSeed}[
        KcCollX (Fin.natAdd nx j) sx] = 0 := by
      refine prEvent_eq_zero_of_forall_mem_support _ _ fun sx _ h ↦ ?_
      obtain ⟨j', hj', -⟩ := h
      exact absurd hj' (by simp [Fin.ext_iff]; omega)
    have h2 : Pr{let ss ← LeanXmss.Concrete.sequenceFin fun _ : Fin ns ↦ Sphincs.sampleMasterSeed}[
        KcCollS (Fin.natAdd nx j) ss] ≤ ns * (2 ^ 256 : ℝ≥0∞)⁻¹ := by
      refine (prEvent_mono _ _ _ fun ss h ↦ ?_).trans (prEvent_seedColl_le j)
      obtain ⟨j', hj', h⟩ := h
      obtain rfl : j' = j := Fin.ext (by have := congrArg Fin.val hj'; simp at this; omega)
      exact h
    rw [h1, zero_add]
    refine h2.trans ?_
    gcongr
    exact_mod_cast Nat.le_add_left ns nx

omit [Sphincs.Params] in
/-- Distinct seeds of a scheme give distinct seed inputs. -/
theorem kcSeedIn_ne {idx : Fin (nx + ns)} {sx : Fin nx → LeanXmss.MasterSeed}
    {ss : Fin ns → Sphincs.MasterSeed} (hx : ¬ KcCollX idx sx) (hs : ¬ KcCollS idx ss)
    (i : Fin (nx + ns)) (hi : i ≠ idx) : kcSeedIn sx ss i ≠ kcSeedIn sx ss idx := by
  have hxi : ∀ a b : LeanXmss.MasterSeed, LeanXmss.seedHashInput a = LeanXmss.seedHashInput b →
      a = b := fun a b h ↦ Guest.Binding.bytesLE_inj (n := 32) (List.append_cancel_left h)
  have hsi : ∀ a b : Sphincs.MasterSeed, Sphincs.schemeSeedInput a = Sphincs.schemeSeedInput b →
      a = b := fun a b h ↦ Guest.Binding.bytesLE_inj (n := 32) (List.append_cancel_left h)
  have hlx : ∀ a, (LeanXmss.seedHashInput a).length = 40 := fun a ↦ by
    simp [LeanXmss.seedHashInput, LeanXmss.seedTag, LeanXmss.bytesLE]
  have hls : ∀ a, (Sphincs.schemeSeedInput a).length = 43 := fun a ↦ by
    simp [Sphincs.schemeSeedInput, Sphincs.seedTag, Sphincs.bytesLE]
  intro he
  induction idx using Fin.addCases with
  | left j =>
    induction i using Fin.addCases with
    | left i =>
      simp only [kcSeedIn, Fin.addCases_left] at he
      exact hx ⟨j, rfl, i, fun e ↦ hi (by rw [e]), hxi _ _ he⟩
    | right i =>
      simp only [kcSeedIn, Fin.addCases_left, Fin.addCases_right] at he
      have := congrArg List.length he
      rw [hls, hlx] at this
      omega
  | right j =>
    induction i using Fin.addCases with
    | left i =>
      simp only [kcSeedIn, Fin.addCases_left, Fin.addCases_right] at he
      have := congrArg List.length he
      rw [hls, hlx] at this
      omega
    | right i =>
      simp only [kcSeedIn, Fin.addCases_right] at he
      exact hs ⟨j, rfl, i, fun e ↦ hi (by rw [e]), hsi _ _ he⟩

/-! ## The bound -/

/-- **Key `idx` coincides rarely in key generation** (W-vis, P7d): another key shares its
parameter, or some parameter is zero, with probability at most `2n/2^128 + Q²/2^256`, `Q` the
key generations' hash queries. -/
theorem prEvent_keygenPhase_keyCollAt_le (idx : Fin (nx + ns)) {cxk csk : ℕ}
    (hxk : ∀ seed, IsTotalQueryBound (LeanXmss.Seeded.keygenFromSeed seed) cxk)
    (hsk : ∀ seed, IsTotalQueryBound (Sphincs.Seeded.keygenFromSeed seed) csk) :
    Pr{let k ← keygenPhase (nx := nx) (ns := ns)}[KeyCollAt k.1.1 idx] ≤
      ((2 * (nx + ns) : ℕ) : ℝ≥0∞) / 2 ^ 128 + ((nx * cxk + ns * csk) ^ 2 : ℕ) / 2 ^ 256 := by
  set Q := nx * cxk + ns * csk with hQ
  set ε : ℝ≥0∞ := ((2 * (nx + ns) - 1 : ℕ) : ℝ≥0∞) * (2 ^ 128 : ℝ≥0∞)⁻¹ +
    ((Q * (Q - 1) : ℕ) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹ with hε
  rw [prEvent_keygenPhase_eq_seeds (fun keys ↦ KeyCollAt keys idx)]
  refine (prEvent_bind_le_prEvent_add _ _ (KcCollX idx) _
    (ε := Pr{let ss ← LeanXmss.Concrete.sequenceFin fun _ : Fin ns ↦ Sphincs.sampleMasterSeed}[
      KcCollS idx ss] + ε) fun sx hx ↦ ?_).trans ?_
  · refine (prEvent_bind_le_prEvent_add _ _ (KcCollS idx) _ (ε := ε) fun ss hs ↦ ?_)
    exact prEvent_kcKeygenFrom_le idx hxk hsk sx ss (kcSeedIn_ne hx hs)
  · rw [← add_assoc]
    refine (add_le_add (prEvent_kcColl_le idx) le_rfl).trans ?_
    -- the arithmetic
    have hn : nx + ns ≤ Q := by
      have h1 := one_le_of_xmss_keygen hxk
      have h2 := one_le_of_sphincs_keygen hsk
      rw [hQ]
      exact Nat.add_le_add (Nat.le_mul_of_pos_right nx h1) (Nat.le_mul_of_pos_right ns h2)
    have hQQ : nx + ns + Q * (Q - 1) ≤ Q ^ 2 := by
      rcases Q with _ | Q
      · simp at hn ⊢; omega
      · simp only [Nat.add_sub_cancel, pow_two]
        nlinarith
    calc ((nx + ns : ℕ) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹ + ε
        = ((2 * (nx + ns) - 1 : ℕ) : ℝ≥0∞) * (2 ^ 128 : ℝ≥0∞)⁻¹ +
            ((nx + ns + Q * (Q - 1) : ℕ) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹ := by
          rw [hε]; push_cast; ring
      _ ≤ ((2 * (nx + ns) : ℕ) : ℝ≥0∞) * (2 ^ 128 : ℝ≥0∞)⁻¹ +
            ((Q ^ 2 : ℕ) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹ := by
          gcongr
          exact Nat.sub_le _ _
      _ = _ := by rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul, mul_comm,
            mul_comm ((Q ^ 2 : ℕ) : ℝ≥0∞)]

/-- **Key `idx` coincides rarely in the game with V_I's trace**: the rest of the game keeps the
keys key generation made. -/
theorem prEvent_gameRec_keyCollAt_le (idx : Fin (nx + ns)) (guest : Program) (fuel budget : ℕ)
    (A : GameAdversary nx ns) {cxk csk : ℕ}
    (hxk : ∀ seed, IsTotalQueryBound (LeanXmss.Seeded.keygenFromSeed seed) cxk)
    (hsk : ∀ seed, IsTotalQueryBound (Sphincs.Seeded.keygenFromSeed seed) csk) :
    Pr{let p ← gameRec guest fuel budget A}[KeyCollAt p.1.1.keys idx] ≤
      ((2 * (nx + ns) : ℕ) : ℝ≥0∞) / 2 ^ 128 + ((nx * cxk + ns * csk) ^ 2 : ℕ) / 2 ^ 256 := by
  rw [gameRec_eq_keygen_bind]
  refine (prEvent_bind_le_prEvent_add _ _ (fun k ↦ KeyCollAt k.1.1 idx) _ (ε := 0)
    fun k hk ↦ ?_).trans ?_
  · refine le_of_eq (prEvent_eq_zero_of_forall_mem_support _ _ fun p hp hc ↦ hk ?_)
    have h1 : p.1 ∈ support ((simulateQ gameImpl (restRec guest fuel budget A k.1.1 k.1.2)).run'
        k.2) := by
      rw [StateT.run'_eq, support_map]; exact ⟨p, hp, rfl⟩
    rwa [restRec_keys (support_simulateQ_run'_subset _ _ _ h1)] at hc
  · rw [add_zero]
    exact prEvent_keygenPhase_keyCollAt_le idx hxk hsk

end Seeds

end Runs

end
end LeanVM.E2E
