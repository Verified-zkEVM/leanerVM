/-
  LeanerVM.Protocol.ToVCVio.UniformSample

  The probability of an event with at most one witness under a uniform sample, and maps that
  push a uniform sample to a uniform sample: first halves of bijections, coordinatewise on
  tuples, low digits, first entries, digits in chunks. Candidate for VCVio.
-/

module

public import VCVio.OracleComp.Constructions.SampleableType.NativeMeasure

/-!
# Uniform samples: the subsingleton bound and pushforwards

VCVio's `SampleableType.prEvent_uniformSample_le_div_iff` says that the probability of an
event under a uniform sample of a finite type is at most `c / |α|` exactly when the event has
at most `c` witnesses. The bound here is the form a soundness argument uses: an event any two
of whose witnesses are equal has probability at most `1/|α|`. It takes its hypothesis as a
statement about witnesses, so that no caller has to name the finite set of all elements of
the type, and its right-hand side is a non-negative real coerced to an extended one, the type
of a round-by-round error.

## Pushing a uniform sample forward

Each statement below says that a map sends a uniform sample to a uniform sample: every event of
the image has its probability under a uniform sample of the target.

* `prEvent_uniformSample_fst_of_bijective`: the first half `f` of a bijection
  `x ↦ (f x, g x) : α → β × γ`;
* `prEvent_uniformSample_pi_of_bijective`: such an `f` applied to each of `m` independent uniform
  samples, giving `m` independent uniform samples of `β`;
* `prEvent_uniformSample_digits`: the `k` low base-`a` digits of a uniform number below `N`, for
  `a ^ k ∣ N`;
* `prEvent_uniformSample_castLE`: the first `t` entries of a uniform tuple of `n ≥ t`;
* `prEvent_uniformSample_digitChunks`: the low digits of `m` uniform numbers read as one sequence,
  `k` to a number; its first `t ≤ m * k` entries.
-/

namespace LeanerVM.Protocol

open OracleComp
open scoped NNReal ENNReal

public section

section Subsingleton

variable {α : Type} [SampleableType α] [Fintype α]

/-- An event any two of whose witnesses are equal has probability at most `1/|α|` under a
uniform sample. -/
theorem probEvent_uniformSample_le_of_subsingleton (p : α → Prop)
    (h : ∀ a b, p a → p b → a = b) :
    Pr{let sample ← $ᵗ α}[p sample] ≤ ((1 / Fintype.card α : ℝ≥0) : ℝ≥0∞) := by
  classical
  have hcard : (Finset.univ.filter p).card ≤ 1 :=
    Finset.card_le_one.mpr fun a ha b hb ↦
      h a b (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2
  have := (SampleableType.prEvent_uniformSample_le_div_iff (p := p) (c := 1)).mpr hcard
  rwa [ENNReal.coe_div (Nat.cast_ne_zero.mpr Fintype.card_ne_zero), ENNReal.coe_one,
    ENNReal.coe_natCast, ← Nat.cast_one (R := ℝ≥0∞)]

end Subsingleton

/-! ## Pushing a uniform sample forward -/

section Pushforward

variable {α β γ : Type} [SampleableType α] [SampleableType β] [SampleableType γ]

/-- The first half of a bijection `α → β × γ` pushes a uniform sample of `α` to a uniform sample
of `β`. -/
theorem prEvent_uniformSample_fst_of_bijective {f : α → β} {g : α → γ}
    (h : Function.Bijective fun x ↦ (f x, g x)) (p : β → Prop) :
    Pr{let x ← $ᵗ α}[p (f x)] = Pr{let y ← $ᵗ β}[p y] :=
  (SampleableType.prEvent_uniformSample_comp_of_bijective h fun z ↦ p z.1).trans
    (SampleableType.prEvent_uniformSample_fst p)

omit [SampleableType α] [SampleableType β] [SampleableType γ] in
/-- A bijection `α → β × γ`, applied coordinatewise, is a bijection of tuples. -/
private theorem bijective_pi_pair {f : α → β} {g : α → γ}
    (h : Function.Bijective fun x ↦ (f x, g x)) (ι : Type) :
    Function.Bijective fun d : ι → α ↦ ((fun i ↦ f (d i)), fun i ↦ g (d i)) := by
  refine ⟨fun d d' hd ↦ funext fun i ↦ h.1 ?_, fun y ↦
    ⟨fun i ↦ (h.2 (y.1 i, y.2 i)).choose, ?_⟩⟩
  · simp only [Prod.mk.injEq] at hd ⊢
    exact ⟨congrFun hd.1 i, congrFun hd.2 i⟩
  · ext i
    · exact congrArg Prod.fst (h.2 (y.1 i, y.2 i)).choose_spec
    · exact congrArg Prod.snd (h.2 (y.1 i, y.2 i)).choose_spec

/-- **Uniform tuples.** The first half `f` of a bijection `α → β × γ`, applied to each of `m`
independent uniform samples of `α`, gives `m` independent uniform samples of `β`. -/
theorem prEvent_uniformSample_pi_of_bijective {f : α → β} {g : α → γ}
    (h : Function.Bijective fun x ↦ (f x, g x)) (m : ℕ) (p : (Fin m → β) → Prop) :
    Pr{let d ← $ᵗ (Fin m → α)}[p fun i ↦ f (d i)] = Pr{let y ← $ᵗ (Fin m → β)}[p y] :=
  prEvent_uniformSample_fst_of_bijective (bijective_pi_pair h (Fin m)) p

/-- The low digits of `x` below `a ^ k` are those of `x`. -/
private theorem mod_pow_div_pow_mod {a k i : ℕ} (x : ℕ) (hi : i < k) :
    x % a ^ k / a ^ i % a = x / a ^ i % a := by
  have h : a ^ k = a ^ i * a ^ (k - i) := by rw [← pow_add, Nat.add_sub_cancel' hi.le]
  rw [h, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (dvd_pow_self a (by omega))]

/-- A number below `N`, for `a ^ k ∣ N`, is its `k` low base-`a` digits and its quotient by
`a ^ k`. -/
private theorem digits_bijective {a k N : ℕ} [NeZero a] (h : a ^ k ∣ N) :
    Function.Bijective fun x : Fin N ↦
      ((fun i : Fin k ↦ (⟨x / a ^ (i : ℕ) % a, Nat.mod_lt _ (NeZero.pos a)⟩ : Fin a)),
        (⟨x / a ^ k, (Nat.div_lt_iff_lt_mul (pow_pos (NeZero.pos a) k)).mpr
          (by rw [Nat.div_mul_cancel h]; exact x.2)⟩ : Fin (N / a ^ k))) := by
  have key : ∀ x : ℕ, (fun i : Fin k ↦ (⟨x / a ^ (i : ℕ) % a, Nat.mod_lt _ (NeZero.pos a)⟩ :
      Fin a)) = finFunctionFinEquiv.symm ⟨x % a ^ k, Nat.mod_lt _ (pow_pos (NeZero.pos a) k)⟩ :=
    fun x ↦ funext fun i ↦
      Fin.ext (by rw [finFunctionFinEquiv_symm_apply_val, mod_pow_div_pow_mod x i.2])
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨fun x y hxy ↦ ?_, ?_⟩
  · simp only [Prod.mk.injEq, Fin.mk.injEq, key] at hxy
    have hmod : (x : ℕ) % a ^ k = y % a ^ k :=
      congrArg Fin.val (finFunctionFinEquiv.symm.injective hxy.1)
    exact Fin.ext (by rw [← Nat.mod_add_div (x : ℕ) (a ^ k), hmod, hxy.2, Nat.mod_add_div])
  · rw [Fintype.card_fin, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
      Fintype.card_fin, Nat.mul_div_cancel' h]

/-- `N / a ^ k` is positive when `a ^ k` divides a positive `N`. -/
private theorem neZero_div {a k N : ℕ} [NeZero a] [NeZero N] (h : a ^ k ∣ N) :
    NeZero (N / a ^ k) :=
  ⟨(Nat.div_pos (Nat.le_of_dvd (NeZero.pos N) h) (pow_pos (NeZero.pos a) k)).ne'⟩

/-- **Low digits of a uniform number.** The `k` low base-`a` digits of a uniform number below `N`,
digit `i` of `x` being `x / a ^ i % a`, are `k` independent uniform digits when `a ^ k ∣ N`. -/
theorem prEvent_uniformSample_digits {a k N : ℕ} [NeZero a] [NeZero N] (h : a ^ k ∣ N)
    (p : (Fin k → Fin a) → Prop) :
    Pr{let x ← $ᵗ (Fin N)}[p fun i ↦ ⟨x / a ^ (i : ℕ) % a, Nat.mod_lt _ (NeZero.pos a)⟩] =
      Pr{let y ← $ᵗ (Fin k → Fin a)}[p y] :=
  have := neZero_div h
  prEvent_uniformSample_fst_of_bijective (digits_bijective h) p

/-- **The first entries of a uniform tuple are uniform.** -/
theorem prEvent_uniformSample_castLE {t n : ℕ} (h : t ≤ n) (p : (Fin t → α) → Prop) :
    Pr{let y ← $ᵗ (Fin n → α)}[p fun q ↦ y (Fin.castLE h q)] =
      Pr{let z ← $ᵗ (Fin t → α)}[p z] := by
  refine prEvent_uniformSample_fst_of_bijective
    (g := fun (y : Fin n → α) (r : Fin (n - t)) ↦ y ⟨t + r, by have := r.2; omega⟩)
    ⟨fun y y' hy ↦ funext fun q ↦ ?_, fun (z : (Fin t → α) × (Fin (n - t) → α)) ↦
      ⟨fun q ↦ if hq : (q : ℕ) < t then z.1 ⟨q, hq⟩ else z.2 ⟨q - t, by have := q.2; omega⟩,
        ?_⟩⟩ p
  · simp only [Prod.mk.injEq] at hy
    by_cases hq : (q : ℕ) < t
    · exact congrFun hy.1 ⟨q, hq⟩
    · have hr := congrFun hy.2 ⟨q - t, by have := q.2; omega⟩
      rwa [show (⟨t + (q - t), by have := q.2; omega⟩ : Fin n) = q from
        Fin.ext (by simp only; omega)] at hr
  · ext q
    · simp [q.2]
    · simp

/-- **Digits of uniform numbers, in chunks.** Read the `k` low base-`a` digits of each of `m`
uniform numbers below `N`, for `a ^ k ∣ N`, as one sequence in which entry `q` is digit `q % k` of
number `q / k`. Its first `t ≤ m * k` entries are `t` independent uniform digits; the digits past
them and the high part of each number are dropped. -/
theorem prEvent_uniformSample_digitChunks {a k N m t : ℕ} [NeZero a] [NeZero N] (h : a ^ k ∣ N)
    (ht : t ≤ m * k) (p : (Fin t → Fin a) → Prop) :
    Pr{let x ← $ᵗ (Fin m → Fin N)}[p fun q ↦
      ⟨x (Fin.castLE ht q).divNat / a ^ ((Fin.castLE ht q).modNat : ℕ) % a,
        Nat.mod_lt _ (NeZero.pos a)⟩] = Pr{let y ← $ᵗ (Fin t → Fin a)}[p y] := by
  have := neZero_div h
  refine (prEvent_uniformSample_pi_of_bijective (digits_bijective h) m
    (fun z ↦ p fun q ↦ z (Fin.castLE ht q).divNat (Fin.castLE ht q).modNat)).trans
    (Eq.trans ?_ (prEvent_uniformSample_castLE ht p))
  exact SampleableType.prEvent_uniformSample_equiv
    ((Equiv.curry (Fin m) (Fin k) (Fin a)).symm.trans (Equiv.arrowCongr finProdFinEquiv
      (Equiv.refl _))) (fun y ↦ p fun q ↦ y (Fin.castLE ht q))

end Pushforward

end
end LeanerVM.Protocol
