import SphincsFors.BridgeVirtualOnce

/-! The one-coin virtual future for monotone base functions. The forest witness (a cover
indicator) is monotone but not supermodular, so the FORS lemmas that add coins by their gains do
not apply. Instead a list of `ℓ` coins of probability `w` dominates any disclosure of a single item
of the list with probability `e` per item, `e (1 + w ℓ) ≤ w`, together with the base value: a coin
coupling that gives each item the leftover mass of the coins before it. For the grinding signer
`w = 1/R` and `e = 1/(ℓ + R)` with `R = (2^128 - Cmax) landing`. -/

open ENNReal

namespace SphincsLayered.Security.Domination

open SphincsFors.Security.Domination

variable {V : Type}

/-! ### Fresh slots and coins for monotone base functions -/

section Mono

variable (U : Finset V) {f : Multiset V → ℝ≥0∞}

theorem fresh_mono (hmono : Monotone' f) : ∀ m, Monotone' (fresh U f m)
  | 0 => hmono
  | m + 1 => fun _small _large hle => freshAvg_mono U fun _u _ =>
      fresh_mono hmono m _ _ (add_le_add hle le_rfl)

theorem fresh_ne_top (hU : U.Nonempty) (hfin : ∀ d, f d ≠ ⊤) : ∀ m d, fresh U f m d ≠ ⊤
  | 0, d => hfin d
  | m + 1, _ => freshAvg_ne_top hU fun _ => fresh_ne_top hU hfin m _

theorem base_le_fresh (hU : U.Nonempty) (hmono : Monotone' f) : ∀ m d, f d ≤ fresh U f m d
  | 0, _ => le_rfl
  | m + 1, d => by
      calc f d = freshAvg U (fun _ => f d) := (freshAvg_const U hU _).symm
        _ ≤ _ := freshAvg_mono U fun u _ =>
            le_trans (hmono _ _ (Multiset.le_add_right _ _)) (base_le_fresh hU hmono m _)

variable {U}

theorem base_le_slotValue {Φ : Multiset V → ℝ≥0∞} (hmono : Monotone' Φ) :
    ∀ (coins : List (ℝ≥0∞ × Multiset V)), (∀ c ∈ coins, c.1 ≤ 1) → ∀ d, Φ d ≤ slotValue Φ d coins
  | [], _, _ => le_rfl
  | (p, extra) :: rest, hp, d => by
      have hp1 : p ≤ 1 := hp _ (List.mem_cons_self ..)
      have hrest : ∀ c ∈ rest, c.1 ≤ 1 := fun c hc => hp c (List.mem_cons_of_mem _ hc)
      simp only [slotValue]
      calc Φ d = p * Φ d + (1 - p) * Φ d := by rw [← add_mul, add_tsub_cancel_of_le hp1, one_mul]
        _ ≤ _ := by
            gcongr
            · exact le_trans (hmono _ _ (Multiset.le_add_right _ _)) (base_le_slotValue hmono rest hrest _)
            · exact base_le_slotValue hmono rest hrest d

variable {w : ℝ≥0∞}

theorem virtualOnce_mono (hmono : Monotone' f) (m : ℕ) (coins : List V) :
    Monotone' (virtualOnce U w f m coins) :=
  slotValue_mono _ (fresh_mono U hmono m) _

theorem virtualOnce_ne_top (hU : U.Nonempty) (hw : w ≤ 1) (hfin : ∀ d, f d ≠ ⊤) (m : ℕ) (coins : List V)
    (d : Multiset V) : virtualOnce U w f m coins d ≠ ⊤ :=
  slotValue_ne_top _ (fresh_ne_top U hU hfin m) _ _ (itemCoins_le hw coins)

/-- More coins, more virtual disclosures. -/
theorem virtualOnce_le_consM (hw : w ≤ 1) (hmono : Monotone' f) (m : ℕ) (coins : List V) (v : V)
    (d : Multiset V) : virtualOnce U w f m coins d ≤ virtualOnce U w f m (v :: coins) d := by
  unfold virtualOnce
  rw [itemCoins_cons]
  simp only [slotValue]
  change virtualOnce U w f m coins d ≤ w * virtualOnce U w f m coins (d + {v}) + (1 - w) * virtualOnce U w f m coins d
  have hab : virtualOnce U w f m coins d ≤ virtualOnce U w f m coins (d + {v}) :=
    virtualOnce_mono hmono m coins _ _ (Multiset.le_add_right _ _)
  calc virtualOnce U w f m coins d = w * virtualOnce U w f m coins d + (1 - w) * virtualOnce U w f m coins d := by
        rw [← add_mul, add_tsub_cancel_of_le hw, one_mul]
    _ ≤ _ := by gcongr

/-- The virtual future only adds disclosures. -/
theorem base_le_virtualOnceM (hU : U.Nonempty) (hw : w ≤ 1) (hmono : Monotone' f) (m : ℕ) (coins : List V)
    (d : Multiset V) : f d ≤ virtualOnce U w f m coins d :=
  le_trans (base_le_fresh U hU hmono m d)
    (base_le_slotValue (fresh_mono U hmono m) _ (itemCoins_le hw coins) d)

end Mono

/-! ### The coin coupling -/

theorem coupling_real (w e a b t1 t2 S1 S2 m : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (he0 : 0 ≤ e) (hab : a ≤ b)
    (hcoef : e * (1 + w * m) ≤ w) (hS : S2 - m * (b - a) ≤ S1)
    (ht1 : b + e * S1 ≤ t1) (ht2 : a + e * S2 ≤ t2) :
    a + e * (b - a) + e * S2 ≤ w * t1 + (1 - w) * t2 := by
  nlinarith [mul_le_mul_of_nonneg_left ht1 (show (0 : ℝ) ≤ w by nlinarith),
    mul_le_mul_of_nonneg_left ht2 (show (0 : ℝ) ≤ 1 - w by linarith),
    mul_le_mul_of_nonneg_left hS (show (0 : ℝ) ≤ w * e by nlinarith),
    mul_nonneg (sub_nonneg.2 hab) (show (0 : ℝ) ≤ w - e * (1 + w * m) by linarith)]

variable {Φ : Multiset V → ℝ≥0∞}

theorem sum_gain_ne_top (hfin : ∀ d, Φ d ≠ ⊤) (L : List V) (d : Multiset V) :
    (L.map fun x => Φ (d + {x}) - Φ d).sum ≠ ⊤ :=
  list_sum_ne_top _ fun v hv => by
    obtain ⟨x, _, rfl⟩ := List.mem_map.1 hv
    exact ne_top_of_le_ne_top (hfin _) tsub_le_self

theorem toReal_sum_gain (hmono : Monotone' Φ) (hfin : ∀ d, Φ d ≠ ⊤) (L : List V) (d : Multiset V) :
    (L.map fun x => Φ (d + {x}) - Φ d).sum.toReal = (L.map fun x => (Φ (d + {x})).toReal - (Φ d).toReal).sum := by
  induction L with
  | nil => simp
  | cons x rest ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ENNReal.toReal_add (ne_top_of_le_ne_top (hfin _) tsub_le_self) (sum_gain_ne_top hfin rest d), ih,
        ENNReal.toReal_sub_of_le (hmono _ _ (Multiset.le_add_right _ _)) (hfin _)]

theorem list_sum_sub_le {α : Type} (L : List α) (f g : α → ℝ) (c : ℝ) (h : ∀ y ∈ L, f y - c ≤ g y) :
    (L.map f).sum - (L.length : ℝ) * c ≤ (L.map g).sum := by
  induction L with
  | nil => simp
  | cons y rest ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_succ]
      have h1 := h y List.mem_cons_self
      have h2 := ih fun z hz => h z (List.mem_cons_of_mem _ hz)
      linarith

/-- **The coin coupling.** A list of `ℓ` coins of probability `w` raises a monotone value by at
least `e` times every single gain of the list, for `e (1 + w ℓ) ≤ w`. -/
theorem slotValue_coupling (hmono : Monotone' Φ) (hfin : ∀ d, Φ d ≠ ⊤) {w e : ℝ≥0∞} (hw : w ≤ 1) (he : e ≠ ⊤) :
    ∀ (L : List V) (d : Multiset V), e * (1 + w * (L.length : ℝ≥0∞)) ≤ w →
      Φ d + e * (L.map fun x => Φ (d + {x}) - Φ d).sum ≤ slotValue Φ d (itemCoins w L)
  | [], d, _ => by simp [itemCoins, slotValue]
  | x :: rest, d, hcoef => by
      have hwt : w ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hw
      have hcoef' : e * (1 + w * (rest.length : ℝ≥0∞)) ≤ w := by
        refine le_trans ?_ hcoef
        gcongr
        exact_mod_cast Nat.le_succ _
      have ih1 := slotValue_coupling hmono hfin hw he rest (d + {x}) hcoef'
      have ih2 := slotValue_coupling hmono hfin hw he rest d hcoef'
      have hT := fun e' => slotValue_ne_top Φ hfin (itemCoins w rest) e' (itemCoins_le hw rest)
      rw [itemCoins_cons]
      simp only [slotValue, List.map_cons, List.sum_cons]
      have hgx := sum_gain_ne_top hfin rest (d + {x})
      have hgd := sum_gain_ne_top hfin rest d
      have h1t : Φ (d + {x}) - Φ d ≠ ⊤ := ne_top_of_le_ne_top (hfin (d + {x})) tsub_le_self
      have hw1 : (1 - w) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
      have hT1 := hT (d + {x})
      have hT2 := hT d
      have hΦx := hfin (d + {x})
      have hΦd := hfin d
      rw [← ENNReal.toReal_le_toReal (by finiteness) (by finiteness)] at ih1 ih2 ⊢
      rw [ENNReal.toReal_add (hfin _) (by finiteness), ENNReal.toReal_mul, toReal_sum_gain hmono hfin] at ih1 ih2
      rw [ENNReal.toReal_add (hfin _) (by finiteness), ENNReal.toReal_mul, ENNReal.toReal_add h1t hgd,
        toReal_sum_gain hmono hfin, ENNReal.toReal_sub_of_le (hmono _ _ (Multiset.le_add_right _ _)) (hfin _),
        ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_mul, ENNReal.toReal_mul,
        ENNReal.toReal_sub_of_le hw ENNReal.one_ne_top, ENNReal.toReal_one]
      have hcoefR : e.toReal * (1 + w.toReal * (rest.length : ℝ)) ≤ w.toReal := by
        have hwl : w * (rest.length : ℝ≥0∞) ≠ ⊤ := ENNReal.mul_ne_top hwt (ENNReal.natCast_ne_top _)
        rw [← ENNReal.toReal_le_toReal (by finiteness) hwt, ENNReal.toReal_mul,
          ENNReal.toReal_add ENNReal.one_ne_top hwl, ENNReal.toReal_mul, ENNReal.toReal_one,
          ENNReal.toReal_natCast] at hcoef'
        exact hcoef'
      have hab : (Φ d).toReal ≤ (Φ (d + {x})).toReal :=
        ENNReal.toReal_mono (hfin _) (hmono _ _ (Multiset.le_add_right _ _))
      have hS : (rest.map fun y => (Φ (d + {y})).toReal - (Φ d).toReal).sum -
          (rest.length : ℝ) * ((Φ (d + {x})).toReal - (Φ d).toReal) ≤
          (rest.map fun y => (Φ (d + {x} + {y})).toReal - (Φ (d + {x})).toReal).sum := by
        have hpt : ∀ y ∈ rest, (Φ (d + {y})).toReal - (Φ d).toReal - ((Φ (d + {x})).toReal - (Φ d).toReal) ≤
            (Φ (d + {x} + {y})).toReal - (Φ (d + {x})).toReal := by
          intro y _
          have : (Φ (d + {y})).toReal ≤ (Φ (d + {x} + {y})).toReal :=
            ENNReal.toReal_mono (hfin _) (hmono _ _ (by rw [add_right_comm]; exact Multiset.le_add_right _ _))
          linarith
        exact list_sum_sub_le rest _ _ _ hpt
      have := coupling_real w.toReal e.toReal (Φ d).toReal (Φ (d + {x})).toReal _ _ _ _ (rest.length : ℝ)
        ENNReal.toReal_nonneg (by simpa using ENNReal.toReal_mono ENNReal.one_ne_top hw) ENNReal.toReal_nonneg hab
        hcoefR hS ih1 ih2
      linarith

end SphincsLayered.Security.Domination
