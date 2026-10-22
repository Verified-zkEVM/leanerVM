/-
  LeanVM.E2E.Vis.Pred

  W-vis, P4: T3 restricted to non-hidden entries. The prediction event `PredS` asks both the
  predicting and the predicted entry to be outside the hidden class; its potential rises only at
  non-hidden fresh queries; and it is enough for T3's conclusion `RankOK` on the guest, given no
  failure and no format event.
-/

module

public import LeanVM.E2E.Vis.Rank
public import LeanVM.E2E.Vis.ShapeFacts

/-!
# T3 restricted (W-vis, P4)

T3 (`LeanVM.E2E.Termination`) excludes `Pred o ℓ`, an entry predicting at the offset `o` the
challenge of the answer of the same or a later entry. On the full log of the visible accounting
this is not rare (decision E2E-6): a signature reveals limbs `0` and `1` of a hidden entry's
challenge. Here:

* `PredS keys o ℓ`: `Pred` with the predicting and the predicted entry both outside `Hid keys`.
* `predPotS keys o n ℓ`: its potential, the indicator and a budget `Σ_{c ≤ k < c+n} (k+1)/2^192`
  where `c = cntV keys ℓ` counts the non-hidden entries. A non-hidden fresh query spends one
  unit of `n` (`predPotS_step_vis`); a hidden one spends nothing (`predPotS_step_hid`). On a log
  of hidden entries only (key generation) it is `n (n+1) / 2^193` (`predPotS_of_allHid`).
* `rankOK_of_vis`: without failure, the format event `FormatT` and `PredS` at the guest's
  offset, `RankOK` holds. The parent's statement input starts with the seed, which a non-hidden
  entry (the IV's preimage) answers, so is no hidden prefix (`not_inPfx_seed`); the batching's
  chain states, from the baked start `aggSeedD`, are answered by non-hidden chain inputs, so are
  no hidden prefixes either (`not_hid_chainInput`, by induction along the chain). So both
  entries of `rank_lt_of_child`'s prediction are non-hidden.
-/

namespace LeanVM.E2E

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Verifier LeanVM.Protocol.Rom
open LeanVM.Protocol.EndToEnd.Sound
open LeanVM.Node LeanVM.Guest.Batch
open scoped ENNReal

@[expose] public section

/- The enumeration of `Digest` must never be unfolded by unification. -/
attribute [local irreducible] instFintypeDigest

/- `E`'s enumeration is the repository's (`sum_challengeOf_div`), not leanDA's. -/
attribute [local instance 1100] LeanVM.Parameters.instFintypeK

/-! ## `Pred`'s form of T3 -/

/-- **`Pred`'s form of T3 gives `RankOK`**: no failure and no prediction at the guest's
offset. -/
theorem rankOK_of_pred {ℓ : Log} (hf : ¬ Fail leanVmSeeds ℓ)
    (hP : ¬ Pred (predOffset (bytecodeWords Guest.guest)) ℓ) : RankOK ℓ := by
  intro seed sd dd pi d cs h c i p ho _ hpi hm hbw hc hi hp hci hpp
  rw [← ho] at hP
  exact rank_lt_of_child hf hP hpi hm hbw hc hi hp hci hpp

variable {nx ns : ℕ} [Sphincs.Params]

/-! ## The restricted event and its potential -/

/-- **The prediction event off the hidden class**: a non-hidden entry's input carries, at the
offset `o`, the 24 bytes of the challenge of the answer of the same or a later non-hidden
entry. -/
def PredS (keys : Keys nx ns) (o : ℕ) (ℓ : Log) : Prop :=
  ∃ (i : ℕ) (hi : i < ℓ.length) (j : ℕ) (hj : j ≤ i), ¬ Hid keys ℓ[i].1 ∧
    ¬ Hid keys (ℓ[j]'(Nat.lt_of_le_of_lt hj hi)).1 ∧
    ((ℓ[j]'(Nat.lt_of_le_of_lt hj hi)).1.drop o).take 24 = eBytes (challengeOf ℓ[i].2)

open Classical in
/-- **The non-hidden entries' inputs**, in order. -/
noncomputable def visInputs (keys : Keys nx ns) (ℓ : Log) : List Bytes :=
  (ℓ.filter fun e ↦ decide (¬ Hid keys e.1)).map Prod.fst

/-- **The count of non-hidden entries.** -/
noncomputable def cntV (keys : Keys nx ns) (ℓ : Log) : ℕ := (visInputs keys ℓ).length

/-- **The restricted prediction's potential** for `n` more non-hidden fresh answers: the
indicator of `PredS`, and the budget from the current count of non-hidden entries. -/
noncomputable def predPotS (keys : Keys nx ns) (o n : ℕ) (ℓ : Log) : ℝ≥0∞ :=
  ind (PredS keys o ℓ) +
    ((∑ k ∈ Finset.Ico (cntV keys ℓ) (cntV keys ℓ + n), (k + 1) : ℕ) : ℝ≥0∞) / 2 ^ 192

/-- The potential's budget is `predBudget` (`LeanVM.E2E.Termination`). -/
theorem predPotS_eq (keys : Keys nx ns) (o n : ℕ) (ℓ : Log) :
    predPotS keys o n ℓ = ind (PredS keys o ℓ) + predBudget (cntV keys ℓ) (cntV keys ℓ + n) :=
  rfl

/-- A non-hidden input is among the non-hidden inputs. -/
theorem mem_visInputs {keys : Keys nx ns} {ℓ : Log} {e : Bytes × Digest} (he : e ∈ ℓ)
    (hv : ¬ Hid keys e.1) : e.1 ∈ visInputs keys ℓ := by
  classical
  unfold visInputs
  exact List.mem_map.mpr ⟨e, List.mem_filter.mpr ⟨he, by simpa using hv⟩, rfl⟩

/-- Appending a non-hidden entry adds its input. -/
theorem visInputs_append_vis {keys : Keys nx ns} {ℓ : Log} {t : Bytes} {u : Digest}
    (ht : ¬ Hid keys t) : visInputs keys (ℓ ++ [(t, u)]) = visInputs keys ℓ ++ [t] := by
  classical
  unfold visInputs
  rw [List.filter_append, List.map_append]
  simp [ht]

/-- Appending a hidden entry adds nothing. -/
theorem visInputs_append_hid {keys : Keys nx ns} {ℓ : Log} {t : Bytes} {u : Digest}
    (ht : Hid keys t) : visInputs keys (ℓ ++ [(t, u)]) = visInputs keys ℓ := by
  classical
  unfold visInputs
  rw [List.filter_append, List.map_append]
  simp [ht]

/-- **A restricted prediction in a log with one more entry** is one in the log, or the new
entry is non-hidden and its answer's challenge is the slice of a non-hidden input (its own or an
earlier one). -/
theorem predS_append {keys : Keys nx ns} {o : ℕ} {ℓ : Log} {t : Bytes} {u : Digest}
    (h : PredS keys o (ℓ ++ [(t, u)])) :
    PredS keys o ℓ ∨ (¬ Hid keys t ∧
      ∃ x ∈ t :: visInputs keys ℓ, (x.drop o).take 24 = eBytes (challengeOf u)) := by
  obtain ⟨i, hi, j, hj, hvi, hvj, heq⟩ := h
  simp only [List.length_append, List.length_singleton] at hi
  by_cases hil : i < ℓ.length
  · refine Or.inl ⟨i, hil, j, hj, ?_, ?_, ?_⟩
    · rwa [List.getElem_append_left hil] at hvi
    · rwa [List.getElem_append_left (Nat.lt_of_le_of_lt hj hil)] at hvj
    · rw [List.getElem_append_left (Nat.lt_of_le_of_lt hj hil),
        List.getElem_append_left hil] at heq
      exact heq
  · obtain rfl : i = ℓ.length := by omega
    rw [List.getElem_append_right (le_refl _)] at heq hvi
    simp only [Nat.sub_self, List.getElem_singleton] at heq hvi
    refine Or.inr ⟨hvi, ?_⟩
    by_cases hjl : j < ℓ.length
    · rw [List.getElem_append_left hjl] at heq hvj
      exact ⟨ℓ[j].1, List.mem_cons_of_mem _ (mem_visInputs (List.getElem_mem _) hvj), heq⟩
    · obtain rfl : j = ℓ.length := by omega
      rw [List.getElem_append_right (le_refl _)] at heq
      simp only [Nat.sub_self, List.getElem_singleton] at heq
      exact ⟨t, List.mem_cons_self, heq⟩

/-- **A hidden entry neither predicts nor is predicted.** -/
theorem predS_append_hid {keys : Keys nx ns} {o : ℕ} {ℓ : Log} {t : Bytes} {u : Digest}
    (ht : Hid keys t) : PredS keys o (ℓ ++ [(t, u)]) ↔ PredS keys o ℓ := by
  constructor
  · intro h
    rcases predS_append h with h | ⟨h, -⟩
    · exact h
    · exact absurd ht h
  · rintro ⟨i, hi, j, hj, hvi, hvj, heq⟩
    have hj' : j < ℓ.length := Nat.lt_of_le_of_lt hj hi
    refine ⟨i, by simp; omega, j, hj, ?_, ?_, ?_⟩
    · rwa [List.getElem_append_left hi]
    · rwa [List.getElem_append_left hj']
    · rw [List.getElem_append_left hj', List.getElem_append_left hi]
      exact heq

/-- **A non-hidden fresh answer spends one unit of the budget**: the potential with `n` left
after it is, on average, at most the potential with `n + 1` left before it. -/
theorem predPotS_step_vis {keys : Keys nx ns} {o : ℕ} {ℓ : Log} {t : Bytes}
    (ht : ¬ Hid keys t) (n : ℕ) :
    (∑ u, predPotS keys o n (ℓ ++ [(t, u)])) / Fintype.card Digest ≤
      predPotS keys o (n + 1) ℓ := by
  have hc : ∀ u : Digest, cntV keys (ℓ ++ [(t, u)]) = cntV keys ℓ + 1 := fun u ↦ by
    simp [cntV, visInputs_append_vis (u := u) ht]
  have hpt : ∀ u, predPotS keys o n (ℓ ++ [(t, u)]) ≤
      (ind (PredS keys o ℓ) + predBudget (cntV keys ℓ + 1) (cntV keys ℓ + 1 + n)) +
        ind (∃ x ∈ t :: visInputs keys ℓ, (x.drop o).take 24 = eBytes (challengeOf u)) := by
    intro u
    rw [predPotS_eq, hc]
    calc ind (PredS keys o (ℓ ++ [(t, u)])) + predBudget (cntV keys ℓ + 1) (cntV keys ℓ + 1 + n)
        ≤ (ind (PredS keys o ℓ) + ind (∃ x ∈ t :: visInputs keys ℓ,
            (x.drop o).take 24 = eBytes (challengeOf u))) +
            predBudget (cntV keys ℓ + 1) (cntV keys ℓ + 1 + n) :=
          add_le_add ((ind_mono fun h ↦ (predS_append h).imp id And.right).trans
            (ind_or_le _ _)) le_rfl
      _ = _ := by ring
  calc (∑ u, predPotS keys o n (ℓ ++ [(t, u)])) / Fintype.card Digest
      ≤ (∑ u, ((ind (PredS keys o ℓ) + predBudget (cntV keys ℓ + 1) (cntV keys ℓ + 1 + n)) +
          ind (∃ x ∈ t :: visInputs keys ℓ, (x.drop o).take 24 = eBytes (challengeOf u)))) /
          Fintype.card Digest :=
        ENNReal.div_le_div_right (Finset.sum_le_sum fun u _ ↦ hpt u) _
    _ = (ind (PredS keys o ℓ) + predBudget (cntV keys ℓ + 1) (cntV keys ℓ + 1 + n)) +
          (∑ u, ind (∃ x ∈ t :: visInputs keys ℓ,
            (x.drop o).take 24 = eBytes (challengeOf u))) / Fintype.card Digest :=
        avg_const_add _ _
    _ ≤ (ind (PredS keys o ℓ) + predBudget (cntV keys ℓ + 1) (cntV keys ℓ + 1 + n)) +
          ((t :: visInputs keys ℓ).length : ℝ≥0∞) / 2 ^ 192 :=
        add_le_add le_rfl (avg_ind_predicts o _)
    _ = predPotS keys o (n + 1) ℓ := by
      rw [predPotS_eq, predBudget_succ (show cntV keys ℓ < cntV keys ℓ + (n + 1) by omega),
        show cntV keys ℓ + 1 + n = cntV keys ℓ + (n + 1) by omega, List.length_cons]
      simp only [cntV]
      push_cast
      ring

/-- **A hidden fresh answer spends nothing**: the potential is unchanged. -/
theorem predPotS_step_hid {keys : Keys nx ns} {o : ℕ} {ℓ : Log} {t : Bytes}
    (ht : Hid keys t) (n : ℕ) :
    (∑ u, predPotS keys o n (ℓ ++ [(t, u)])) / Fintype.card Digest ≤ predPotS keys o n ℓ := by
  have he : ∀ u : Digest, predPotS keys o n (ℓ ++ [(t, u)]) = predPotS keys o n ℓ := fun u ↦ by
    simp only [predPotS, cntV, visInputs_append_hid ht, predS_append_hid ht]
  simp only [he, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [mul_comm, ENNReal.mul_div_cancel_right (by exact_mod_cast Fintype.card_ne_zero)
    (ENNReal.natCast_ne_top _)]

/-- **More budget, more potential.** -/
theorem predPotS_mono {keys : Keys nx ns} {o : ℕ} {ℓ : Log} (n : ℕ) :
    predPotS keys o n ℓ ≤ predPotS keys o (n + 1) ℓ := by
  rw [predPotS_eq, predPotS_eq]
  refine add_le_add le_rfl ?_
  rw [predBudget, predBudget]
  refine ENNReal.div_le_div_right ?_ _
  exact_mod_cast Finset.sum_le_sum_of_subset
    (Finset.Ico_subset_Ico_right (by omega))

/-- **On a log of hidden entries only** (key generation), the potential is the full budget
`n (n + 1) / 2^193`. -/
theorem predPotS_of_allHid {keys : Keys nx ns} {o : ℕ} {ℓ : Log}
    (hall : ∀ e ∈ ℓ, Hid keys e.1) (n : ℕ) :
    predPotS keys o n ℓ = n * (n + 1) / 2 ^ 193 := by
  have hc : cntV keys ℓ = 0 := by
    classical
    simp only [cntV, visInputs, List.length_map, List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro e he
    simpa using hall e he
  have hP : ¬ PredS keys o ℓ := fun ⟨i, hi, _, _, hvi, _⟩ ↦ hvi (hall _ (List.getElem_mem hi))
  have h0 := predPot_nil o n
  rw [predPot, ind_of_not (not_pred_nil o), zero_add, List.length_nil] at h0
  rw [predPotS_eq, ind_of_not hP, zero_add, hc, zero_add, h0]

/-! ## T3 restricted: the guest's rank -/

section Rank

variable {keys : Keys nx ns} {ℓ : Log}

/-- **Answered by a non-hidden entry.** -/
def VisAns (keys : Keys nx ns) (ℓ : Log) (cv : Digest) : Prop :=
  ∃ e ∈ ℓ, e.2 = cv ∧ ¬ Hid keys e.1

/-- Without the format event, a digest a non-hidden entry answers is no hidden prefix. -/
theorem VisAns.not_inPfx (hF : ¬ FormatT keys ℓ) {cv : Digest} (h : VisAns keys ℓ cv) :
    ¬ InPfx keys cv := by
  obtain ⟨e, he, rfl, hv⟩ := h
  exact fun hp ↦ hF ⟨e, he, hv, hp⟩

/-- **A chain step from a state that is no hidden prefix** is answered by a non-hidden
entry. -/
theorem visAns_step {cv cv' : Digest} (hcv : ¬ InPfx keys cv) {x : E} {tag : ℕ}
    (h : look ℓ (digestBytes cv ++ blockOf x tag) = some cv') : VisAns keys ℓ cv' := by
  obtain ⟨j, hj, hej, -⟩ := (look_eq_some_iff ℓ _ _).mp h
  refine ⟨ℓ[j], List.getElem_mem hj, by rw [hej], ?_⟩
  rw [hej]
  exact not_hid_chainInput hcv (by rw [blockOf_length]; omega) (by rw [blockOf_length]; omega)

/-- A chain step keeps the state off the hidden prefixes. -/
theorem not_inPfx_step (hF : ¬ FormatT keys ℓ) {cv cv' : Digest} (hcv : ¬ InPfx keys cv)
    {x : E} {tag : ℕ} (h : look ℓ (digestBytes cv ++ blockOf x tag) = some cv') :
    ¬ InPfx keys cv' :=
  (visAns_step hcv h).not_inPfx hF

/-- Absorbing scalars keeps the state off the hidden prefixes. -/
theorem not_inPfx_obsAllW (hF : ¬ FormatT keys ℓ) :
    ∀ (xs : List E) (cv cv' : Digest), ¬ InPfx keys cv → obsAllW (look ℓ) cv xs = some cv' →
      ¬ InPfx keys cv'
  | [], cv, cv', hcv, h => by
    simp only [obsAllW, List.foldlM_nil, pure, Option.some.injEq] at h
    exact h ▸ hcv
  | x :: xs, cv, cv', hcv, h => by
    rw [obsAllW_cons, Option.bind_eq_some_iff] at h
    obtain ⟨c, hc, h⟩ := h
    exact not_inPfx_obsAllW hF xs c cv' (not_inPfx_step hF hcv hc) h

/-- Two squeezes per child keep the state off the hidden prefixes. -/
theorem not_inPfx_sq2W (hF : ¬ FormatT keys ℓ) :
    ∀ (n : ℕ) (cv : Digest) {ls : List (E × E)} {cv' : Digest}, ¬ InPfx keys cv →
      sq2W (look ℓ) n cv = some (ls, cv') → ¬ InPfx keys cv'
  | 0, cv, ls, cv', hcv, h => by
    simp only [sq2W, Option.some.injEq, Prod.mk.injEq] at h
    exact h.2 ▸ hcv
  | n + 1, cv, ls, cv', hcv, h => by
    simp only [sq2W, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨c1, h1, c2, h2, r, hr, he⟩ := h
    obtain ⟨-, rfl⟩ := Prod.mk.inj he
    exact not_inPfx_sq2W hF n c2 (not_inPfx_step hF (not_inPfx_step hF hcv h1) h2) hr

/-- Three squeezes per child keep the state off the hidden prefixes. -/
theorem not_inPfx_sq3W (hF : ¬ FormatT keys ℓ) :
    ∀ (n : ℕ) (cv : Digest) {ls : List (E × E × E)} {cv' : Digest}, ¬ InPfx keys cv →
      sq3W (look ℓ) n cv = some (ls, cv') → ¬ InPfx keys cv'
  | 0, cv, ls, cv', hcv, h => by
    simp only [sq3W, Option.some.injEq, Prod.mk.injEq] at h
    exact h.2 ▸ hcv
  | n + 1, cv, ls, cv', hcv, h => by
    simp only [sq3W, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨c1, h1, c2, h2, c3, h3, r, hr, he⟩ := h
    obtain ⟨-, rfl⟩ := Prod.mk.inj he
    exact not_inPfx_sq3W hF n c3
      (not_inPfx_step hF (not_inPfx_step hF (not_inPfx_step hF hcv h1) h2) h3) hr

/-- **A sumcheck's rounds keep the state off the hidden prefixes**, and a nonempty sumcheck
ends at a state a non-hidden entry answers. -/
theorem not_inPfx_batchRoundsWith (hF : ¬ FormatT keys ℓ) :
    ∀ (rounds : List (E × E)) (claim : E) (cv : Digest) {r : (List E × E) × Digest},
      ¬ InPfx keys cv → (batchRoundsWith (look ℓ) claim rounds).run cv = some r →
        ¬ InPfx keys r.2 ∧ (rounds ≠ [] → VisAns keys ℓ r.2)
  | [], claim, cv, r, hcv, h => by
    simp only [batchRoundsWith, StateT.run_pure, Option.pure_def, Option.some.injEq] at h
    subst h
    exact ⟨hcv, fun h ↦ absurd rfl h⟩
  | (g1, gInf) :: rounds, claim, cv, r, hcv, h => by
    rw [batchRoundsWith_run_cons, Option.bind_eq_some_iff] at h
    obtain ⟨c1, h1, h⟩ := h
    rw [Option.bind_eq_some_iff] at h
    obtain ⟨c2, h2, h⟩ := h
    rw [Option.bind_eq_some_iff] at h
    obtain ⟨c3, h3, h⟩ := h
    rw [Option.map_eq_some_iff] at h
    obtain ⟨r', hr', rfl⟩ := h
    have hv3 : VisAns keys ℓ c3 :=
      visAns_step (not_inPfx_step hF (not_inPfx_step hF hcv h1) h2) h3
    obtain ⟨hn, hv⟩ := not_inPfx_batchRoundsWith hF rounds _ c3 (r := r') (hv3.not_inPfx hF) hr'
    refine ⟨hn, fun _ ↦ ?_⟩
    rcases rounds with _ | ⟨rd, rounds⟩
    · simp only [batchRoundsWith, StateT.run_pure, Option.pure_def, Option.some.injEq] at hr'
      subst hr'
      exact hv3
    · exact hv (List.cons_ne_nil _ _)

/-- **The parent's statement input is not hidden** when its seed is no hidden prefix: its first
32 bytes are the seed, and it is longer than every derivation. -/
theorem not_hid_stmtInput {seed sd dd : Digest} {d : DeferredClaim} (hs : ¬ InPfx keys seed) :
    ¬ Hid keys (stmtInput seed sd dd d) := by
  have e : stmtInput seed sd dd d = digestBytes seed ++ (digestBytes sd ++ digestBytes dd ++
      ((d.cells ++ if d.cells.length % 2 = 1 then [0] else []).flatMap eBytes ++
        List.replicate ((64 - (digestBytes seed ++ digestBytes sd ++ digestBytes dd ++
          (d.cells ++ if d.cells.length % 2 = 1 then [0] else []).flatMap eBytes).length % 64)
            % 64) 0)) := by
    simp only [stmtInput, List.append_assoc]
  rw [e]
  refine not_hid_chainInput hs ?_ ?_ <;> simp [digestBytes_length] <;> omega

/-- **The seed is no hidden prefix**: a non-hidden entry, the IV's preimage, answers it. -/
theorem not_inPfx_seed (_hf : ¬ Fail leanVmSeeds ℓ) (hF : ¬ FormatT keys ℓ) {seed : Digest}
    (hs : fiatShamirIvWith (look ℓ) (bytecodeWords Guest.guest) = some seed) :
    ¬ InPfx keys seed := by
  simp only [fiatShamirIvWith, bind, Option.bind_eq_some_iff] at hs
  obtain ⟨bh, -, hs⟩ := hs
  obtain ⟨j, hj, hej, -⟩ := (look_eq_some_iff ℓ _ _).mp hs
  refine VisAns.not_inPfx hF ⟨ℓ[j], List.getElem_mem hj, by rw [hej], ?_⟩
  rw [hej, ivPreimage_eq]
  exact not_hid_ivPrefix_append keys bh

/-- **T3 restricted, the cache form**: `rank_lt_of_child` with `PredS` for `Pred`, given no
format event, a batching start and a seed that are no hidden prefixes. -/
theorem rank_lt_of_child_vis {X : Type} {σ : Seeds X} (hf : ¬ Fail σ ℓ)
    (hF : ¬ FormatT keys ℓ) {seed sd dd pi : Digest} {d : DeferredClaim}
    (hseed : ¬ InPfx keys seed)
    (hP : ¬ PredS keys (96 + 24 * (d.bytecodePoint.length + d.matrixPoint.length)) ℓ)
    (hpi : look ℓ (stmtInput seed sd dd d) = some pi) (hm : d.matrixPoint ≠ [])
    {s0 : Digest} (hs0 : ¬ InPfx keys s0) {cs : List ChildClaims} {h : BatchHints}
    (hbw : batchWith (look ℓ) s0 cs h = some (some d)) {c : ChildClaims} (hc : c ∈ cs)
    {i p : ℕ} (hi : i < ℓ.length) (hp : p < ℓ.length) (hci : ℓ[i].2 = c.publicInput)
    (hpp : ℓ[p].2 = pi) : i < p := by
  obtain ⟨cvA, lB, cv1, rB, fB, cv2, lM, cv3, cM, fM, cv4, hA, h1, h2, h3, h4⟩ :=
    batchWith_some_full hbw
  have nA := not_inPfx_obsAllW hF _ _ _ hs0 hA
  have n1 := not_inPfx_sq2W hF _ _ nA h1
  have n2 := (not_inPfx_batchRoundsWith hF _ _ _ n1 h2).1
  have n3 := not_inPfx_sq3W hF _ _ n2 h3
  rw [obsAllW_cons, Option.bind_eq_some_iff] at hA
  obtain ⟨cv0, -, hA⟩ := hA
  have hab := absorbed_obsAllW_children hf cs cv0 cvA hA c hc ⟨i, hi, hci⟩
  have hc4 : ChainLE ℓ cvA cv4 :=
    (((chainLE_sq2W hf _ _ h1).trans (chainLE_batchRoundsWith hf _ _ _ h2)).trans
      (chainLE_sq3W hf _ _ h3)).trans (chainLE_batchRoundsWith hf _ _ _ h4)
  obtain ⟨i', k, hi', hk, hci', hik, hck⟩ := (hab.chain hc4).exists_lt
  obtain rfl : i' = i := index_eq_of_output hf hi' hi (by rw [hci', hci])
  have hround : h.matrixRounds ≠ [] := by
    intro he
    have hl := length_batchRoundsWith (look ℓ) _ _ _ h4
    rw [he] at hl
    exact hm (List.eq_nil_of_length_eq_zero hl)
  have hlast := getLast_batchRoundsWith _ _ _ h4 hround
  obtain ⟨e, he, he4, hve⟩ := (not_inPfx_batchRoundsWith hF _ _ _ n3 h4).2 hround
  obtain ⟨k', hk', rfl⟩ := List.getElem_of_mem he
  obtain rfl : k' = k := index_eq_of_output hf hk' hk (by rw [he4, hck])
  obtain ⟨p', hp', hep, -⟩ := (look_eq_some_iff ℓ _ _).mp hpi
  obtain rfl : p' = p := index_eq_of_output hf hp' hp (by rw [hep, hpp])
  have hkp : k' < p' := by
    by_contra hle
    refine hP ⟨k', hk', p', by omega, hve, ?_, ?_⟩
    · rw [hep]
      exact not_hid_stmtInput hseed
    · rw [hep, hck]
      exact slice_stmtInput seed sd dd hlast
  omega

/-- **T3 restricted gives `RankOK`**: without failure, the format event and a restricted
prediction at the guest's offset. -/
theorem rankOK_of_vis (hf : ¬ Fail leanVmSeeds ℓ) (hF : ¬ FormatT keys ℓ)
    (hP : ¬ PredS keys (predOffset (bytecodeWords Guest.guest)) ℓ) : RankOK ℓ := by
  intro seed sd dd pi d cs h c i p ho hs hpi hm hbw hc hi hp hci hpp
  rw [← ho] at hP
  exact rank_lt_of_child_vis hf hF (not_inPfx_seed hf hF hs) hP hpi hm
    (not_inPfx_aggSeedD keys) hbw hc hi hp hci hpp

end Rank

end
end LeanVM.E2E
