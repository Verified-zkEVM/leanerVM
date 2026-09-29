import LeanerVM.Parameters.CleanField
import Clean.Air.FlatEnsemble

/-!
Probe `CleanBalance`: Clean's bus balance over `K = GF(2^64)`.

1. The universe of `EnsembleWitness`.
2. The countermodel: a tuple pushed twice and never pulled has field-sum balance zero at every
   message.
3. The side condition `interactions.length < ringChar F` rejects that list, and rejects every
   list of two or more interactions; a balanced singleton has multiplicity zero. So over `K`
   the relation `BalancedInteractions` holds of no bus with two interactions.
4. Hence `Ensemble.Statement` forces every channel of every ensemble over `K` to carry at most
   one interaction.
-/

open LeanerVM.Parameters

/-! ## 1. Universes -/

#check @Air.Flat.Component
#check @Air.Flat.Table
#check @Air.Flat.Ensemble
#check @Air.Flat.EnsembleWitness
#check @RawChannel
#check @Interaction
#check @ProverData
#check @TypeMap
#check @Air.Flat.Ensemble.Statement
#check @Air.Flat.Ensemble.Soundness
#check @BalancedInteractions
#check @balanceOf
#print axioms Air.Flat.Ensemble.soundness_of_tableSoundness_and_specConsistency
#print axioms exists_push_of_pull

/-! ## 2. The countermodel -/

theorem ringChar_K : ringChar K = 2 := ringChar.eq K 2

example : (-1 : K) = 1 := by decide
example : (1 : K) + 1 = 0 := by decide

/-- A channel with one coordinate and no guarantee. -/
def ch : RawChannel K where
  name := "bus"
  arity := 1
  Guarantees _ _ _ := True
  Requirements _ _ _ := True

/-- The tuple `(m)` pushed once: multiplicity `1`. -/
def push (m : K) : Interaction K where
  channel := ch
  mult := 1
  msg := #[m]
  same_size := rfl
  assumeGuarantees := false

/-- The tuple `(7)` pushed twice and never pulled. -/
def pushedTwice : List (Interaction K) := [push 7, push 7]

/-- Its field-sum balance is zero at every message: `1 + 1 = 0` in characteristic two. -/
theorem pushedTwice_balance (msg : Array K) : balanceOf pushedTwice msg = 0 := by
  -- no default `simp` here: core's `BitVec` simprocs would read `1 + 1` in `K` as `2#64`
  have h11 : (1 : K) + ((1 : K) + 0) = 0 := by decide
  by_cases h : (push 7).msg = msg
  · simp only [balanceOf, pushedTwice, List.filter_cons, List.filter_nil, decide_eq_true h,
      ↓reduceIte, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    exact h11
  · simp only [balanceOf, pushedTwice, List.filter_cons, List.filter_nil, decide_eq_false h,
      Bool.false_eq_true, ↓reduceIte, List.map_nil, List.sum_nil]

/-- As a multiset the same bus is not balanced: two pushes, no pull. -/
theorem pushedTwice_not_perm :
    ¬ (pushedTwice.map (·.msg)).Perm ([] : List (Array K)) := by
  intro h
  have := h.length_eq
  simp [pushedTwice] at this

/-! ## 3. The side condition -/

/-- Clean's relation rejects the countermodel, but only through the side condition. -/
theorem pushedTwice_not_balanced : ¬ BalancedInteractions pushedTwice := by
  rintro ⟨h, -⟩
  rw [ringChar_K] at h
  simp [pushedTwice] at h

/-- Over `K`, a balanced list has at most one interaction. -/
theorem length_le_one_of_balanced {l : List (Interaction K)} (h : BalancedInteractions l) :
    l.length ≤ 1 := by
  obtain ⟨h, -⟩ := h
  rw [ringChar_K] at h
  omega

/-- And that interaction has multiplicity zero. -/
theorem mult_eq_zero_of_balanced_singleton {i : Interaction K}
    (h : BalancedInteractions [i]) : i.mult = 0 := by
  have := h.2 i.msg
  simpa [balanceOf] using this

/-- A push and its matching pull, the smallest honest bus, are rejected. -/
def pull (m : K) : Interaction K where
  channel := ch
  mult := -1
  msg := #[m]
  same_size := rfl
  assumeGuarantees := true

theorem honest_pair_not_balanced : ¬ BalancedInteractions [push 7, pull 7] := fun h ↦ by
  have := length_le_one_of_balanced h
  simp at this

/-! ## 4. The ensemble statement -/

open Air.Flat in
/-- Whatever the ensemble over `K`, a witness of Clean's `Statement` has at most one
interaction on each of the ensemble's channels. -/
theorem statement_forces_at_most_one_interaction {PublicIO : TypeMap} [ProvableType PublicIO]
    (ens : Ensemble K PublicIO) (w : EnsembleWitness ens) (h : w.BalancedChannels)
    (c : RawChannel K) (hc : c ∈ ens.channels) :
    (w.allTablesWitness.interactionsWith c).length ≤ 1 :=
  length_le_one_of_balanced (h c hc)

#print axioms pushedTwice_balance
#print axioms pushedTwice_not_perm
#print axioms pushedTwice_not_balanced
#print axioms length_le_one_of_balanced
#print axioms mult_eq_zero_of_balanced_singleton
#print axioms honest_pair_not_balanced
#print axioms statement_forces_at_most_one_interaction
