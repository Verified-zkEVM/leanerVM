/-
  LeanVM.Guest.B1.Sig.SpWotsArmFacts

  An arm of `sp_wots`'s digit dispatch, its padding run at the group's digit cells: in
  single-assignment form, its values and outputs placed, its `KECCAK`s on canonical cells, its
  walks laid out and its chains' starts apart.
-/

module

public import LeanVM.Guest.B1.Sig.SpWotsParComplete
public import LeanVM.Guest.B1.Sig.SpWotsPadCheck
public import LeanVM.Guest.B1.Sig.WotsGroupComplete

/-!
# An arm's facts

`SpArmFacts B L E …`: what completing arm `L` (the shared arm over `spWp B`, its run at the group's
digit cells `B ..< B + 5`) needs: single-assignment form, its outputs in `B + 5 ..< E`, its values
below `E`, its `KECCAK`s on canonical cells from canonical starts, its walks laid out above
`B + 5`, its starts placed and apart, its other values `PadGood`. `spArm0_facts`, `spArmPos_facts`:
arm `0` (laying out the slots) and a later arm (writing them).
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

/-- What completing an arm of `sp_wots` needs. -/
structure SpArmFacts (B : Nat) (slots : Nat → Nat → Nat) (first n : Nat) (fold : Bool)
    (prodIn encIn po eo : V) (k a E : Nat) : Prop where
  ssa : SSA (armT (spWp B) slots first n fold prodIn encIn po eo k a).1
  outs : ∀ x ∈ outsList (armT (spWp B) slots first n fold prodIn encIn po eo k a).1,
    ∃ j, x = .n j ∧ B + 5 ≤ j ∧ j < E
  vals : ∀ x ∈ Stmt.valsList (armT (spWp B) slots first n fold prodIn encIn po eo k a).1,
    ∃ j, x = .n j ∧ j < E
  canon : ∀ σ, SpGood B σ → (∀ t < n, StartCanon σ (slots t) (dig k t)
      (walkBase (if k = 0 then 3 + 13 else 3) k 0 t (if fold then a + 1 else a))) →
    KCanon (fwd (armT (spWp B) slots first n fold prodIn encIn po eo k a).1 σ)
        (armT (spWp B) slots first n fold prodIn encIn po eo k a).1 ∧
      ∀ t < n, IsCanonical128 (fwd (armT (spWp B) slots first n fold prodIn encIn po eo k a).1 σ
        (.n (slots t 2)))
  lay : ∀ t < n, WalkLay (spWp B) (B + 5) (slots t) (if k = 0 then 3 + 13 else 3) (dig k t)
    (walkBase (if k = 0 then 3 + 13 else 3) k 0 t (if fold then a + 1 else a))
  starts : ∀ t < n, ∃ j, armStart spW slots fold k a t = .n j ∧ B + 5 ≤ j ∧ j < E
  startsNe : ∀ t t', t < t' → t' < n → armStart spW slots fold k a t ≠ armStart spW slots fold k a t'
  tipsE : ∀ t < n, slots t 2 < E
  tail : ∀ x ∈ [V.n a, po, eo, prodIn, encIn, V.n (3 + digitSum k n),
    V.n (walkBase 3 k 0 n (if fold then a + 1 else a))], PadGood B spVPad x

theorem walkLay_raise {W : WotsT} {B B' : Nat} {slot : Nat → Nat} {stride d b : Nat}
    (h : WalkLay W B slot stride d b) (h1 : B' ≤ b) (h2 : ∀ s < 3, B' ≤ slot s) :
    WalkLay W B' slot stride d b :=
  ⟨h1, h2, h.inc, h.strideOK, h.apart, h.start⟩

theorem start_walkR (slot : Nat → Nat) (stride d b : Nat) :
    WalkR slot stride d b (walkStartV slot d b) := by
  unfold walkStartV
  split
  · exact Or.inr ⟨2, by norm_num, 0, by norm_num, rfl⟩
  · rename_i h3
    exact Or.inl ⟨0, by simp [walkSize, h3], rfl⟩

/-- **An arm's starts are apart**, their walks' regions disjoint. -/
theorem armStart_ne {slots : Nat → Nat → Nat} {fold : Bool} {k a n : Nat} {S : Nat}
    (hS : S = if k = 0 then 3 + 13 else 3)
    (hwd : ∀ t < n, ∀ t' < n, t ≠ t' → ∀ x,
      WalkR (slots t) S (dig k t) (walkBase S k 0 t (if fold then a + 1 else a)) x →
      ¬ WalkR (slots t') S (dig k t') (walkBase S k 0 t' (if fold then a + 1 else a)) x) :
    ∀ t t', t < t' → t' < n → armStart spW slots fold k a t ≠ armStart spW slots fold k a t' := by
  intro t t' h ht' e
  subst hS
  have h1 := start_walkR (slots t) (if k = 0 then 3 + 13 else 3) (dig k t)
    (walkBase (if k = 0 then 3 + 13 else 3) k 0 t (if fold then a + 1 else a))
  have h2 := start_walkR (slots t') (if k = 0 then 3 + 13 else 3) (dig k t')
    (walkBase (if k = 0 then 3 + 13 else 3) k 0 t' (if fold then a + 1 else a))
  unfold armStart at e
  simp only [spW] at e
  rw [e] at h1
  exact hwd t (by omega) t' ht' (by omega) _ h1 h2

theorem spGood_shape {B : Nat} (hB : 2 ≤ B) : StepShape (spWp B) (B + 5) := spWp_shape le_rfl (by omega)

theorem spGood_canon {B : Nat} (hB : 2 ≤ B) : StepCanon (spWp B) (B + 5) (SpGood B) :=
  spWp_canon le_rfl (by omega)

theorem digitSum_le_nine' (k n : Nat) (hn : n ≤ 3) : 3 + digitSum k n ≤ 12 := by
  have := digitSum_le_nine k n hn; omega

/-- **Arm `0`'s facts**: its slots and outputs as the shared template lays them out from `B`. -/
theorem spArm0_facts {B first n : Nat} {fold : Bool} {prodIn encIn : V} (hB : 13 ≤ B) (hn : n ≤ 3)
    (hpi : NBv B prodIn) (hei : NBv B encIn)
    (hX : groupStart fold B + chainStride (spWp B) * n + 2 ≤ spVPad) :
    SpArmFacts B (slotsT (spWp B) fold B) first n fold prodIn encIn (prodT (spWp B) fold n B)
      (encT (spWp B) fold n B) 0 (B + 5) (groupStart fold B + chainStride (spWp B) * n + 2) := by
  have hW := spGood_shape (B := B) (by omega)
  have hc := spGood_canon (B := B) (by omega)
  have hsz : (spWp B).size = 3 := rfl
  have hds := digitSum_le_nine' 0 n hn
  obtain ⟨l1, l2, l3⟩ := arm0_lay (spWp B) fold (n := n) (le_refl B)
  have hgs : B + 5 ≤ groupStart fold B := by rw [groupStart_eq]; split <;> omega
  have hgsf : fold = true → B + 6 ≤ groupStart fold B := by intro hf; rw [groupStart_eq, hf]; simp
  have hb0 : (if fold then B + 5 + 1 else B + 5) = groupStart fold B := by cases fold <;> rfl
  have hwb : ∀ t, walkBase ((spWp B).size + 13) 0 0 t (if fold then B + 5 + 1 else B + 5) =
      groupStart fold B + chainStride (spWp B) * t := by
    intro t; rw [walkBase_zero, hb0, chainStride_eq, hsz, mul_comm]
  have hwb' : ∀ t, walkBase (3 + 13) 0 0 t (if fold then B + 5 + 1 else B + 5) =
      groupStart fold B + chainStride (spWp B) * t := hwb
  have l1' : ∀ t < n, WalkLay (spWp B) (B + 5) (slotsT (spWp B) fold B t) ((spWp B).size + 13) (dig 0 t)
      (walkBase ((spWp B).size + 13) 0 0 t (if fold then B + 5 + 1 else B + 5)) := by
    intro t ht
    refine walkLay_raise (l1 t ht) (by rw [hwb]; omega) (fun s hs => ?_)
    have := slot_bounds (spWp B) fold B t s hs
    omega
  have hR : ∀ x, WalksR (slotsT (spWp B) fold B) ((spWp B).size + 13) 0 n
      (if fold then B + 5 + 1 else B + 5) x →
      x ≠ .n (groupStart fold B + chainStride (spWp B) * n) ∧
      x ≠ .n (groupStart fold B + chainStride (spWp B) * n + 1) ∧ (fold = true → x ≠ .n (B + 5)) ∧
      (0 ≠ 0 → x ≠ .n (walksT (spWp B) (slotsT (spWp B) fold B) first 0 (spWp B).size n 0
        (if fold then B + 5 + 1 else B + 5)).2) := by
    intro x hx
    obtain ⟨j, rfl, h1, h2⟩ := l3 x hx
    refine ⟨fun e => ?_, fun e => ?_, fun hf e => ?_, fun h => absurd rfl h⟩ <;>
      simp only [V.mk.injEq, true_and] at e
    · omega
    · omega
    · have := hgsf hf; omega
  have hssa := armT_ssa (first := first) (prodIn := prodIn) (encIn := encIn) (k := 0) (b := B + 5) hW
    l1' l2 (hpi.mono' (by omega)) (hei.mono' (by omega)) ⟨_, by omega, rfl⟩
    (show groupStart fold B + chainStride (spWp B) * n ≠ groupStart fold B + chainStride (spWp B) * n + 1
      by omega) (by omega) (by omega)
    (fun hf => ⟨by have := hgsf hf; omega, by have := hgsf hf; omega⟩) hR (fun h => absurd rfl h)
  have hE : ∀ x, WalksR (slotsT (spWp B) fold B) ((spWp B).size + 13) 0 n
      (if fold then B + 5 + 1 else B + 5) x →
      ∃ j, x = .n j ∧ B + 5 ≤ j ∧ j < groupStart fold B + chainStride (spWp B) * n + 2 := by
    intro x hx
    obtain ⟨j, rfl, h1, h2⟩ := l3 x hx
    exact ⟨j, rfl, by omega, by omega⟩
  refine ⟨hssa.1, fun x hx => ?_, fun x hx => ?_, fun σ hg hs => ?_, l1', fun t ht => ?_,
    armStart_ne (S := 3 + 13) rfl l2, fun t ht => ?_, fun x hx => ?_⟩
  · rcases hssa.2 x hx with h | rfl | rfl | ⟨-, rfl⟩ | ⟨h, -⟩
    · exact hE x h
    · exact ⟨_, rfl, by omega, by omega⟩
    · exact ⟨_, rfl, by omega, by omega⟩
    · exact ⟨B + 5, rfl, le_rfl, by omega⟩
    · exact absurd rfl h
  · refine armT_vals hW l1' l2
      (P := fun x => ∃ j, x = .n j ∧ j < groupStart fold B + chainStride (spWp B) * n + 2)
      (fun x ⟨j, hj, e⟩ => ⟨j, e, by omega⟩) (fun x hx => let ⟨j, e, _, h⟩ := hE x hx; ⟨j, e, h⟩)
      ⟨⟨_, rfl, by omega⟩, ⟨_, rfl, by omega⟩, ⟨_, rfl, by omega⟩,
        let ⟨j, hj, e⟩ := hpi; ⟨j, e, by omega⟩, let ⟨j, hj, e⟩ := hei; ⟨j, e, by omega⟩,
        ⟨_, rfl, by omega⟩, ?_⟩ x hx
    rw [walksT_snd]
    refine ⟨_, rfl, ?_⟩
    rw [walkBase_zero, hb0, chainStride_eq, hsz]
    omega
  · exact armT_canon hW hc l1' l2 (le_refl _) hR hssa.1 σ hg hs
  · unfold armStart walkStartV
    simp only [↓reduceIte, Nat.zero_div, Nat.zero_mod, show (0 : Nat) ≠ 3 by omega, spW]
    have := hwb' t
    have : chainStride (spWp B) * t ≤ chainStride (spWp B) * n := Nat.mul_le_mul_left _ (by omega)
    exact ⟨_, rfl, by omega, by omega⟩
  · have := slot_bounds (spWp B) fold B t 2 (by norm_num)
    have : chainStride (spWp B) * (t + 1) ≤ chainStride (spWp B) * n := Nat.mul_le_mul_left _ (by omega)
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    obtain ⟨jp, hjp, rfl⟩ := hpi
    obtain ⟨je, hje, rfl⟩ := hei
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact padGood_of (Or.inr le_rfl) (by omega)
    · exact padGood_of (Or.inr (by omega)) (by omega)
    · exact padGood_of (Or.inr (by omega)) (by omega)
    · exact padGood_of (Or.inl hjp) (by omega)
    · exact padGood_of (Or.inl hje) (by omega)
    · exact padGood_of (Or.inl (by omega)) (by omega)
    · have := hwb n
      exact padGood_of (Or.inr (by simp only [walkBase_zero]; omega)) (by
        simp only [walkBase_zero]; rw [chainStride_eq, hsz] at this hX; rw [hb0]; omega)

/-- **A later arm's facts**: its slots and outputs the group's real ones, as the shared template
lays them out from `B + 5`. -/
theorem spArmPos_facts {B first n : Nat} {fold : Bool} {prodIn encIn : V} {k a : Nat} (hB : 13 ≤ B)
    (hn : n ≤ 3) (hk : k ≠ 0) (hpi : NBv B prodIn) (hei : NBv B encIn)
    (ha : groupStart fold (B + 5) + chainStride (spWp B) * n + 2 ≤ a)
    (hX : walkBase 3 k 0 n (if fold then a + 1 else a) + 1 ≤ spVPad) :
    SpArmFacts B (slotsT (spWp B) fold (B + 5)) first n fold prodIn encIn
      (prodT (spWp B) fold n (B + 5)) (encT (spWp B) fold n (B + 5)) k a
      (walkBase 3 k 0 n (if fold then a + 1 else a) + 1) := by
  have hW := spGood_shape (B := B) (by omega)
  have hc := spGood_canon (B := B) (by omega)
  have hsz : (spWp B).size = 3 := rfl
  have hds := digitSum_le_nine' k n hn
  obtain ⟨l1, l2, l3⟩ := armPos_lay (spWp B) fold (n := n) (k := k) (a := a) (le_refl (B + 5)) ha
  have hgs : B + 5 + 5 ≤ groupStart fold (B + 5) := by rw [groupStart_eq]; split <;> omega
  have hws2 := walksT_snd (spWp B) (slotsT (spWp B) fold (B + 5)) first k (spWp B).size n 0
    (if fold then a + 1 else a)
  have hb0 : a ≤ (if fold then a + 1 else a) := by split <;> omega
  have hb0f : fold = true → a + 1 ≤ (if fold then a + 1 else a) := by intro hf; simp [hf]
  have hwb := walkBase_le (spWp B).size k (if fold then a + 1 else a) (Nat.zero_le n)
  simp only [walkBase] at hwb
  have hR : ∀ x, WalksR (slotsT (spWp B) fold (B + 5)) (spWp B).size k n (if fold then a + 1 else a) x →
      x ≠ .n (groupStart fold (B + 5) + chainStride (spWp B) * n) ∧
      x ≠ .n (groupStart fold (B + 5) + chainStride (spWp B) * n + 1) ∧
      (fold = true → x ≠ .n a) ∧
      (k ≠ 0 → x ≠ .n (walksT (spWp B) (slotsT (spWp B) fold (B + 5)) first k (spWp B).size n 0
        (if fold then a + 1 else a)).2) := by
    intro x hx
    obtain ⟨j, rfl, h⟩ := l3 x hx
    rw [hws2]
    refine ⟨fun e => ?_, fun e => ?_, fun hf e => ?_, fun _ e => ?_⟩ <;>
      simp only [V.mk.injEq, true_and] at e <;> rcases h with h | h
    all_goals first | omega | (have := hb0f hf; omega)
  have hssa := armT_ssa (first := first) (prodIn := prodIn) (encIn := encIn)
    (po := groupStart fold (B + 5) + chainStride (spWp B) * n)
    (eo := groupStart fold (B + 5) + chainStride (spWp B) * n + 1) (k := k) (b := a) hW
    (by simpa [hk] using l1) (by simpa [hk] using l2) (hpi.mono' (by omega)) (hei.mono' (by omega))
    ⟨_, by omega, rfl⟩ (by omega) (by omega) (by omega) (fun hf => ⟨by omega, by omega⟩)
    (by simpa [hk] using hR)
    (fun _ => ⟨by rw [hws2]; rintro ⟨j, hj, e⟩; simp only [V.mk.injEq, true_and] at e; omega,
      by rw [hws2]; omega, by rw [hws2]; omega, fun hf => by rw [hws2]; have := hb0f hf; omega⟩)
  have hwe : walkBase (spWp B).size k 0 n (if fold then a + 1 else a) =
      walkBase 3 k 0 n (if fold then a + 1 else a) := rfl
  have hE : ∀ x, WalksR (slotsT (spWp B) fold (B + 5)) (spWp B).size k n (if fold then a + 1 else a) x →
      ∃ j, x = .n j ∧ B + 5 ≤ j ∧ j < walkBase 3 k 0 n (if fold then a + 1 else a) + 1 := by
    intro x hx
    obtain ⟨j, rfl, h⟩ := l3 x hx
    rcases h with h | h
    · exact ⟨j, rfl, by omega, by omega⟩
    · exact ⟨j, rfl, by omega, by omega⟩
  have l1' : ∀ t < n, WalkLay (spWp B) (B + 5) (slotsT (spWp B) fold (B + 5) t)
      (if k = 0 then (spWp B).size + 13 else (spWp B).size) (dig k t)
      (walkBase (if k = 0 then (spWp B).size + 13 else (spWp B).size) k 0 t (if fold then a + 1 else a)) := by
    simpa [hk] using l1
  have l2' : ∀ t < n, ∀ t' < n, t ≠ t' → ∀ x,
      WalkR (slotsT (spWp B) fold (B + 5) t) (if k = 0 then (spWp B).size + 13 else (spWp B).size) (dig k t)
        (walkBase (if k = 0 then (spWp B).size + 13 else (spWp B).size) k 0 t (if fold then a + 1 else a)) x →
      ¬ WalkR (slotsT (spWp B) fold (B + 5) t') (if k = 0 then (spWp B).size + 13 else (spWp B).size) (dig k t')
        (walkBase (if k = 0 then (spWp B).size + 13 else (spWp B).size) k 0 t' (if fold then a + 1 else a)) x := by
    simpa [hk] using l2
  refine ⟨hssa.1, fun x hx => ?_, fun x hx => ?_, fun σ hg hs => ?_, l1', fun t ht => ?_,
    armStart_ne (S := if k = 0 then 3 + 13 else 3) rfl l2', fun t ht => ?_, fun x hx => ?_⟩
  · rcases hssa.2 x hx with h | rfl | rfl | ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact hE x (by simpa [hk] using h)
    · exact ⟨_, rfl, by omega, by omega⟩
    · exact ⟨_, rfl, by omega, by omega⟩
    · exact ⟨_, rfl, by omega, by omega⟩
    · rw [hws2]; exact ⟨_, rfl, by omega, by omega⟩
  · refine armT_vals hW l1' l2'
      (P := fun x => ∃ j, x = .n j ∧ j < walkBase 3 k 0 n (if fold then a + 1 else a) + 1)
      (fun x ⟨j, hj, e⟩ => ⟨j, e, by omega⟩)
      (fun x hx => let ⟨j, e, _, h⟩ := hE x (by simpa [hk] using hx); ⟨j, e, h⟩)
      ⟨⟨_, rfl, by omega⟩, ⟨_, rfl, by omega⟩, ⟨_, rfl, by omega⟩,
        let ⟨j, hj, e⟩ := hpi; ⟨j, e, by omega⟩, let ⟨j, hj, e⟩ := hei; ⟨j, e, by omega⟩,
        ⟨_, rfl, by omega⟩, ⟨_, by rw [hws2], by omega⟩⟩ x hx
  · exact armT_canon hW hc l1' l2' (by omega) (by simpa [hk] using hR) hssa.1 σ hg hs
  · unfold armStart walkStartV
    simp only [hk, ↓reduceIte, spW]
    have hwt := walkBase_le 3 k (if fold then a + 1 else a) (Nat.zero_le t)
    have hwt' := walkBase_le 3 k (if fold then a + 1 else a) (show t + 1 ≤ n by omega)
    simp only [walkBase] at hwt
    split
    · have := slot_bounds (spWp B) fold (B + 5) t 2 (by norm_num)
      have : chainStride (spWp B) * (t + 1) ≤ chainStride (spWp B) * n := Nat.mul_le_mul_left _ (by omega)
      exact ⟨_, rfl, by omega, by omega⟩
    · rename_i h3
      have hlt := walkBase_lt_succ 3 k (if fold then a + 1 else a) t h3
      exact ⟨_, rfl, by omega, by omega⟩
  · have := slot_bounds (spWp B) fold (B + 5) t 2 (by norm_num)
    have : chainStride (spWp B) * (t + 1) ≤ chainStride (spWp B) * n := Nat.mul_le_mul_left _ (by omega)
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    obtain ⟨jp, hjp, rfl⟩ := hpi
    obtain ⟨je, hje, rfl⟩ := hei
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact padGood_of (Or.inr (by omega)) (by omega)
    · exact padGood_of (Or.inr (by omega)) (by omega)
    · exact padGood_of (Or.inr (by omega)) (by omega)
    · exact padGood_of (Or.inl hjp) (by omega)
    · exact padGood_of (Or.inl hje) (by omega)
    · exact padGood_of (Or.inl (by omega)) (by omega)
    · exact padGood_of (Or.inr (by omega)) (by omega)

end
end LeanVM.Guest.B1.Sig
