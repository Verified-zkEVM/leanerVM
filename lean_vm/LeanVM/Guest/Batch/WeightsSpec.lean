/-
  LeanVM.Guest.Batch.WeightsSpec

  The batching after its children, stopped at the matrices' weights and accepting when both
  vanish, and its doom specification: the weight of `A0` is not identically zero in the
  challenges still to come, and each group of challenges escapes with probability at most
  `1/|E|`.
-/

module

public import LeanVM.Guest.Batch.RomSpec

/-!
# The matrices' weights: a doom specification

At the end of a node's batching the matrices' final check reads two weights
(`Guest.Batch.Matrix`):

    w_A(λ, z) = Σ_i λ_i,1 · freshWeight(f_i, z) + λ_i,2 · eq(p_i, z),

`λ` the matrices' lambdas (a triple per child) and `z` the challenges of the matrices' sumcheck
(`2 · blake2sR1csLogSize = 28` coordinates). The honest prover solves the final check for the
matrices' values, which it can do unless both weights vanish (T6-det's good event G2,
`docs/roadmap/t6-prob.md` §1.4). `weightsRest bytecode cs` is the batching after the children `cs`
cut there: the bytecode's lambdas and sumcheck, the matrices' lambdas and sumcheck, then it
*accepts* when both weights vanish. `weightsRestSpec` is its doom specification, for children of
the bytecode's shapes, at least one:

* **the start**: `w_A` is not the zero function of `(λ, z)`: at `λ_0,2 = 1`, the other lambdas
  `0` and `z = p_0`, it is `eq(p_0, p_0) = Π (1 + 2 p) = 1` (characteristic two);
* **the bytecode's side**: a fact the challenges do not touch (`constSpec`);
* **the matrices' lambdas**: `w_A` is linear in `λ` with coefficients functions of `z`
  (`weightGaps`): doom is the lambdas' doom of `RomSpec` at some point `z` (`FDoom`), and the
  whole group escapes at most at the last nonzero coefficient, for one value: `1/|E|`;
* **the matrices' rounds**: some completion of the challenges so far has `w_A ≠ 0` (`ZDoom`).
  `w_A` is affine in each coordinate (`Multilinear`), so two values of a challenge that kill every
  completion would kill every completion of every value: one bad value, `1/|E|`;
* **the check**: all challenges drawn, `w_A ≠ 0`, so the program rejects.
-/

namespace LeanVM.Guest.Batch

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node
open scoped ENNReal

@[expose] public section

-- Two enumerations of `K` are in scope here (`LeanVM.Parameters`' and `LeanDa`'s); the
-- calculus (`Spec.sampleE`, `Spec.sample`) counts `E` with the first.
attribute [local instance 1100] LeanVM.Parameters.instFintypeK

/-! ## Lambdas against functions -/

section Fun

variable {Z : Type}

/-- The coefficients `G` at the point `z`. -/
def gapsAt (G : List (Z → E)) (z : Z) : List E := G.map fun g ↦ g z

theorem getD_gapsAt (G : List (Z → E)) (z : Z) (i : ℕ) :
    (gapsAt G z).getD i 0 = G.getD i 0 z := by
  unfold gapsAt
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases G[i]? <;> simp

/-- **Doom of the lambdas against functions**: at some point, the lambdas' doom of the
coefficients there. -/
def FDoom (G : List (Z → E)) (ls : List E) : Prop := ∃ z, LDoom (gapsAt G z) ls

/-- The function is not zero. -/
def FNz (g : Z → E) : Prop := ∃ z, g z ≠ 0

/-- The `k`-th coefficient is the last nonzero one. -/
def FLast (G : List (Z → E)) (k : ℕ) : Prop :=
  FNz (G.getD k 0) ∧ ∀ i, k < i → ∀ z, G.getD i 0 z = 0

open Classical in
/-- The escape bound of the `k`-th lambda: `1/|E|` at the last nonzero coefficient, else `0`. -/
noncomputable def fLamE (G : List (Z → E)) (k : ℕ) : ℝ≥0∞ := if FLast G k then invE else 0

open Classical in
/-- The lead of the lambdas from the `k`-th: `1/|E|` while a nonzero coefficient is to come. -/
noncomputable def fLamLead (G : List (Z → E)) (k : ℕ) : ℝ≥0∞ :=
  if ∃ i, k ≤ i ∧ FNz (G.getD i 0) then invE else 0

theorem fLamLead_le (G : List (Z → E)) (k : ℕ) : fLamLead G k ≤ invE := by
  unfold fLamLead; split_ifs
  · exact le_rfl
  · exact zero_le

/-- A lambda's escape bound and the next lead fit in the lead. -/
theorem fLamE_add_le (G : List (Z → E)) (k : ℕ) :
    fLamE G k + fLamLead G (k + 1) ≤ fLamLead G k := by
  unfold fLamE fLamLead
  by_cases h1 : ∃ i, k + 1 ≤ i ∧ FNz (G.getD i 0)
  · obtain ⟨i, hi, hne⟩ := h1
    have hn : ¬ FLast G k := fun h ↦ by
      obtain ⟨z, hz⟩ := hne
      exact hz (h.2 i hi z)
    have h0 : ∃ i, k ≤ i ∧ FNz (G.getD i 0) := ⟨i, by omega, hne⟩
    have h1 : ∃ i, k + 1 ≤ i ∧ FNz (G.getD i 0) := ⟨i, hi, hne⟩
    simp only [hn, h0, h1, ite_true, ite_false, zero_add, le_refl]
  · simp only [h1, ite_false, add_zero]
    split_ifs with hL h0
    · exact le_rfl
    · exact absurd ⟨k, le_rfl, hL.1⟩ h0
    · exact zero_le
    · exact le_rfl

/-- Away from the last nonzero coefficient, a lambda keeps doom. -/
theorem fDoom_concat {G : List (Z → E)} {ls : List E} (h : ¬ FLast G ls.length)
    (hd : FDoom G ls) (c : E) : FDoom G (ls ++ [c]) := by
  by_cases hi : ∃ i, ls.length < i ∧ FNz (G.getD i 0)
  · obtain ⟨i, hi, z, hz⟩ := hi
    exact ⟨z, .inl ⟨i, by simp; omega, by rwa [getD_gapsAt]⟩⟩
  · have hz : ∀ i, ls.length < i → ∀ z, G.getD i 0 z = 0 := fun i hi' z ↦
      by_contra fun hne ↦ hi ⟨i, hi', z, hne⟩
    have hk : ∀ z, G.getD ls.length 0 z = 0 := fun z ↦ by_contra fun hne ↦ h ⟨⟨z, hne⟩, hz⟩
    obtain ⟨z, hd⟩ := hd
    refine ⟨z, ?_⟩
    rcases hd with ⟨i, hi', hne⟩ | hp
    · rw [getD_gapsAt] at hne
      rcases hi'.lt_or_eq with hlt | rfl
      · exact absurd (hz i hlt z) hne
      · exact absurd (hk z) hne
    · exact .inr (by rwa [psum_concat, getD_gapsAt, hk, mul_zero, add_zero])

/-- At a nonzero coefficient, at most one lambda breaks doom. -/
theorem eq_of_not_fDoom {G : List (Z → E)} {ls : List E} {c c' : E}
    (hg : FNz (G.getD ls.length 0)) (hc : ¬ FDoom G (ls ++ [c]))
    (hc' : ¬ FDoom G (ls ++ [c'])) : c = c' := by
  obtain ⟨z, hz⟩ := hg
  have hz' : (gapsAt G z).getD ls.length 0 ≠ 0 := by rwa [getD_gapsAt]
  rw [eq_of_not_lDoom hz' fun h ↦ hc ⟨z, h⟩, eq_of_not_lDoom hz' fun h ↦ hc' ⟨z, h⟩]

/-- The bad lambdas at position `k` are a fraction `fLamE G k` of the challenges. -/
theorem fLam_bad {G : List (Z → E)} {ls : List E} {k : ℕ} (hk : ls.length = k) (hd : FDoom G ls)
    {_ : DecidablePred fun c ↦ ¬ FDoom G (ls ++ [c])} :
    invE * ((Finset.univ.filter fun c ↦ ¬ FDoom G (ls ++ [c])).card : ℝ≥0∞) ≤ fLamE G k := by
  subst hk
  unfold fLamE
  split_ifs with hL
  · refine (card_filter_le (m := 1) ?_).trans (by simp)
    exact (Set.ncard_le_one (Set.toFinite _)).2 fun a ha b hb ↦ eq_of_not_fDoom hL.1 ha hb
  · refine (card_filter_le (m := 0) ?_).trans (by simp)
    have he : {c | ¬ FDoom G (ls ++ [c])} = ∅ :=
      Set.eq_empty_iff_forall_notMem.2 fun c hc ↦ hc (fDoom_concat hL hd c)
    rw [he, Set.ncard_empty]

/-- **A lambda**, the `k`-th: doom kept but for a fraction `fLamE G k` of the challenges. -/
noncomputable def fLamStep (G : List (Z → E)) (k : ℕ) (ls : List E) (hk : ls.length = k) :
    Spec Prog.sampleE (fun _ ↦ FDoom G ls) (fun c _ ↦ FDoom G (ls ++ [c])) invE
      (fLamLead G k) (fLamLead G (k + 1)) :=
  (Spec.sampleE (Pre := fun _ ↦ FDoom G ls) (Post := fun c _ ↦ FDoom G (ls ++ [c]))
      (T := fLamLead G (k + 1)) (fLamE G k) fun _ hd ↦ fLam_bad hk hd).mono
    (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl (fLamE_add_le G k) le_rfl

/-- **The matrices' lambdas against functions** from the `k`-th, after `ls`. -/
noncomputable def fLamSpecM (G : List (Z → E)) : (n k : ℕ) → (ls : List E) → ls.length = k →
    Spec (sampleLM n) (fun _ ↦ FDoom G ls)
      (fun l _ ↦ l.length = n ∧ FDoom G (ls ++ flat3 l)) invE (fLamLead G k) 0
  | 0, _, _, _ => (Spec.ret []).mono (fun _ h ↦ ⟨rfl, by simpa using h⟩) (fun _ _ h ↦ h)
      le_rfl (zero_le) le_rfl
  | n + 1, k, ls, hk =>
    (fLamStep G k ls hk).bind' fun a ↦
      (fLamStep G (k + 1) (ls ++ [a]) (by simp [hk])).bind' fun b ↦
        (fLamStep G (k + 1 + 1) (ls ++ [a] ++ [b]) (by simp [hk])).bind' fun c ↦
          (fLamSpecM G n (k + 1 + 1 + 1) (ls ++ [a] ++ [b] ++ [c]) (by simp [hk])).bind' fun l ↦
            (Spec.ret ((a, b, c) :: l)).mono (fun _ h ↦ ⟨by simp [h.1], by simpa using h.2⟩)
              (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

end Fun

/-! ## The weight of `A0` as a combination of the lambdas -/

/-- Points of the matrices' sumcheck: `2 · blake2sR1csLogSize` coordinates. -/
abbrev MPoint : Type := {z : List E // z.length = 2 * blake2sR1csLogSize}

/-- **The coefficients of the weight of `A0`** as functions of the point: per child, its proof's
weight, its statement's equality weight, and nothing for its third lambda. -/
def weightGaps (cs : List ChildClaims) : List (MPoint → E) :=
  cs.flatMap fun c ↦
    [fun z ↦ freshWeight c.fresh z.1, fun z ↦ eqEval c.carried.matrixPoint z.1, fun _ ↦ 0]

/-- A dot product, the first terms split off. -/
theorem dot_cons_E (a b : E) (l r : List E) : dot (a :: l) (b :: r) = a * b + dot l r := by
  show sumE _ = a * b + sumE _
  rw [Whir.Complete.sumE_eq, Whir.Complete.sumE_eq, List.zipWith_cons_cons, List.sum_cons]

/-- The weight of `A0`, the first child split off. -/
theorem matrixWeightA_cons (c : ChildClaims) (cs : List ChildClaims) (l : E × E × E)
    (lM : List (E × E × E)) (z : List E) :
    matrixWeightA (c :: cs) (l :: lM) z =
      (l.1 * freshWeight c.fresh z + l.2.1 * eqEval c.carried.matrixPoint z) +
        matrixWeightA cs lM z := by
  simp only [matrixWeightA, List.zipWith_cons_cons, Whir.Complete.sumE_eq, List.sum_cons]

/-- **The weight of `A0` is the lambdas' combination of its coefficients.** -/
theorem dot_weightGaps : ∀ (cs : List ChildClaims) (lM : List (E × E × E)),
    lM.length = cs.length → ∀ z : MPoint,
      dot (flat3 lM) (gapsAt (weightGaps cs) z) = matrixWeightA cs lM z.1
  | [], [], _, z => by simp [dot, matrixWeightA, sumE, gapsAt, weightGaps]
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | c :: cs, l :: lM, h, z => by
    have ih := dot_weightGaps cs lM (by simpa using h) z
    have e1 : flat3 (l :: lM) = l.1 :: l.2.1 :: l.2.2 :: flat3 lM := by simp
    have e2 : gapsAt (weightGaps (c :: cs)) z = freshWeight c.fresh z.1 ::
        eqEval c.carried.matrixPoint z.1 :: 0 :: gapsAt (weightGaps cs) z := by
      simp [gapsAt, weightGaps]
    rw [e1, e2, dot_cons_E, dot_cons_E, dot_cons_E, ih, matrixWeightA_cons]
    ring

/-- The equality weight of a point with itself is `1`: `1 + 2p = 1` in characteristic two. -/
theorem eqEval_self : ∀ p : List E, eqEval p p = 1
  | [] => rfl
  | x :: p => by
    rw [Whir.Complete.eqEval_cons, eqEval_self p, mul_one]
    linear_combination x * Whir.Complete.two_eq_zero_E

/-- **The weight of `A0` is not the zero function** of the lambdas and the point, for at least
one child of the bytecode's shapes: the start is doomed. -/
theorem fDoom_weightGaps_nil {bytecode : List K} {cs : List ChildClaims}
    (hs : ∀ c ∈ cs, ChildShaped bytecode c) (hne : cs ≠ []) : FDoom (weightGaps cs) [] := by
  obtain ⟨c, cs', rfl⟩ := List.exists_cons_of_ne_nil hne
  refine ⟨⟨c.carried.matrixPoint, (matrixShaped hs c List.mem_cons_self).2.2.2⟩,
    .inl ⟨1, Nat.zero_le _, ?_⟩⟩
  rw [getD_gapsAt]
  simp [weightGaps, eqEval_self]

/-- Lambdas drawn in doom leave a point where the weight of `A0` is not zero. -/
theorem weightA_ne_of_fDoom {cs : List ChildClaims} {lM : List (E × E × E)}
    (hl : lM.length = cs.length) (hd : FDoom (weightGaps cs) ([] ++ flat3 lM)) :
    ∃ z : MPoint, matrixWeightA cs lM z.1 ≠ 0 := by
  obtain ⟨z, hz⟩ := hd
  refine ⟨z, ?_⟩
  rw [← dot_weightGaps cs lM hl z]
  refine dot_ne_of_lDoom ?_ (by simpa using hz)
  rw [length_flatMap_const _ 3 (fun _ ↦ rfl), gapsAt, List.length_map, weightGaps,
    length_flatMap_const _ 3 (fun _ ↦ rfl), hl]

/-- The weight of `A0` is multilinear, for children of the matrices' shapes. -/
theorem multilinear_matrixWeightA : ∀ {cs : List ChildClaims}, (∀ c ∈ cs, MatrixShaped c) →
    ∀ lM : List (E × E × E), Multilinear (2 * blake2sR1csLogSize) (matrixWeightA cs lM)
  | [], _, lM => by intro pre post _ x; simp [matrixWeightA, sumE]
  | _ :: _, _, [] => by intro pre post _ x; simp [matrixWeightA, sumE]
  | c :: cs, hs, l :: lM => by
    obtain ⟨hrow, hcol, hsl, hmp⟩ := hs c List.mem_cons_self
    have hf : Multilinear (2 * blake2sR1csLogSize) (freshWeight c.fresh) :=
      multilinear_freshWeight hrow hcol hsl
    have h := ((hf.const_mul l.1).add ((multilinear_eqEval hmp).const_mul l.2.1)).add
      (multilinear_matrixWeightA (fun c' h' ↦ hs c' (List.mem_cons_of_mem _ h')) lM)
    intro pre post hlen x
    simp only [matrixWeightA_cons]
    exact h pre post hlen x

/-! ## The rounds -/

/-- **Doom of the matrices' rounds** after the challenges `pre`: some completion to a point of
`n` coordinates where `W` is not zero. -/
def ZDoom (n : ℕ) (W : List E → E) (pre : List E) : Prop :=
  ∃ w : List E, pre.length + w.length = n ∧ W (pre ++ w) ≠ 0

/-- **A challenge breaks doom for at most one value**: `W` is affine in it. -/
theorem eq_of_not_zDoom {n : ℕ} {W : List E → E} (hW : Multilinear n W) {pre : List E}
    (hl : pre.length < n) (hd : ZDoom n W pre) {r r' : E} (hr : ¬ ZDoom n W (pre ++ [r]))
    (hr' : ¬ ZDoom n W (pre ++ [r'])) : r = r' := by
  obtain ⟨w, hw, hne⟩ := hd
  obtain ⟨y, post, rfl⟩ : ∃ y post, w = y :: post := by
    cases w with
    | nil => simp at hw; omega
    | cons y post => exact ⟨y, post, rfl⟩
  have hlen : pre.length + 1 + post.length = n := by simp at hw; omega
  have z1 : W (pre ++ r :: post) = 0 := by
    by_contra h
    exact hr ⟨post, by simp; omega, by simpa using h⟩
  have z2 : W (pre ++ r' :: post) = 0 := by
    by_contra h
    exact hr' ⟨post, by simp; omega, by simpa using h⟩
  have e := hW pre post hlen r
  have e' := hW pre post hlen r'
  have e'' := hW pre post hlen y
  by_contra hrr
  have hab : W (pre ++ 0 :: post) + W (pre ++ 1 :: post) = 0 := by
    have h : (r - r') * (W (pre ++ 0 :: post) + W (pre ++ 1 :: post)) = 0 := by
      linear_combination (z1 - e) - (z2 - e')
    exact (mul_eq_zero.1 h).resolve_left (sub_ne_zero.2 hrr)
  have ha : W (pre ++ 0 :: post) = 0 := by linear_combination (z1 - e) - r * hab
  have hb : W (pre ++ 1 :: post) = 0 := by linear_combination hab - ha
  exact hne (by linear_combination e'' + (1 + y) * ha + y * hb)

/-- **The matrices' rounds** from `claim`, after the challenges `pre`: some completion with `W`
not zero leaves `W` not zero at the challenges, each challenge escaping at most `1/|E|` of the
time. -/
noncomputable def zRoundsSpec {n : ℕ} {W : List E → E} (hW : Multilinear n W) :
    (k : ℕ) → (claim : E) → (pre : List E) → pre.length + k = n →
    Spec (roundsProg claim k) (fun _ ↦ ZDoom n W pre) (fun r _ ↦ W (pre ++ r.1) ≠ 0) invE 0 0
  | 0, claim, pre, hk => (Spec.ret (Post := fun r _ ↦ W (pre ++ r.1) ≠ 0) ([], claim)).mono
      (fun _ h ↦ by
        obtain ⟨w, hw, hne⟩ := h
        obtain rfl : w = [] := List.eq_nil_of_length_eq_zero (by omega)
        exact hne) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
  | k + 1, claim, pre, hk =>
    (Spec.readE (Pre := fun _ ↦ ZDoom n W pre) (Post := fun _ _ ↦ ZDoom n W pre) (T := 0)
        (fun _ _ h ↦ h) (zero_le)).bind' fun g1 ↦
      (Spec.readE (Pre := fun _ ↦ ZDoom n W pre) (Post := fun _ _ ↦ ZDoom n W pre)
          (T := invE + 0) (fun _ _ h ↦ h) (add_zero _).le).bind' fun gInf ↦
        (Spec.sampleE (Pre := fun _ ↦ ZDoom n W pre)
            (Post := fun r _ ↦ ZDoom n W (pre ++ [r])) (T := 0) invE fun _ h ↦ by
              refine (card_filter_le (m := 1) ?_).trans (by simp)
              exact (Set.ncard_le_one (Set.toFinite _)).2 fun a ha b hb ↦
                eq_of_not_zDoom hW (by omega) h ha hb).bind' fun r ↦
          (zRoundsSpec hW k _ (pre ++ [r]) (by simp; omega)).bind' fun rest ↦
            (Spec.ret (r :: rest.1, rest.2)).mono (fun _ h ↦ by simpa using h)
              (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

/-- Lambdas drawn in doom leave the rounds doomed at their start. -/
theorem zDoom_of_fDoom {cs : List ChildClaims} {lM : List (E × E × E)}
    (hl : lM.length = cs.length) (hd : FDoom (weightGaps cs) ([] ++ flat3 lM)) :
    ZDoom (2 * blake2sR1csLogSize) (matrixWeightA cs lM) [] := by
  obtain ⟨z, hz⟩ := weightA_ne_of_fDoom hl hd
  exact ⟨z.1, by simp [z.2], by simpa using hz⟩

/-! ## The program and its specification -/

/-- **The batching after its children, stopped at the matrices' weights**: the bytecode's lambdas
and sumcheck, the matrices' lambdas and sumcheck, then acceptance when both weights vanish. -/
noncomputable def weightsRest (bytecode : List K) (cs : List ChildClaims) : Prog Bool := do
  let lB ← sampleLB cs.length
  let _ ← roundsProg (claimBOf cs lB) (Nat.log2 bytecode.length)
  let lM ← sampleLM cs.length
  let rm ← roundsProg (claimMOf cs lM) (2 * blake2sR1csLogSize)
  Prog.require (matrixWeightA cs lM rm.1 = 0 ∧ matrixWeightB cs lM rm.1 = 0)
  return true

/-- **The doom specification of the weights' program** after at least one child of the
bytecode's shapes: doom at the start, rejection at the end, each group of challenges escaping at
most `1/|E|`. -/
noncomputable def weightsRestSpec {bytecode : List K} {cs : List ChildClaims}
    (hs : ∀ c ∈ cs, ChildShaped bytecode c) (hne : cs ≠ []) :
    Spec (weightsRest bytecode cs) (fun h ↦ h = []) (fun b _ ↦ b = false) invE invE 0 :=
  ((constSpec _ (FDoom (weightGaps cs) []) (fLamLead_le (weightGaps cs) 0)).bind' fun lB ↦
    (constSpec _ (FDoom (weightGaps cs) []) (fLamLead_le (weightGaps cs) 0)).bind' fun _ ↦
      (fLamSpecM (weightGaps cs) cs.length 0 [] rfl).bind' fun lM ↦
        ((zRoundsSpec (multilinear_matrixWeightA (matrixShaped hs) lM) _ (claimMOf cs lM) []
            (by simp)).mono (fun _ h ↦ zDoom_of_fDoom h.1 h.2) (fun _ _ h ↦ h) le_rfl le_rfl
            le_rfl).bind' fun rm ↦
          (Spec.require (Post := fun _ _ ↦ False) fun _ hφ hc ↦ hφ (by
              rw [List.nil_append]; exact hc.1)).bind' fun _ ↦
            Spec.dead).mono
    (fun _ _ ↦ fDoom_weightGaps_nil hs hne) (fun _ _ h ↦ h) le_rfl (fLamLead_le _ _) le_rfl

end
end LeanVM.Guest.Batch
