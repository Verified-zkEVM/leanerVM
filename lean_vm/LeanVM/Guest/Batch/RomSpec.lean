/-
  LeanVM.Guest.Batch.RomSpec

  The doom specification of the batching after its children: children with a false claim leave
  the prover doomed, and each group of challenges escapes with probability at most `2/|E|`.
-/

module

public import LeanVM.Guest.Batch.Prog
public import LeanVM.Protocol.Compile.SpecRules.Cert
public import LeanVM.Protocol.Compile.SpecRules.Leaves

/-!
# The batching's doom specification

For children `cs` of the bytecode's shapes with some nonzero gap (`SomeGap`), `restSpec` is a
specification (`LeanVM.Protocol.Compile.Spec`) of `batchRest bytecode cs` from the empty history,
with doom at the start, rejection at the end, and every group of challenges escaping doom with
probability at most `batchε = 2/|E|`:

* **the lambdas**: the partial combination of the gaps with the lambdas drawn so far is nonzero,
  or a nonzero gap is still to come. A lambda breaks it only at the last nonzero gap, and there
  for one value: the group escapes with probability at most `1/|E|`;
* **a round**: the claim is not the cube sum after the earlier challenges (`cubeSum`); the
  round's messages keep it, and its challenge breaks it at a root of the round's gap, a nonzero
  quadratic: at most `2/|E|` (`quadratic_roots`);
* **the final value and the check**: the final claim, not the polynomial at the challenges,
  contradicts the check and the deferred claim's truth, so the program rejects.
-/

namespace LeanVM.Guest.Batch

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node
open scoped ENNReal

@[expose] public section

/-- The batching's escape bound per group of challenges: `2/|E|`. -/
noncomputable def batchε : ℝ≥0∞ := 2 / Fintype.card E

/-- Some child's claim leaves a nonzero gap. -/
def SomeGap (bytecode : List K) (cs : List ChildClaims) : Prop :=
  ∃ g ∈ gapsB bytecode cs, g ≠ 0

-- Two enumerations of `K` are in scope here (`LeanVM.Parameters`' and `LeanDa`'s); the
-- calculus (`Spec.sampleE`, `Spec.sample`) counts `E` with the first.
attribute [local instance 1100] LeanVM.Parameters.instFintypeK

/-- `|E|⁻¹`, the escape bound of a group of lambdas. -/
noncomputable abbrev invE : ℝ≥0∞ := (Fintype.card E : ℝ≥0∞)⁻¹

/-- `batchε` is twice `|E|⁻¹`, whichever enumeration of `E` counts it. -/
theorem batchε_eq : batchε = invE * 2 := by
  simp only [batchε, invE, ENNReal.div_eq_inv_mul, Fintype.card_eq_nat_card]

/-- A lambda group's bound is within `batchε`. -/
theorem invE_le_batchε : invE ≤ batchε := by
  rw [batchε_eq]
  exact le_mul_of_one_le_right zero_le one_le_two

/-- The average of a constant over the challenges is the constant. -/
theorem avg_const (v : ℝ≥0∞) : invE * ∑ _c : E, v = v := by
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
    ENNReal.inv_mul_cancel (by simp) (by simp), one_mul]

/-- A fraction of the challenges from a bound on the set they form. -/
theorem card_filter_le {p : E → Prop} {_ : DecidablePred p} {m : ℕ} (h : {c | p c}.ncard ≤ m) :
    invE * ((Finset.univ.filter p).card : ℝ≥0∞) ≤ invE * m := by
  gcongr
  rw [← Set.ncard_coe_finset]
  simpa using h

/-! ## Constant doom -/

open Classical in
/-- **Constant doom**: any program keeps a doom that ignores the history, at the potential the
follower's lead. -/
noncomputable def constSpec {α : Type} (p : Prog α) (φ : Prop) {εmax T : ℝ≥0∞}
    (hT : T ≤ εmax) : Spec p (fun _ ↦ φ) (fun _ _ ↦ φ) εmax T T where
  D _ _ := φ
  V _ _ := if φ then min 1 T else 1
  le_one _ _ := by split_ifs <;> simp
  start_D _ h := h
  start_V _ h := by simp [h]
  read := fun _ _ _ h ↦ h
  grind := fun _ _ h ↦ h
  commit := fun _ _ _ _ h ↦ h
  sample := fun _ _ ↦ (avg_const _).le
  query := fun _ _ _ ↦ le_rfl
  moveEnd := fun _ _ _ hD ↦ by simp [hD]
  retEnd := fun _ _ hD ↦ by simp [hD]
  retDoom := fun _ _ hD ↦ by simp [hD]
  post := fun _ _ hD ↦ hD
  bound := fun _ _ _ hD ↦ by
    simp only [hD, ite_true]
    calc _ ≤ 1 * min 1 T := by
          gcongr; exact pow_le_one₀ (zero_le) (ENNReal.inv_le_one.2 one_le_two)
      _ ≤ εmax := by rw [one_mul]; exact (min_le_right _ _).trans hT

/-! ## The lambdas -/

/-- The combination of the gaps `G` with the lambdas `ls` drawn so far. -/
def psum (G ls : List E) : E := ∑ i ∈ Finset.range ls.length, ls.getD i 0 * G.getD i 0

/-- **Doom of the lambdas** `ls` drawn so far: a nonzero gap is still to come, or the partial
combination is nonzero. -/
def LDoom (G ls : List E) : Prop := (∃ i, ls.length ≤ i ∧ G.getD i 0 ≠ 0) ∨ psum G ls ≠ 0

/-- The `k`-th gap is the last nonzero one. -/
def LastGap (G : List E) (k : ℕ) : Prop := G.getD k 0 ≠ 0 ∧ ∀ i, k < i → G.getD i 0 = 0

open Classical in
/-- The escape bound of the `k`-th lambda: `1/|E|` at the last nonzero gap, else `0`. -/
noncomputable def lamE (G : List E) (k : ℕ) : ℝ≥0∞ := if LastGap G k then invE else 0

open Classical in
/-- The lead of the lambdas from the `k`-th: `1/|E|` while a nonzero gap is to come. -/
noncomputable def lamLead (G : List E) (k : ℕ) : ℝ≥0∞ :=
  if ∃ i, k ≤ i ∧ G.getD i 0 ≠ 0 then invE else 0

/-- A lambda group's lead is within `batchε`. -/
theorem lamLead_le (G : List E) (k : ℕ) : lamLead G k ≤ batchε := by
  unfold lamLead; split_ifs
  · exact invE_le_batchε
  · exact zero_le

/-- A lambda's escape bound and the next lead fit in the lead. -/
theorem lamE_add_le (G : List E) (k : ℕ) : lamE G k + lamLead G (k + 1) ≤ lamLead G k := by
  unfold lamE lamLead
  by_cases h1 : ∃ i, k + 1 ≤ i ∧ G.getD i 0 ≠ 0
  · obtain ⟨i, hi, hne⟩ := h1
    have hn : ¬ LastGap G k := fun h ↦ hne (h.2 i hi)
    have h0 : ∃ i, k ≤ i ∧ G.getD i 0 ≠ 0 := ⟨i, by omega, hne⟩
    have h1 : ∃ i, k + 1 ≤ i ∧ G.getD i 0 ≠ 0 := ⟨i, hi, hne⟩
    simp only [hn, h0, h1, ite_true, ite_false, zero_add, le_refl]
  · simp only [h1, ite_false, add_zero]
    split_ifs with hL h0
    · exact le_rfl
    · exact absurd ⟨k, le_rfl, hL.1⟩ h0
    · exact zero_le
    · exact le_rfl

/-- One more lambda adds its term to the partial combination. -/
theorem psum_concat (G ls : List E) (c : E) :
    psum G (ls ++ [c]) = psum G ls + c * G.getD ls.length 0 := by
  simp only [psum, List.length_append, List.length_singleton, Finset.sum_range_succ]
  rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero,
    Finset.sum_congr rfl fun i hi ↦ by rw [List.getD_append _ _ _ _ (Finset.mem_range.1 hi)]]

/-- Away from the last nonzero gap, a lambda keeps doom. -/
theorem lDoom_concat {G ls : List E} (h : ¬ LastGap G ls.length) (hd : LDoom G ls) (c : E) :
    LDoom G (ls ++ [c]) := by
  by_cases hi : ∃ i, ls.length < i ∧ G.getD i 0 ≠ 0
  · obtain ⟨i, hi, hne⟩ := hi
    exact .inl ⟨i, by simp; omega, hne⟩
  · have hz : ∀ i, ls.length < i → G.getD i 0 = 0 := fun i hi' ↦
      by_contra fun hne ↦ hi ⟨i, hi', hne⟩
    have hk : G.getD ls.length 0 = 0 := by_contra fun hne ↦ h ⟨hne, hz⟩
    rcases hd with ⟨i, hi', hne⟩ | hp
    · rcases hi'.lt_or_eq with hlt | rfl
      · exact absurd (hz i hlt) hne
      · exact absurd hk hne
    · exact .inr (by rwa [psum_concat, hk, mul_zero, add_zero])

/-- At a nonzero gap, one lambda breaks doom. -/
theorem eq_of_not_lDoom {G ls : List E} {c : E} (hg : G.getD ls.length 0 ≠ 0)
    (hc : ¬ LDoom G (ls ++ [c])) : c = -psum G ls / G.getD ls.length 0 := by
  have hp : psum G (ls ++ [c]) = 0 := by_contra fun hne ↦ hc (.inr hne)
  rw [psum_concat] at hp
  rw [eq_div_iff hg]
  linear_combination hp

/-- The bad lambdas at position `k` are a fraction `lamE G k` of the challenges. -/
theorem lam_bad {G ls : List E} {k : ℕ} (hk : ls.length = k) (hd : LDoom G ls)
    {_ : DecidablePred fun c ↦ ¬ LDoom G (ls ++ [c])} :
    invE * ((Finset.univ.filter fun c ↦ ¬ LDoom G (ls ++ [c])).card : ℝ≥0∞) ≤ lamE G k := by
  subst hk
  unfold lamE
  split_ifs with hL
  · refine (card_filter_le (m := 1) ?_).trans (by simp)
    refine (Set.ncard_le_ncard (t := {-psum G ls / G.getD ls.length 0}) fun c hc ↦ ?_).trans
      (Set.ncard_singleton _).le
    exact eq_of_not_lDoom hL.1 hc
  · refine (card_filter_le (m := 0) ?_).trans (by simp)
    have he : {c | ¬ LDoom G (ls ++ [c])} = ∅ :=
      Set.eq_empty_iff_forall_notMem.2 fun c hc ↦ hc (lDoom_concat hL hd c)
    rw [he, Set.ncard_empty]

/-- **A lambda**, the `k`-th: doom kept but for a fraction `lamE G k` of the challenges. -/
noncomputable def lamStep (G : List E) (k : ℕ) (ls : List E) (hk : ls.length = k) :
    Spec Prog.sampleE (fun _ ↦ LDoom G ls) (fun c _ ↦ LDoom G (ls ++ [c])) batchε
      (lamLead G k) (lamLead G (k + 1)) :=
  (Spec.sampleE (Pre := fun _ ↦ LDoom G ls) (Post := fun c _ ↦ LDoom G (ls ++ [c]))
      (T := lamLead G (k + 1)) (lamE G k) fun _ hd ↦ lam_bad hk hd).mono
    (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl (lamE_add_le G k) le_rfl

/-- **The lambdas** from the `k`-th, after `ls`. -/
noncomputable def lamSpec (G : List E) : (n k : ℕ) → (ls : List E) → ls.length = k →
    Spec (sampleL n) (fun _ ↦ LDoom G ls)
      (fun l _ ↦ l.length = n ∧ LDoom G (ls ++ flat2 l)) batchε (lamLead G k) 0
  | 0, _, _, _ => (Spec.ret []).mono (fun _ h ↦ ⟨rfl, by simpa using h⟩) (fun _ _ h ↦ h)
      le_rfl (zero_le) le_rfl
  | n + 1, k, ls, hk =>
    (lamStep G k ls hk).bind' fun a ↦
      (lamStep G (k + 1) (ls ++ [a]) (by simp [hk])).bind' fun b ↦
        (lamSpec G n (k + 1 + 1) (ls ++ [a] ++ [b]) (by simp [hk])).bind' fun l ↦
          (Spec.ret ((a, b) :: l)).mono (fun _ h ↦ ⟨by simp [h.1], by simpa using h.2⟩)
            (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

/-- A nonzero gap dooms the start. -/
theorem lDoom_nil {G : List E} (h : ∃ g ∈ G, g ≠ 0) : LDoom G [] := by
  obtain ⟨g, hg, hne⟩ := h
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
  exact .inl ⟨i, Nat.zero_le _, by rwa [List.getD_eq_getElem _ _ hi]⟩

/-- All lambdas drawn in doom: the combination is nonzero. -/
theorem dot_ne_of_lDoom {G ls : List E} (hl : ls.length = G.length) (hd : LDoom G ls) :
    dot ls G ≠ 0 := by
  rcases hd with ⟨i, hi, hne⟩ | hp
  · exact absurd (List.getD_eq_default _ _ (by omega)) hne
  · rwa [Whir.Complete.dot_eq_sum _ _ hl]

/-- A flat map of blocks of `m` entries has `m` entries per element. -/
theorem length_flatMap_const {α β : Type} (f : α → List β) (m : ℕ) (hf : ∀ a, (f a).length = m) :
    ∀ l : List α, (l.flatMap f).length = m * l.length
  | [] => by simp
  | a :: l => by
    rw [List.flatMap_cons, List.length_append, hf, length_flatMap_const f m hf l,
      List.length_cons]
    ring

/-! ## The rounds -/

/-- A round's challenge breaks doom at a root of its gap: at most two. -/
theorem round_bad {n : ℕ} {f : List E → E} (hf : QuadraticIn n f) {claim : E} {pre : List E}
    (hl : pre.length < n) (g : E × E) (hc : claim ≠ cubeSum n f pre) :
    {r | ¬ roundPoly claim g r ≠ cubeSum n f (pre ++ [r])}.ncard ≤ 2 := by
  have hq : Quadratic fun x ↦ roundPoly claim g x - cubeSum n f (pre ++ [x]) :=
    Quadratic.sub ⟨g.2, claim + g.1 + g.1 + g.2, claim + g.1, fun x ↦ by
      simp only [roundPoly]; ring⟩ (quadratic_cubeSum hf hl)
  have hne : ∃ x, roundPoly claim g x - cubeSum n f (pre ++ [x]) ≠ 0 := by
    by_contra hz'
    have hz : ∀ x, roundPoly claim g x - cubeSum n f (pre ++ [x]) = 0 := fun x ↦
      by_contra fun hx ↦ hz' ⟨x, hx⟩
    apply hc
    have h0 := hz 0
    have h1 := hz 1
    simp only [roundPoly, sub_eq_zero] at h0 h1
    rw [cubeSum_split hl, ← h0, ← h1]
    linear_combination (-(claim + g.2 + 2 * g.1)) * Whir.Complete.two_eq_zero_E
  simpa [sub_eq_zero] using quadratic_roots hq hne

/-- **The rounds** from `claim`, after the challenges `pre`: a claim that is not the cube sum
leaves a final claim that is not `f` at the challenges, each challenge escaping at most `2/|E|`
of the time. -/
noncomputable def roundsSpec {n : ℕ} {f : List E → E} (hf : QuadraticIn n f) :
    (k : ℕ) → (claim : E) → (pre : List E) → pre.length + k = n →
    Spec (roundsProg claim k) (fun _ ↦ claim ≠ cubeSum n f pre)
      (fun r _ ↦ r.2 ≠ f (pre ++ r.1)) batchε 0 0
  | 0, claim, pre, hk => (Spec.ret (Post := fun r _ ↦ r.2 ≠ f (pre ++ r.1)) ([], claim)).mono
      (fun _ h ↦ by simpa [cubeSum_full (f := f) (by simpa using hk)] using h) (fun _ _ h ↦ h)
      le_rfl le_rfl le_rfl
  | k + 1, claim, pre, hk =>
    (Spec.readE (Pre := fun _ ↦ claim ≠ cubeSum n f pre)
        (Post := fun _ _ ↦ claim ≠ cubeSum n f pre) (T := 0) (fun _ _ h ↦ h)
        (zero_le)).bind' fun g1 ↦
      (Spec.readE (Pre := fun _ ↦ claim ≠ cubeSum n f pre)
          (Post := fun _ _ ↦ claim ≠ cubeSum n f pre) (T := batchε + 0) (fun _ _ h ↦ h)
          (add_zero _).le).bind' fun gInf ↦
        (Spec.sampleE (Pre := fun _ ↦ claim ≠ cubeSum n f pre)
            (Post := fun r _ ↦ roundPoly claim (g1, gInf) r ≠ cubeSum n f (pre ++ [r]))
            (T := 0) batchε fun _ h ↦ by
              refine (card_filter_le (round_bad hf (by omega) (g1, gInf) h)).trans ?_
              rw [batchε_eq]
              simp).bind' fun r ↦
          (roundsSpec hf k _ (pre ++ [r]) (by simp; omega)).bind' fun rest ↦
            (Spec.ret (r :: rest.1, rest.2)).mono (fun _ h ↦ by simpa using h)
              (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

/-! ## The claims -/

/-- Children of the bytecode's shapes have points of `log₂` of its length. -/
theorem bytecodePoints {bytecode : List K} {cs : List ChildClaims}
    (hs : ∀ c ∈ cs, ChildShaped bytecode c) : ∀ c ∈ cs,
      c.fresh.bytecodePoint.length = Nat.log2 bytecode.length ∧
        c.carried.bytecodePoint.length = Nat.log2 bytecode.length :=
  fun c hc ↦ ⟨(hs c hc).1, (hs c hc).2⟩

/-- Lambdas in doom leave a claim that is not the cube sum. -/
theorem claimB_ne {bytecode : List K} (hb : bytecode.length = 2 ^ Nat.log2 bytecode.length)
    {cs : List ChildClaims} (hs : ∀ c ∈ cs, ChildShaped bytecode c) {l : List (E × E)}
    (hl : l.length = cs.length) (hd : LDoom (gapsB bytecode cs) ([] ++ flat2 l)) :
    claimBOf cs l ≠ cubeSum (Nat.log2 bytecode.length) (bytecodePoly bytecode cs l) [] := by
  rw [bytecode_cubeSum hb (bytecodePoints hs) l]
  intro heq
  refine dot_ne_of_lDoom ?_ hd ((claimB_sub bytecode cs l hl).symm.trans (sub_eq_zero.2 heq))
  rw [List.nil_append, length_flatMap_const _ 2 (fun _ ↦ rfl),
    gapsB, length_flatMap_const _ 2 (fun _ ↦ rfl), hl]

/-- **The final value and the check**: a fixed doom, which contradicts the check. -/
noncomputable def endSpec (φ : Prop) (C : E → Prop) {_ : ∀ a, Decidable (C a)}
    (h : ∀ a, φ → C a → False) :
    Spec (do
        let a ← Prog.readE
        Prog.require (C a)
        return true) (fun _ ↦ φ) (fun b _ ↦ b = false) batchε 0 0 :=
  (constSpec _ φ zero_le).bind' fun a ↦
    (Spec.require (Post := fun _ _ ↦ False) fun _ hφ hc ↦ h a hφ hc).bind' fun _ ↦
      Spec.dead

/-- **The batching's doom specification** after children with a nonzero gap: the lambdas and
the rounds tracked, then a fixed fact. -/
noncomputable def restSpec {bytecode : List K}
    (hb : bytecode.length = 2 ^ Nat.log2 bytecode.length) {cs : List ChildClaims}
    (hs : ∀ c ∈ cs, ChildShaped bytecode c) (hg : SomeGap bytecode cs) :
    Spec (batchRest bytecode cs) (fun h ↦ h = []) (fun b _ ↦ b = false) batchε batchε 0 :=
  ((lamSpec (gapsB bytecode cs) cs.length 0 [] rfl).bind' fun l ↦
    ((roundsSpec (bytecode_quadraticIn hb (bytecodePoints hs) l) _ (claimBOf cs l) []
        (by simp)).mono (fun _ h ↦ claimB_ne hb hs h.1 h.2) (fun _ _ h ↦ h) le_rfl le_rfl
        le_rfl).bind' fun rb ↦
      endSpec _ _ fun bv hφ hc ↦ by
        obtain ⟨-, -, hv⟩ := hc.2
        apply hφ
        rw [hc.1, List.nil_append, bytecodePoly, hv]).mono
    (fun _ _ ↦ lDoom_nil hg) (fun _ _ h ↦ h) le_rfl (lamLead_le _ _) le_rfl

end
end LeanVM.Guest.Batch
