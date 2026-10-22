/-
  LeanerVM.Protocol.Whir.Lanes

  The vocabulary of lists for the soundness of WHIR's opening: lane words and messages, the
  agreement of a codeword with a word, mutual correlated agreement and the list bound as
  interfaces in counting form, and the lemma that folding preserves lists.
-/

module

public import LeanerVM.Protocol.Whir.Word
public import LeanerVM.Protocol.ToArkLib.Component
public import LeanerVM.Protocol.NovelBasis

/-!
# Lists of codewords near a word, and folding

Category B: Annex B, `sec:codes` and `sec:tools` (`def:interleaved`, `thm:mca-johnson`,
`lem:fold-list`), at leanVM pin `a386121f84292f6fa663aaa3e570c15bc0240ea2`.

An interleaved codeword of `2 ^ m` lanes is a family of `2 ^ m` messages (`Msgs m κ`), one table of
`κ` variables per lane; it agrees with a word on a position when every lane's encoding does. The
word is a *lane word* (`LW`): a function of the position and of a lane number in `ℕ`, so that the
folded words of the proof, whose lane counts differ from stage to stage, need no cast; lanes past
the word's own are junk that nothing reads. A threshold `a` replaces the radius `γ`: a codeword is
within `γ` of a word when it agrees with it on at least `a = (1 - γ) · 2 ^ (κ + R)` positions
(`Cl`). `ofLanes` decodes an interleaved codeword to the table of `ℓ + κ` variables whose
lane `i` is the message `i`.

Two interfaces, in counting form (a bound on the number of elements, never a probability), with
the constants as parameters; each is a theorem of coding theory that this repository consumes:

* `ListBound κ R a m L`: at most `L` interleaved codewords of `2 ^ m` lanes are within `a` of any
  word (the Johnson bound, `thm:johnson-interleaved`, with `L = 1 / (2 η √ρ)` at the radius
  `1 - √ρ - η`);
* `McaBound κ R a N`: for every two-lane word at most `N` of the folds `c ∈ E` are bad
  (`thm:mca-johnson`: on a set of at least `a` positions the fold agrees with the code while the two
  lanes do not agree with it); its error is `N / |E|`, so `N` is the Annex's `a` (here `a` is the
  agreement threshold). `McaBad` is the event.

Proved here from the encoder's distance (`LeanerVM.Protocol.NovelBasis.encode_eq_of_agree`):

* `lift_fold`: a fold that is bad for no lane pair lifts: messages within `a` of the folded word are
  the fold (`fold1M`) of messages within `a` of the word. For a lane pair the event not occurring
  gives two messages that equal the pair on the common set of agreement, those of all the pairs make
  the lifted codeword, and it folds to the given one because two codewords that agree on `a ≥ 2 ^ κ`
  positions are equal;
* `card_fold_bad_le` (`lem:fold-list`, one lane coordinate): at most `2 ^ m · N` folds are bad for
  some lane pair, so at most that many break the correspondence between the lists of a word and of
  its fold.
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters CompPoly CMlPolynomialEval

@[expose] public section

namespace Whir

/-! ## Lane words and messages -/

/-- The table whose lane `i` is the message `m i`: the decoded multilinear of an interleaved
codeword. -/
def ofLanes {L κ : ℕ} (m : Fin (2 ^ L) → CMlPolynomialEval E κ) : CMlPolynomialEval E (L + κ) :=
  Vector.ofFn fun i ↦ (m ((cubeSplit L κ).symm i).1)[((cubeSplit L κ).symm i).2]

/-- The entries of the decoded table. -/
theorem ofLanes_getElem {L κ : ℕ} (m : Fin (2 ^ L) → CMlPolynomialEval E κ) (u : Fin (2 ^ L))
    (x : Fin (2 ^ κ)) : (ofLanes m)[cubeIndex u x] = (m u)[x] := by
  have hs : (cubeSplit L κ).symm (cubeIndex u x) = (u, x) :=
    (Equiv.symm_apply_eq _).mpr (cubeSplit_apply u x).symm
  simp only [Fin.getElem_fin, ofLanes, Vector.getElem_ofFn, Fin.eta, hs]

/-- A word as a function of position and lane; lanes past the word's own are junk. -/
abbrev LW (b : ℕ) : Type := Fin (2 ^ b) → ℕ → E

/-- The messages of an interleaved codeword of `2 ^ m` lanes, one table per lane. -/
abbrev Msgs (m κ : ℕ) : Type := Fin (2 ^ m) → CMlPolynomialEval E κ

/-- The lanes of a word. -/
def Word.lanes {ℓ b t : ℕ} (w : Word ℓ b t) : LW b := fun y u ↦ (w.row y).getD u 0

/-- The codeword of the messages `V` agrees with the lane word `F` on at least `a` positions. -/
def Cl (κ R a m : ℕ) (F : LW (κ + R)) (V : Msgs m κ) : Prop :=
  a ≤ (Finset.univ.filter fun y : Fin (2 ^ (κ + R)) ↦
    ∀ u : Fin (2 ^ m), encode (algebraMap K E) κ R (V u) y = F y u).card

instance (κ R a m : ℕ) (F : LW (κ + R)) (V : Msgs m κ) : Decidable (Cl κ R a m F V) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-- Halving a lane index of `2 ^ (m + 1)` lanes gives a lane index of `2 ^ m`. -/
private theorem half_lt {m : ℕ} (l : Fin (2 ^ (m + 1))) : l.val / 2 < 2 ^ m := by
  have h := l.2
  have h2 : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
  omega

/-- Twice a lane index of `2 ^ m` lanes, and one more, are lane indices of `2 ^ (m + 1)`. -/
theorem two_mul_lt {m : ℕ} (u : Fin (2 ^ m)) {b : ℕ} (hb : b < 2) :
    2 * u.val + b < 2 ^ (m + 1) := by
  have h := u.2
  have h2 : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
  omega

/-- The combination `a m₁ + b m₂` of two tables, entry by entry. -/
def comb {κ : ℕ} (a b : E) (m₁ m₂ : CMlPolynomialEval E κ) : CMlPolynomialEval E κ :=
  Vector.ofFn fun x ↦ a * m₁[x] + b * m₂[x]

/-- The encoder respects combinations. -/
theorem encode_comb (κ R : ℕ) (a b : E) (m₁ m₂ : CMlPolynomialEval E κ) (y : Fin (2 ^ (κ + R))) :
    encode (algebraMap K E) κ R (comb a b m₁ m₂) y =
      a * encode (algebraMap K E) κ R m₁ y + b * encode (algebraMap K E) κ R m₂ y := by
  simp only [encode_eq_sum, comb, Fin.getElem_fin, Vector.getElem_ofFn, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  ring

/-- A lane word folded at `c` along its lowest lane coordinate. -/
def fold1W {b : ℕ} (c : E) (F : LW b) : LW b := fun y u ↦
  (1 - c) * F y (2 * u) + c * F y (2 * u + 1)

/-- Messages folded at `c` along their lowest lane coordinate. -/
def fold1M {m κ : ℕ} (c : E) (V : Msgs (m + 1) κ) : Msgs m κ := fun u ↦
  comb (1 - c) c (V ⟨2 * u.val, two_mul_lt (b := 0) u (by norm_num)⟩)
    (V ⟨2 * u.val + 1, two_mul_lt (b := 1) u (by norm_num)⟩)

/-- The two-lane word of the lane pair `2u, 2u + 1`. -/
def pairF {b : ℕ} (F : LW b) (u : ℕ) : LW b := fun y i ↦ F y (2 * u + i)

/-- The event of mutual correlated agreement for a two-lane word and a fold `c`: on some set of
at least `a` positions the fold agrees with the code while the two lanes do not agree with the
code (as two messages). -/
def McaBad (κ R a : ℕ) (F : LW (κ + R)) (c : E) : Prop :=
  ∃ A : Finset (Fin (2 ^ (κ + R))), a ≤ A.card ∧
    (∃ m : CMlPolynomialEval E κ, ∀ y ∈ A,
      encode (algebraMap K E) κ R m y = (1 - c) * F y 0 + c * F y 1) ∧
    ¬ ∃ m₀ m₁ : CMlPolynomialEval E κ, ∀ y ∈ A,
      encode (algebraMap K E) κ R m₀ y = F y 0 ∧ encode (algebraMap K E) κ R m₁ y = F y 1

/-- Mutual correlated agreement up to the Johnson bound, in counting form (`thm:mca-johnson`):
for every two-lane word at most `N` folds are bad; the error is `N / |E|`. -/
def McaBound (κ R a N : ℕ) : Prop :=
  ∀ F : LW (κ + R), Nat.card {c : E // McaBad κ R a F c} ≤ N

/-- The list-size bound (the Johnson bound): at most `L` interleaved codewords of `2 ^ m` lanes
are within the threshold `a` of any lane word. -/
def ListBound (κ R a m L : ℕ) : Prop :=
  ∀ F : LW (κ + R), Nat.card {V : Msgs m κ // Cl κ R a m F V} ≤ L

/-! ## Folding preserves lists -/

/-- Folds that are not bad for any lane pair lift: messages within `a` of the fold are the fold of
messages within `a` of the word. -/
theorem lift_fold {κ R a m : ℕ} (hdist : 2 ^ κ ≤ a) (hb : κ + R ≤ 64) (c : E)
    (F : LW (κ + R)) (hc : ∀ u : Fin (2 ^ m), ¬ McaBad κ R a (pairF F u) c)
    (V : Msgs m κ) (hV : Cl κ R a m (fold1W c F) V) :
    ∃ V₀ : Msgs (m + 1) κ, Cl κ R a (m + 1) F V₀ ∧ fold1M c V₀ = V := by
  classical
  set A := Finset.univ.filter fun y : Fin (2 ^ (κ + R)) ↦
    ∀ u : Fin (2 ^ m), encode (algebraMap K E) κ R (V u) y = fold1W c F y u with hA
  have hAcard : a ≤ A.card := hV
  have hu : ∀ u : Fin (2 ^ m), ∃ m₀ m₁ : CMlPolynomialEval E κ, ∀ y ∈ A,
      encode (algebraMap K E) κ R m₀ y = F y (2 * u.val) ∧
        encode (algebraMap K E) κ R m₁ y = F y (2 * u.val + 1) := by
    intro u
    have h := hc u
    unfold McaBad at h
    push Not at h
    obtain ⟨m₀, m₁, h'⟩ := h A hAcard ⟨V u, fun y hy ↦ by
      have := (Finset.mem_filter.mp hy).2 u
      simpa [fold1W, pairF] using this⟩
    exact ⟨m₀, m₁, fun y hy ↦ by simpa [pairF] using h' y hy⟩
  choose m₀ m₁ hm using hu
  let V₀ : Msgs (m + 1) κ := fun l ↦
    if l.val % 2 = 0 then m₀ ⟨l.val / 2, half_lt l⟩ else m₁ ⟨l.val / 2, half_lt l⟩
  have hV0 : ∀ u : Fin (2 ^ m), V₀ ⟨2 * u.val, two_mul_lt (b := 0) u (by norm_num)⟩ = m₀ u ∧
      V₀ ⟨2 * u.val + 1, two_mul_lt (b := 1) u (by norm_num)⟩ = m₁ u := by
    intro u
    simp only [V₀]
    constructor
    · rw [ite_eq_left (by omega)]
      congr 1
      exact Fin.ext (by simp)
    · rw [ite_eq_right (by omega)]
      congr 1
      exact Fin.ext (by simp; omega)
  refine ⟨V₀, ?_, ?_⟩
  · refine le_trans hAcard (Finset.card_le_card fun y hy ↦ ?_)
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun l ↦ ?_⟩
    obtain ⟨h0, h1⟩ := hm ⟨l.val / 2, half_lt l⟩ y hy
    simp only at h0 h1
    by_cases hpar : l.val % 2 = 0
    · simp only [V₀, ite_eq_left hpar]
      rw [h0]
      congr 1
      omega
    · simp only [V₀, ite_eq_right hpar]
      rw [h1]
      congr 1
      omega
  · funext u
    have hy : ∀ y ∈ A, encode (algebraMap K E) κ R (V u) y =
        encode (algebraMap K E) κ R (fold1M c V₀ u) y := by
      intro y hy
      obtain ⟨h0, h1⟩ := hm u y hy
      obtain ⟨e0, e1⟩ := hV0 u
      have hVu := (Finset.mem_filter.mp hy).2 u
      simp only [fold1M, encode_comb, e0, e1, h0, h1]
      rw [hVu]
      simp [fold1W]
    have hT : 2 ^ κ ≤ A.card := hdist.trans hAcard
    exact (encode_eq_of_agree (algebraMap K E) hb (algebraMap K E).injective
      (m := V u) (m' := fold1M c V₀ u) A hT hy).symm

/-- At most `2 ^ m N` folds break the correspondence between the lists of a lane word and of its
fold (`lem:fold-list`, one lane coordinate): the union of the `2 ^ m` events of the lane pairs. -/
theorem card_fold_bad_le {κ R a N m : ℕ} (hmca : McaBound κ R a N) (hdist : 2 ^ κ ≤ a)
    (hb : κ + R ≤ 64) (F : LW (κ + R)) :
    Nat.card {c : E // ¬ ∀ V : Msgs m κ, Cl κ R a m (fold1W c F) V →
        ∃ V₀ : Msgs (m + 1) κ, Cl κ R a (m + 1) F V₀ ∧ fold1M c V₀ = V} ≤ 2 ^ m * N := by
  classical
  have := Fintype.ofFinite E
  rw [natCard_subtype_eq_card_filter]
  calc _ ≤ (Finset.univ.biUnion fun u : Fin (2 ^ m) ↦
          Finset.univ.filter fun c : E ↦ McaBad κ R a (pairF F u) c).card := by
        refine Finset.card_le_card fun c hc ↦ ?_
        have hc' := (Finset.mem_filter.mp hc).2
        by_contra hnot
        apply hc'
        refine fun V hV ↦ lift_fold hdist hb c F (fun u hu ↦ hnot ?_) V hV
        exact Finset.mem_biUnion.mpr ⟨u, Finset.mem_univ _, Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, hu⟩⟩
    _ ≤ ∑ u : Fin (2 ^ m), (Finset.univ.filter fun c : E ↦ McaBad κ R a (pairF F u) c).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _u : Fin (2 ^ m), N := Finset.sum_le_sum fun u _ ↦ by
        rw [← natCard_subtype_eq_card_filter]
        exact hmca (pairF F u)
    _ = 2 ^ m * N := by simp

end Whir

end

end LeanerVM.Protocol
