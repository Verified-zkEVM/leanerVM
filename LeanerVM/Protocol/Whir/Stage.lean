/-
  LeanerVM.Protocol.Whir.Stage

  The folds of a lane word and of messages at several challenges, one coordinate at a time, and the
  correspondence of the folded lists.
-/

module

public import LeanerVM.Protocol.Whir.Lanes

/-!
# Folding at several challenges

Category B: After `j` fold challenges `cs` (the first binds the lowest lane coordinate) the lane
`u` of the folded word is `Σ_ι eq(cs, ι) · F[ι + 2 ^ j u]` (`foldW`), and the same combination of
messages is the fold of an interleaved codeword (`foldM`). One more challenge folds the next lane
coordinate (`foldW_push`, `foldM_push`).

`FoldOK κ R a ℓ cs F` is the invariant the proof of `thm:rbr` keeps across the fold challenges of a
level of `ℓ` lanes: every interleaved codeword within `a` of the folded word, at each lane count the
folds leave, is the fold of an interleaved codeword within `a` of the word. It holds before the
first challenge (`foldOK_nil`) and survives a challenge at which the stepwise correspondence holds
(`foldOK_push`), the event whose complement `card_fold_bad_le` bounds.
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters CompPoly CMlPolynomialEval

@[expose] public section

namespace Whir

/-- The low coordinate of a point with one more challenge pushed is the earlier point. -/
private theorem lowVec_push {j : ℕ} (cs : Vector E j) (c : E) :
    lowVec (m := 1) (cs.push c) = cs := by
  apply Vector.ext
  intro i hi
  simp [lowVec]

/-- The high coordinate of a point with one more challenge pushed is that challenge. -/
private theorem highVec_push {j : ℕ} (cs : Vector E j) (c : E) :
    highVec (k := j) (m := 1) (cs.push c) = #v[c] := by
  apply Vector.ext
  intro i hi
  have : i = 0 := by omega
  subst this
  simp [highVec]

/-- A sum over `Fin (2 ^ 1)` is the sum of its two terms. -/
private theorem sum_fin_two_pow_one {M : Type*} [AddCommMonoid M] (f : Fin (2 ^ 1) → M) :
    ∑ b, f b = f ⟨0, by norm_num⟩ + f ⟨1, by norm_num⟩ := by
  show ∑ b : Fin 2, f b = _
  rw [Fin.sum_univ_two]
  rfl

/-- The Lagrange weights of one more challenge split a sum over the lanes of `j + 1` folds into the
two sums over the lanes of `j` folds, at the lanes `2u` and `2u + 1` of the next. -/
private theorem sum_lagrange_push {j : ℕ} (cs : Vector E j) (c : E) (G : ℕ → E) (u : ℕ) :
    ∑ x : Fin (2 ^ (j + 1)), (lagrangeBasis (cs.push c))[x] * G (x.val + 2 ^ (j + 1) * u) =
      (1 - c) * ∑ ι : Fin (2 ^ j), (lagrangeBasis cs)[ι] * G (ι.val + 2 ^ j * (2 * u)) +
        c * ∑ ι : Fin (2 ^ j), (lagrangeBasis cs)[ι] * G (ι.val + 2 ^ j * (2 * u + 1)) := by
  rw [sum_cube_split (k := j) (m := 1), sum_fin_two_pow_one]
  have hb0 : (lagrangeBasis #v[c])[(⟨0, by norm_num⟩ : Fin (2 ^ 1))] = 1 - c := by
    rw [Fin.getElem_fin, lagrangeBasis_getElem_nat _ (by norm_num)]
    simp
  have hb1 : (lagrangeBasis #v[c])[(⟨1, by norm_num⟩ : Fin (2 ^ 1))] = c := by
    rw [Fin.getElem_fin, lagrangeBasis_getElem_nat _ (by norm_num)]
    simp
  have e0 : ∀ ι : Fin (2 ^ j),
      (lagrangeBasis (cs.push c))[cubeIndex ι (⟨0, by norm_num⟩ : Fin (2 ^ 1))] *
        G ((cubeIndex ι (⟨0, by norm_num⟩ : Fin (2 ^ 1))).val + 2 ^ (j + 1) * u) =
      (1 - c) * ((lagrangeBasis cs)[ι] * G (ι.val + 2 ^ j * (2 * u))) := by
    intro ι
    rw [lagrangeBasis_cubeIndex, lowVec_push, highVec_push, hb0, cubeIndex_val]
    rw [show ι.val + 2 ^ j * (⟨0, by norm_num⟩ : Fin (2 ^ 1)).val + 2 ^ (j + 1) * u =
      ι.val + 2 ^ j * (2 * u) by simp; ring]
    ring
  have e1 : ∀ ι : Fin (2 ^ j),
      (lagrangeBasis (cs.push c))[cubeIndex ι (⟨1, by norm_num⟩ : Fin (2 ^ 1))] *
        G ((cubeIndex ι (⟨1, by norm_num⟩ : Fin (2 ^ 1))).val + 2 ^ (j + 1) * u) =
      c * ((lagrangeBasis cs)[ι] * G (ι.val + 2 ^ j * (2 * u + 1))) := by
    intro ι
    rw [lagrangeBasis_cubeIndex, lowVec_push, highVec_push, hb1, cubeIndex_val]
    rw [show ι.val + 2 ^ j * (⟨1, by norm_num⟩ : Fin (2 ^ 1)).val + 2 ^ (j + 1) * u =
      ι.val + 2 ^ j * (2 * u + 1) by simp; ring]
    ring
  rw [Finset.sum_congr rfl fun ι _ ↦ e0 ι, Finset.sum_congr rfl fun ι _ ↦ e1 ι,
    ← Finset.mul_sum, ← Finset.mul_sum]

/-- The lane word folded at the challenges `cs`: lane `u` is `Σ_ι eq(cs, ι) F[ι + 2^j u]`. -/
def foldW {b j : ℕ} (cs : Vector E j) (F : LW b) : LW b := fun y u ↦
  ∑ ι : Fin (2 ^ j), (lagrangeBasis cs)[ι] * F y (ι.val + 2 ^ j * u)

/-- With nothing folded the lane word is unchanged. -/
private theorem foldW_nil {b : ℕ} (F : LW b) : foldW (#v[] : Vector E 0) F = F := by
  funext y u
  simp [foldW, lagrangeBasis]

/-- One more challenge folds the next lane coordinate. -/
theorem foldW_push {b j : ℕ} (cs : Vector E j) (c : E) (F : LW b) :
    foldW (cs.push c) F = fold1W c (foldW cs F) := by
  funext y u
  simp only [foldW, fold1W]
  rw [sum_lagrange_push cs c (F y) u]

/-- The lane `n` of the entry `x` of the messages `g`, zero past the last lane. -/
def Msgs.get {ℓ κ : ℕ} (g : Msgs ℓ κ) (n : ℕ) (x : Fin (2 ^ κ)) : E :=
  if h : n < 2 ^ ℓ then (g ⟨n, h⟩)[x] else 0

/-- The messages folded at the challenges `cs`: lane `u` is `Σ_ι eq(cs, ι) g[ι + 2^j u]`. -/
def foldM {j κ ℓ : ℕ} (m : ℕ) (cs : Vector E j) (g : Msgs ℓ κ) : Msgs m κ := fun u ↦
  Vector.ofFn fun x ↦ ∑ ι : Fin (2 ^ j), (lagrangeBasis cs)[ι] * g.get (ι.val + 2 ^ j * u.val) x

/-- The entries of the messages folded at `cs`, as a sum over the lanes the fold combines. -/
private theorem foldM_getElem {j κ ℓ : ℕ} (m : ℕ) (cs : Vector E j) (g : Msgs ℓ κ) (u : Fin (2 ^ m))
    (x : Fin (2 ^ κ)) :
    (foldM m cs g u)[x] =
      ∑ ι : Fin (2 ^ j), (lagrangeBasis cs)[ι] * g.get (ι.val + 2 ^ j * u.val) x := by
  simp [foldM]

/-- One more fold challenge folds the next lane coordinate: the entries of the fold at `cs.push c`
are the combination of the entries of the fold at `cs` on the lane pair. -/
private theorem foldM_getElem_push {j κ ℓ : ℕ} (m : ℕ) (cs : Vector E j) (c : E) (g : Msgs ℓ κ)
    (u : Fin (2 ^ m)) (x : Fin (2 ^ κ)) :
    (foldM m (cs.push c) g u)[x] =
      (1 - c) * (foldM (m + 1) cs g ⟨2 * u.val, two_mul_lt (b := 0) u (by norm_num)⟩)[x] +
        c * (foldM (m + 1) cs g ⟨2 * u.val + 1, two_mul_lt (b := 1) u (by norm_num)⟩)[x] := by
  rw [foldM_getElem, foldM_getElem, foldM_getElem]
  exact sum_lagrange_push cs c (fun n ↦ g.get n x) u.val

/-- One more challenge folds the next lane coordinate of the messages. -/
theorem foldM_push {j κ ℓ : ℕ} (m : ℕ) (cs : Vector E j) (c : E) (g : Msgs ℓ κ)
    (u : Fin (2 ^ m)) :
    foldM m (cs.push c) g u = comb (1 - c) c
      (foldM (m + 1) cs g ⟨2 * u.val, two_mul_lt (b := 0) u (by norm_num)⟩)
      (foldM (m + 1) cs g ⟨2 * u.val + 1, two_mul_lt (b := 1) u (by norm_num)⟩) := by
  apply Vector.ext
  intro i hi
  rw [comb, Vector.getElem_ofFn]
  exact foldM_getElem_push m cs c g u ⟨i, hi⟩

/-- The correspondence of the folded lists, at each lane count `m` the folds leave: every messages
within `a` of the lane word folded at `cs` are the fold of messages within `a` of the word. -/
def FoldOK (κ R a ℓ : ℕ) {j : ℕ} (cs : Vector E j) (F : LW (κ + R)) : Prop :=
  ∀ m, m + j = ℓ → ∀ V : Msgs m κ, Cl κ R a m (foldW cs F) V →
    ∃ g : Msgs ℓ κ, Cl κ R a ℓ F g ∧ ∀ u : Fin (2 ^ m), V u = foldM m cs g u

/-- With nothing folded the correspondence is trivial. -/
theorem foldOK_nil (κ R a ℓ : ℕ) (F : LW (κ + R)) : FoldOK κ R a ℓ (#v[] : Vector E 0) F := by
  intro m hm V hV
  have hmℓ : m = ℓ := by omega
  subst hmℓ
  refine ⟨V, ?_, fun u ↦ ?_⟩
  · rwa [foldW_nil] at hV
  · apply Vector.ext
    intro i hi
    simp [foldM, Msgs.get, lagrangeBasis]

/-- The correspondence survives a challenge at which the fold of the folded lists is the folded
list of the fold (the step of `lem:fold-list`). -/
theorem foldOK_push (κ R a ℓ : ℕ) {j : ℕ} (cs : Vector E j) (c : E) (F : LW (κ + R))
    (hok : FoldOK κ R a ℓ cs F)
    (hstep : ∀ m, m + (j + 1) = ℓ → ∀ V : Msgs m κ, Cl κ R a m (fold1W c (foldW cs F)) V →
      ∃ V₀ : Msgs (m + 1) κ, Cl κ R a (m + 1) (foldW cs F) V₀ ∧ fold1M c V₀ = V) :
    FoldOK κ R a ℓ (cs.push c) F := by
  intro m hm V hV
  rw [foldW_push] at hV
  obtain ⟨V₀, hV₀, hf⟩ := hstep m hm V hV
  obtain ⟨g, hg, hgf⟩ := hok (m + 1) (by omega) V₀ hV₀
  refine ⟨g, hg, fun u ↦ ?_⟩
  rw [← hf, foldM_push]
  simp only [fold1M, hgf]

/-- The lane `0` of a word folded at all its lanes is the folded row. -/
theorem foldW_lane0 {ℓ b t : ℕ} (r : Vector E ℓ) (w : Word ℓ b t) (y : Fin (2 ^ b)) :
    foldW r w.lanes y 0 = foldRow r (w.row y) := by
  simp only [foldW, foldRow, Word.lanes, mul_zero, add_zero]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  congr 1
  simp [Vector.getD, u.2]

/-- The message of a single lane folded at all the lanes is the folded table. -/
theorem foldM_zero {ℓ κ : ℕ} (r : Vector E ℓ) (g : Msgs ℓ κ) :
    foldM 0 r g ⟨0, by norm_num⟩ = foldTable (ofLanes g) r := by
  apply Vector.ext
  intro i hi
  have h := foldM_getElem 0 r g ⟨0, by norm_num⟩ ⟨i, hi⟩
  have h2 := foldTable_getElem (ofLanes g) r ⟨i, hi⟩
  refine h.trans (Eq.trans ?_ h2.symm)
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [ofLanes_getElem, mul_comm]
  simp [Msgs.get, u.2]

end Whir

end

end LeanerVM.Protocol
