/-
  LeanerVM.Protocol.ToCompPoly.BindStep

  Binding a hypercube table's coordinates one value at a time: a table bound on its top
  coordinates to some values, bound on one more, is the table bound to the values with the new
  one appended; the table bound on every coordinate holds the extension at the point. Candidate
  for CompPoly.
-/

module

public import LeanerVM.Protocol.ToCompPoly.TableFold

/-!
# Binding one coordinate more

`bindHighs t s` binds the top coordinates of `t` to `s` (`LeanerVM.Protocol.ToCompPoly.TableFold`).
A sumcheck that binds the highest coordinate first holds, after the challenges `c_0, …, c_{j-1}`,
the table `bindHighs t c.reverse`, and the next challenge `a` is bound below them:
`bindHigh (bindHighs t c.reverse) a = bindHighs t (c.push a).reverse`
(`bindHigh_bindHighs_reverse`), so the bound table is updated by one halving per challenge
instead of being bound afresh. With every coordinate bound, the table's one entry is the
extension at the point (`bindHighs_getElem_zero`). `bindHighs_cast` renames the number of free
coordinates. The low mirror, for a sumcheck that binds the lowest coordinate first, holds
`bindLows t c` and binds the next challenge with one `bindLow` (`bindLow_bindLows`), and its
table bound on every coordinate holds the extension at `c` (`bindLows_getElem_zero`). Over an
arbitrary commutative ring; nothing here transcribes a source.
-/

namespace LeanerVM.Protocol

open CompPoly CMlPolynomialEval

@[expose] public section

variable {R : Type*} [CommRing R]

/-- Binding the top coordinates commutes with renaming the number of free ones. -/
theorem bindHighs_cast {k k' j : ℕ} (h : k = k') (t : CMlPolynomialEval R (k + j))
    (s : Vector R j) :
    Vector.cast (congrArg (2 ^ ·) h) (bindHighs t s) =
      bindHighs (k := k') (Vector.cast (congrArg (2 ^ ·) (by rw [h])) t) s := by
  subst h
  rfl

omit [CommRing R] in
/-- The point `z`, then `a`, then `c` reversed, is `z` followed by `c` with `a` pushed, reversed. -/
private theorem push_append_reverse {k j : ℕ} (z : Vector R k) (c : Vector R j) (a : R) :
    Vector.cast (by omega) (z.push a ++ c.reverse) = z ++ (c.push a).reverse := by
  refine Vector.ext fun i hi ↦ ?_
  simp only [Vector.getElem_cast, Vector.getElem_append, Vector.getElem_push,
    Vector.getElem_reverse]
  by_cases h1 : i < k
  · simp [h1, show i < k + 1 by omega]
  · by_cases h2 : i = k
    · subst h2
      simp
    · simp only [h1, show ¬ i < k + 1 by omega, dite_false]
      rw [dite_eq_left (by omega)]
      congr 1
      omega

/-- Binding one more top coordinate: a table bound to the challenges `c`, the first the
highest, bound at its new top coordinate to `a`, is the table bound to `c` with `a` pushed. -/
theorem bindHigh_bindHighs_reverse {k j : ℕ} (t : CMlPolynomialEval R (k + 1 + j))
    (c : Vector R j) (a : R) :
    bindHigh (bindHighs t c.reverse) a =
      bindHighs (k := k) (Vector.cast (congrArg (2 ^ ·) (by omega)) t) (c.push a).reverse := by
  have key : ∀ z : Vector R k, evalMle (bindHigh (bindHighs t c.reverse) a) z =
      evalMle (bindHighs (k := k) (Vector.cast (congrArg (2 ^ ·) (by omega)) t)
        (c.push a).reverse) z := fun z ↦ by
    rw [← evalMle_push, ← evalMle_append_eq_bindHighs, ← evalMle_append_eq_bindHighs,
      ← push_append_reverse, evalMle_cast]
  refine Vector.ext fun x hx ↦ ?_
  have h := key (boolVec ⟨x, hx⟩)
  rwa [evalMle_boolVec, evalMle_boolVec, Fin.getElem_fin, Fin.getElem_fin] at h

/-- With every coordinate bound, the table's one entry is the extension at the point. -/
theorem bindHighs_getElem_zero {k j : ℕ} (hk : k = 0) (t : CMlPolynomialEval R (k + j))
    (s : Vector R j) :
    (bindHighs t s)[0]'(by rw [hk]; exact Nat.two_pow_pos 0) =
      evalMle t (Vector.cast (by omega) s) := by
  subst hk
  have hs : (#v[] : Vector R 0) ++ s = Vector.cast (by omega) s :=
    Vector.ext fun i hi ↦ by simp
  rw [← hs, evalMle_append_eq_bindHighs, evalMle_zero]
  rfl

/-! ## From the bottom -/

/-- Binding the low coordinates commutes with renaming the number of free ones. -/
theorem bindLows_cast {k k' j : ℕ} (h : k = k') (t : CMlPolynomialEval R (j + k))
    (s : Vector R j) :
    Vector.cast (congrArg (2 ^ ·) h) (bindLows t s) =
      bindLows (k := k') (Vector.cast (congrArg (2 ^ ·) (by rw [h])) t) s := by
  subst h
  rfl

/-- An entry of a table bound on its low coordinates, whatever the number of free ones is
called. -/
theorem getElem_bindLows_cast {a k k' j : ℕ} (h : k = k') (ha : a = j + k) (ha' : a = j + k')
    (t : CMlPolynomialEval R a) (s : Vector R j) (i : ℕ) (hi : i < 2 ^ k) :
    (bindLows (k := k) (Vector.cast (congrArg (2 ^ ·) ha) t) s)[i] =
      (bindLows (k := k') (Vector.cast (congrArg (2 ^ ·) ha') t) s)[i]'(h ▸ hi) := by
  subst h
  rfl

/-- Binding one more low coordinate: a table bound to `c`, lowest first, bound at its new lowest
coordinate to `a`, is the table bound to `c` with `a` pushed. -/
theorem bindLow_bindLows {k j : ℕ} (t : CMlPolynomialEval R (j + (k + 1))) (c : Vector R j)
    (a : R) :
    bindLow (bindLows t c) a =
      bindLows (k := k) (Vector.cast (congrArg (2 ^ ·) (by omega)) t) (c.push a) := by
  rw [bindLows, Vector.pop_push, Vector.getElem_push_eq, Vector.cast_cast]
  rfl

/-- With every coordinate bound from the bottom, the table's one entry is the extension at the
point. -/
theorem bindLows_getElem_zero {k j : ℕ} (hk : k = 0) (t : CMlPolynomialEval R (j + k))
    (s : Vector R j) :
    (bindLows t s)[0]'(by rw [hk]; exact Nat.two_pow_pos 0) =
      evalMle t (Vector.cast (by omega) s) := by
  subst hk
  have hs : s ++ (#v[] : Vector R 0) = Vector.cast (by omega) s :=
    Vector.ext fun i hi ↦ by simp
  rw [← hs, evalMle_append_eq_bindLows, evalMle_zero]
  rfl

end
end LeanerVM.Protocol
