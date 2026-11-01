module

public import LeanVM.Guest.Fast.Numbers
public import LeanVM.Guest.Core

/-!
# The readers' common pieces

`sibN`, a Merkle path level's sibling (`mSib`, `B1/Sig/Merkle.lean`), and the lemmas reading a
table built by `List.range`.
-/

namespace LeanVM.Guest.Fast

open LeanVM.Parameters LeanVM.Guest.Core

@[expose] public section

/-- A path level's sibling: the hinted child at `b`, `b + 1` the node is not (`mSib`). -/
def sibN (σ : Val) (bit b : ℕ) : E := if σ (.n bit) = 1 then σ (.n b) else σ (.n (b + 1))

theorem getD_map_range {f : ℕ → ℕ} {n l : ℕ} (hl : l < n) :
    ((List.range n).map f).getD l 0 = f l := by
  simp [List.getD_eq_getElem?_getD, hl]

theorem getD_map_range' {α : Type} {f : ℕ → α} {n l : ℕ} (d : α) (hl : l < n) :
    ((List.range n).map f).getD l d = f l := by
  simp [List.getD_eq_getElem?_getD, hl]

theorem offAt_map {f : ℕ → ℕ → ℕ} {n m r k : ℕ} (hr : r < n) (hk : k < m) :
    offAt ((List.range n).map fun r ↦ (List.range m).map (f r)) r k = f r k := by
  simp [offAt, List.getD_eq_getElem?_getD, hr, hk]

theorem ite_sigma {σ : Val} (p : Prop) [Decidable p] (x y : ℕ) :
    σ (if p then V.n x else V.n y) = σ (.n (if p then x else y)) := by
  split <;> rfl

end
end LeanVM.Guest.Fast
