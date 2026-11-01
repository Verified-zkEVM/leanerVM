module

public import LeanVM.Cost.Bounds.Basic
public import LeanVM.Cost.Samples.AddRaw
import all CompPoly.Data.Array.Lemmas

/-!
# Bound: `addRaw` over `K`

The price of the compiled `addRaw` (`Cost/Samples/AddRaw.lean`) is linear in the operands' sizes:
`addRawK_cost_le`, at most `44 + 28·max(|p|, |q|)` for sizes below `2^64` (the padding writes
`|p − q| + 2·max` entries, the zip `18` per entry, the conversions to and from lists `7` per
entry). From the recurrences: padding (`Array.rightpad`, exact), the
zip of the padded arrays (`listZipWith_le` with the closure's price `3`), the array conversions.
-/

namespace LeanVM.Cost.Bounds.Samples

open LeanVM.Cost LeanVM.Cost.Samples LeanVM.Cost.Library LeanVM.Cost.Bounds LeanVM.Parameters

public section

/-- `Array.rightpad n a xs`: its price, exactly, for word-sized lengths. -/
theorem rightpadK_cost (P : Program) (hP : Includes P Auto.Array.rightpad.c4.costDeps) (n : ℕ)
    (a : K) (xs : Array K) (hn : n < 2 ^ 64) (hs : xs.size < 2 ^ 64) :
    machineCost P Auto.Array.rightpad.c4.costIdx [enc n, enc a, enc xs] =
      9 + (n - xs.size) + max n xs.size := by
  rw [Auto.Array.rightpad.c4.costEq P hP]
  simp only [limbs_of_lt hn, limbs_of_lt hs, Array.size_replicate]
  omega

/-- **`addRaw` over `K`**: at most `44 + 28·max(|p|, |q|)`. -/
theorem addRawK_cost_le (P : Program) (hP : Includes P addRawK.costDeps)
    (p q : CompPoly.CPolynomial.Raw K) (hp : p.size < 2 ^ 64) (hq : q.size < 2 ^ 64) :
    machineCost P addRawK.costIdx [enc p, enc q] ≤ 44 + 28 * max p.size q.size := by
  rw [addRawK.costEq P hP]
  have hz := listZipWith_le P (by includes) (fun x y : K ↦ x + y) (.fn addRawK.lam0.costIdx [])
    (fun a b ↦ RunsApp.of_spec (addRawK.lam0.costSpec P (by includes) a b)) 3
    (p.rightpad q.size 0).toList (q.rightpad p.size 0).toList
    (fun a _ b _ ↦ by rw [appCost_fn, List.nil_append, addRawK.lam0.costEq P (by includes)])
  simp only [Array.length_toList, Array.size_rightpad, List.length_zipWith] at hz ⊢
  cost_facts [rightpadK_cost P]
  omega

end

end LeanVM.Cost.Bounds.Samples
