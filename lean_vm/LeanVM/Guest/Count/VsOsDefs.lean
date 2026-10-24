/-
  LeanVM.Guest.Count.VsOsDefs

  `open_stacked`'s words at a candidate by the search tree's lookups (`osCF`), and its parts the
  kernel evaluates one module each (`Count/VsOs*`): the frame and buffers, and ranges of its calls'
  bounds (`osCF_split`). Few imports, so that each part's module stays small.
-/

module

public import LeanVM.Guest.Count.Fast
public import LeanVM.Guest.B1.Place.OsFinalB
public import LeanVM.Guest.B1.Place.OsBos

namespace LeanVM.Guest.Count

open LeanVM.Guest.Core LeanVM.Guest.B1.Whir

@[expose] public section

/-- The core indices of `osKindTable`'s names. -/
def osKindIdx : List ℕ :=
  [7, 1, 409, 416, 411, 456, 475, 419, 437, 453, 472, 414, 434, 450, 469, 408, 431, 447, 466, 485,
    499, 513, 458, 477, 423, 440, 523, 421, 417, 532, 412, 460, 479, 426, 442]

/-- `open_stacked`'s named callees' words (`osBnd`) by the tree: `wSB` at the indices of
`osKindTable`'s names, `0` elsewhere. -/
noncomputable def osBndFast (f : String) : ℕ :=
  match wNameIdx f with
  | some j => if j ∈ osKindIdx then wSBJ j else 0
  | none => 0

/-- `open_stacked`'s words at candidate `c` (`osC`), by the search tree's lookups. -/
noncomputable def osCF (c : ℕ) : ℕ :=
  B1.osBos fsFast (B1.osBk fsFast osBndFast wSKFast (osCfg c)) ("open_stacked__L" ++ natStr c)
    (osCfg c)

/-- Its calls' bounds, in order. -/
noncomputable def osCallsF (c : ℕ) : List ℕ :=
  ((osBodyA (osCfg c)).filterMap B1.Main.Stmt.callS).map fun x =>
    B1.osCallB fsFast (B1.osBk fsFast osBndFast wSKFast (osCfg c)) x.2.1

/-- Its frame and buffers. -/
noncomputable def osHeadF (c : ℕ) : ℕ :=
  fsFast ("open_stacked__L" ++ natStr c) + (B1.osSizesL (osCfg c)).sum

/-- Its calls `a` to `a + n - 1`. -/
noncomputable def osPartF (c a n : ℕ) : ℕ := (((osCallsF c).drop a).take n).sum

/-- Its calls from `a`. -/
noncomputable def osRestF (c a : ℕ) : ℕ := ((osCallsF c).drop a).sum

theorem sum_take_drop : ∀ (l : List ℕ) (i : ℕ), l.sum = (l.take i).sum + (l.drop i).sum
  | [], _ => by simp
  | _ :: _, 0 => by simp
  | a :: l, i + 1 => by
    simp only [List.take_succ_cons, List.drop_succ_cons, List.sum_cons]
    have := sum_take_drop l i
    omega

/-- **`osCF` in three parts.** -/
theorem osCF_split (c k m : ℕ) :
    osCF c = osHeadF c + osPartF c 0 k + osPartF c k m + osRestF c (k + m) := by
  have h : osCF c = osHeadF c + (osCallsF c).sum := rfl
  rw [h, sum_take_drop (osCallsF c) k, sum_take_drop ((osCallsF c).drop k) m]
  unfold osPartF osRestF
  rw [List.drop_drop, List.drop_zero]
  omega

end
end LeanVM.Guest.Count
