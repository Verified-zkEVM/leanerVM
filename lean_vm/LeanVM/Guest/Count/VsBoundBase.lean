/-
  LeanVM.Guest.Count.VsBoundBase

  `open_stacked`'s bound per candidate with its name spelled by `natStr` (`osC`), so that the
  kernel evaluates it (`openNames` spells the names by `toString`, whose body the kernel cannot
  see), and by the search tree's lookups (`osCF`).
-/

module

public import LeanVM.Guest.Budget.Closed
public import LeanVM.Guest.B1.Whir.Names
public import LeanVM.Guest.Count.Fast

namespace LeanVM.Guest.Count

open LeanVM.Guest.B1.Whir

@[expose] public section

/-- `open_stacked`'s words at candidate `c`, its name spelled by `natStr`. -/
noncomputable def osC (c : ℕ) : ℕ :=
  B1.osBos B2C.fs (B1.osBk B2C.fs wSB wSK (osCfg c)) ("open_stacked__L" ++ natStr c) (osCfg c)

/-- `osC` by the search tree's lookups (`Count.Fast`), for the kernel. -/
noncomputable def osCF (c : ℕ) : ℕ :=
  B1.osBos fsFast (B1.osBk fsFast wSBFast wSKFast (osCfg c)) ("open_stacked__L" ++ natStr c) (osCfg c)

theorem osC_eq_fast (c : ℕ) : osC c = osCF c := by
  unfold osC osCF
  rw [fsFast_eq, wSBFast_eq, wSKFast_eq]

/-- `osBosAt` at a candidate is `osC`. -/
theorem osBosAt_eq {μ r : ℕ} (h : candidate μ r < 28) :
    B1.osBosAt B2C.fs wSB wSK μ r = osC (candidate μ r) := by
  unfold B1.osBosAt osC openName openNames
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h, Option.map_some,
    Option.getD_some, natStr_eq]

theorem foldl_max_le {M : ℕ} : ∀ (l : List ℕ) (a : ℕ), a ≤ M → (∀ x ∈ l, x ≤ M) → l.foldl max a ≤ M
  | [], _, ha, _ => ha
  | y :: l, a, ha, h => by
    rw [List.foldl_cons]
    exact foldl_max_le l _ (max_le ha (h y List.mem_cons_self))
      fun x hx => h x (List.mem_cons_of_mem _ hx)

/-- The largest of a list within `M`. -/
theorem lmax_le {l : List ℕ} {M : ℕ} (h : ∀ x ∈ l, x ≤ M) : B1.VerifySub.lmax l ≤ M :=
  foldl_max_le l 0 (Nat.zero_le _) h

end
end LeanVM.Guest.Count
