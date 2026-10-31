/-
  LeanVM.Guest.B1.Tables.VtC.NotStored

  Whether a read is one of `verify_tables`' stores, decided fast: by its three numbers.
-/

module

public import LeanVM.Guest.B1.Tables.VtC.Stores

/-!
# A read that is not a store

A kernel check `a ∉ vtSL` through the derived `DecidableEq Atom` compares `a` with the 623 stores
structurally, about half a millisecond each: `∀ r < 54, ∀ a ∈ reads r, a ∉ vtSL` took minutes.
`vtNotStoredB` decides a read `.load (.n d) (.n p) off` by numbers: no store goes through `p`
(`vtStorePtrs`, the stores' pointers, `vtSL_ptrs`), or none is the read, by its three numbers;
`instDecidableNotMemVtSL` makes every `decide` of `a ∉ vtSL` use it (`vtNotStoredB_iff`).
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Guest.Core

@[expose] public section

/-- The pointers of `verify_tables`' stores (`vtSL_ptrs`). -/
def vtStorePtrs : List ℕ :=
  [16, 17, 31, 197, 221, 246, 271, 296, 321, 346, 371, 396, 421, 446, 471, 496, 521, 546, 571,
    596, 621, 646, 671, 696, 721, 746, 771, 796, 821, 846, 871, 896, 921, 946, 971, 996, 1021,
    1046, 1071, 1096, 1121, 1146, 1171, 1196, 1221, 1246, 1271, 1296, 1321, 1346, 1371, 1396, 1421,
    1446, 1471, 1496, 1521, 1536, 1560, 1585, 1610, 1635, 1660, 1685, 1710, 1735, 1760, 1785, 1810,
    1835, 1860, 1885, 1910, 1935, 1960, 1985, 2010, 2035, 2060, 2085, 2110, 2135, 2160, 2185, 2210,
    2235, 2260, 2285, 2310, 2335, 2360, 2385, 2410, 2435, 2460, 2485, 2510, 2535, 2560, 2585, 2610,
    2635, 2732, 2851, 5912, 5915]

/-- A store's pointer is in `vtStorePtrs`. -/
def vtPtrInB : Atom → Bool
  | .load _ (.n q) _ => vtStorePtrs.contains q
  | _ => false

theorem vtSL_ptrs : vtSL.all vtPtrInB = true := by decide +kernel

/-- A store is not the read `.load (.n d) (.n p) off`, by the numbers. -/
def vtOtherB (d p off : ℕ) : Atom → Bool
  | .load (.n d') (.n p') off' => !(p' == p && d' == d && off' == off)
  | _ => true

/-- `a` is none of `verify_tables`' stores: a read by its numbers, another atom structurally. -/
def vtNotStoredB : Atom → Bool
  | .load (.n d) (.n p) off => !vtStorePtrs.contains p || vtSL.all (vtOtherB d p off)
  | a => decide (a ∉ vtSL)

theorem vtOtherB_iff (d p off : ℕ) (b : Atom) :
    vtOtherB d p off b = true ↔ b ≠ .load (.n d) (.n p) off := by
  unfold vtOtherB
  split
  · simp only [Bool.not_eq_true', Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq,
      Atom.load.injEq, V.mk.injEq, true_and, not_and]
    omega
  · rename_i h
    simp only [true_iff]
    rintro rfl
    exact h d p off rfl

theorem vtNotStoredB_iff (a : Atom) : vtNotStoredB a = true ↔ a ∉ vtSL := by
  unfold vtNotStoredB
  split
  · rename_i d p off
    rw [Bool.or_eq_true, List.all_eq_true]
    simp only [vtOtherB_iff, Bool.not_eq_true']
    refine ⟨fun h hm ↦ h.elim (fun hp ↦ ?_) (fun h ↦ h _ hm rfl),
      fun h ↦ .inr fun b hb e ↦ h (e ▸ hb)⟩
    have := List.all_eq_true.mp vtSL_ptrs _ hm
    simp only [vtPtrInB] at this
    rw [this] at hp
    exact Bool.false_ne_true hp.symm
  · exact decide_eq_true_iff

instance (priority := high) instDecidableNotMemVtSL (a : Atom) : Decidable (a ∉ vtSL) :=
  decidable_of_iff _ (vtNotStoredB_iff a)

end
end LeanVM.Guest.B1.Tables
