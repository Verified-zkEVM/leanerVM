/-
  LeanVM.Guest.B1.Tables.VtC.NotStored

  Whether a read is one of `verify_tables`' stores, decided fast: by its numbers (`Fwd.notStoredB`).
-/

module

public import LeanVM.Guest.B1.Tables.VtC.Stores
public import LeanVM.Guest.B1.Fwd.NotStored

/-!
# A read that is not a store

`a ∉ vtSL` by the read's numbers, its pointer first (`Fwd.notStoredB`, `vtStorePtrs`): every
`decide` of it uses `instDecidableNotMemVtSL`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Guest.Core LeanVM.Guest.B1.Fwd

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

theorem vtSL_ptrs : vtSL.all (ptrInB vtStorePtrs) = true := by decide +kernel

instance (priority := high) instDecidableNotMemVtSL (a : Atom) : Decidable (a ∉ vtSL) :=
  decidable_of_iff _ (notStoredB_iff vtSL_ptrs a)

end
end LeanVM.Guest.B1.Tables
