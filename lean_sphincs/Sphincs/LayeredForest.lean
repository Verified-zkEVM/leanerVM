module


/-!
# leanSPHINCS, layered: the forest's parameters and codeword table

The forest's parameters, index types and codeword table of `SphincsLayered` (`Sphincs/Layered.lean`,
which imports this module): numbers and finite types alone, so that the kernel-checked tables
(`H0FTab`, `H0PTab`, `H0NTab`, `LifetimeCertificates`), which read them, do not depend on the
scheme, the statement or the proofs.
-/

@[expose] public section

namespace SphincsLayered

/-! #### Forest parameters and types -/

/-- Number of coordinates. -/
def forestCoords : Nat := 8
/-- Height of a coordinate's top tree (16 super-children). -/
def topHeight : Nat := 4
/-- Height of a sub-tree (8 children). -/
def subHeight : Nat := 3
/-- Chains per child. -/
def childChains : Nat := 6
/-- The top position of a chain: positions `0 .. 4`. -/
def chainTop : Nat := 4

abbrev Coord := Fin forestCoords
abbrev SuperIdx := Fin (2 ^ topHeight)
abbrev SubIdx := Fin 2
abbrev ChildIdx := Fin (2 ^ subHeight)
abbrev FChain := Fin childChains
/-- A pair of chains `(2t, 2t + 1)` of a forest WOTS key, `t < 3`: one seed derivation. -/
abbrev FPair := Fin 3
/-- A forest chain position, `0 .. 4`. -/
abbrev FPos := Fin (chainTop + 1)
/-- A forest chain step, from position `t` to `t + 1`, `t < 4`. -/
abbrev FStep := Fin chainTop
/-- A codeword: the deficit `d_i ∈ {0..4}` of every chain. -/
abbrev Codeword := FChain → FPos
/-- A codeword index, 8 digest bits. -/
abbrev LutIdx := Fin 256

/-! #### The codeword table -/

/-- The 256 entries of the codeword table as base-5 numbers with `d_0` the most significant digit; a
codeword listed twice is chosen by two digest values. The table is `codewordRule`
(`codewordCodes_eq_rule`): the codewords sorted by decreasing `Σ d_i²`, then lexicographically, entry
`t` being codeword number `t mod 214`. By digit pattern: the 30 codewords with digits `{4,1}` twice
each; of the 30 with `{3,2}`, 12 twice and 18 once; the 60 with `{3,1,1}` and the 60 with `{2,2,1}`
once; 34 of the 60 with `{2,1,1,1}` once; none of the 6 with `{1,1,1,1,1}`. Written by
`scripts/forest_table.py`. -/
def codewordCodes : List Nat :=
  [9, 21, 29, 45, 101, 105, 129, 145, 225, 501, 505, 525, 629, 645, 725, 1125,
   2501, 2505, 2525, 2625, 3129, 3145, 3225, 3625, 5625, 12501, 12505, 12525, 12625, 13125, 13, 17,
   53, 65, 77, 85, 253, 265, 325, 377, 385, 425, 1253, 1265, 1325, 1625, 1877, 1885,
   1925, 2125, 6253, 6265, 6325, 6625, 8125, 9377, 9385, 9425, 9625, 10625, 33, 41, 81, 133,
   141, 153, 165, 201, 205, 381, 401, 405, 633, 641, 653, 665, 701, 705, 753, 765,
   825, 1001, 1005, 1025, 1881, 1901, 1905, 2001, 2005, 2025, 3133, 3141, 3153, 3165, 3201, 3205,
   3253, 3265, 3325, 3501, 3505, 3525, 3753, 3765, 3825, 4125, 5001, 5005, 5025, 5125, 9381, 9401,
   9405, 9501, 9505, 9525, 10001, 10005, 10025, 10125, 37, 57, 61, 137, 177, 185, 257, 261,
   277, 285, 301, 305, 637, 677, 685, 877, 885, 925, 1257, 1261, 1277, 1285, 1301, 1305,
   1377, 1385, 1425, 1501, 1505, 1525, 3137, 3177, 3185, 3377, 3385, 3425, 4377, 4385, 4425, 4625,
   6257, 6261, 6277, 6285, 6301, 6305, 6377, 6385, 6425, 6501, 6505, 6525, 6877, 6885, 6925, 7125,
   7501, 7505, 7525, 7625, 157, 161, 181, 281, 657, 661, 681, 757, 761, 777, 785, 801,
   805, 881, 901, 905, 1281, 1381, 1401, 1405, 3157, 3161, 3181, 3257, 3261, 3277, 3285, 3301,
   3305, 3381, 3401, 3405, 3757, 3761, 9, 21, 29, 45, 101, 105, 129, 145, 225, 501,
   505, 525, 629, 645, 725, 1125, 2501, 2505, 2525, 2625, 3129, 3145, 3225, 3625, 5625, 12501,
   12505, 12525, 12625, 13125, 13, 17, 53, 65, 77, 85, 253, 265, 325, 377, 385, 425]

/-- Digit `i` (`i = 0` most significant) of a base-5 code with 6 digits. -/
def codeDigit (code : Nat) (i : FChain) : FPos :=
  ⟨code / 5 ^ (5 - i.val) % 5, Nat.mod_lt _ (by decide)⟩

/-- `lut t`: entry `t` of the table. -/
def lut (t : LutIdx) : Codeword := codeDigit (codewordCodes.getD t.val 0)

end SphincsLayered

end
