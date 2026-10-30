/-
  LeanVM.Guest.B1.VerifySub.Template

  `verify_sub`'s body as a template (G:3140-3329), section by section.
-/

module

public import LeanVM.Guest.B1.VerifySub.Interface
public import LeanVM.Guest.B1.KeccakGkr.Lib
public import LeanVM.Guest.B1.Whir.Interface
public import LeanVM.Guest.B1.Whir.Names

/-!
# `verify_sub` as a template

The sections, in order (G = `lean_ethereum.py` at leanVM `3375f7a13`):

* `vsHeadT`: the pool and the lengths allocated, the seed's permutation (`keccak_cells`), the
  stream (G:3152-3161);
* `vsReadsT`: the eight announced words read (`fs_next`), the table rows stored, the first four
  absorbed (G:3169-3181);
* `vsSizesT`: the rate and the memory's log-size as `g`-powers, their range checks, `dims_g`,
  `kappa_base` (G:3182-3193);
* `vsKappaT`: `block_kappa` (G:3194-3198);
* `vsPushT`: the push blocks' total and the bus depth `g^μ`, `zeta` (G:3199-3204);
* `vsRootsT`: the last four announced words absorbed, the root's two words read and checked
  (G:3206-3218);
* `vsAlphasT`: the four bus challenges (G:3224-3230);
* `vsFpwT`: their equality weights, then `β` (G:3231-3234);
* `vsCallsT`: `verify_bus_gkr`, `verify_tables`, `verify_keccak` (G:3236-3248);
* `vsMapsT`: the ring map's challenges (G:3257-3263);
* `vsCtabT`: their Frobenius coefficients `c_table`, and `ring_switch_target` (G:3264-3273);
* `vsLamT`: the batching challenge and the target (G:3274-3292);
* `vsTailT`: `certify_placement`, the stack's log, the candidate, the dispatch to `open_stacked`,
  the terminal, the deferred claim (G:3294-3329).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Atoms on numbered values -/

/-- `d = p[off]`. -/
def vsLd (d p off : ℕ) : Stmt := .atom (.load (.n d) (.n p) off)

/-- `d = c`. -/
def vsConst (d : ℕ) (c : E) : Stmt := .atom (.const (.n d) c)

/-- `d = a · b`. -/
def vsMul (d a b : ℕ) : Stmt := .atom (.mul (.n d) (.n a) (.n b))

/-- `d = a + b`. -/
def vsAdd (d a b : ℕ) : Stmt := .atom (.add (.n d) (.n a) (.n b))

/-- A fresh buffer of `n` words at `d`. -/
def vsAlloc (d n : ℕ) : Stmt := .atom (.hint (.alloc (.n d) n))

/-- `assert log x < log k` through `y`, `t1`, `t2`. -/
def vsRange (x y t1 t2 k : ℕ) : Stmt := .atom (.rangeCheck (.n x) (.n y) (.n t1) (.n t2) (.n k))

/-- A call on numbered values. -/
def vsCall (f : String) (args rets : List ℕ) : Stmt := .call f (args.map .n) (rets.map .n)

/-- The values `b, …, b + n - 1`. -/
def vsRun (b n : ℕ) : List V := (List.range n).map fun k ↦ .n (b + k)

/-- A squeeze with nothing waiting (the zero cell `10`, the cells `11 .. 13`), on the capacity
from `capb`, outputs from `o`, the challenge at `o + 19`. -/
def vsSqzT (capb o : ℕ) : List Stmt :=
  keccakA ([.n 10, .n 10, .n 10, .n 10, .n 10, .n 11, .n 12, .n 13] ++ vsRun capb 5) (vsRun o 13) ::
    challengeT (.n o) (.n (o + 1)) (o + 13)

/-! ## The sections -/

/-- The pool and the lengths, the seed, the stream (G:3152-3161). -/
def vsHeadT : List Stmt :=
  [vsAlloc 7 165, vsAlloc 8 165, vsConst 9 (word 1 0 0), vsConst 10 (word 0 0 0),
    vsConst 11 (word 0 0 0), vsConst 12 (word 0 0 0), vsConst 13 (word 0 0 0),
    keccakA [.n 2, .n 3, .n 0, .n 1, .n 10, .n 11, .n 12, .n 13, .n 10, .n 10, .n 11, .n 12, .n 13]
      (vsRun 14 13),
    vsAlloc 27 8192, .atom (.hint (.witness "stream" (.heap (.n 27) 0 8192))), vsAlloc 28 6]

/-- The eight announced words: `x_i` at `29 + 10 i` (`i < 4`) and `82 + 10 (i - 4)`, rows `1 .. 6`
stored in `table_rows`, the first four absorbed after the fourth (G:3169-3181). -/
def vsReadsT : List Stmt :=
  fsNextT (.n 27) 0 29 ++ fsNextT (.n 27) 1 39 ++ [vsLd 39 28 0] ++ fsNextT (.n 27) 2 49 ++
    [vsLd 49 28 1] ++ fsNextT (.n 27) 3 59 ++ [vsLd 59 28 2] ++
    [keccakA [.n 36, .n 38, .n 46, .n 48, .n 56, .n 58, .n 66, .n 68, .n 22, .n 23, .n 24, .n 25,
      .n 26] (vsRun 69 13)] ++
    fsNextT (.n 27) 4 82 ++ [vsLd 82 28 3] ++ fsNextT (.n 27) 5 92 ++ [vsLd 92 28 4] ++
    fsNextT (.n 27) 6 102 ++ [vsLd 102 28 5] ++ fsNextT (.n 27) 7 112

/-- The rate and the memory's log as `g`-powers, `dims_g`, `kappa_base` (G:3182-3193). -/
def vsSizesT : List Stmt :=
  [vsCall "g_power_of_word" [112] [122], vsConst 123 (word 2 0 0), vsMul 122 124 123,
    vsConst 125 (word 8 0 0), vsRange 124 126 127 128 125, vsAlloc 129 7,
    vsCall "g_power_of_word" [29] [130], vsConst 131 (word (2 ^ 32) 0 0),
    vsRange 130 132 133 134 131, vsConst 135 (word (2 ^ 32) 0 0), vsConst 136 (word 65536 0 0),
    vsMul 130 137 136, vsRange 137 138 139 140 135, vsLd 130 129 0,
    .atom (.hint (.witness "table_logs" (.heap (.n 129) 1 6))), vsAlloc 141 8,
    vsConst 142 (word 1 0 0), vsLd 142 141 0, vsLd 130 141 1] ++
  (List.range 6).flatMap fun t ↦ [vsLd (143 + t) 129 (1 + t), vsLd (143 + t) 141 (2 + t)]

/-- Block `b`'s value in `vsKappaT`: the two bytecode blocks (`2`, `56`) take three. -/
def vsKV (b : ℕ) : ℕ := 150 + b + (if 2 < b then 2 else 0) + (if 56 < b then 2 else 0)

/-- Block `b`'s `g^κ`: its source's, times `g^19` for the bytecode blocks. -/
def vsKappaStep (b : ℕ) : List Stmt :=
  if Tables.blockKappaAdj b = 0 then
    [vsLd (vsKV b) 141 (Tables.blockKappaSrc.getD b 0), vsLd (vsKV b) 149 b]
  else
    [vsLd (vsKV b) 141 (Tables.blockKappaSrc.getD b 0), vsConst (vsKV b + 1) (word (2 ^ 19) 0 0),
      vsMul (vsKV b + 2) (vsKV b) (vsKV b + 1), vsLd (vsKV b + 2) 149 b]

/-- `block_kappa` (G:3194-3198). -/
def vsKappaT : List Stmt := vsAlloc 149 153 :: (List.range Tables.nBlocks).flatMap vsKappaStep

/-- The running product after push block `b`. -/
def vsPV (b : ℕ) : ℕ := 309 + 4 * b

/-- Push block `b`: `g_squares[block_kappa[b]]`, multiplied in. -/
def vsPushStep (b : ℕ) : List Stmt :=
  if b = 0 then [vsLd 307 149 0, vsMul 308 5 307, vsLd 309 308 0]
  else [vsLd (306 + 4 * b) 149 b, vsMul (307 + 4 * b) 5 (306 + 4 * b),
    vsLd (308 + 4 * b) (307 + 4 * b) 0, vsMul (vsPV b) (vsPV (b - 1)) (308 + 4 * b)]

/-- The push blocks' total, the bus depth, `zeta` (G:3199-3204). -/
def vsPushT : List Stmt :=
  (List.range 54).flatMap vsPushStep ++
    [vsCall "log2_ceil_in_the_exponent__L0_L34" [521, 4, 5] [522],
      .atom (.hint (.allocDyn (.n 523) (.n 522)))]

/-- The last four words absorbed, the root read and checked (G:3206-3218). -/
def vsRootsT : List Stmt :=
  [keccakA [.n 89, .n 91, .n 99, .n 101, .n 109, .n 111, .n 119, .n 121, .n 77, .n 78, .n 79,
    .n 80, .n 81] (vsRun 524 13)] ++
  fsNextT (.n 27) 8 537 ++ fsNextT (.n 27) 9 547 ++
  [vsCall "assert_canonical" [537] [557], vsCall "assert_canonical" [547] [558], vsAlloc 559 4]

/-- The four bus challenges, the first with the root waiting (G:3224-3230). -/
def vsAlphasT : List Stmt :=
  keccakA [.n 544, .n 546, .n 554, .n 556, .n 10, .n 11, .n 12, .n 13, .n 532, .n 533, .n 534,
    .n 535, .n 536] (vsRun 560 13) :: challengeT (.n 560) (.n 561) 573 ++ [vsLd 579 559 0] ++
  vsSqzT 568 580 ++ [vsLd 599 559 1] ++ vsSqzT 588 600 ++ [vsLd 619 559 2] ++
  vsSqzT 608 620 ++ [vsLd 639 559 3]

/-- One factor of `eq_weight(bus_alpha, 4, x, 0)` at `v`: `α_t` or `1 + α_t`; the statements, the
factor's value and the next free value. -/
def vsEqwFactor (x t v : ℕ) : List Stmt × ℕ × ℕ :=
  if x.testBit t then ([vsLd v 559 t], v, v + 1)
  else ([vsLd v 559 t, vsConst (v + 1) (word 1 0 0), vsAdd (v + 2) (v + 1) v], v + 2, v + 3)

/-- `eq_weight(bus_alpha, 4, x, 0)` from `v`, the product of its factors in order: the
statements, the product's value and the next free value. -/
def vsEqwT (x v : ℕ) : List Stmt × ℕ × ℕ :=
  let f0 := vsEqwFactor x 0 v
  let f1 := vsEqwFactor x 1 f0.2.2
  let p1 := f1.2.2
  let f2 := vsEqwFactor x 2 (p1 + 1)
  let p2 := f2.2.2
  let f3 := vsEqwFactor x 3 (p2 + 1)
  let p3 := f3.2.2
  (f0.1 ++ f1.1 ++ [vsMul p1 f0.2.1 f1.2.1] ++ f2.1 ++ [vsMul p2 p1 f2.2.1] ++ f3.1 ++
    [vsMul p3 p2 f3.2.1], p3, p3 + 1)

/-- The first value of `fp_w[x]`'s block. -/
def vsFpwStart : ℕ → ℕ
  | 0 => 641
  | x + 1 => (vsEqwT x (vsFpwStart x)).2.2

/-- `fp_w`, then `β` (G:3231-3234). -/
def vsFpwT : List Stmt :=
  vsAlloc 640 16 :: (List.range 16).flatMap (fun x ↦
    (vsEqwT x (vsFpwStart x)).1 ++ [vsLd (vsEqwT x (vsFpwStart x)).2.1 640 x]) ++ vsSqzT 628 817

/-- The bus's GKR, the tables, the Keccak reduction (G:3236-3248). -/
def vsCallsT : List Stmt :=
  [vsConst 837 (word 1024 0 0), vsMul 838 27 837,
    vsCall "verify_bus_gkr" [825, 826, 827, 828, 829, 838, 522, 523] ((List.range 9).map (839 + ·)),
    vsAlloc 848 34,
    vsCall "verify_tables" [839, 840, 841, 842, 843, 844, 0, 1, 523, 522, 129, 28, 149, 5, 640, 836, 7,
      8, 848, 845, 846, 847] ((List.range 9).map (849 + ·)),
    vsLd 858 129 6, vsAlloc 859 78, vsAlloc 860 64, vsConst 861 (word 1899956092796928 0 0),
    vsMul 862 7 861,
    vsCall "verify_keccak" [849, 850, 851, 852, 853, 854, 858, 848, 862, 859, 860]
      ((List.range 8).map (863 + ·))] ++
  (List.range 5).map fun i ↦ .atom (.copy (.n (871 + i)) (.n (863 + i)))

/-- The ring map's challenges: the first from `verify_keccak`, five squeezed (G:3257-3263). -/
def vsMapsT : List Stmt :=
  [vsAlloc 876 6, vsAlloc 877 64, vsLd 870 876 0] ++
  vsSqzT 871 878 ++ [vsLd 897 876 1] ++ vsSqzT 886 898 ++ [vsLd 917 876 2] ++
  vsSqzT 906 918 ++ [vsLd 937 876 3] ++ vsSqzT 926 938 ++ [vsLd 957 876 4] ++
  vsSqzT 946 958 ++ [vsLd 977 876 5]

/-- `v ↦ v²`, `s` times, from `v` (`v + 1 .. v + s`). -/
def vsSqChainT (v s : ℕ) : List Stmt := (List.range s).map fun k ↦ vsMul (v + 1 + k) (v + k) (v + k)

/-- Slot `slot` of a stage of shift `s` with challenge `mc`, from `v`:
`c[2 s·slot + s] = mc · c[2 s·slot]^(2^s)`. -/
def vsSlotT (mc s slot v : ℕ) : List Stmt :=
  vsLd v 877 (2 * s * slot) :: vsSqChainT v s ++
    [vsMul (v + s + 1) mc (v + s), vsLd (v + s + 1) 877 (2 * s * slot + s)]

/-- Stage `st` of shift `s` from `b`: its challenge, then its `32 / s` slots. -/
def vsStageT (st s b : ℕ) : List Stmt :=
  vsLd b 876 st :: (List.range (32 / s)).flatMap fun slot ↦ vsSlotT b s slot (b + 1 + slot * (s + 2))

/-- `c_table`, then `ring_switch_target` (G:3264-3273). -/
def vsCtabT : List Stmt :=
  [vsConst 978 (word 1 0 0), vsLd 978 877 0] ++ vsStageT 0 32 979 ++ vsStageT 1 16 1014 ++
    vsStageT 2 8 1051 ++ vsStageT 3 4 1092 ++ vsStageT 4 2 1141 ++ vsStageT 5 1 1206 ++
    [vsCall "ring_switch_target" [860, 876] [1303]]

/-- The pooled claim of the `i`-th batched one: the output lanes' `110 .. 134` are left out. -/
def vsKept (i : ℕ) : ℕ := if i < 110 then i else i + 25

/-- The power of `λ` before batched claim `i`. -/
def vsPw (i : ℕ) : ℕ := if i = 0 then 1323 else 1324 + 4 * i

/-- The target before batched claim `i`. -/
def vsTg (i : ℕ) : ℕ := if i = 0 then 1303 else 1323 + 4 * i

/-- Batched claim `i`: its power stored, its value read, the target and the power updated. -/
def vsLamStep (i : ℕ) : List Stmt :=
  [vsLd (vsPw i) 1324 (vsKept i), vsLd (1325 + 4 * i) 7 (vsKept i),
    vsMul (1326 + 4 * i) (vsPw i) (1325 + 4 * i), vsAdd (1327 + 4 * i) (vsTg i) (1326 + 4 * i),
    vsMul (1328 + 4 * i) (vsPw i) 1323]

/-- The batching challenge, the target (G:3274-3292). -/
def vsLamT : List Stmt :=
  vsSqzT 966 1304 ++ [vsAlloc 1324 165] ++ (List.range 140).flatMap vsLamStep ++
    [vsMul 1885 1884 869, vsAdd 1886 1883 1885]

/-- `open_stacked`'s specializations, named by `natStr` (which the kernel evaluates). -/
def vsOpenNames : List String := (List.range 28).map fun m ↦ "open_stacked__L" ++ B1.Whir.natStr m

theorem vsOpenNames_eq : vsOpenNames = B1.Whir.openNames := by
  simp only [vsOpenNames, B1.Whir.openNames, B1.Whir.natStr_eq]

/-- The placement, the stack's log, the dispatch, the terminal, the deferred claim
(G:3294-3329). -/
def vsTailT : List Stmt :=
  [vsCall "certify_placement" [141, 5] [1887, 1888, 1889],
    vsCall "log2_ceil_in_the_exponent__L15_L34" [1887, 4, 5] [1890],
    vsConst 1891 (word 8198552432976855044 0 0), vsMul 1892 1890 1891, vsConst 1893 (word 64 0 0),
    vsRange 1892 1894 1895 1896 1893, vsMul 1897 124 124, vsMul 1898 1897 124,
    vsMul 1899 1898 1898, vsMul 1900 1899 124, vsMul 1901 1892 1900,
    vsConst 1902 (word 134217728 0 0), vsRange 1901 1903 1904 1905 1902,
    .dispatch (.n 1901) vsOpenNames
      [.n 1312, .n 1313, .n 1314, .n 1315, .n 1316, .n 1886, .n 537, .n 547, .n 868] (vsRun 1906 5),
    vsCall "check_opening_terminal" [523, 848, 857, 522, 855, 130, 858, 8, 1884, 1324, 1888, 1889,
      859, 877, 1907, 1908, 1909, 1910, 1906] []] ++
  (List.range 19).flatMap (fun k ↦ [vsLd (1911 + k) 523 k, vsLd (1911 + k) 6 k]) ++
  (List.range 4).flatMap (fun k ↦ [vsLd (1930 + k) 559 k, vsLd (1930 + k) 6 (19 + k)]) ++
  [vsLd 856 6 23, .ret []]

/-- **`verify_sub`'s body as a template.** -/
def vsT : List Stmt :=
  vsHeadT ++ vsReadsT ++ vsSizesT ++ vsKappaT ++ vsPushT ++ vsRootsT ++ vsAlphasT ++ vsFpwT ++
    vsCallsT ++ vsMapsT ++ vsCtabT ++ vsLamT ++ vsTailT

end
end LeanVM.Guest.B1.VerifySub
