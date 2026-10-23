/-
  LeanVM.Guest.B1.Opening.QueriesT

  The expansion of `opening_queries` and of its loop helper as templates over the shape of a
  level: the leaf row and its dot product, the leaf hash, the Merkle path below the cap, the cap
  leaf, and the query chain.
-/

module

public import LeanVM.Guest.B1.Opening.Meaning
public import LeanVM.Guest.B1.Fs.Templates

/-!
# The templates of `opening_queries` (TRIAGE G #33, #39, #40)

`opening_queries(cap, flags, lam, lam_n, query_bit_ptrs, row_eq_weights, n_iters_g, odd, base, I,
leaf_cells, depth, cd)` (G:1246-1269) has 56 specializations, one per level shape (`Oq`). One
query (`opening_query`, G:1179-1243, inline, with `verify_merkle_path`, G:1028-1043) from its first
value `b` is `oqQueryT`:

* the row: `R` hinted words (`I` at level 0, `base = 1`; `3I` limbs deeper) at `b .. b + R`, packed
  in pairs (`pack64x2`), the packed cell `j` at `oqPk b R j`;
* its dot product with the weights at `wp`: `I / 8` groups of `8` words, each a sum of words times
  `wp[l]`, times `wp[8 + h]`, summed (`oqDotT`), the deeper levels' words assembled from their
  limbs first; the result at `oqDot`;
* the zero/padding run `pr .. pr + 4` (`1, 0, 0, 0, 0`), emitted by the first query of a function
  and reused by the second;
* the leaf hash: `keccak_cells` of the `R / 2` packed cells in `B = 16·(R/2)/136 + 1` blocks
  (`oqLeafT`), the padding `0x01` (the run's first cell) and `0x80` XORed into the last block;
* the path: the hinted children (`merkle_children`) in a frame run of 80 cells at `pp`, one level
  per path bit: the node stored into the child its bit selects, the children hashed (`oqLevelT`);
* the cap leaf: the parent's flag set and the node stored at the cap leaf (`oqCapT`).

The templates mirror the compiler's expansion exactly; `B1/Opening/QueriesBody*.lean` check them
against the data by kernel evaluation.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Shapes -/

/-- A level's shape: `base` (`1` at level 0), the interleave `I`, the path depth below the cap
`pd = depth - cd` and the cap depth `cd`. -/
structure Oq where
  base : ℕ
  I : ℕ
  pd : ℕ
  cd : ℕ

namespace Oq

/-- The row's hinted words. -/
def R (s : Oq) : ℕ := if s.base = 1 then s.I else 3 * s.I

/-- The words of a group of the dot product. -/
def lo (s : Oq) : ℕ := rowLo s.I

/-- The values a deeper level's word takes to assemble. -/
def tsz (s : Oq) : ℕ := if s.base = 1 then 0 else 3

/-- The values of group `0` of the dot product (the others take one more, their sum). -/
def G (s : Oq) : ℕ := (2 + s.tsz) + (s.lo - 1) * (3 + s.tsz) + 2

/-- The values of the dot product. -/
def D (s : Oq) : ℕ := s.G + (s.I / s.lo - 1) * (s.G + 1)

/-- The packed cells. -/
def ncells (s : Oq) : ℕ := s.R / 2

/-- The leaf hash's blocks. -/
def B (s : Oq) : ℕ := 16 * s.ncells / rate + 1

/-- The values of the leaf hash (`B ≥ 2`): block `0` writes 13, a middle block XORs 9 and writes 13,
the last XORs 9 with one padding constant. -/
def chainLen (s : Oq) : ℕ := 13 + (s.B - 2) * 22 + 23

end Oq

/-- `1 + g^(2^j)` as the compiler folds it (`K` words, `x^64 = x^4 + x^3 + x + 1`). -/
def capFac : List ℕ := [3, 5, 17, 257, 65537, 4294967297, 26]

/-! ## The row -/

/-- The packed cell `j` of a row hinted at `b`. -/
def oqPk (b R j : ℕ) : ℕ := b + R + 3 * j + 2

/-- The row's hint. -/
def oqRowT (b R : ℕ) : List Stmt :=
  [.atom (.hint (.witness "merkle_leaf_rows" (.stack ((List.range R).map fun j ↦ .n (b + j)))))]

/-- Pack `j` of the row (`pack64x2(row[2j], row[2j+1])`). -/
def oqPackT (b R j : ℕ) : List Stmt :=
  [.atom (.assertInK (.n (b + 2 * j)) (.n (b + 2 * j + 1))),
    .atom (.const (.n (b + R + 3 * j)) (word 0 1 0)),
    .atom (.mul (.n (b + R + 3 * j + 1)) (.n (b + R + 3 * j)) (.n (b + 2 * j + 1))),
    .atom (.add (.n (b + R + 3 * j + 2)) (.n (b + 2 * j)) (.n (b + R + 3 * j + 1)))]

/-- The row's packs. -/
def oqPacksT (b R : ℕ) : List Stmt := ((List.range (R / 2)).map (oqPackT b R)).flatten

/-- The first value of the dot product. -/
def oqK1 (b R : ℕ) : ℕ := b + R + 3 * (R / 2)

/-! ## The dot product -/

/-- The first value of group `h`. -/
def oqGs (s : Oq) (b h : ℕ) : ℕ := oqK1 b s.R + (if h = 0 then 0 else h * (s.G + 1) - 1)

/-- The first value of term `l` of group `h`. -/
def oqTs (s : Oq) (b h l : ℕ) : ℕ :=
  oqGs s b h + (if l = 0 then 0 else (2 + s.tsz) + (l - 1) * (3 + s.tsz))

/-- The row word of term `l` of group `h`: the hinted word at level 0, the assembled one deeper. -/
def oqWordV (s : Oq) (b h l : ℕ) : ℕ :=
  if s.base = 1 then b + (s.lo * h + l) else oqTs s b h l + 2

/-- A deeper level's word `jw` from its limbs, first value `t`. -/
def oqWordT (s : Oq) (b jw t : ℕ) : List Stmt :=
  if jw % 2 = 0 then
    [.atom (.const (.n t) (word 0 0 1)), .atom (.mul (.n (t + 1)) (.n t) (.n (b + (3 * jw + 2)))),
      .atom (.add (.n (t + 2)) (.n (oqPk b s.R (3 * jw / 2))) (.n (t + 1)))]
  else
    [.atom (.const (.n t) (word 0 1 0)),
      .atom (.mul (.n (t + 1)) (.n t) (.n (oqPk b s.R ((3 * jw + 1) / 2)))),
      .atom (.add (.n (t + 2)) (.n (b + 3 * jw)) (.n (t + 1)))]

/-- The running part of group `h` after its term `l`. -/
def oqPart (s : Oq) (b h l : ℕ) : ℕ :=
  oqTs s b h l + s.tsz + (if l = 0 then 1 else 2)

/-- Term `l` of group `h`: the word (deeper levels), its weight `wp[l]`, the product, the sum. -/
def oqTermT (s : Oq) (wp : V) (b h l : ℕ) : List Stmt :=
  (if s.base = 1 then [] else oqWordT s b (s.lo * h + l) (oqTs s b h l)) ++
    [.atom (.load (.n (oqTs s b h l + s.tsz)) wp l),
      .atom (.mul (.n (oqTs s b h l + s.tsz + 1)) (.n (oqWordV s b h l)) (.n (oqTs s b h l + s.tsz)))] ++
    (if l = 0 then [] else
      [.atom (.add (.n (oqTs s b h l + s.tsz + 2)) (.n (oqPart s b h (l - 1)))
        (.n (oqTs s b h l + s.tsz + 1)))])

/-- The dot product after group `h`. -/
def oqDotAfter (s : Oq) (b h : ℕ) : ℕ := oqGs s b h + s.G - (if h = 0 then 1 else 0)

/-- Group `h`: its terms, times `wp[lo + h]`, added to the running dot product. -/
def oqGroupT (s : Oq) (wp : V) (b h : ℕ) : List Stmt :=
  ((List.range s.lo).map (oqTermT s wp b h)).flatten ++
    [.atom (.load (.n (oqGs s b h + s.G - 2)) wp (s.lo + h)),
      .atom (.mul (.n (oqGs s b h + s.G - 1)) (.n (oqGs s b h + s.G - 2))
        (.n (oqPart s b h (s.lo - 1))))] ++
    (if h = 0 then [] else
      [.atom (.add (.n (oqGs s b h + s.G)) (.n (oqDotAfter s b (h - 1))) (.n (oqGs s b h + s.G - 1)))])

/-- The dot product. -/
def oqDotT (s : Oq) (wp : V) (b : ℕ) : List Stmt :=
  ((List.range (s.I / s.lo)).map (oqGroupT s wp b)).flatten

/-- The value of the dot product. -/
def oqDot (s : Oq) (b : ℕ) : ℕ := oqDotAfter s b (s.I / s.lo - 1)

/-! ## The padding run and the leaf hash -/

/-- The zero/padding run (`keccak_pad_run`): `1`, then four zeros. -/
def oqPadT (pr : ℕ) : List Stmt :=
  [.atom (.const (.n pr) (word 1 0 0)), .atom (.const (.n (pr + 1)) (word 0 0 0)),
    .atom (.const (.n (pr + 2)) (word 0 0 0)), .atom (.const (.n (pr + 3)) (word 0 0 0)),
    .atom (.const (.n (pr + 4)) (word 0 0 0))]

/-- The first value of block `k` of the leaf hash. -/
def oqBs (kL k : ℕ) : ℕ := if k = 0 then kL else kL + 13 + (k - 1) * 22

/-- Cell `c` of the state after block `k` (`k < B`): block `k`'s outputs. -/
def oqOut (s : Oq) (kL k c : ℕ) : ℕ :=
  if k = 0 then kL + c else if k + 1 = s.B then oqBs kL k + 10 + c else oqBs kL k + 9 + c

/-- The `0x80` padding constant of the last block's cell `8` (`byteCell (136B - 1) 0x80`). -/
def oqW80 (s : Oq) : E :=
  if (rate * s.B - 1) % 16 < 8 then word (2 ^ 63) 0 0 else word 0 (2 ^ 63) 0

/-- Block `k ≥ 1`'s input cell `c < 9`: the previous output plus the packed cell, the padding
`0x01` (the run's first cell) or the padding `0x80` (a constant), as the cell index is a row cell,
the cell after it or the next. -/
def oqXorT (s : Oq) (b pr kL k c : ℕ) : List Stmt :=
  let m := 17 * k / 2 + c
  let t := oqBs kL k + c
  if m < s.ncells then [.atom (.add (.n t) (.n (oqOut s kL (k - 1) c)) (.n (oqPk b s.R m)))]
  else if m = s.ncells then [.atom (.add (.n t) (.n (oqOut s kL (k - 1) c)) (.n pr))]
  else [.atom (.const (.n t) (oqW80 s)), .atom (.add (.n (t + 1)) (.n (oqOut s kL (k - 1) c)) (.n t))]

/-- Block `k ≥ 1`'s input cell `c < 9`'s value. -/
def oqIn (s : Oq) (kL k c : ℕ) : ℕ :=
  if 17 * k / 2 + c ≤ s.ncells then oqBs kL k + c else oqBs kL k + c + 1

/-- Block `k` of the leaf hash. -/
def oqBlockT (s : Oq) (b pr kL k : ℕ) : List Stmt :=
  if k = 0 then
    [.atom (.keccak (((List.range 9).map fun c ↦ .n (oqPk b s.R c)) ++
        [.n (pr + 1), .n (pr + 2), .n (pr + 3), .n (pr + 4)])
      ((List.range 13).map fun c ↦ .n (oqOut s kL 0 c)) (Keccak.inLayout 0) (Keccak.outLayout s.B 0))]
  else
    ((List.range 9).map (oqXorT s b pr kL k)).flatten ++
      [.atom (.keccak (((List.range 9).map fun c ↦ .n (oqIn s kL k c)) ++
          ((List.range 4).map fun c ↦ .n (oqOut s kL (k - 1) (9 + c))))
        ((List.range 13).map fun c ↦ .n (oqOut s kL k c)) (Keccak.inLayout k) (Keccak.outLayout s.B k))]

/-- The leaf hash. -/
def oqLeafT (s : Oq) (b pr kL : ℕ) : List Stmt :=
  ((List.range s.B).map (oqBlockT s b pr kL)).flatten

/-! ## The path -/

/-- The first level's value of the path, the hinted children at `ch`, the frame address at
`ch + 4pd`, its 80-cell run ending at `ch + 80`, the step `pp·(1 + g²)` at `ch + 82`. -/
def oqL0 (ch : ℕ) : ℕ := ch + 83

/-- The node a path level starts from: the leaf digest, then the previous level's. -/
def oqNode (s : Oq) (kL ch l i : ℕ) : ℕ :=
  if l = 0 then oqOut s kL (s.B - 1) i else oqL0 ch + 17 * (l - 1) + 4 + i

/-- Level `l` of the path: the bit, the selected child, the node stored there, the children
hashed (`keccak(path[4l:4l+2], path[4l+2:4l+4], node)`). -/
def oqLevelT (s : Oq) (bp : V) (pr kL ch l : ℕ) : List Stmt :=
  let L := oqL0 ch + 17 * l
  let pp := ch + 4 * s.pd
  [.atom (.load (.n L) bp l), .atom (.mul (.n (L + 1)) (.n L) (.n (ch + 82))),
    .atom (.add (.n (L + 2)) (.n pp) (.n (L + 1))),
    .atom (.load (.n (oqNode s kL ch l 0)) (.n (L + 2)) (4 * l)),
    .atom (.load (.n (oqNode s kL ch l 1)) (.n (L + 2)) (4 * l + 1)),
    .atom (.const (.n (L + 3)) (word (2 ^ 63) 0 0)),
    .atom (.keccak [.n (ch + 4 * l), .n (ch + 4 * l + 1), .n (ch + 4 * l + 2), .n (ch + 4 * l + 3),
      .n pr, .n (pr + 1), .n (pr + 2), .n (pr + 3), .n (L + 3), .n (pr + 1), .n (pr + 2), .n (pr + 3),
      .n (pr + 4)] ((List.range 13).map fun c ↦ .n (L + 4 + c)) false false)]

/-- The path: the children hinted, the frame run, the step `pp·(1 + g²)`, the levels. -/
def oqPathT (s : Oq) (bp : V) (pr kL ch : ℕ) : List Stmt :=
  let pp := ch + 4 * s.pd
  [.atom (.hint (.witness "merkle_children" (.stack ((List.range (4 * s.pd)).map fun j ↦ .n (ch + j))))),
    .atom (.frameAddr (.n pp) (((List.range (4 * s.pd)).map fun j ↦ .n (ch + j)) ++
      ((List.range (80 - 4 * s.pd)).map fun j ↦ .n (pp + 1 + j)))),
    .atom (.const (.n (pp + 81 - 4 * s.pd)) (word 5 0 0)),
    .atom (.mul (.n (ch + 82)) (.n pp) (.n (ch + 81)))] ++
    ((List.range s.pd).map (oqLevelT s bp pr kL ch)).flatten

/-! ## The cap leaf -/

/-- The cap section's first value. -/
def oqCq (s : Oq) (ch : ℕ) : ℕ := oqL0 ch + 17 * s.pd

/-- The product `q` after the cap bits `1 .. j`. -/
def oqQ (s : Oq) (ch j : ℕ) : ℕ := oqCq s ch + 4 + 6 * j

/-- Cap bit `j ≥ 1`: `q ← q·(1 + b·(1 + g^(2^j)))`. -/
def oqCapBitT (s : Oq) (bp : V) (ch j : ℕ) : List Stmt :=
  let Y := oqCq s ch + 5 + 6 * (j - 1)
  [.atom (.const (.n Y) (word 1 0 0)), .atom (.load (.n (Y + 1)) bp (s.pd + 1 + j)),
    .atom (.const (.n (Y + 2)) (word (capFac.getD j 0) 0 0)),
    .atom (.mul (.n (Y + 3)) (.n (Y + 1)) (.n (Y + 2))),
    .atom (.add (.n (Y + 4)) (.n Y) (.n (Y + 3))),
    .atom (.mul (.n (Y + 5)) (.n (oqQ s ch (j - 1))) (.n (Y + 4)))]

/-- The cap leaf (`cd ≥ 2`): `q = g^(q / 2^(pd+1))` from the cap bits, the parent's flag set, the
node stored at the cap leaf `cap·q⁴·g^(2b)` at `2^(cd+1)`. -/
def oqCapT (s : Oq) (bp cap flags : V) (kL ch : ℕ) : List Stmt :=
  let Cq := oqCq s ch
  let q := oqQ s ch (s.cd - 2)
  let z := Cq + 5 + 6 * (s.cd - 2)
  [.atom (.const (.n Cq) (word 1 0 0)), .atom (.load (.n (Cq + 1)) bp (s.pd + 1)),
    .atom (.const (.n (Cq + 2)) (word (capFac.getD 0 0) 0 0)),
    .atom (.mul (.n (Cq + 3)) (.n (Cq + 1)) (.n (Cq + 2))),
    .atom (.add (.n (Cq + 4)) (.n Cq) (.n (Cq + 3)))] ++
    ((List.range (s.cd - 2)).map fun j ↦ oqCapBitT s bp ch (j + 1)).flatten ++
    [.atom (.mul (.n z) flags (.n q)), .atom (.const (.n (z + 1)) (word 1 0 0)),
      .atom (.load (.n (z + 1)) (.n z) (2 ^ (s.cd - 1))),
      .atom (.mul (.n (z + 2)) (.n q) (.n q)), .atom (.mul (.n (z + 3)) cap (.n (z + 2))),
      .atom (.mul (.n (z + 4)) (.n (z + 3)) (.n (z + 2))), .atom (.const (.n (z + 5)) (word 1 0 0)),
      .atom (.load (.n (z + 6)) bp s.pd), .atom (.const (.n (z + 7)) (word 5 0 0)),
      .atom (.mul (.n (z + 8)) (.n (z + 6)) (.n (z + 7))),
      .atom (.add (.n (z + 9)) (.n (z + 5)) (.n (z + 8))),
      .atom (.mul (.n (z + 10)) (.n (z + 4)) (.n (z + 9))),
      .atom (.load (.n (oqNode s kL ch s.pd 0)) (.n (z + 10)) (2 ^ (s.cd + 1))),
      .atom (.load (.n (oqNode s kL ch s.pd 1)) (.n (z + 10)) (2 ^ (s.cd + 1) + 1))]

/-! ## One query -/

/-- The first value of the leaf hash: after the dot product, and the padding run if emitted. -/
def oqKL (s : Oq) (b : ℕ) (emit : Bool) : ℕ := oqK1 b s.R + s.D + (if emit then 5 else 0)

/-- The padding run's first value. -/
def oqPr (s : Oq) (b : ℕ) (emit : Bool) (pr : ℕ) : ℕ := if emit then oqK1 b s.R + s.D else pr

/-- The first hinted child of the path. -/
def oqCh (s : Oq) (b : ℕ) (emit : Bool) : ℕ := oqKL s b emit + s.chainLen

/-- **One query** from the value `b`, its bits at `bp`, emitting the padding run (`emit`) or
reusing the one at `pr`. -/
def oqQueryT (s : Oq) (bp cap flags wp : V) (b : ℕ) (emit : Bool) (pr : ℕ) : List Stmt :=
  oqRowT b s.R ++ oqPacksT b s.R ++ oqDotT s wp b ++ (if emit then oqPadT (oqK1 b s.R + s.D) else []) ++
    oqLeafT s b (oqPr s b emit pr) (oqKL s b emit) ++
    oqPathT s bp (oqPr s b emit pr) (oqKL s b emit) (oqCh s b emit) ++
    oqCapT s bp cap flags (oqKL s b emit) (oqCh s b emit)

/-- The first value after a query. -/
def oqEnd (s : Oq) (b : ℕ) (emit : Bool) : ℕ := oqCq s (oqCh s b emit) + 16 + 6 * (s.cd - 2)

/-! ## The loop and the function -/

/-- The loop helper's body (`base = 1`: two queries an iteration, from the bit pointers at
`qptrs·x²` offsets `odd`, `odd + 1`), on its parameters `x, N, qptrs, cap, flags, wp, chain, μ`
(`0 .. 7`). -/
def oqLoop1T (s : Oq) (odd : ℕ) (name : String) : List Stmt :=
  let e1 := oqEnd s 11 true
  let e2 := oqEnd s (e1 + 1) false
  let c := e2
  [.atom (.mul (.n 8) (.n 2) (.n 0)), .atom (.mul (.n 9) (.n 8) (.n 0)), .atom (.load (.n 10) (.n 9) odd)] ++
    oqQueryT s (.n 10) (.n 3) (.n 4) (.n 5) 11 true 0 ++
    [.atom (.load (.n e1) (.n 9) (odd + 1))] ++
    oqQueryT s (.n e1) (.n 3) (.n 4) (.n 5) (e1 + 1) false (oqK1 11 s.R + s.D) ++
    [.atom (.mul (.n c) (.n 6) (.n 0)), .atom (.load (.n (c + 1)) (.n c) 0),
      .atom (.add (.n (c + 2)) (.n (c + 1)) (.n (oqDot s 11))),
      .atom (.mul (.n (c + 3)) (.n (c + 2)) (.n 7)),
      .atom (.add (.n (c + 4)) (.n (c + 3)) (.n (oqDot s (e1 + 1)))),
      .atom (.mul (.n (c + 5)) (.n (c + 4)) (.n 7)), .atom (.mul (.n (c + 6)) (.n 6) (.n 0)),
      .atom (.load (.n (c + 5)) (.n (c + 6)) 1),
      .atom (.const (.n (c + 7)) (word 2 0 0)), .atom (.mul (.n (c + 8)) (.n 0) (.n (c + 7))),
      .atom (.add (.n (c + 9)) (.n (c + 8)) (.n 1)), .atom (.const (.n (c + 10)) (word 2 0 0)),
      .atom (.mul (.n (c + 11)) (.n 0) (.n (c + 10))),
      .callIf (.n (c + 9)) name [.n (c + 11), .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7], .ret []]

/-- The loop helper's body (`base = 0`: one query an iteration, from the bit pointer `qptrs[x]`). -/
def oqLoop0T (s : Oq) (name : String) : List Stmt :=
  let c := oqEnd s 10 true
  [.atom (.mul (.n 8) (.n 2) (.n 0)), .atom (.load (.n 9) (.n 8) 0)] ++
    oqQueryT s (.n 9) (.n 3) (.n 4) (.n 5) 10 true 0 ++
    [.atom (.mul (.n c) (.n 6) (.n 0)), .atom (.load (.n (c + 1)) (.n c) 0),
      .atom (.add (.n (c + 2)) (.n (c + 1)) (.n (oqDot s 10))),
      .atom (.mul (.n (c + 3)) (.n (c + 2)) (.n 7)), .atom (.mul (.n (c + 4)) (.n 6) (.n 0)),
      .atom (.load (.n (c + 3)) (.n (c + 4)) 1),
      .atom (.const (.n (c + 5)) (word 2 0 0)), .atom (.mul (.n (c + 6)) (.n 0) (.n (c + 5))),
      .atom (.add (.n (c + 7)) (.n (c + 6)) (.n 1)), .atom (.const (.n (c + 8)) (word 2 0 0)),
      .atom (.mul (.n (c + 9)) (.n 0) (.n (c + 8))),
      .callIf (.n (c + 7)) name [.n (c + 9), .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7], .ret []]

/-- The function's body on its parameters `cap, flags, λ, λ_n, qptrs, wp, N` (`0 .. 6`): `μ` with
`1 = μ·λ`, the chain allocated, its start (the odd first query's value times `μ`, or `0`), the
loop, the chain's end times `λ_n`. -/
def oqMainT (s : Oq) (odd : ℕ) (loop : String) : List Stmt :=
  let head : List Stmt := [.atom (.const (.n 7) (word 1 0 0)), .atom (.mul (.n 7) (.n 8) (.n 2)),
    .atom (.const (.n 9) (word 2 0 0)), .atom (.mul (.n 10) (.n 6) (.n 9)),
    .atom (.hint (.allocDyn (.n 11) (.n 10)))]
  let k := if odd = 1 then oqEnd s 13 true + 1 else 13
  let start : List Stmt :=
    if odd = 1 then
      [.atom (.load (.n 12) (.n 4) 0)] ++ oqQueryT s (.n 12) (.n 0) (.n 1) (.n 5) 13 true 0 ++
        [.atom (.mul (.n (k - 1)) (.n (oqDot s 13)) (.n 8)), .atom (.load (.n (k - 1)) (.n 11) 0)]
    else [.atom (.const (.n 12) (word 0 0 0)), .atom (.load (.n 12) (.n 11) 0)]
  head ++ start ++
    [.atom (.const (.n k) (word 1 0 0)), .atom (.add (.n (k + 1)) (.n k) (.n 6)),
      .atom (.const (.n (k + 2)) (word 1 0 0)),
      .callIf (.n (k + 1)) loop [.n (k + 2), .n 6, .n 4, .n 0, .n 1, .n 5, .n 11, .n 8],
      .atom (.mul (.n (k + 3)) (.n 11) (.n 6)), .atom (.load (.n (k + 4)) (.n (k + 3)) 0),
      .atom (.mul (.n (k + 5)) (.n (k + 4)) (.n 3)), .ret [.n (k + 5)]]

end
end LeanVM.Guest.B1
