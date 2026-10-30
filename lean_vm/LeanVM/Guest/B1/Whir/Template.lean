/-
  LeanVM.Guest.B1.Whir.Template

  The core IR of `open_stacked` and of its loop helpers, generated from a candidate's
  configuration as the expansion numbers it: the head, the levels, the tail rounds, the point,
  the induced bases, the residual chains and the out-of-domain weights.
-/

module

public import LeanVM.Guest.B1.Whir.Config
public import LeanVM.Guest.B1.Fs.Templates
public import LeanVM.Guest.B1.Whir.Interface

/-!
# The template of `open_stacked` (TRIAGE G #42)

`osBody c` is the body of `open_stacked__L{c.m}` (`lean_ethereum.py:1276-1604` at leanVM
`4af2cdddd`) at the configuration `c = osCfg m`, value by value as the expansion numbers it: every
block takes the first free value `k` and returns the next, the running sponge cells, the cursor
(a base value and a word offset), the waiting scalars, the quadratic and the claim in `OsSt`.
`sqLoopBody` (G:1421-1433, one squeeze and its `decode_query_bits` an iteration) and
`resLoopBody` (G:1581-1594, two queries' induced products an iteration) are the loop helpers'.
The inline Fiat-Shamir helpers are B1-a's templates (`fsPackT`, `fsNextT`, `challengeT`,
`keccakA`, `B1/Fs/Templates.lean`).

`Whir/Data*.lean` check every candidate's body and loops equal to these by kernel evaluation.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Guest.Core LeanVM.Guest.B1

@[expose] public section

/-! ## Small blocks -/

/-- `g^e` as a word, its limbs written out for the kernel (`gpowK`, `Guest/Word.lean`). -/
def gw (e : ℕ) : E := E.ofLimbs (gpowK e) 0 0

/-- A value's name. -/
abbrev nv (k : ℕ) : V := .n k

/-- `HeapBuf(g^e)` at `k`: its size `k`, its pointer `k + 1`. -/
def osHeap (e k : ℕ) : List Stmt :=
  [.atom (.const (.n k) (gw e)), .atom (.hint (.allocDyn (.n (k + 1)) (.n k)))]

/-- The pointer `base·g^off`, materialized from `k` when the offset is not zero: the statements,
the pointer's value and the next free value. -/
def osMat (base off k : ℕ) : List Stmt × ℕ × ℕ :=
  if off = 0 then ([], base, k)
  else ([.atom (.const (.n k) (gw off)), .atom (.mul (.n (k + 1)) (.n base) (.n k))],
    k + 1, k + 2)

/-- Values `k .. k + n - 1`. -/
def osRun (k n : ℕ) : List V := (List.range n).map fun j ↦ .n (k + j)

/-- `x^e` by the compiler's square-and-multiply from `acc = x` over the digits after the leading
one, from `k`: the statements and the result. -/
def osPowSteps (x : ℕ) : List Bool → ℕ → ℕ → List Stmt × ℕ
  | [], acc, _ => ([], acc)
  | d :: ds, acc, k =>
    if d then
      let r := osPowSteps x ds (k + 1) (k + 2)
      (.atom (.mul (.n k) (.n acc) (.n acc)) :: .atom (.mul (.n (k + 1)) (.n k) (.n x)) :: r.1, r.2)
    else
      let r := osPowSteps x ds k (k + 1)
      (.atom (.mul (.n k) (.n acc) (.n acc)) :: r.1, r.2)

/-- The binary digits of `e` after its leading one, most significant first. -/
def osPowDigits (e : ℕ) : List Bool := (Nat.bits e).reverse.tail

/-- The values `osPowSteps` takes for `e`'s digits. -/
def osPowLen (e : ℕ) : ℕ := (osPowDigits e).length + ((osPowDigits e).filter id).length

/-- The `mul_range` loop's tail (`x·g ≠ N`: call the loop at `x·g`), from `k`, for a helper of
`n` parameters, the first the counter and the second the bound. -/
def osLoopTail (name : String) (n k : ℕ) : List Stmt :=
  [.atom (.const (.n k) (word 2 0 0)), .atom (.mul (.n (k + 1)) (.n 0) (.n k)),
    .atom (.add (.n (k + 2)) (.n (k + 1)) (.n 1)), .atom (.const (.n (k + 3)) (word 2 0 0)),
    .atom (.mul (.n (k + 4)) (.n 0) (.n (k + 3))),
    .callIf (.n (k + 2)) name (.n (k + 4) :: (List.range (n - 1)).map fun i ↦ .n (i + 1)),
    .ret []]

/-- A loop's entry `for x in mul_range(1, g^n)`, from `k`: the guard `1 + g^n` at `k + 2`, the
loop called at `[1, g^n] ++ args`. -/
def osLoopCall (name : String) (n : ℕ) (args : List ℕ) (k : ℕ) : List Stmt :=
  [.atom (.const (.n k) (word 1 0 0)), .atom (.const (.n (k + 1)) (gw n)),
    .atom (.add (.n (k + 2)) (.n k) (.n (k + 1))), .atom (.const (.n (k + 3)) (word 1 0 0)),
    .atom (.const (.n (k + 4)) (gw n)),
    .callIf (.n (k + 2)) name (.n (k + 3) :: .n (k + 4) :: args.map V.n)]

/-- The zero run of the sponge's padding (`keccak_pad_run`), allocated at its first use: the
statements, its first cell (`1`; the next four are `0`) and the next free value. -/
def osPad (pad : Option ℕ) (k : ℕ) : List Stmt × ℕ × ℕ :=
  match pad with
  | some p => ([], p, k)
  | none => ([.atom (.const (.n k) (word 1 0 0)), .atom (.const (.n (k + 1)) (word 0 0 0)),
      .atom (.const (.n (k + 2)) (word 0 0 0)), .atom (.const (.n (k + 3)) (word 0 0 0)),
      .atom (.const (.n (k + 4)) (word 0 0 0))], k, k + 5)

/-- A squeeze with nothing waiting (`squeeze(sp, no_rate, 0)`) on the five capacity values `cap`,
the zero run at `p`, from `k`: the permutation's outputs `k .. k + 12`, the challenge `k + 19`. -/
def osSqueeze0 (p : ℕ) (cap : List ℕ) (k : ℕ) : List Stmt :=
  keccakA (([p + 1, p + 1, p + 1, p + 1, p + 1, p + 2, p + 3, p + 4] ++ cap).map V.n)
      (osRun k 13) :: challengeT (.n k) (.n (k + 1)) (k + 13)

/-- `residual_query(chain, row_d, vanish, n_cols)` (G:1265-1273) inline, the position at `pos`,
the row's `d` words at `bd·g^row`, from `k`: the product `Π_t (d_t + chain_t)`, the chain from
the position by `chain ← chain·(chain + v)` over the vanishing values from `vo`. The statements,
the product's value and the next free value. -/
def osResQ (pos bd row vo : ℕ) : ℕ → ℕ → ℕ → ℕ → List Stmt × ℕ × ℕ
  | 0, _, pe, k => ([], pe, k)
  | n + 1, t, pe, k =>
    let ch := if t = 1 then pos else k - 4
    let r := osResQ pos bd row vo n (t + 1) (k + 5) (k + 6)
    ([.atom (.const (.n k) (word (vanishVal (vo + t - 1)) 0 0)), .atom (.add (.n (k + 1)) (.n ch) (.n k)),
      .atom (.mul (.n (k + 2)) (.n ch) (.n (k + 1))), .atom (.load (.n (k + 3)) (.n bd) (row + t)),
      .atom (.add (.n (k + 4)) (.n (k + 3)) (.n (k + 2))),
      .atom (.mul (.n (k + 5)) (.n pe) (.n (k + 4)))] ++ r.1, r.2)

/-- The whole inline `residual_query` from `k` over `ncols` coordinates: `d_0 + pos` at `k + 1`,
then the steps. -/
def osResQuery (pos bd row vo ncols k : ℕ) : List Stmt × ℕ × ℕ :=
  let r := osResQ pos bd row vo (ncols - 1) 1 (k + 1) (k + 2)
  ([.atom (.load (.n k) (.n bd) row), .atom (.add (.n (k + 1)) (.n k) (.n pos))] ++ r.1, r.2)

/-! ## The running state -/

/-- The values the body carries between its blocks. -/
structure OsSt where
  /-- The next free value. -/
  k : ℕ
  /-- The sponge's five capacity cells. -/
  fs : List ℕ
  /-- The two scalars waiting in the sponge. -/
  w0 : ℕ
  w1 : ℕ
  /-- The cursor: a base value and a word offset. -/
  cb : ℕ
  co : ℕ
  /-- The running quadratic's coefficients and the running claim. -/
  c : ℕ
  b : ℕ
  a : ℕ
  t : ℕ
  /-- The zero run, once allocated. -/
  pad : Option ℕ
  deriving Repr, Inhabited

/-- The fixed buffers' pointers, allocated by the head: `merkle_caps`, `cap_flags`, `final_msg`,
`level_roots`, `fold_challenges`, `level_betas`, `query_weights`, `query_positions`,
`query_bit_ptrs`, `ood_z`, `ood`. -/
abbrev osCaps : ℕ := 13
abbrev osFlags : ℕ := 15
abbrev osFmsg : ℕ := 17
abbrev osRoots : ℕ := 19
abbrev osFch : ℕ := 21
abbrev osBetas : ℕ := 23
abbrev osQw : ℕ := 25
abbrev osQpos : ℕ := 27
abbrev osQbp : ℕ := 29
abbrev osOodz : ℕ := 31
abbrev osOod : ℕ := 33

/-! ## The head and the levels -/

/-- The head (G:1294-1335): the first quadratic read (`c` at `9`, `a` at `10`, `b = target + a` at
`11`), the fixed buffers, the commitment's root into `level_roots`. -/
def osHead (c : OsCfg) : List Stmt × OsSt :=
  let n := c.levels.length
  ([.atom (.load (.n 9) (.n 8) 0), .atom (.load (.n 10) (.n 8) 1), .atom (.add (.n 11) (.n 5) (.n 10))] ++
    osHeap (4 * c.capLen) 12 ++
    [.atom (.hint (.witness "merkle_caps" (.heap (.n osCaps) 0 (4 * c.capLen))))] ++
    osHeap c.capLen 14 ++
    [.atom (.hint (.witness "merkle_cap_active" (.heap (.n osFlags) 0 c.capLen)))] ++
    osHeap c.yrLen 16 ++ osHeap (2 * n) 18 ++
    [.atom (.load (.n 6) (.n osRoots) 0), .atom (.load (.n 7) (.n osRoots) 1)] ++
    osHeap c.nFolds 20 ++ osHeap n 22 ++ osHeap (n * c.maxQ) 24 ++ osHeap c.posLen 26 ++
    osHeap c.posLen 28 ++ osHeap (n * ligColsCap) 30 ++ osHeap (n * oodSlots) 32,
   ⟨34, [0, 1, 2, 3, 4], 9, 10, 8, 2, 9, 11, 10, 5, none⟩)

/-- One sumcheck round (`opening_fold`, G:1096), its challenge stored at `p·g^off`: the cursor
materialized, the call, the store, `b = claim + a`. -/
def osFold (p off : ℕ) (s : OsSt) : List Stmt × OsSt :=
  let m := osMat s.cb s.co s.k
  let r := m.2.2
  (m.1 ++ [.call "opening_fold" ((s.fs ++ [s.w0, s.w1, m.2.1, s.c, s.b, s.a]).map V.n) (osRun r 10),
    .atom (.load (.n (r + 9)) (.n p) off), .atom (.add (.n (r + 10)) (.n (r + 6)) (.n (r + 8)))],
   { s with k := r + 11, fs := [r, r + 1, r + 2, r + 3, r + 4], cb := r + 5, co := 0, t := r + 6,
            c := r + 7, a := r + 8, w0 := r + 7, w1 := r + 8, b := r + 10 })

/-- `n` rounds, the challenges stored from `p·g^off`. -/
def osFolds (p : ℕ) : ℕ → ℕ → OsSt → List Stmt × OsSt
  | _, 0, s => ([], s)
  | off, n + 1, s =>
    let r := osFold p off s
    let t := osFolds p (off + 1) n r.2
    (r.1 ++ t.1, t.2)

/-- The final level's message (`opening_final_message`, G:1340): the call, the sponge after the
nonce's permutation; its first cell (the grinding word) and the nonce. -/
def osFinal (c : OsCfg) (s : OsSt) : List Stmt × OsSt × ℕ :=
  let m := osMat s.cb s.co s.k
  let r := m.2.2
  (m.1 ++ [.call ("opening_final_message__L" ++ natStr c.yrLen)
      ((s.fs ++ [s.w0, s.w1, m.2.1, osFmsg]).map V.n) (osRun r 8)],
   { s with k := r + 8, fs := [r + 1, r + 2, r + 3, r + 4, r + 5], cb := r + 6, co := 0 }, r)

/-- A level's next commitment (G:1342-1386): the capacity copied (`fs_cap`), the waiting scalars
packed, the root's two halves read, checked canonical and stored, the out-of-domain point
(`opening_ood_point`), its value and intro message read and stored in `ood`, the nonce read and
absorbed with them (`fs_absorb_nonce`): the permutation's first cell (the grinding word) and its
capacity. -/
def osCommit (lvl : ℕ) (lv : OsLv) (s : OsSt) : List Stmt × OsSt × ℕ :=
  let k := s.k
  let sb := (lvl + 1) * oodSlots
  ((s.fs.zipIdx.map fun (f, i) ↦ .atom (.copy (.n (k + i)) (.n f))) ++
    fsPackT (.n s.w0) (k + 5) 1 ++ fsPackT (.n s.w1) (k + 14) 1 ++
    fsNextT (.n s.cb) s.co (k + 23) ++ fsNextT (.n s.cb) (s.co + 1) (k + 33) ++
    [.call "assert_canonical" [.n (k + 23)] [.n (k + 43)],
      .call "assert_canonical" [.n (k + 33)] [.n (k + 44)],
      .atom (.load (.n (k + 23)) (.n osRoots) (2 * lvl + 2)),
      .atom (.load (.n (k + 33)) (.n osRoots) (2 * lvl + 3)),
      .atom (.const (.n (k + 45)) (gw ((lvl + 1) * ligColsCap))),
      .atom (.mul (.n (k + 46)) (.n osOodz) (.n (k + 45))),
      .call ("opening_ood_point__L" ++ natStr lv.logCols)
        ((s.fs ++ [k + 11, k + 13, k + 20, k + 22, k + 30, k + 32, k + 40, k + 42, k + 46]).map V.n)
        (osRun (k + 47) 5)] ++
    fsNextT (.n s.cb) (s.co + 2) (k + 52) ++ fsNextT (.n s.cb) (s.co + 3) (k + 62) ++
    fsNextT (.n s.cb) (s.co + 4) (k + 72) ++
    [.atom (.load (.n (k + 52)) (.n osOod) (sb + 1)), .atom (.load (.n (k + 62)) (.n osOod) (sb + 2)),
      .atom (.load (.n (k + 72)) (.n osOod) (sb + 3)), .atom (.load (.n (k + 82)) (.n s.cb) (s.co + 5))] ++
    ((List.range 5).map fun i ↦ .atom (.copy (.n (k + 83 + i)) (.n (k + 47 + i)))) ++
    fsPackT (.n (k + 82)) (k + 88) 4 ++
    [keccakA ([k + 59, k + 61, k + 69, k + 71, k + 79, k + 81, k + 94, k + 96, k + 83, k + 84, k + 85,
      k + 86, k + 87].map V.n) (osRun (k + 97) 13)],
   { s with k := k + 110, fs := [k + 105, k + 106, k + 107, k + 108, k + 109], co := s.co + 6 }, k + 97)

/-- The query positions (G:1407-1435): the squeeze run `sqz`, the capacity stored in it, the loop
of `squeezes` squeezes decoding the positions, the last capacity loaded, and the batching
challenge `lam` squeezed from it (at the returned `k - 1`); its capacity becomes the sponge's. -/
def osSqueezes (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) : List Stmt × OsSt :=
  let k := s.k
  let pd := osPad s.pad (k + 14)
  let j := pd.2.2
  (osHeap ((c.maxSq + 1) * 5) k ++
    (s.fs.zipIdx.map fun (f, i) ↦ .atom (.load (.n f) (.n (k + 1)) i)) ++
    osLoopCall (c.sqLoop lvl) lv.squeezes [k + 1, osQpos, osQbp] (k + 2) ++
    [.atom (.const (.n (k + 7)) (gw (lv.squeezes * 5))), .atom (.mul (.n (k + 8)) (.n (k + 1)) (.n (k + 7)))] ++
    ((List.range 5).map fun i ↦ .atom (.load (.n (k + 9 + i)) (.n (k + 8)) i)) ++
    pd.1 ++ osSqueeze0 pd.2.1 [k + 9, k + 10, k + 11, k + 12, k + 13] j,
   { s with k := j + 20, fs := [j + 8, j + 9, j + 10, j + 11, j + 12], pad := some pd.2.1 })

/-- The query weights `qw[base + i] = lam^i`, `i < q` (G:1443-1446), from `k`: `1` at `k`, then
`lam^i` at `k + i - 1`, `2 ≤ i ≤ q`; `lam^q` (the last) is not stored. -/
def osLamPows (lam base k : ℕ) : ℕ → List Stmt
  | 0 => []
  | q + 1 =>
    [.atom (.const (.n k) (word 1 0 0)), .atom (.load (.n k) (.n osQw) base)] ++
      (if q = 0 then [] else
        .atom (.load (.n lam) (.n osQw) (base + 1)) :: .atom (.mul (.n (k + 1)) (.n lam) (.n lam)) ::
        ((List.range (q - 1)).map fun i ↦
          [.atom (.load (.n (k + 1 + i)) (.n osQw) (base + 2 + i)),
            .atom (.mul (.n (k + 2 + i)) (.n (k + 1 + i)) (.n lam))]).flatten)

/-- The name of a level's `opening_queries` specialization. -/
def osQueriesName (lvl : ℕ) (lv : OsLv) : String :=
  let base := if lvl = 0 then 1 else 0
  "opening_queries__L" ++ natStr (lv.queries % 2 * base) ++ "_L" ++ natStr base ++ "_L" ++
    natStr lv.interleave ++ "_L" ++ natStr lv.leafCells ++ "_L" ++ natStr lv.depth ++ "_L" ++
    natStr lv.capDepth

/-- The level's queries (G:1447-1469), from `k`, after the weights: the row weights, the cap's
root (into `level_roots`), the queries' sum, the intro message's two words and its linear
coefficient. The statements, the next free value, and the values of the sum and of `c0`, `c1`,
`c2`. -/
def osQueries (c : OsCfg) (lvl : ℕ) (lv : OsLv) (lam lamN : ℕ) (s : OsSt) :
    List Stmt × ℕ × ℕ × ℕ × ℕ × ℕ :=
  let k := s.k
  let fp := osMat osFch lv.foldsOff (k + 2)
  let cp := osMat osCaps (4 * lv.capOff) fp.2.2
  let flp := osMat osFlags lv.capOff cp.2.2
  let r := flp.2.2
  let cp2 := osMat osCaps (4 * lv.capOff) (r + 2)
  let flp2 := osMat osFlags lv.capOff cp2.2.2
  let bp := osMat osQbp lv.posOff flp2.2.2
  let g := bp.2.2
  (osHeap c.maxIl k ++ fp.1 ++
    [.call ("opening_row_weights__L" ++ natStr lv.folds ++ "_L" ++ natStr (if lvl = 0 then 1 else 0))
      [.n fp.2.1, .n (k + 1)] []] ++
    cp.1 ++ flp.1 ++
    [.call ("verify_merkle_cap__L" ++ natStr lv.capDepth) [.n cp.2.1, .n flp.2.1] [.n r, .n (r + 1)],
      .atom (.load (.n r) (.n osRoots) (2 * lvl)), .atom (.load (.n (r + 1)) (.n osRoots) (2 * lvl + 1))] ++
    cp2.1 ++ flp2.1 ++ bp.1 ++
    [.atom (.const (.n g) (gw (lv.queries / (1 + if lvl = 0 then 1 else 0)))),
      .call (osQueriesName lvl lv) [.n cp2.2.1, .n flp2.2.1, .n lam, .n lamN, .n bp.2.1, .n (k + 1), .n g]
        [.n (g + 1)],
      .atom (.load (.n (g + 2)) (.n s.cb) s.co), .atom (.load (.n (g + 3)) (.n s.cb) (s.co + 1)),
      .atom (.add (.n (g + 4)) (.n (g + 1)) (.n (g + 3)))],
   g + 5, g + 1, g + 2, g + 4, g + 3)

/-- A level's out-of-domain claim glued with the scalar `lam` (G:1479-1489), from `k`: its value
and intro reread from `ood`, the scalar stored, the running sums updated; the next scalar
`lam²` at `k + 12`. -/
def osOodGlue (lvl lam : ℕ) (s : OsSt) : List Stmt × OsSt :=
  let k := s.k
  let sb := (lvl + 1) * oodSlots
  ([.atom (.load (.n k) (.n osOod) (sb + 1)), .atom (.load (.n (k + 1)) (.n osOod) (sb + 3)),
    .atom (.load (.n lam) (.n osOod) sb), .atom (.load (.n (k + 2)) (.n osOod) (sb + 2)),
    .atom (.mul (.n (k + 3)) (.n lam) (.n (k + 2))), .atom (.add (.n (k + 4)) (.n s.c) (.n (k + 3))),
    .atom (.add (.n (k + 5)) (.n k) (.n (k + 1))), .atom (.mul (.n (k + 6)) (.n lam) (.n (k + 5))),
    .atom (.add (.n (k + 7)) (.n s.b) (.n (k + 6))), .atom (.mul (.n (k + 8)) (.n lam) (.n (k + 1))),
    .atom (.add (.n (k + 9)) (.n s.a) (.n (k + 8))), .atom (.mul (.n (k + 10)) (.n lam) (.n k)),
    .atom (.add (.n (k + 11)) (.n s.t) (.n (k + 10))), .atom (.mul (.n (k + 12)) (.n lam) (.n lam))],
   { s with k := k + 13, c := k + 4, b := k + 7, a := k + 9, t := k + 11 })

/-- The level's batch glued with the scalar `beta` (G:1491-1495), from `k`: the intro `c0, c1, c2`
and the queries' sum `v`. -/
def osGlue (beta v c0 c1 c2 : ℕ) (s : OsSt) : List Stmt × OsSt :=
  let k := s.k
  ([.atom (.mul (.n k) (.n beta) (.n c0)), .atom (.add (.n (k + 1)) (.n s.c) (.n k)),
    .atom (.mul (.n (k + 2)) (.n beta) (.n c1)), .atom (.add (.n (k + 3)) (.n s.b) (.n (k + 2))),
    .atom (.mul (.n (k + 4)) (.n beta) (.n c2)), .atom (.add (.n (k + 5)) (.n s.a) (.n (k + 4))),
    .atom (.mul (.n (k + 6)) (.n beta) (.n v)), .atom (.add (.n (k + 7)) (.n s.t) (.n (k + 6)))],
   { s with k := k + 8, c := k + 1, b := k + 3, a := k + 5, t := k + 7 })

/-- One level (G:1336-1495). -/
def osLevel (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) : List Stmt × OsSt :=
  let f := osFolds osFch lv.foldsOff lv.folds s
  let m := if lvl = c.yrLevel then osFinal c f.2 else osCommit lvl lv f.2
  let gr : List Stmt := [.call ("grind_check__L" ++ natStr lv.grind) [.n m.2.2] []]
  let sq := osSqueezes c lvl lv m.2.1
  let lam := sq.2.k - 1
  let lp := osLamPows lam (lvl * c.maxQ) sq.2.k lv.queries
  let lamN := if lv.queries ≤ 1 then lam else sq.2.k + lv.queries - 1
  let q := osQueries c lvl lv lam lamN { sq.2 with k := sq.2.k + lv.queries }
  let s1 : OsSt := { sq.2 with k := q.2.1, w0 := q.2.2.2.1, w1 := q.2.2.2.2.2,
                               co := sq.2.co + 2 }
  let o := if lvl = c.yrLevel then (([] : List Stmt), s1, lam) else
    let g := osOodGlue lvl lam s1
    (g.1, g.2, s1.k + 12)
  let beta := o.2.2
  let gl := osGlue beta q.2.2.1 q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2 o.2.1
  (f.1 ++ m.1 ++ gr ++ sq.1 ++ lp ++ q.1 ++ o.1 ++ [.atom (.load (.n beta) (.n osBetas) lvl)] ++ gl.1,
   gl.2)

/-- The levels `lvl ..`. -/
def osLevels (c : OsCfg) : ℕ → List OsLv → OsSt → List Stmt × OsSt
  | _, [], s => ([], s)
  | lvl, lv :: rest, s =>
    let r := osLevel c lvl lv s
    let t := osLevels c (lvl + 1) rest r.2
    (r.1 ++ t.1, t.2)

/-! ## The tail and the rest -/

/-- The tail rounds (G:1497-1515) into `tail_challenges` (`HeapBuf(g^5)` at `k + 1`): `yrLog - 1`
rounds, the closing squeeze on the two waiting scalars, its challenge stored, the final claim, the
unused entries zeroed. The statements, the state (its claim `t`) and the buffer. -/
def osTail (c : OsCfg) (s : OsSt) : List Stmt × OsSt × ℕ :=
  let tch := s.k + 1
  let f := osFolds tch 0 (c.yrLog - 1) { s with k := s.k + 2 }
  let j := f.2.k
  let p := (f.2.pad.getD 0)
  (osHeap yrLogCap s.k ++ f.1 ++
    (f.2.fs.zipIdx.map fun (x, i) ↦ .atom (.copy (.n (j + i)) (.n x))) ++
    fsPackT (.n f.2.w0) (j + 5) 1 ++ fsPackT (.n f.2.w1) (j + 14) 1 ++
    keccakA ([j + 11, j + 13, j + 20, j + 22, p + 1, p + 2, p + 3, p + 4, j, j + 1, j + 2, j + 3,
      j + 4].map V.n) (osRun (j + 23) 13) ::
    challengeT (.n (j + 23)) (.n (j + 24)) (j + 36) ++
    [.atom (.load (.n (j + 42)) (.n tch) (c.yrLog - 1)),
      .atom (.mul (.n (j + 43)) (.n (j + 42)) (.n f.2.b)), .atom (.add (.n (j + 44)) (.n f.2.c) (.n (j + 43))),
      .atom (.mul (.n (j + 45)) (.n (j + 42)) (.n (j + 42))),
      .atom (.mul (.n (j + 46)) (.n (j + 45)) (.n f.2.a)),
      .atom (.add (.n (j + 47)) (.n (j + 44)) (.n (j + 46)))] ++
    ((List.range (yrLogCap - c.yrLog)).map fun i ↦
      [.atom (.const (.n (j + 48 + i)) (word 0 0 0)),
        .atom (.load (.n (j + 48 + i)) (.n tch) (c.yrLog + i))]).flatten,
   { f.2 with k := j + 48 + (yrLogCap - c.yrLog), t := j + 47 }, tch)

/-- The source of entry `i` of the rotated point (G:1522-1536): the fold challenges past the lane
folds, the tail challenges, the lane folds; then zeros. -/
def osPtSrc (c : OsCfg) (tch i : ℕ) : Option (ℕ × ℕ) :=
  let lane := (c.levels.headD default).folds
  if i < c.nFolds - lane then some (osFch, lane + i)
  else if i < c.nFolds - lane + c.yrLog then some (tch, i - (c.nFolds - lane))
  else if i < c.nFolds + c.yrLog then some (osFch, i - (c.nFolds - lane) - c.yrLog)
  else none

/-- Entry `i` of the point at `pt` and of `point1` at `pt1`, from `k`; the next free value. -/
def osPtBlk (pt pt1 i k : ℕ) : Option (ℕ × ℕ) → List Stmt × ℕ
  | some (b, o) =>
    ([.atom (.load (.n k) (.n b) o), .atom (.load (.n k) (.n pt) i),
      .atom (.const (.n (k + 1)) (word 1 0 0)), .atom (.load (.n (k + 2)) (.n b) o),
      .atom (.add (.n (k + 3)) (.n (k + 1)) (.n (k + 2))), .atom (.load (.n (k + 3)) (.n pt1) i)], k + 4)
  | none =>
    ([.atom (.const (.n k) (word 0 0 0)), .atom (.load (.n k) (.n pt) i),
      .atom (.const (.n (k + 1)) (word 1 0 0)), .atom (.load (.n (k + 1)) (.n pt1) i)], k + 2)

/-- The entries `i ..` of the point, from `k`. -/
def osPtBlks (c : OsCfg) (pt pt1 tch : ℕ) : ℕ → ℕ → ℕ → List Stmt × ℕ
  | _, 0, k => ([], k)
  | i, n + 1, k =>
    let r := osPtBlk pt pt1 i k (osPtSrc c tch i)
    let t := osPtBlks c pt pt1 tch (i + 1) n r.2
    (r.1 ++ t.1, t.2)

/-- One coordinate of a level's basis row (G:1554-1560): the challenge at `src`, its coefficient
`b = c·inv` (`c` itself when `inv = 1`), `d = (1 + c)/b` stored at `basis_d[slot]`, the scale
times `b`; from `k`, the scale `sc`. The statements, the new scale and the next free value. -/
def osBasisBlk (bd slot : ℕ) (src : ℕ × ℕ) (inv sc k : ℕ) : List Stmt × ℕ × ℕ :=
  if inv = 1 then
    ([.atom (.load (.n k) (.n src.1) src.2), .atom (.const (.n (k + 1)) (word 1 0 0)),
      .atom (.add (.n (k + 2)) (.n (k + 1)) (.n k)), .atom (.mul (.n (k + 2)) (.n (k + 3)) (.n k)),
      .atom (.load (.n (k + 3)) (.n bd) slot), .atom (.mul (.n (k + 4)) (.n sc) (.n k))], k + 4, k + 5)
  else
    ([.atom (.load (.n k) (.n src.1) src.2), .atom (.const (.n (k + 1)) (word inv 0 0)),
      .atom (.mul (.n (k + 2)) (.n k) (.n (k + 1))), .atom (.const (.n (k + 3)) (word 1 0 0)),
      .atom (.add (.n (k + 4)) (.n (k + 3)) (.n k)), .atom (.mul (.n (k + 4)) (.n (k + 5)) (.n (k + 2))),
      .atom (.load (.n (k + 5)) (.n bd) slot), .atom (.mul (.n (k + 6)) (.n sc) (.n (k + 2)))], k + 6, k + 7)

/-- A level's basis coordinates `(slot, source, inverse)`: the fold challenges after its folds,
then the tail challenges. -/
def osBasisCoords (c : OsCfg) (tch lvl : ℕ) (lv : OsLv) : List (ℕ × (ℕ × ℕ) × ℕ) :=
  (List.range (lv.prefixLen + c.yrLog)).map fun t ↦
    (lvl * ligColsCap + t,
      (if t < lv.prefixLen then (osFch, lv.resFoldOff + t) else (tch, t - lv.prefixLen)),
      vanishInv (lv.vanish + t))

/-- The coordinates of a basis row from the scale `sc` and `k`: the statements, the final scale and
the next free value. -/
def osBasisRow (bd : ℕ) : List (ℕ × (ℕ × ℕ) × ℕ) → ℕ → ℕ → List Stmt × ℕ × ℕ
  | [], sc, k => ([], sc, k)
  | (slot, src, inv) :: rest, sc, k =>
    let r := osBasisBlk bd slot src inv sc k
    let t := osBasisRow bd rest r.2.1 r.2.2
    (r.1 ++ t.1, t.2)

/-- Every level's basis row and its scale (G:1548-1567), from `k`. -/
def osBases (c : OsCfg) (tch bd ls : ℕ) : ℕ → List OsLv → ℕ → List Stmt × ℕ
  | _, [], k => ([], k)
  | lvl, lv :: rest, k =>
    let r := osBasisRow bd (osBasisCoords c tch lvl lv) k (k + 1)
    let t := osBases c tch bd ls (lvl + 1) rest r.2.2
    (.atom (.load (.n k) (.n osBetas) lvl) :: r.1 ++ [.atom (.load (.n r.2.1) (.n ls) lvl)] ++ t.1, t.2)

/-- Level `lvl`'s residual sum (G:1568-1591), from `k`: its chain's buffer, the loop over its
query pairs, the last query of an odd count inline, `inner[lvl + 1] = inner[lvl] + scale·sum`. -/
def osResidual (c : OsCfg) (ich bd ls lvl : ℕ) (lv : OsLv) (k : ℕ) : List Stmt × ℕ :=
  let ev : List Stmt × ℕ × ℕ :=
    if lv.queries % 2 = 1 then
      let r := osResQuery (k + 9) bd (lvl * ligColsCap) lv.vanish lv.logCols (k + 10)
      ([.atom (.load (.n (k + 9)) (.n osQpos) (lv.posOff + lv.queries - 1))] ++ r.1 ++
        [.atom (.load (.n r.2.2) (.n osQw) (lvl * c.maxQ + lv.queries - 1)),
          .atom (.mul (.n (r.2.2 + 1)) (.n r.2.2) (.n r.2.1)),
          .atom (.add (.n (r.2.2 + 2)) (.n (k + 8)) (.n (r.2.2 + 1)))], r.2.2 + 2, r.2.2 + 3)
    else ([], k + 8, k + 9)
  let e := ev.2.2
  (osHeap (c.maxQ + 1) k ++
    [.atom (.const (.n (k + 2)) (word 0 0 0)), .atom (.load (.n (k + 2)) (.n (k + 1)) 0)] ++
    osLoopCall (c.resLoop lvl) (lv.queries / 2) [osQpos, osQw, bd, k + 1] (k + 3) ++
    [.atom (.load (.n (k + 8)) (.n (k + 1)) (lv.queries / 2))] ++ ev.1 ++
    [.atom (.load (.n e) (.n ich) lvl), .atom (.load (.n (e + 1)) (.n ls) lvl),
      .atom (.mul (.n (e + 2)) (.n (e + 1)) (.n ev.2.1)), .atom (.add (.n (e + 3)) (.n e) (.n (e + 2))),
      .atom (.load (.n (e + 3)) (.n ich) (lvl + 1))], e + 4)

/-- Every level's residual sum, from `k`. -/
def osResiduals (c : OsCfg) (ich bd ls : ℕ) : ℕ → List OsLv → ℕ → List Stmt × ℕ
  | _, [], k => ([], k)
  | lvl, lv :: rest, k =>
    let r := osResidual c ich bd ls lvl lv k
    let t := osResiduals c ich bd ls (lvl + 1) rest r.2
    (r.1 ++ t.1, t.2)

/-- The factors of an out-of-domain weight (G:1599-1604) over the coordinates `(z slot, source)`,
from the scalar `sc` at `k`: each `sc ← sc·(1 + z + c)`. The statements, the weight and the next
free value. -/
def osOodFacs (sc : ℕ) : List (ℕ × ℕ × ℕ) → ℕ → List Stmt × ℕ × ℕ
  | [], k => ([], sc, k)
  | (zo, src) :: rest, k =>
    let r := osOodFacs (k + 5) rest (k + 6)
    ([.atom (.const (.n k) (word 1 0 0)), .atom (.load (.n (k + 1)) (.n osOodz) zo),
      .atom (.add (.n (k + 2)) (.n k) (.n (k + 1))), .atom (.load (.n (k + 3)) (.n src.1) src.2),
      .atom (.add (.n (k + 4)) (.n (k + 2)) (.n (k + 3))), .atom (.mul (.n (k + 5)) (.n sc) (.n (k + 4)))] ++
      r.1, r.2)

/-- The out-of-domain weight of the commitment level `ol` reads, its sample `0` (G:1596-1605),
after `prevCols` message coordinates, from `k`: the scalar, then the factors. -/
def osOodWeight (c : OsCfg) (tch prevCols ol : ℕ) (lv : OsLv) (k : ℕ) : List Stmt × ℕ × ℕ :=
  let zf := prevCols - c.yrLog
  let r := osOodFacs k ((List.range (zf + c.yrLog)).map fun t ↦
    (ol * ligColsCap + t, if t < zf then (osFch, lv.foldsOff + t) else (tch, t - zf))) (k + 1)
  (.atom (.load (.n k) (.n osOod) (ol * oodSlots)) :: r.1, r.2)

/-- The out-of-domain weights of the levels `ol ..` (each with one sample), summed into `acc`, from
`k`: the statements, the sum and the next free value. -/
def osOodWeights (c : OsCfg) (tch : ℕ) :
    ℕ → ℕ → List OsLv → Option ℕ → ℕ → List Stmt × Option ℕ × ℕ
  | _, _, [], acc, k => ([], acc, k)
  | prevCols, ol, lv :: rest, acc, k =>
    let w := osOodWeight c tch prevCols ol lv k
    let a : List Stmt × Option ℕ × ℕ := match acc with
      | none => ([], some w.2.1, w.2.2)
      | some x => ([.atom (.add (.n w.2.2) (.n x) (.n w.2.1))], some w.2.2, w.2.2 + 1)
    let t := osOodWeights c tch lv.logCols (ol + 1) rest a.2.1 a.2.2
    (w.1 ++ a.1 ++ t.1, t.2)

/-- The body after the tail (G:1516-1606), from the tail's state `st` and `tail_challenges` at
`tch`: the residual's value, the point, the basis rows, the residual sums, the out-of-domain
weights, the returns. -/
def osFinish (c : OsCfg) (st : OsSt) (tch : ℕ) : List Stmt :=
  let n := c.levels.length
  let yat := st.k
  let pt := yat + 1
  let pts := osPtBlks c pt (pt + 1) tch 0 pointCap (pt + 2)
  let bd := pts.2 + 1
  let ls := pts.2 + 3
  let bs := osBases c tch bd ls 0 c.levels (pts.2 + 4)
  let ich := bs.2 + 1
  let rs := osResiduals c ich bd ls 0 c.levels (bs.2 + 3)
  let od := osOodWeights c tch ((c.levels.headD default).logCols) 1 c.levels.tail none rs.2
  let k := od.2.2
  [.call ("fold_final_msg__L" ++ natStr c.yrLog) [.n osFmsg, .n tch] [.n yat],
    .atom (.hint (.alloc (.n pt) pointCap)), .atom (.hint (.alloc (.n (pt + 1)) pointCap))] ++
    pts.1 ++ osHeap (n * ligColsCap) pts.2 ++ osHeap n (pts.2 + 2) ++ bs.1 ++
    osHeap (n + 1) bs.2 ++
    [.atom (.const (.n (bs.2 + 2)) (word 0 0 0)), .atom (.load (.n (bs.2 + 2)) (.n ich) 0)] ++
    rs.1 ++ od.1 ++
    [.atom (.copy (.n k) (.n st.t)), .atom (.copy (.n (k + 1)) (.n pt)),
      .atom (.copy (.n (k + 2)) (.n (pt + 1))), .atom (.load (.n (k + 3)) (.n ich) n),
      .atom (.add (.n (k + 4)) (.n (k + 3)) (.n (od.2.1.getD 0))), .atom (.copy (.n (k + 5)) (.n yat)),
      .ret [.n k, .n (k + 1), .n (k + 2), .n (k + 4), .n (k + 5)]]

/-- **The body of `open_stacked` at a configuration.** -/
def osBody (c : OsCfg) : List Stmt :=
  let h := osHead c
  let lv := osLevels c 0 c.levels h.2
  let tl := osTail c lv.2
  h.1 ++ lv.1 ++ tl.1 ++ osFinish c tl.2.1 tl.2.2

/-! ## The loop helpers -/

/-- The squeeze loop's body (G:1421-1433), at `x, N, sqz, qpos, qbp` (values `0 .. 4`): the row
`sqz·x^5`, its capacity loaded, one squeeze, the next capacity stored, the decoded positions and
bit runs at `g^posOff·x^(192/depth)`, then the loop's tail. -/
def sqLoopBody (lv : OsLv) (name : String) : List Stmt :=
  let pw := osPowSteps 0 (osPowDigits (192 / lv.depth)) 0 39
  let p1 := osMat 3 lv.posOff (39 + osPowLen (192 / lv.depth))
  let p2 := osMat 4 lv.posOff (p1.2.2 + 1)
  let e := p2.2.2 + 1
  [.atom (.mul (.n 5) (.n 0) (.n 0)), .atom (.mul (.n 6) (.n 5) (.n 5)), .atom (.mul (.n 7) (.n 6) (.n 0)),
    .atom (.mul (.n 8) (.n 2) (.n 7))] ++
    ((List.range 5).map fun i ↦ .atom (.load (.n (9 + i)) (.n 8) i)) ++
    [.atom (.const (.n 14) (word 1 0 0)), .atom (.const (.n 15) (word 0 0 0)),
      .atom (.const (.n 16) (word 0 0 0)), .atom (.const (.n 17) (word 0 0 0)),
      .atom (.const (.n 18) (word 0 0 0))] ++
    osSqueeze0 14 [9, 10, 11, 12, 13] 19 ++
    ((List.range 5).map fun i ↦ .atom (.load (.n (27 + i)) (.n 8) (5 + i))) ++
    pw.1 ++ p1.1 ++ [.atom (.mul (.n p1.2.2) (.n p1.2.1) (.n pw.2))] ++
    p2.1 ++ [.atom (.mul (.n p2.2.2) (.n p2.2.1) (.n pw.2))] ++
    [.call ("decode_query_bits__L" ++ natStr lv.depth) [.n 38, .n p1.2.2, .n p2.2.2] []] ++
    osLoopTail name 5 e

/-- The residual loop's body (G:1581-1594), at `xr, N, qpos, qw, basis_d, chain` (values `0 .. 5`):
the pair `xr²`, the two positions and weights, their induced products, the chain's next entry,
then the loop's tail. -/
def resLoopBody (c : OsCfg) (lvl : ℕ) (lv : OsLv) (name : String) : List Stmt :=
  let pp := osMat 2 lv.posOff 7
  let wp := osMat 3 (lvl * c.maxQ) (pp.2.2 + 1)
  let k := wp.2.2 + 1
  let e0 := osResQuery k 4 (lvl * ligColsCap) lv.vanish lv.logCols (k + 1)
  let e1 := osResQuery e0.2.2 4 (lvl * ligColsCap) lv.vanish lv.logCols (e0.2.2 + 1)
  let r := e1.2.2
  [.atom (.mul (.n 6) (.n 0) (.n 0))] ++ pp.1 ++ [.atom (.mul (.n pp.2.2) (.n pp.2.1) (.n 6))] ++
    wp.1 ++ [.atom (.mul (.n wp.2.2) (.n wp.2.1) (.n 6))] ++
    [.atom (.load (.n k) (.n pp.2.2) 0)] ++ e0.1 ++
    [.atom (.load (.n e0.2.2) (.n pp.2.2) 1)] ++ e1.1 ++
    [.atom (.mul (.n r) (.n 5) (.n 0)), .atom (.load (.n (r + 1)) (.n r) 0),
      .atom (.load (.n (r + 2)) (.n wp.2.2) 0), .atom (.mul (.n (r + 3)) (.n (r + 2)) (.n e0.2.1)),
      .atom (.add (.n (r + 4)) (.n (r + 1)) (.n (r + 3))), .atom (.load (.n (r + 5)) (.n wp.2.2) 1),
      .atom (.mul (.n (r + 6)) (.n (r + 5)) (.n e1.2.1)), .atom (.add (.n (r + 7)) (.n (r + 4)) (.n (r + 6))),
      .atom (.mul (.n (r + 8)) (.n 5) (.n 0)), .atom (.load (.n (r + 7)) (.n (r + 8)) 1)] ++
    osLoopTail name 6 (r + 9)

end
end LeanVM.Guest.B1.Whir
