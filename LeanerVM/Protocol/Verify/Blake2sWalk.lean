/-
  LeanerVM.Protocol.Verify.Blake2sWalk

  The forward walk of the BLAKE2s circuit at a vector of column weights: the products `A w` and
  `B w` of the circuit's two matrices, computed word by word, over any type with `+` and `0`.
-/

module

public import CompPoly.Multilinear.Basic
public import LeanerVM.Parameters.Blake2s
public import LeanerVM.Parameters.Flock

/-!
# The forward walk of the BLAKE2s circuit

Category B: transcribed from the second verifier at leanVM
`a386121f84292f6fa663aaa3e570c15bc0240ea2`, `python-verifier/verifier.py:1167-1298`
(`blake2s_row_values`), itself pinned against the Rust's `forward_walk`
(`crates/flock/src/hash.rs:295-358`). The lincheck's terminal reads the two matrices of the
BLAKE2s circuit only through `A w` and `B w` for one vector `w` of column weights
(`Flock.linTerminal`); the circuit's own block R1CS (`blake2sCircuit.toBlockR1CS`) evaluates them
entry by entry, `2^28` terms a matrix, which no verifier can run. `blake2sRows w` computes both
in one walk of the circuit's words: an input or the constant is its weight, a word is the
vector of its bits' values at `w`, XOR is addition, rotation permutes, and each adder writes its
carry gates' rows, `(x_i + c, y_i + c)` for `x + y` and the majority and ripple rows for
`x + y + z`, with the carry the sum of the earlier gates' weights; the output rows are
`(out bit, w_c)` and the inputs' and the constant's `(w_j, w_c)`, `w_c` the constant's weight.
The layout is `LeanerVM.Protocol.Blake2sCircuit`'s.

The walk is written once over any type with `+` and `0` (`blake2sRowsOf`): at `E` it is
`blake2sRows`, and on GF(2) linear forms over the positions, `+` their XOR and input `j` the form
of position `j`, it returns each row's two forms, the rows of the circuit's matrices as bitsets.

**Unproved target: the walk is the circuit's.** The verifier's Flock check rests on

```
theorem blake2sRows_eq (w : CMlPolynomialEval E (Flock.kSkip + Flock.kIn)) :
    blake2sRows w = (blake2sCircuit.toBlockR1CS E).rows w
```

the forward walk of `LeanerVM.Protocol.Blake2sCircuit`'s block R1CS: row `k` of each side is
the sum of the weights at the set bits of `(blake2sCircuit.rowOf k).a` and `.b`. Both sides are
additive in `w`, so it is the equality of the walk's forms with the gates' forms at every row.
The `leanervm-verify` executable checks that at all `2^14` rows, both forms as bitsets against
`rowOf` (`LeanerVMTests.Protocol.VerifyFlock.walkMismatches`); the tests check the walk at `E`
against the gates at rows of every kind, and the Rust proof's lincheck passes on it. A proof
goes gate by gate, the circuit's construction and the walk visiting the same gates in the same
order.
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters CompPoly CMlPolynomialEval

@[expose] public section

namespace Blake2sWalk

variable {α : Type} [Add α] [Zero α]

variable (α) in
/-- The products of the walk. -/
structure Rows where
  /-- The left products `A w`. -/
  left : Array α
  /-- The right products `B w`. -/
  right : Array α

variable (α) in
/-- A word's 32 bits at the weights. -/
abbrev W32 := Array α

variable (w : Array α)

/-- The weight of the constant position. -/
def constWeight : α := w.getD Flock.constPos.val 0

/-- The input word at `base`: its bits' weights. -/
def slots (base : ℕ) : W32 α := (Array.range 32).map fun i ↦ w.getD (base + i) 0

/-- A literal word: the constant's weight at its set bits. -/
def literal (v : UInt32) : W32 α :=
  (Array.range 32).map fun i ↦ if v.toNat.testBit i then constWeight w else 0

/-- XOR of words. -/
def xorW (x y : W32 α) : W32 α := (Array.range 32).map fun i ↦ x.getD i 0 + y.getD i 0

/-- Rotation right. -/
def rotr (x : W32 α) (n : ℕ) : W32 α := (Array.range 32).map fun i ↦ x.getD ((i + n) % 32) 0

/-- `x + y` with its carry gates at `base`: their rows, and the sum's bits. -/
def add (r : Rows α) (x y : W32 α) (base : ℕ) : Rows α × W32 α := Id.run do
  let mut r := r
  let mut carry : α := 0
  let mut out : W32 α := #[]
  for bit in [0:32] do
    if bit < 31 then
      r := ⟨r.left.set! (base + bit) (x.getD bit 0 + carry),
        r.right.set! (base + bit) (y.getD bit 0 + carry)⟩
    out := out.push (x.getD bit 0 + y.getD bit 0 + carry)
    if bit < 31 then carry := carry + w.getD (base + bit) 0
  return (r, out)

/-- `x + y + z` with its 31 majority and 30 ripple gates at `base`: their rows, and the sum's
bits. -/
def add3 (r : Rows α) (x y z : W32 α) (base : ℕ) : Rows α × W32 α := Id.run do
  let mut r := r
  let mut maj : W32 α := #[]
  for bit in [0:31] do
    r := ⟨r.left.set! (base + bit) (x.getD bit 0 + z.getD bit 0),
      r.right.set! (base + bit) (y.getD bit 0 + z.getD bit 0)⟩
    maj := maj.push (w.getD (base + bit) 0 + z.getD bit 0)
  let rb := base + 31
  let mut carry : α := 0
  let mut out : W32 α := #[]
  for bit in [0:32] do
    let q := if bit = 0 then 0 else maj.getD (bit - 1) 0
    let l := x.getD bit 0 + y.getD bit 0 + z.getD bit 0 + carry
    out := out.push (l + q)
    if 1 ≤ bit ∧ bit ≤ 30 then
      r := ⟨r.left.set! (rb + bit - 1) l, r.right.set! (rb + bit - 1) (q + carry)⟩
      carry := carry + w.getD (rb + bit - 1) 0
  return (r, out)

/-- The mixing function `G` on lanes `a, b, c, d` with the message words `mx, my`, its gates at
`base`. -/
def mix (r : Rows α) (v : Array (W32 α)) (a b c d : ℕ) (mx my : W32 α) (base : ℕ) :
    Rows α × Array (W32 α) :=
  let (r, a1) := add3 w r (v.getD a #[]) (v.getD b #[]) mx base
  let d1 := rotr (xorW (v.getD d #[]) a1) 16
  let (r, c1) := add w r (v.getD c #[]) d1 (base + 61)
  let b1 := rotr (xorW (v.getD b #[]) c1) 12
  let (r, a2) := add3 w r a1 b1 my (base + 92)
  let d2 := rotr (xorW d1 a2) 8
  let (r, c2) := add w r c1 d2 (base + 153)
  let b2 := rotr (xorW b1 c2) 7
  (r, (((v.set! a a2).set! b b2).set! c c2).set! d d2)

/-- The lanes of the eight `G` calls of a round. -/
def gLanes : List (ℕ × ℕ × ℕ × ℕ) :=
  [(0, 4, 8, 12), (1, 5, 9, 13), (2, 6, 10, 14), (3, 7, 11, 15),
    (0, 5, 10, 15), (1, 6, 11, 12), (2, 7, 8, 13), (3, 4, 9, 14)]

end Blake2sWalk

open Blake2sWalk in
/-- The forward walk of the BLAKE2s circuit at the column weights `wa`, over any type with `+`
and `0`: the rows `A w` and `B w` (`blake2s_row_values`, `verifier.py:1167-1298`). -/
def blake2sRowsOf {α : Type} [Add α] [Zero α] (wa : Array α) : Array α × Array α :=
  let size := 2 ^ (Flock.kSkip + Flock.kIn)
  let wc := constWeight wa
  Id.run do
    let mut r : Rows α := ⟨Array.replicate size 0, Array.replicate size 0⟩
    -- The inputs: the chaining value, the message, the counter and the flags.
    for (base, len) in [(0, 256), (640, 512), (1152, 128)] do
      for row in [base:base + len] do
        r := ⟨r.left.set! row (wa.getD row 0), r.right.set! row wc⟩
    -- The working vector.
    let mut v : Array (W32 α) := Array.replicate 16 #[]
    for i in [0:8] do
      v := v.set! i (slots wa (32 * i))
    for i in [0:4] do
      v := v.set! (8 + i) (literal wa iv[i]!)
    for (i, base) in [(0, 1152), (1, 1184), (2, 1216), (3, 1248)] do
      v := v.set! (12 + i) (xorW (literal wa iv[4 + i]!) (slots wa base))
    -- Ten rounds of eight mixing steps, 184 gates each from `1280`.
    for rnd in [0:10] do
      let s := sigma[rnd]!
      for (gi, (a, b, c, d)) in (List.range 8).zip gLanes do
        let base := 1280 + 184 * (8 * rnd + gi)
        let mx := slots wa (640 + 32 * (s[2 * gi]!).val)
        let my := slots wa (640 + 32 * (s[2 * gi + 1]!).val)
        let (r', v') := mix wa r v a b c d mx my base
        r := r'
        v := v'
    -- The output rows `(out bit, w_c)`.
    for i in [0:8] do
      let out := xorW (xorW (v.getD i #[]) (v.getD (i + 8) #[])) (slots wa (32 * i))
      for bit in [0:32] do
        r := ⟨r.left.set! (256 + 32 * i + bit) (out.getD bit 0),
          r.right.set! (256 + 32 * i + bit) wc⟩
    r := ⟨r.left.set! Flock.constPos.val wc, r.right.set! Flock.constPos.val wc⟩
    return (r.left, r.right)

/-- The forward walk of the BLAKE2s circuit at the column weights `w`: `A w` and `B w`. -/
def blake2sRows (w : CMlPolynomialEval E (Flock.kSkip + Flock.kIn)) :
    CMlPolynomialEval E (Flock.kSkip + Flock.kIn) × CMlPolynomialEval E (Flock.kSkip + Flock.kIn) :=
  let r := blake2sRowsOf w.toArray
  (Vector.ofFn fun k ↦ r.1.getD k 0, Vector.ofFn fun k ↦ r.2.getD k 0)

end
end LeanerVM.Protocol
