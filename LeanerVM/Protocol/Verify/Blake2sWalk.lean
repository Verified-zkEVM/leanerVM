/-
  LeanerVM.Protocol.Verify.Blake2sWalk

  The forward walk of the BLAKE2s circuit at a vector of column weights: the products `A w` and
  `B w` of the circuit's two matrices, computed word by word, and the lincheck terminal on it.
-/

module

public import LeanerVM.Protocol.ToArkLib.Flock.Tables
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

`linTerminalWith rows` is `Flock.linTerminal` with the walk `rows` (`linTerminalWith_rows`), and
the column weights' table built once (`wColWith`).

That `blake2sRows` is the circuit's `rows` is owed: the verifier's Flock check rests on it, and
the Rust proof's acceptance is its test, with the differential `#guard`s of the tests on rows of
each kind.
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters CompPoly CMlPolynomialEval

@[expose] public section

namespace Blake2sWalk

/-- The constant position. -/
abbrev cpos : ℕ := 512

/-- The products of the walk. -/
structure Rows where
  /-- The left products `A w`. -/
  left : Array E
  /-- The right products `B w`. -/
  right : Array E

/-- A word's 32 bits at the weights. -/
abbrev W32 := Array E

variable (w : Array E)

/-- The input word at `base`: its bits' weights. -/
def slots (base : ℕ) : W32 := (Array.range 32).map fun i ↦ w.getD (base + i) 0

/-- A literal word: the constant's weight at its set bits. -/
def literal (v : UInt32) : W32 :=
  (Array.range 32).map fun i ↦ if v.toNat.testBit i then w.getD cpos 0 else 0

/-- XOR of words. -/
def xorW (x y : W32) : W32 := (Array.range 32).map fun i ↦ x.getD i 0 + y.getD i 0

/-- Rotation right. -/
def rotr (x : W32) (n : ℕ) : W32 := (Array.range 32).map fun i ↦ x.getD ((i + n) % 32) 0

/-- `x + y` with its carry gates at `base`: their rows, and the sum's bits. -/
def add (r : Rows) (x y : W32) (base : ℕ) : Rows × W32 := Id.run do
  let mut r := r
  let mut carry : E := 0
  let mut out : W32 := #[]
  for bit in [0:32] do
    if bit < 31 then
      r := ⟨r.left.set! (base + bit) (x.getD bit 0 + carry),
        r.right.set! (base + bit) (y.getD bit 0 + carry)⟩
    out := out.push (x.getD bit 0 + y.getD bit 0 + carry)
    if bit < 31 then carry := carry + w.getD (base + bit) 0
  return (r, out)

/-- `x + y + z` with its 31 majority and 30 ripple gates at `base`: their rows, and the sum's
bits. -/
def add3 (r : Rows) (x y z : W32) (base : ℕ) : Rows × W32 := Id.run do
  let mut r := r
  let mut maj : W32 := #[]
  for bit in [0:31] do
    r := ⟨r.left.set! (base + bit) (x.getD bit 0 + z.getD bit 0),
      r.right.set! (base + bit) (y.getD bit 0 + z.getD bit 0)⟩
    maj := maj.push (w.getD (base + bit) 0 + z.getD bit 0)
  let rb := base + 31
  let mut carry : E := 0
  let mut out : W32 := #[]
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
def mix (r : Rows) (v : Array W32) (a b c d : ℕ) (mx my : W32) (base : ℕ) :
    Rows × Array W32 :=
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
/-- The forward walk of the BLAKE2s circuit at the column weights `w`: `A w` and `B w`
(`blake2s_row_values`, `verifier.py:1167-1298`). -/
def blake2sRows (w : CMlPolynomialEval E (Flock.kSkip + Flock.kIn)) :
    CMlPolynomialEval E (Flock.kSkip + Flock.kIn) × CMlPolynomialEval E (Flock.kSkip + Flock.kIn) :=
  let wa := w.toArray
  let size := 2 ^ (Flock.kSkip + Flock.kIn)
  let wc := wa.getD cpos 0
  Id.run do
    let mut r : Rows := ⟨Array.replicate size 0, Array.replicate size 0⟩
    -- The inputs: the chaining value, the message, the counter and the flags.
    for (base, len) in [(0, 256), (640, 512), (1152, 128)] do
      for row in [base:base + len] do
        r := ⟨r.left.set! row (wa.getD row 0), r.right.set! row wc⟩
    -- The working vector.
    let mut v : Array W32 := Array.replicate 16 #[]
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
    r := ⟨r.left.set! cpos wc, r.right.set! cpos wc⟩
    return (Vector.ofFn fun k ↦ r.left.getD k 0, Vector.ofFn fun k ↦ r.right.getD k 0)

namespace Flock

variable {F : Type} [Field F] {s m : ℕ}

/-- `wCol` with the equality kernel at `p` built once. -/
def wColWith (sv : Vector F (2 ^ s)) (p : Vector F m) : CMlPolynomialEval F (s + m) :=
  let Lp := lagrangeBasis p
  Vector.ofFn fun j ↦ sv[((cubeSplit s m).symm j).1] * Lp[((cubeSplit s m).symm j).2]

theorem wColWith_eq (sv : Vector F (2 ^ s)) (p : Vector F m) : wColWith sv p = wCol sv p := rfl

/-- The lincheck terminal with the circuit's matrices evaluated by the walk `rows`. -/
def linTerminalWith (rows : CMlPolynomialEval F (s + m) →
      CMlPolynomialEval F (s + m) × CMlPolynomialEval F (s + m))
    (nodes : SkipDomain F s) (cpos : Fin (2 ^ (s + m))) (Y : F) (χin : Vector F m) (α : F)
    (p : Vector F m) (sv : Vector F (2 ^ s)) : F :=
  let e := eRow nodes Y χin
  let w := wColWith sv p
  let rw := rows w
  let L := skipWeights nodes Y
  (∑ k : Fin (2 ^ (s + m)), e[k] * rw.1[k]) + α * (∑ k : Fin (2 ^ (s + m)), e[k] * rw.2[k]) +
    α ^ 2 * (eqTilde χin p * ∑ i : Fin (2 ^ s), L[i] * sv[i]) + α ^ 3 * w[cpos]

/-- With the circuit's own walk it is the lincheck terminal. -/
theorem linTerminalWith_rows (C : BlockR1CS F (s + m)) (nodes : SkipDomain F s)
    (cpos : Fin (2 ^ (s + m))) (Y : F) (χin : Vector F m) (α : F) (p : Vector F m)
    (sv : Vector F (2 ^ s)) :
    linTerminalWith C.rows nodes cpos Y χin α p sv = linTerminal nodes C cpos Y χin α p sv :=
  rfl

end Flock

end
end LeanerVM.Protocol
