module

public import Mathlib.Data.Nat.Notation
public import CompPoly.Fields.Binary.BF64.Impl

/-!
# The cost machine

A first-order functional language with prices (the extractor plan's §5). A program is an array of
function bodies; a body reads its arguments and the values it binds by position, calls functions
by index, applies closures, builds and inspects constructors, and runs priced primitive
operations on 64-bit words, natural numbers and arrays. Values are immutable, so sharing one is
free and building one is priced by the words it writes.

`run P fuel x` runs function `0` of `P` on `x`: its value and its price (the sum of the prices of
the steps it takes), or `none` when the run misuses a value (a primitive on the wrong kind of
value, a variable or a field that does not exist, a call of a function `P` lacks) or nests more
than `fuel` calls. A misuse is a failure, never undefined behavior. `outputWithin P x b` is the
value if the price is at most `b`; each call costs at least `1`, so `fuel = b` is never the
bound that fails a run of price at most `b` (`outputWithin_of_runs`, `Cost/Spec.lean`).

**Prices.** Each step costs at least `1` and at least the words it writes:
* a variable, a literal, a field, a `case`'s selection, a `let`: `1`;
* a constructor or a closure of `n` values: `n + 1` (a tag and `n` words);
* a call or a closure's application: `1`;
* a word operation (`+`, `−`, `·` modulo `2^64`, `and`, `or`, `xor`, `not`, shifts, comparisons):
  `1`, each one CPU instruction;
* a `GF(2^64)` multiplication: `256`, the carry-less product by 64 shift-and-xor steps of four
  operations each, and its reduction;
* an operation on natural numbers of at most `m` and `m'` limbs of 64 bits: `max m m' + 1` for
  `+`, `−`, comparisons and bitwise operations, `m·m' + 1` for `·`, `/` and `%` (schoolbook), and
  the limbs written plus one for shifts;
* arrays: the size or an entry `1`; a new array of `n` entries (from a list, a slice, an append, a
  copy with one entry set or appended, a replicate) `n + 1`, and a list of `n` cells from an array
  `3·n + 1`.
-/

namespace LeanVM.Cost

@[expose] public section

/-- The machine's values. -/
inductive Val where
  /-- A 64-bit word. -/
  | word (x : UInt64)
  /-- A natural number, of any size. -/
  | nat (n : ℕ)
  /-- A constructor: its tag and its fields. -/
  | ctor (tag : ℕ) (fields : List Val)
  /-- An array. -/
  | arr (xs : Array Val)
  /-- A closure: function `f` with its first arguments. -/
  | fn (f : ℕ) (args : List Val)
  deriving Inhabited, BEq, Repr

/-- `false` and `true`: the constructors of tags `0` and `1`. -/
def Val.ofBool (b : Bool) : Val := .ctor (if b then 1 else 0) []

/-- A list: `nil` the constructor of tag `0`, `cons` of tag `1`. -/
def Val.ofList : List Val → Val
  | [] => .ctor 0 []
  | x :: xs => .ctor 1 [x, Val.ofList xs]

/-- The elements of a list value. -/
def Val.toList? : Val → Option (List Val)
  | .ctor 0 [] => some []
  | .ctor 1 [x, xs] => (Val.toList? xs).map (x :: ·)
  | _ => none

/-- The limbs of 64 bits of a natural number, at least one. -/
def limbs (n : ℕ) : ℕ := n.log2 / 64 + 1

/-- `GF(2^64)` multiplication on words, as `BF64` multiplies. -/
def gfMulWord (a b : UInt64) : UInt64 :=
  UInt64.ofBitVec (BF64.mul ⟨a.toBitVec⟩ ⟨b.toBitVec⟩).toBitVec

/-- The primitive operations. -/
inductive Op where
  | wadd | wsub | wmul | wand | wor | wxor | wnot | wshl | wshr | weq | wlt | wle | gfmul
  /-- A word as a natural number, and a natural number modulo `2^64` as a word. -/
  | wtoNat | wofNat
  | nadd | nsub | nmul | ndiv | nmod | neq | nlt | nle | nand | nor | nxor | nshl | nshr
  /-- An array's size; its entry `i` or a default. -/
  | asize | aget
  /-- A copy with entry `i` set (unchanged out of bounds), with one entry appended. -/
  | aset | apush
  /-- An array from a list; a list from an array; two arrays appended; entries `[i, j)`; `n`
  copies of a value. -/
  | aofList | atoList | aappend | aextract | areplicate
  deriving DecidableEq, Repr

/-- A word operation of price `1`. -/
def wordOp (f : UInt64 → UInt64 → Val) (x y : UInt64) : Option (Val × ℕ) := some (f x y, 1)

/-- An operation on natural numbers of price `max m m' + 1`. -/
def natOp (f : ℕ → ℕ → ℕ) (a b : ℕ) : Option (Val × ℕ) :=
  some (.nat (f a b), max (limbs a) (limbs b) + 1)

/-- A primitive's value and price on its arguments, or `none` on a misuse. -/
def Op.apply : Op → List Val → Option (Val × ℕ)
  | .wadd, [.word x, .word y] => wordOp (fun x y ↦ .word (x + y)) x y
  | .wsub, [.word x, .word y] => wordOp (fun x y ↦ .word (x - y)) x y
  | .wmul, [.word x, .word y] => wordOp (fun x y ↦ .word (x * y)) x y
  | .wand, [.word x, .word y] => wordOp (fun x y ↦ .word (x &&& y)) x y
  | .wor, [.word x, .word y] => wordOp (fun x y ↦ .word (x ||| y)) x y
  | .wxor, [.word x, .word y] => wordOp (fun x y ↦ .word (x ^^^ y)) x y
  | .wnot, [.word x] => some (.word (~~~x), 1)
  | .wshl, [.word x, .word y] => wordOp (fun x y ↦ .word (x <<< y)) x y
  | .wshr, [.word x, .word y] => wordOp (fun x y ↦ .word (x >>> y)) x y
  | .weq, [.word x, .word y] => wordOp (fun x y ↦ .ofBool (x == y)) x y
  | .wlt, [.word x, .word y] => wordOp (fun x y ↦ .ofBool (decide (x < y))) x y
  | .wle, [.word x, .word y] => wordOp (fun x y ↦ .ofBool (decide (x ≤ y))) x y
  | .gfmul, [.word x, .word y] => some (.word (gfMulWord x y), 256)
  | .wtoNat, [.word x] => some (.nat x.toNat, 1)
  | .wofNat, [.nat n] => some (.word n.toUInt64, 1)
  | .nadd, [.nat a, .nat b] => natOp (· + ·) a b
  | .nsub, [.nat a, .nat b] => natOp (· - ·) a b
  | .nmul, [.nat a, .nat b] => some (.nat (a * b), limbs a * limbs b + 1)
  | .ndiv, [.nat a, .nat b] => some (.nat (a / b), limbs a * limbs b + 1)
  | .nmod, [.nat a, .nat b] => some (.nat (a % b), limbs a * limbs b + 1)
  | .neq, [.nat a, .nat b] => some (.ofBool (a == b), max (limbs a) (limbs b) + 1)
  | .nlt, [.nat a, .nat b] => some (.ofBool (decide (a < b)), max (limbs a) (limbs b) + 1)
  | .nle, [.nat a, .nat b] => some (.ofBool (decide (a ≤ b)), max (limbs a) (limbs b) + 1)
  | .nand, [.nat a, .nat b] => natOp (· &&& ·) a b
  | .nor, [.nat a, .nat b] => natOp (· ||| ·) a b
  | .nxor, [.nat a, .nat b] => natOp (· ^^^ ·) a b
  | .nshl, [.nat a, .nat k] => some (.nat (a <<< k), limbs (a <<< k) + limbs k + 1)
  | .nshr, [.nat a, .nat k] => some (.nat (a >>> k), limbs a + limbs k + 1)
  | .asize, [.arr xs] => some (.nat xs.size, 1)
  | .aget, [.arr xs, .nat i, d] => some (xs.getD i d, 1)
  | .aset, [.arr xs, .nat i, v] => some (.arr (xs.setIfInBounds i v), xs.size + 1)
  | .apush, [.arr xs, v] => some (.arr (xs.push v), xs.size + 2)
  | .aofList, [l] => (Val.toList? l).map fun xs ↦ (.arr xs.toArray, xs.length + 1)
  | .atoList, [.arr xs] => some (.ofList xs.toList, 3 * xs.size + 1)
  | .aappend, [.arr xs, .arr ys] => some (.arr (xs ++ ys), xs.size + ys.size + 1)
  | .aextract, [.arr xs, .nat i, .nat j] =>
    some (.arr (xs.extract i j), (xs.extract i j).size + 1)
  | .areplicate, [.nat n, v] => some (.arr (Array.replicate n v), n + 1)
  | _, _ => none

/-- The language's terms. -/
inductive Term where
  /-- The value at position `i` of the environment. -/
  | var (i : ℕ)
  /-- A literal value (part of the program). -/
  | val (v : Val)
  /-- A primitive operation on the values of the terms. -/
  | op (o : Op) (args : List Term)
  /-- A constructor of the values of the terms. -/
  | ctor (tag : ℕ) (args : List Term)
  /-- Field `i` of a constructor. -/
  | proj (i : ℕ) (t : Term)
  /-- On a constructor of tag `k`, alternative `k` with the fields in front of the
  environment. -/
  | case (t : Term) (alts : List Term)
  /-- The body with the value of `t` in front of the environment. -/
  | letE (t body : Term)
  /-- A call of function `f` on the values of the terms. -/
  | call (f : ℕ) (args : List Term)
  /-- A closure of function `f` with the values of the terms as its first arguments. -/
  | fn (f : ℕ) (args : List Term)
  /-- A closure applied to the values of the terms. -/
  | app (t : Term) (args : List Term)
  deriving Inhabited

/-- A program: the function bodies; function `0` is the entry. -/
abbrev Program := Array Term

mutual

/-- A term's value and price in an environment, with `fuel` nested calls at most. -/
def eval (P : Program) : ℕ → List Val → Term → Option (Val × ℕ)
  | _, env, .var i => env[i]?.map (·, 1)
  | _, _, .val v => some (v, 1)
  | n, env, .op o ts => do
    let (vs, c) ← evalList P n env ts
    let (v, d) ← o.apply vs
    pure (v, c + d)
  | n, env, .ctor k ts => do
    let (vs, c) ← evalList P n env ts
    pure (.ctor k vs, c + vs.length + 1)
  | n, env, .proj i t => do
    let (v, c) ← eval P n env t
    match v with
    | .ctor _ fs => fs[i]?.map (·, c + 1)
    | _ => none
  | n, env, .case t alts => do
    let (v, c) ← eval P n env t
    match v with
    | .ctor k fs => do
      let (w, d) ← evalAlt P n env fs k alts
      pure (w, c + d + 1)
    | _ => none
  | n, env, .letE t b => do
    let (v, c) ← eval P n env t
    let (w, d) ← eval P n (v :: env) b
    pure (w, c + d + 1)
  | n, env, .call f ts => do
    let (vs, c) ← evalList P n env ts
    let (w, d) ← evalBody P n f vs
    pure (w, c + d + 1)
  | n, env, .fn f ts => do
    let (vs, c) ← evalList P n env ts
    pure (.fn f vs, c + vs.length + 1)
  | n, env, .app t ts => do
    let (g, c) ← eval P n env t
    let (vs, d) ← evalList P n env ts
    match g with
    | .fn f us => do
      let (w, e) ← evalBody P n f (us ++ vs)
      pure (w, c + d + e + 1)
    | _ => none
termination_by n _ t => (n, sizeOf t, 0)

/-- The terms' values, in order, and their total price. -/
def evalList (P : Program) : ℕ → List Val → List Term → Option (List Val × ℕ)
  | _, _, [] => some ([], 0)
  | n, env, t :: ts => do
    let (v, c) ← eval P n env t
    let (vs, d) ← evalList P n env ts
    pure (v :: vs, c + d)
termination_by n _ ts => (n, sizeOf ts, 0)

/-- Alternative `k` of `alts`, with the fields `fs` in front of the environment. -/
def evalAlt (P : Program) : ℕ → List Val → List Val → ℕ → List Term → Option (Val × ℕ)
  | _, _, _, _, [] => none
  | n, env, fs, 0, a :: _ => eval P n (fs ++ env) a
  | n, env, fs, k + 1, _ :: as => evalAlt P n env fs k as
termination_by n _ _ _ as => (n, sizeOf as, 0)

/-- Function `f`'s body on the arguments `vs`, one call deeper. -/
def evalBody (P : Program) : ℕ → ℕ → List Val → Option (Val × ℕ)
  | 0, _, _ => none
  | n + 1, f, vs => match P[f]? with
    | some b => eval P n vs b
    | none => none
termination_by n _ _ => (n, 0, 0)

end

/-- **A run**: function `0` on the input `x`, with `fuel` nested calls at most below it. -/
def run (P : Program) (fuel : ℕ) (x : Val) : Option (Val × ℕ) := evalBody P (fuel + 1) 0 [x]

/-- **The output within a budget**: `P`'s value on `x` if its run costs at most `b`. -/
def outputWithin (P : Program) (x : Val) (b : ℕ) : Option Val :=
  match run P b x with
  | some (v, c) => if c ≤ b then some v else none
  | none => none

/-! ## Size -/

mutual

/-- A value's size: one per word, number, constructor, array and closure. -/
def Val.size : Val → ℕ
  | .word _ | .nat _ => 1
  | .ctor _ fs => Val.sizeList fs + 1
  | .arr xs => Val.sizeList xs.toList + 1
  | .fn _ us => Val.sizeList us + 1

/-- The sizes of the values. -/
def Val.sizeList : List Val → ℕ
  | [] => 0
  | v :: vs => v.size + Val.sizeList vs

end

mutual

/-- A term's size: one per node, literals by their size. -/
def Term.size : Term → ℕ
  | .var _ => 1
  | .val v => v.size + 1
  | .op _ ts | .ctor _ ts | .call _ ts | .fn _ ts => Term.sizeList ts + 1
  | .proj _ t => t.size + 1
  | .case t alts => t.size + Term.sizeList alts + 1
  | .letE t b => t.size + b.size + 1
  | .app t ts => t.size + Term.sizeList ts + 1

/-- The sizes of the terms. -/
def Term.sizeList : List Term → ℕ
  | [] => 0
  | t :: ts => t.size + Term.sizeList ts

end

/-- A program's size: the sizes of its bodies. -/
def Program.size (P : Program) : ℕ := (P.toList.map Term.size).sum

end

end LeanVM.Cost
