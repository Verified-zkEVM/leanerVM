module

public import Statement.LeanVm
public import Mathlib.Data.Nat.Notation

/-!
# The cost machine and the extractor a program computes

**The machine.** A first-order functional language with prices. A program is an array of
function bodies; a body reads its arguments and the values it binds by position, calls functions
by index, applies closures, builds and inspects constructors, and runs priced primitive
operations on 64-bit words, natural numbers and arrays. Values are immutable, so sharing one is
free and building one is priced by the words it writes. The machine's only runtime data is its
input: a program carries its literals, nothing else.

`run P fuel x` runs function `0` of `P` on `x`: its value and its price (the sum of the prices of
the steps it takes), or `none` when the run misuses a value (a primitive on the wrong kind of
value, a variable or a field that does not exist, a call of a function `P` lacks) or nests more
than `fuel` calls. A misuse is a failure, never undefined behavior. `outputWithin P x b` is the
value if the price is at most `b`, `none` otherwise; each call costs at least `1`, so nesting
depth `b` never fails a run of price at most `b`.

**Prices** (trusted, not a hypothesis: that they are honest, each a constant-time CPU primitive or
priced by the algorithm that computes it, is what makes the budgets of `KnowledgeSoundness
(extractorOf P)` and of `GuestKnowledge`, `Theorems.lean`, meaningful). Each step costs at least
`1`, and every step but two at least the words it writes. The two: a `case` puts the constructor's
fields in front of the environment, and a closure's application puts its captured values in front of
the arguments, each at `1`, which is honest for an environment kept as a frame pointer into the
constructor or the closure (its fields read in place, not copied), where each is `O(1)`. The prices:
* a variable, a literal, a field, a `case`'s selection, a `let`: `1`;
* a constructor or a closure of `n` values: `n + 1` (a tag and `n` words);
* a call or a closure's application: `1`;
* a word operation (`+`, `−`, `·` modulo `2^64`, `and`, `or`, `xor`, `not`, shifts, comparisons):
  `1`, each one CPU instruction;
* a `GF(2^64)` multiplication: `256`: the `64×64` carry-less product (one instruction on current
  CPUs: PCLMULQDQ, PMULL) and its reduction by the sparse modulus `x^64 + x^4 + x^3 + x + 1`
  (about `21` word operations, `Statement/Fast/FieldWords.lean`'s `reduceWords`), well within
  `256`; a software shift-and-xor loop would cost about `800`;
* an operation on natural numbers of at most `m` and `m'` limbs of 64 bits: `max m m' + 1` for
  `+`, `−`, comparisons and bitwise operations, `m·m' + 1` for `·`, `/` and `%` (schoolbook), and,
  for shifts, the shifted number's limbs (the result's for a left shift, the operand's for a right
  shift) plus the shift amount's limbs plus one; a conversion between a word and a natural
  number: `1`;
* arrays: the size or an entry `1`; a new array of `n` entries (from a list, a slice, an append, a
  copy with one entry set or appended, a replicate) `n + 1`, and a list of `n` cells from an array
  `3·n + 1`.

**The encoding** (`MachineEncoding`, `encodeValue`): words for `UInt64` and `K`, natural numbers
for `ℕ` and `Fin n`, a constructor for each inductive type (its constructor's index as the tag,
its fields in order), arrays for `Vector` and for the functions of a finite domain
(`encodeFiniteFunction`: `Semantics.Program.code`, `PublicInput.lanes`, an execution's memory).
`encodeExtractorInput prog input T proof` is the extractor's input: the program, the public
input, the transcript's permutation queries (`permutationQueries`: the transcript without the
adversary's coin flips, its private randomness) and the proof.
`decodeExecution prog` is a linear parse of an execution, the inverse of its encoding: no search
and no run, its only check that the memory has `2^κ` words.

**The extractor a program computes** (`LeanVM.extractorOf P`): the program `P` run on the encoded
statement, transcript and proof within `extractorBudget`, the budget read off the shape the proof
announces (`announced`: the layout and the rate exponent the verifier's first step reads), its
output parsed as an execution. A run that fails or exceeds its budget extracts
nothing, which counts as a break in `KnowledgeSoundness`. `Statement.Theorems` takes the program
as a parameter, with its size at most `extractorSizeBound`; `lean_vm` proves it for its knowledge
extractor compiled. What excludes a vacuous statement: `P` is a program (no classical choice),
the size bound leaves no room for a useful table of witnesses beside the compiled extractor, the
machine's only runtime data is its input, and the budget is the one below. The guest decoder is
a program of the same machine, with a size bound and a budget of its own (`GuestKnowledge`,
`Theorems.lean`).

**The budget** (`extractorBudgetFor`) is a closed formula in the number `N` of the adversary's
permutation queries: `2^95` and `O(N·log³N)`, polylogarithmic per query, so about `2^95` for
`N ≤ 2^64`, `2^107.76` at `N = 2^80` and `2^157.08` at `N = 2^128`. Near `Q = 2^128` queries the soundness bound
(`KnowledgeSoundness`) is already trivial.
-/

namespace LeanVM.Cost

@[expose] public section

/-- The machine's values. -/
inductive MachineValue where
  /-- A 64-bit word. -/
  | word (x : UInt64)
  /-- A natural number, of any size. -/
  | nat (n : ℕ)
  /-- A constructor: its tag and its fields. -/
  | ctor (tag : ℕ) (fields : List MachineValue)
  /-- An array. -/
  | arr (xs : Array MachineValue)
  /-- A closure: function `f` with its first arguments. -/
  | closure (f : ℕ) (args : List MachineValue)
  deriving Inhabited, BEq, Repr

/-- `false` and `true`: the constructors of tags `0` and `1`. -/
def MachineValue.ofBool (b : Bool) : MachineValue := .ctor (if b then 1 else 0) []

/-- A list: `nil` the constructor of tag `0`, `cons` of tag `1`. -/
def MachineValue.ofList : List MachineValue → MachineValue
  | [] => .ctor 0 []
  | x :: xs => .ctor 1 [x, MachineValue.ofList xs]

/-- The elements of a list value. -/
def MachineValue.toList? : MachineValue → Option (List MachineValue)
  | .ctor 0 [] => some []
  | .ctor 1 [x, xs] => (MachineValue.toList? xs).map (x :: ·)
  | _ => none

/-- The limbs of 64 bits of a natural number, at least one. -/
def limbCount (n : ℕ) : ℕ := n.log2 / 64 + 1

/-- `GF(2^64)` multiplication on words, as `BF64` multiplies. -/
def binaryFieldMultiplyWords (a b : UInt64) : UInt64 :=
  UInt64.ofBitVec (BF64.mul ⟨a.toBitVec⟩ ⟨b.toBitVec⟩).toBitVec

/-- The primitive operations. None reads a constructor's tag or a closure's function index as a
number (see `MachineValue.size`): their operands are words, natural numbers, arrays and lists. -/
inductive PrimitiveOperation where
  /-- On words modulo `2^64`: `+`, `−`, `·`, `and`, `or`, `xor`, `not`, the shifts, `=`, `<`,
  `≤`. -/
  | wordAdd | wordSubtract | wordMultiply | wordAnd | wordOr | wordXor | wordNot
  | wordShiftLeft | wordShiftRight | wordEqual | wordLessThan | wordLessOrEqual
  /-- The `GF(2^64)` product of two words. -/
  | binaryFieldMultiply
  /-- A word as a natural number, and a natural number modulo `2^64` as a word. -/
  | wordToNatural | wordOfNatural
  /-- On natural numbers: `+`, truncated `−`, `·`, `/`, `%`, `=`, `<`, `≤`, `and`, `or`, `xor`, the
  shifts. -/
  | naturalAdd | naturalSubtract | naturalMultiply | naturalDivide | naturalModulo
  | naturalEqual | naturalLessThan | naturalLessOrEqual | naturalAnd | naturalOr | naturalXor
  | naturalShiftLeft | naturalShiftRight
  /-- An array's size; its entry `i` or a default. -/
  | arraySize | arrayGet
  /-- A copy with entry `i` set (unchanged out of bounds), with one entry appended. -/
  | arraySet | arrayPush
  /-- An array from a list; a list from an array; two arrays appended; entries `[i, j)`; `n`
  copies of a value. -/
  | arrayOfList | arrayToList | arrayAppend | arrayExtract | arrayReplicate
  deriving DecidableEq, Repr

/-- A word operation of price `1`. -/
def wordOperation (f : UInt64 → UInt64 → MachineValue) (x y : UInt64) :
    Option (MachineValue × ℕ) :=
  some (f x y, 1)

/-- An operation on natural numbers of price `max m m' + 1`. -/
def naturalOperation (f : ℕ → ℕ → ℕ) (a b : ℕ) : Option (MachineValue × ℕ) :=
  some (.nat (f a b), max (limbCount a) (limbCount b) + 1)

/-- A primitive's value and price on its arguments, or `none` on a misuse. -/
def PrimitiveOperation.apply : PrimitiveOperation → List MachineValue → Option (MachineValue × ℕ)
  | .wordAdd, [.word x, .word y] => wordOperation (fun x y ↦ .word (x + y)) x y
  | .wordSubtract, [.word x, .word y] => wordOperation (fun x y ↦ .word (x - y)) x y
  | .wordMultiply, [.word x, .word y] => wordOperation (fun x y ↦ .word (x * y)) x y
  | .wordAnd, [.word x, .word y] => wordOperation (fun x y ↦ .word (x &&& y)) x y
  | .wordOr, [.word x, .word y] => wordOperation (fun x y ↦ .word (x ||| y)) x y
  | .wordXor, [.word x, .word y] => wordOperation (fun x y ↦ .word (x ^^^ y)) x y
  | .wordNot, [.word x] => some (.word (~~~x), 1)
  | .wordShiftLeft, [.word x, .word y] => wordOperation (fun x y ↦ .word (x <<< y)) x y
  | .wordShiftRight, [.word x, .word y] => wordOperation (fun x y ↦ .word (x >>> y)) x y
  | .wordEqual, [.word x, .word y] => wordOperation (fun x y ↦ .ofBool (x == y)) x y
  | .wordLessThan, [.word x, .word y] => wordOperation (fun x y ↦ .ofBool (decide (x < y))) x y
  | .wordLessOrEqual, [.word x, .word y] => wordOperation (fun x y ↦ .ofBool (decide (x ≤ y))) x y
  | .binaryFieldMultiply, [.word x, .word y] => some (.word (binaryFieldMultiplyWords x y), 256)
  | .wordToNatural, [.word x] => some (.nat x.toNat, 1)
  | .wordOfNatural, [.nat n] => some (.word n.toUInt64, 1)
  | .naturalAdd, [.nat a, .nat b] => naturalOperation (· + ·) a b
  | .naturalSubtract, [.nat a, .nat b] => naturalOperation (· - ·) a b
  | .naturalMultiply, [.nat a, .nat b] => some (.nat (a * b), limbCount a * limbCount b + 1)
  | .naturalDivide, [.nat a, .nat b] => some (.nat (a / b), limbCount a * limbCount b + 1)
  | .naturalModulo, [.nat a, .nat b] => some (.nat (a % b), limbCount a * limbCount b + 1)
  | .naturalEqual, [.nat a, .nat b] =>
    some (.ofBool (a == b), max (limbCount a) (limbCount b) + 1)
  | .naturalLessThan, [.nat a, .nat b] =>
    some (.ofBool (decide (a < b)), max (limbCount a) (limbCount b) + 1)
  | .naturalLessOrEqual, [.nat a, .nat b] =>
    some (.ofBool (decide (a ≤ b)), max (limbCount a) (limbCount b) + 1)
  | .naturalAnd, [.nat a, .nat b] => naturalOperation (· &&& ·) a b
  | .naturalOr, [.nat a, .nat b] => naturalOperation (· ||| ·) a b
  | .naturalXor, [.nat a, .nat b] => naturalOperation (· ^^^ ·) a b
  | .naturalShiftLeft, [.nat a, .nat k] =>
    some (.nat (a <<< k), limbCount (a <<< k) + limbCount k + 1)
  | .naturalShiftRight, [.nat a, .nat k] => some (.nat (a >>> k), limbCount a + limbCount k + 1)
  | .arraySize, [.arr xs] => some (.nat xs.size, 1)
  | .arrayGet, [.arr xs, .nat i, d] => some (xs.getD i d, 1)
  | .arraySet, [.arr xs, .nat i, v] => some (.arr (xs.setIfInBounds i v), xs.size + 1)
  | .arrayPush, [.arr xs, v] => some (.arr (xs.push v), xs.size + 2)
  | .arrayOfList, [l] => (MachineValue.toList? l).map fun xs ↦ (.arr xs.toArray, xs.length + 1)
  | .arrayToList, [.arr xs] => some (.ofList xs.toList, 3 * xs.size + 1)
  | .arrayAppend, [.arr xs, .arr ys] => some (.arr (xs ++ ys), xs.size + ys.size + 1)
  | .arrayExtract, [.arr xs, .nat i, .nat j] =>
    some (.arr (xs.extract i j), (xs.extract i j).size + 1)
  | .arrayReplicate, [.nat n, v] => some (.arr (Array.replicate n v), n + 1)
  | _, _ => none

/-- The language's terms. -/
inductive Term where
  /-- The value at position `i` of the environment. -/
  | var (i : ℕ)
  /-- A literal value (part of the program). -/
  | val (v : MachineValue)
  /-- A primitive operation on the values of the terms. -/
  | op (o : PrimitiveOperation) (args : List Term)
  /-- A constructor of the values of the terms. -/
  | ctor (tag : ℕ) (args : List Term)
  /-- Field `i` of a constructor. -/
  | field (i : ℕ) (t : Term)
  /-- On a constructor of tag `k`, alternative `k` with the fields in front of the
  environment. -/
  | case (t : Term) (alts : List Term)
  /-- The body with the value of `t` in front of the environment. -/
  | letIn (t body : Term)
  /-- A call of function `f` on the values of the terms. -/
  | call (f : ℕ) (args : List Term)
  /-- A closure of function `f` with the values of the terms as its first arguments. -/
  | closure (f : ℕ) (args : List Term)
  /-- A closure applied to the values of the terms. -/
  | applyClosure (t : Term) (args : List Term)
  deriving Inhabited

/-- A program: the function bodies; function `0` is the entry. -/
abbrev MachineProgram := Array Term

mutual

/-- A term's value and price in an environment, with `fuel` nested calls at most. -/
def evaluateTerm (P : MachineProgram) : ℕ → List MachineValue → Term → Option (MachineValue × ℕ)
  | _, env, .var i => env[i]?.map (·, 1)
  | _, _, .val v => some (v, 1)
  | n, env, .op o ts => do
    let (vs, c) ← evaluateTerms P n env ts
    let (v, d) ← o.apply vs
    pure (v, c + d)
  | n, env, .ctor k ts => do
    let (vs, c) ← evaluateTerms P n env ts
    pure (.ctor k vs, c + vs.length + 1)
  | n, env, .field i t => do
    let (v, c) ← evaluateTerm P n env t
    match v with
    | .ctor _ fs => fs[i]?.map (·, c + 1)
    | _ => none
  | n, env, .case t alts => do
    let (v, c) ← evaluateTerm P n env t
    match v with
    | .ctor k fs => do
      let (w, d) ← evaluateAlternative P n env fs k alts
      pure (w, c + d + 1)
    | _ => none
  | n, env, .letIn t b => do
    let (v, c) ← evaluateTerm P n env t
    let (w, d) ← evaluateTerm P n (v :: env) b
    pure (w, c + d + 1)
  | n, env, .call f ts => do
    let (vs, c) ← evaluateTerms P n env ts
    let (w, d) ← evaluateFunctionBody P n f vs
    pure (w, c + d + 1)
  | n, env, .closure f ts => do
    let (vs, c) ← evaluateTerms P n env ts
    pure (.closure f vs, c + vs.length + 1)
  | n, env, .applyClosure t ts => do
    let (g, c) ← evaluateTerm P n env t
    let (vs, d) ← evaluateTerms P n env ts
    match g with
    | .closure f us => do
      let (w, e) ← evaluateFunctionBody P n f (us ++ vs)
      pure (w, c + d + e + 1)
    | _ => none
termination_by n _ t => (n, sizeOf t, 0)

/-- The terms' values, in order, and their total price. -/
def evaluateTerms (P : MachineProgram) :
    ℕ → List MachineValue → List Term → Option (List MachineValue × ℕ)
  | _, _, [] => some ([], 0)
  | n, env, t :: ts => do
    let (v, c) ← evaluateTerm P n env t
    let (vs, d) ← evaluateTerms P n env ts
    pure (v :: vs, c + d)
termination_by n _ ts => (n, sizeOf ts, 0)

/-- Alternative `k` of `alts`, with the fields `fs` in front of the environment. -/
def evaluateAlternative (P : MachineProgram) :
    ℕ → List MachineValue → List MachineValue → ℕ → List Term → Option (MachineValue × ℕ)
  | _, _, _, _, [] => none
  | n, env, fs, 0, a :: _ => evaluateTerm P n (fs ++ env) a
  | n, env, fs, k + 1, _ :: as => evaluateAlternative P n env fs k as
termination_by n _ _ _ as => (n, sizeOf as, 0)

/-- Function `f`'s body on the arguments `vs`, one call deeper. -/
def evaluateFunctionBody (P : MachineProgram) :
    ℕ → ℕ → List MachineValue → Option (MachineValue × ℕ)
  | 0, _, _ => none
  | n + 1, f, vs => match P[f]? with
    | some b => evaluateTerm P n vs b
    | none => none
termination_by n _ _ => (n, 0, 0)

end

/-- **A run**: function `0` on the input `x`, with `fuel` nested calls at most below it. -/
def run (P : MachineProgram) (fuel : ℕ) (x : MachineValue) : Option (MachineValue × ℕ) :=
  evaluateFunctionBody P (fuel + 1) 0 [x]

/-- **The output within a budget**: `P`'s value on `x` if its run costs at most `b`. -/
def outputWithin (P : MachineProgram) (x : MachineValue) (b : ℕ) : Option MachineValue :=
  match run P b x with
  | some (v, c) => if c ≤ b then some v else none
  | none => none

/-! ## Size

A constructor's tag and a closure's function index count one with their node, whatever their
number, and so do a term's positions and function indices (`var`, `field`, `call`, `closure`).
That is sound because the machine reads them only by bounded lookups, never as data: a tag selects
one of a `case`'s alternatives, which the program lists, or is compared with a constant (a list's
`nil` and `cons` in `arrayOfList`, `MachineValue.toList?`); a function index is looked up in the
program (`P[f]?`); no primitive operation (`PrimitiveOperation.apply`) takes a tag or an index as
a number. -/

mutual

/-- A value's size: one per word, constructor, array and closure, and a natural number's limbs
(a literal counts in full; a tag or a function index counts with its node). -/
def MachineValue.size : MachineValue → ℕ
  | .word _ => 1
  | .nat n => limbCount n
  | .ctor _ fs => MachineValue.sizeList fs + 1
  | .arr xs => MachineValue.sizeList xs.toList + 1
  | .closure _ us => MachineValue.sizeList us + 1

/-- The sizes of the values. -/
def MachineValue.sizeList : List MachineValue → ℕ
  | [] => 0
  | v :: vs => v.size + MachineValue.sizeList vs

end

mutual

/-- A term's size: one per node, literals by their size (a position, a tag or a function index
counts with its node). -/
def Term.size : Term → ℕ
  | .var _ => 1
  | .val v => v.size + 1
  | .op _ ts | .ctor _ ts | .call _ ts | .closure _ ts => Term.sizeList ts + 1
  | .field _ t => t.size + 1
  | .case t alts => t.size + Term.sizeList alts + 1
  | .letIn t b => t.size + b.size + 1
  | .applyClosure t ts => t.size + Term.sizeList ts + 1

/-- The sizes of the terms. -/
def Term.sizeList : List Term → ℕ
  | [] => 0
  | t :: ts => t.size + Term.sizeList ts

end

/-- A program's size: the sizes of its bodies. -/
def MachineProgram.size (P : MachineProgram) : ℕ := (P.toList.map Term.size).sum

/-! ## The encoding -/

/-- A machine encoding of `α`. -/
class MachineEncoding (α : Type) where
  /-- The value of `a`. -/
  encodeValue : α → MachineValue

export MachineEncoding (encodeValue)

open LeanVM.Parameters LeanVM.Semantics Common LeanVM.Protocol.Compile

instance : MachineEncoding UInt64 := ⟨.word⟩
instance : MachineEncoding ℕ := ⟨.nat⟩
instance {n : ℕ} : MachineEncoding (Fin n) := ⟨fun i ↦ .nat i.val⟩
instance : MachineEncoding Bool := ⟨MachineValue.ofBool⟩
instance : MachineEncoding K := ⟨fun a ↦ .word a.lane⟩
instance : MachineEncoding E :=
  ⟨fun x ↦ .ctor 0 [encodeValue (x.limb 0), encodeValue (x.limb 1), encodeValue (x.limb 2)]⟩

instance {α : Type} [MachineEncoding α] : MachineEncoding (List α) :=
  ⟨fun l ↦ .ofList (l.map encodeValue)⟩

instance {α β : Type} [MachineEncoding α] [MachineEncoding β] : MachineEncoding (α × β) :=
  ⟨fun p ↦ .ctor 0 [encodeValue p.1, encodeValue p.2]⟩

/-- An option: `none` the constructor of tag `0`, `some a` of tag `1`. -/
instance {α : Type} [MachineEncoding α] : MachineEncoding (Option α) where
  encodeValue | none => .ctor 0 [] | some a => .ctor 1 [encodeValue a]

instance {α : Type} [MachineEncoding α] {n : ℕ} : MachineEncoding (Vector α n) :=
  ⟨fun v ↦ .arr (v.toArray.map encodeValue)⟩

/-- A function of a finite domain, as the array of its values. -/
def encodeFiniteFunction {α : Type} [MachineEncoding α] {n : ℕ} (f : Fin n → α) : MachineValue :=
  .arr (Array.ofFn fun i ↦ encodeValue (f i))

/-- A function of a finite domain: the array of its values. -/
instance {α : Type} [MachineEncoding α] {n : ℕ} : MachineEncoding (Fin n → α) :=
  ⟨encodeFiniteFunction⟩

instance {S : Type} [MachineEncoding S] : MachineEncoding (PermutationQuery S) where
  encodeValue | .forward x => .ctor 0 [encodeValue x] | .inverse y => .ctor 1 [encodeValue y]

instance : MachineEncoding PublicInput := ⟨fun p ↦ .ctor 0 [encodeFiniteFunction p.lanes]⟩

instance : MachineEncoding DerefMode where
  encodeValue | .cell => .ctor 0 [] | .pc => .ctor 1 [] | .fp => .ctor 2 []

instance : MachineEncoding Instr where
  encodeValue
    | .xor a b c => .ctor 0 [encodeValue a, encodeValue b, encodeValue c]
    | .mulNative a b c => .ctor 1 [encodeValue a, encodeValue b, encodeValue c]
    | .setConstant o k => .ctor 2 [encodeValue o, encodeValue k]
    | .deref a b c m => .ctor 3 [encodeValue a, encodeValue b, encodeValue c, encodeValue m]
    | .jump c d f => .ctor 4 [encodeValue c, encodeValue d, encodeValue f]
    | .keccak om t b c o i j =>
      .ctor 5 [encodeFiniteFunction om, encodeValue t, encodeValue b, encodeValue c, encodeValue o,
        encodeValue i, encodeValue j]

instance : MachineEncoding Semantics.Program :=
  ⟨fun p ↦ .ctor 0 [encodeValue p.logSize, encodeFiniteFunction p.code]⟩

instance : MachineEncoding Opening := ⟨fun o ↦ .ctor 0 [encodeValue o.leaf, encodeValue o.path]⟩

instance : MachineEncoding Proof :=
  ⟨fun π ↦ .ctor 0 [encodeValue π.stream, encodeValue π.openings]⟩

instance {prog : Semantics.Program} : MachineEncoding (Execution prog) :=
  ⟨fun t ↦ .ctor 0 [encodeValue t.logMemorySize, encodeFiniteFunction t.memory,
    encodeValue t.steps]⟩

/-- **The extractor's input**: the program, the public input, the transcript's permutation
queries, the proof. -/
def encodeExtractorInput (prog : Semantics.Program) (input : PublicInput) (T : OracleQueryLog)
    (proof : Proof) : MachineValue :=
  .ctor 0 [encodeValue prog, encodeValue input, encodeValue (permutationQueries T),
    encodeValue proof]

/-- A word of `E` from its encoding. -/
def decodeExtensionElement : MachineValue → Option E
  | .ctor 0 [.word a, .word b, .word c] => some (E.ofLimbs (K.ofLane a) (K.ofLane b) (K.ofLane c))
  | _ => none

/-- **An execution from its encoding**: the memory's log-size `κ`, its `2^κ` words, the steps;
`none` on anything else. -/
def decodeExecution (prog : Semantics.Program) : MachineValue → Option (Execution prog)
  | .ctor 0 [.nat κ, .arr mem, .nat steps] =>
    match (mem.toList.mapM decodeExtensionElement) with
    | some words =>
      if h : words.length = 2 ^ κ then
        some ⟨κ, fun i ↦ words[i.val]'(by rw [h]; exact i.isLt), steps⟩
      else none
    | none => none
  | _ => none

end

end LeanVM.Cost

/-! ## The extractor's budget -/

namespace LeanVM.Cost

@[expose] public section

/-- **The extractor's budget** for `N` permutation queries: `2^95 + (N + 2^30)·(D + 2)²·(2^15 +
2D)`, with `D = log₂(N + 2) + 1` the levels of the extractor's sorted tables of the transcript.
`lean_vm` proves the compiled extractor's price at most this at every shape the replay admits
(stack log-size `15` to `28`, rate exponent `1` to `4`, memory and program log-sizes at most `32`):
`2^95` bounds the list decoder (about `2^94.07`, its `64` lanes' Guruswami–Sudan decoding at the
worst shape, each lane interpolated by an approximant basis) and the runs of the candidate
executions (about `2^71.8`); the second term bounds
the transcript's index (about `2^14.7` per query and level squared, a level's positions growing by
a limb per `64` levels) and the committed leaves (`2^26` at most, the `2^30`). So about `2^95`
for at most `2^64` queries, `2^107.76` for `2^80` and `2^157.08` for `2^128`. -/
def extractorBudgetFor (N : ℕ) : ℕ :=
  2 ^ 95 + (N + 2 ^ 30) * (Nat.log2 (N + 2) + 3) ^ 2 * (2 ^ 15 + 2 * (Nat.log2 (N + 2) + 1))

end

end LeanVM.Cost

/-! ## The extractor a program computes -/

namespace LeanVM

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open Common

@[expose] public section

/-- **The bound on the extractor program's size** (`MachineProgram.size`): `14400`, the compiled
extractor's size (`13895`: its `697` compiled bodies and the entry, at `752` indices, `54` of
them holes, a literal `0` each) and a slack of `505`, room for one leanXMSS signature's encoding
(`309`: two layers of `153`, each a randomizer, `58` chain values and a path of `16`, digests of
two limbs) but not two, so the compiled extractor could carry no useful table of witnesses beside
its code. -/
def extractorSizeBound : ℕ := 14400

/-- **The extractor's budget**: `extractorBudgetFor` at the transcript's number of permutation
queries, where the proof's stream announces a shape (`announced`, `LeanVmVerifier.lean`: a layout
and a rate exponent); `0` when it announces none (the run is then out of budget: nothing is
extracted). -/
def extractorBudget (prog : Semantics.Program) (T : OracleQueryLog) (proof : Proof) : ℕ :=
  match announced (bytecodeWords prog) proof.stream with
  | some _ => Cost.extractorBudgetFor (permutationQueries T).length
  | none => 0

/-- **The extractor a program computes**: the program run within the budget on the encoded
statement, transcript and proof (`encodeExtractorInput`, `extractorBudget`), its output parsed
as an execution (`decodeExecution`); `none` if the run fails, exceeds its budget, or outputs no
execution's encoding. -/
def extractorOf (P : Cost.MachineProgram) : StraightLineExtractor :=
  fun prog input T proof ↦
    (Cost.outputWithin P (Cost.encodeExtractorInput prog input T proof)
      (extractorBudget prog T proof)).bind (Cost.decodeExecution prog)

end

end LeanVM
