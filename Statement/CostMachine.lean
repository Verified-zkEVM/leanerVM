module

public import Statement.LeanVm
public import Mathlib.Data.Nat.Notation

/-!
# The cost machine and the extractor a program computes

**The machine.** A first-order functional language with prices. A program is an array of
function bodies; a body reads its arguments and the values it binds by position, calls functions
by index, applies closures, builds and inspects constructors, and runs priced primitive operations
on natural numbers and arrays. Values are immutable. A program carries its literals, and its size
counts them in full (`MachineProgram.size`); its only runtime data is its input.

`run P fuel x` runs function `0` of `P` on `x`: its value and its price, the sum of its steps'
prices, or `none` when the run misuses a value (a primitive on the wrong kind of value, a missing
variable, field, alternative or function) or nests more than `fuel` calls. A misuse is a failure,
never undefined behavior. `outputWithin P x b` is the value if the price is at most `b`; each call
costs at least `1`, so the fuel never fails a run of price at most `b`.

**Why the prices are honest** (trusted, not a hypothesis: they give the budgets of
`KnowledgeSoundness (extractorOf P)` and `GuestKnowledge` their meaning). Each step is priced by
the algorithm that computes it on a 64-bit machine, at least `1`. The environment is a stack frame,
read in place: a position costs `1`; a `let` pushes one value, a `case` the fields it binds and a
closure's application the captured values it puts in front of the arguments, each at `1` per
value; a call's frame is written by its argument terms, each of price at least `1`. A constructor,
a closure and a new array cost `1` and their entries; a field and an array's entry cost `1`, read
in place: values are immutable, so they are shared, not copied (an array's update copies it). A
natural number is held in limbs of 64 bits (`limbCount`) and knows their count: an operation on
natural numbers costs the limbs it reads or writes, the larger count (`linearlyPricedResult`), and
a product, quotient, remainder or carry-less product the product of its operands' limb counts, at
least the limbs it writes (`quadraticallyPricedResult`, schoolbook); an array index of more than
one limb is out of bounds. The unit is a word operation: on one-limb operands each operation is a
few instructions of a 64-bit CPU (one, and a comparison for a shift by `64` or more, a truncated
subtraction or a division by `0`), the carry-less product x86-64's PCLMULQDQ or ARMv8's PMULL; on
more limbs, a constant number per limb or pair of limbs.

**The extractor a program computes** (`LeanVM.extractorOf P`): `P` run on the encoded statement,
transcript and proof (`encodeExtractorInput`; the transcript without the adversary's coin flips)
within its budget (`extractorBudget`: `extractorBudgetFor` at the transcript's number of
permutation queries wherever the proof announces a shape, the same for every shape, and `0` where
it announces none), its output parsed as an execution (`decodeExecution`, a linear parse: no
search, no run). A run that fails or exceeds its budget extracts nothing, which counts as a break.
`Statement.Theorems` takes `P` as a parameter with its size at most `extractorSizeBound`; `lean_vm`
proves it for its knowledge extractor, compiled. What excludes a vacuous statement: `P` is a
program (no classical choice), its size bound leaves no room for a useful table of witnesses
beside the compiled extractor, its only runtime data is its input, and its budget is a closed
formula, polylogarithmic per query (`extractorBudgetFor`). The guest decoder is a program of the
same machine, with a size bound and a budget of its own (`GuestKnowledge`, `Theorems.lean`).
-/

namespace LeanVM.Cost

@[expose] public section

/-- The machine's values. -/
inductive MachineValue where
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

/-- The primitive operations, on natural numbers and arrays. None reads a constructor's tag or a
closure's function index as a number (see the section *Size* below). -/
inductive PrimitiveOperation where
  /-- `and`, `or`, `xor`, the shifts, `+`, truncated `−`, `=`, `<`. -/
  | bitwiseAnd | bitwiseOr | bitwiseXor | shiftLeft | shiftRight | add | truncatedSubtract
  | equal | lessThan
  /-- `·`, `/`, `%` (by `0`: `0` and `a`, as Lean's), the carry-less product (the product of
  `a` and `b` read as polynomials over `GF(2)`, the verifier's `carryless`). -/
  | multiply | divide | modulo | carrylessMultiply
  /-- An array's size; its entry `i` or a default. -/
  | arraySize | arrayGet
  /-- A copy with entry `i` set (unchanged out of bounds), with one entry appended. -/
  | arraySet | arrayPush
  /-- An array from a list; a list from an array; two arrays appended; entries `[i, j)`; `n`
  copies of a value. -/
  | arrayOfList | arrayToList | arrayAppend | arrayExtract | arrayReplicate
  deriving DecidableEq, Repr

/-- The result `r` of an operation reading `a` and `b` once: the limbs it reads or writes, the
larger count. -/
def linearlyPricedResult (r a b : ℕ) : Option (MachineValue × ℕ) :=
  some (.nat r, max (limbCount r) (max (limbCount a) (limbCount b)))

/-- The result `r` of an operation pairing each limb of `a` with each limb of `b`: the product of
their counts, at least the limbs it writes. -/
def quadraticallyPricedResult (r a b : ℕ) : Option (MachineValue × ℕ) :=
  some (.nat r, max (limbCount r) (limbCount a * limbCount b))

/-- A primitive's value and price on its arguments, or `none` on a misuse. -/
def PrimitiveOperation.apply : PrimitiveOperation → List MachineValue → Option (MachineValue × ℕ)
  | .bitwiseAnd, [.nat a, .nat b] => linearlyPricedResult (a &&& b) a b
  | .bitwiseOr, [.nat a, .nat b] => linearlyPricedResult (a ||| b) a b
  | .bitwiseXor, [.nat a, .nat b] => linearlyPricedResult (a ^^^ b) a b
  | .shiftLeft, [.nat a, .nat k] => linearlyPricedResult (a <<< k) a k
  | .shiftRight, [.nat a, .nat k] => linearlyPricedResult (a >>> k) a k
  | .add, [.nat a, .nat b] => linearlyPricedResult (a + b) a b
  | .truncatedSubtract, [.nat a, .nat b] => linearlyPricedResult (a - b) a b
  | .equal, [.nat a, .nat b] => some (.ofBool (decide (a = b)), max (limbCount a) (limbCount b))
  | .lessThan, [.nat a, .nat b] => some (.ofBool (decide (a < b)), max (limbCount a) (limbCount b))
  | .multiply, [.nat a, .nat b] => quadraticallyPricedResult (a * b) a b
  | .divide, [.nat a, .nat b] => quadraticallyPricedResult (a / b) a b
  | .modulo, [.nat a, .nat b] => quadraticallyPricedResult (a % b) a b
  | .carrylessMultiply, [.nat a, .nat b] => quadraticallyPricedResult (Protocol.Verifier.carryless a b) a b
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
    | .ctor k fs =>
      match _h : alts[k]? with
      | some a => do
        let (w, d) ← evaluateTerm P n (fs ++ env) a
        pure (w, c + d + fs.length + 1)
      | none => none
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
      pure (w, c + d + e + us.length + 1)
    | _ => none
termination_by n _ t => (n, sizeOf t)
decreasing_by
  all_goals
    (try have := List.sizeOf_lt_of_mem (List.mem_of_getElem? ‹_[_]? = some _›))
    decreasing_tactic

/-- The terms' values, in order, and their total price. -/
def evaluateTerms (P : MachineProgram) :
    ℕ → List MachineValue → List Term → Option (List MachineValue × ℕ)
  | _, _, [] => some ([], 0)
  | n, env, t :: ts => do
    let (v, c) ← evaluateTerm P n env t
    let (vs, d) ← evaluateTerms P n env ts
    pure (v :: vs, c + d)
termination_by n _ ts => (n, sizeOf ts)

/-- Function `f`'s body on the arguments `vs`, one call deeper. -/
def evaluateFunctionBody (P : MachineProgram) :
    ℕ → ℕ → List MachineValue → Option (MachineValue × ℕ)
  | 0, _, _ => none
  | n + 1, f, vs => match P[f]? with
    | some b => evaluateTerm P n vs b
    | none => none
termination_by n _ _ => (n, 0)

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

/-- A value's size: one per constructor, array and closure, and a natural number's limbs (a
literal counts in full; a tag or a function index counts with its node). -/
def MachineValue.size : MachineValue → ℕ
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

instance : MachineEncoding UInt64 := ⟨fun x ↦ .nat x.toNat⟩
instance : MachineEncoding ℕ := ⟨.nat⟩
instance {n : ℕ} : MachineEncoding (Fin n) := ⟨fun i ↦ .nat i.val⟩
instance : MachineEncoding Bool := ⟨MachineValue.ofBool⟩
instance : MachineEncoding K := ⟨fun a ↦ .nat a.lane.toNat⟩
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

/-- A word of `E` from its encoding (each limb modulo `2^64`). -/
def decodeExtensionElement : MachineValue → Option E
  | .ctor 0 [.nat a, .nat b, .nat c] =>
    some (E.ofLimbs (K.ofLane a.toUInt64) (K.ofLane b.toUInt64) (K.ofLane c.toUInt64))
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

/-! ## The extractor's budget -/

/-- **The extractor's budget** for `N` permutation queries: `2^95 + (N + 2^30)·(D + 2)²·(2^15 +
2D)`, with `D = log₂(N + 2) + 1` the levels of the extractor's sorted tables of the transcript.
`lean_vm` proves the compiled extractor's price at most this at every shape the replay admits
(stack log-size `15` to `28`, rate exponent `1` to `4`, memory and program log-sizes at most `32`):
`2^95` bounds the list decoder (about `2^94.07`, its `64` lanes' Guruswami–Sudan decoding at the
worst shape, each lane interpolated by an approximant basis) and the runs of the candidate
executions (about `2^71.8`); the second term bounds
the transcript's index (about `2^14.7` per query and level squared, a level's positions growing by
a limb per `64` levels) and the committed leaves (`2^26` at most, the `2^30`). So about `2^95`
for at most `2^60` queries, `2^107.76` for `2^80` and `2^157.08` for `2^128`. -/
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
extractor's size (`13811`: its `697` compiled bodies and the entry, at `710` indices, `12` of
them holes, a literal `0` each) and a slack of `589`, room for one leanXMSS signature's encoding
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
