/-
  LeanVM.Cost.Lang

  A draft of the cost machine (extractor plan, §5.2): a first-order structured language on 64-bit
  words and arrays of words, with a deterministic, priced big-step semantics. Spike: its first
  use is to hand-compile samples of the extractor and measure what their proofs cost.
-/

module

public import Mathlib.Data.Nat.Notation
public import CompPoly.Fields.Binary.BF64.Impl

/-!
# A structured RAM language with prices

Registers hold 64-bit words; a word may be the handle of an array in the heap. An expression reads
registers and arrays; a statement writes registers and arrays, allocates, branches and loops. The
semantics is big-step and deterministic: `exec fuel s σ` is the final state and the charged cost,
or `none` when the run misuses memory (an unallocated handle, an index out of bounds) or runs out
of `fuel` loop iterations. A misuse is a failure, never undefined behavior.

**Prices** (§5.3: each at least `max(1, words written)`):
* a literal, a register read, an array read or length: `1`;
* a word operation (`+`, `−`, `·` modulo `2^64`, `and`, `or`, `xor`, shifts, comparisons): `1`,
  each a single CPU instruction;
* `GF(2^64)` multiplication: `gfMulPrice = 256`, the carry-less product of two words by 64
  shift-and-xor steps (four operations each) and its reduction; one `pclmulqdq` on hardware that
  has it, so the price is generous to the machine's honesty;
* a register write or an array write: `1` plus the cost of its expressions;
* an allocation of `n` words: `max 1 n` (the words are zeroed);
* a branch or a loop test: `1` plus its condition.
-/

namespace LeanVM.Cost

@[expose] public section

/-- The price of a `GF(2^64)` multiplication. -/
def gfMulPrice : ℕ := 256

/-- The word operations. -/
inductive BinOp where
  | add | sub | mul | and | or | xor | shl | shr | eq | lt | gfMul
  deriving DecidableEq, Repr

/-- `GF(2^64)` multiplication on words, as `K = BF64` multiplies. -/
def gfMulWord (a b : UInt64) : UInt64 :=
  UInt64.ofBitVec (BF64.mul ⟨a.toBitVec⟩ ⟨b.toBitVec⟩).toBitVec

/-- A word operation's value. -/
def BinOp.eval : BinOp → UInt64 → UInt64 → UInt64
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b
  | .and, a, b => a &&& b
  | .or, a, b => a ||| b
  | .xor, a, b => a ^^^ b
  | .shl, a, b => a <<< b
  | .shr, a, b => a >>> b
  | .eq, a, b => if a = b then 1 else 0
  | .lt, a, b => if a < b then 1 else 0
  | .gfMul, a, b => gfMulWord a b

/-- A word operation's price. -/
def BinOp.price : BinOp → ℕ
  | .gfMul => gfMulPrice
  | _ => 1

/-- Expressions. -/
inductive Expr where
  /-- A word. -/
  | lit (x : UInt64)
  /-- Register `r`. -/
  | var (r : ℕ)
  /-- A word operation. -/
  | bin (op : BinOp) (a b : Expr)
  /-- The length of the array whose handle is in register `r`. -/
  | len (r : ℕ)
  /-- Entry `i` of the array whose handle is in register `r`. -/
  | read (r : ℕ) (i : Expr)

/-- Statements. -/
inductive Stmt where
  | skip
  /-- `r := e`. -/
  | set (r : ℕ) (e : Expr)
  /-- A new array of `n` zeros, its handle in register `r`. -/
  | alloc (r : ℕ) (n : Expr)
  /-- Entry `i` of the array whose handle is in register `r` becomes `e`. -/
  | write (r : ℕ) (i e : Expr)
  | seq (s t : Stmt)
  /-- `if c ≠ 0 then s else t`. -/
  | ite (c : Expr) (s t : Stmt)
  /-- `while c ≠ 0 do s`. -/
  | loop (c : Expr) (s : Stmt)

/-- A machine state: registers and the heap of arrays. -/
structure State where
  regs : ℕ → UInt64
  heap : Array (Array UInt64)

/-- The array a handle names, if it is allocated. -/
def State.arr (σ : State) (h : UInt64) : Option (Array UInt64) := σ.heap[h.toNat]?

/-- An expression's value and price, or `none` on a misuse. -/
def Expr.eval (σ : State) : Expr → Option (UInt64 × ℕ)
  | .lit x => some (x, 1)
  | .var r => some (σ.regs r, 1)
  | .bin op a b => do
    let (x, c) ← a.eval σ
    let (y, d) ← b.eval σ
    pure (op.eval x y, c + d + op.price)
  | .len r => do
    let a ← σ.arr (σ.regs r)
    pure (a.size.toUInt64, 1)
  | .read r i => do
    let (j, c) ← i.eval σ
    let a ← σ.arr (σ.regs r)
    let x ← a[j.toNat]?
    pure (x, c + 1)

/-- Register `r` set to `x`. -/
def State.setReg (σ : State) (r : ℕ) (x : UInt64) : State :=
  { σ with regs := Function.update σ.regs r x }

@[simp] theorem State.setReg_regs (σ : State) (r : ℕ) (x : UInt64) (r' : ℕ) :
    (σ.setReg r x).regs r' = if r' = r then x else σ.regs r' := by
  simp [State.setReg, Function.update_apply]

@[simp] theorem State.setReg_heap (σ : State) (r : ℕ) (x : UInt64) :
    (σ.setReg r x).heap = σ.heap := rfl

@[simp] theorem State.setReg_arr (σ : State) (r : ℕ) (x : UInt64) (h : UInt64) :
    (σ.setReg r x).arr h = σ.arr h := rfl

/-- A statement's final state and price, or `none` on a misuse or when `fuel` loop iterations do
not suffice. -/
def Stmt.exec : ℕ → Stmt → State → Option (State × ℕ)
  | _, .skip, σ => some (σ, 1)
  | _, .set r e, σ => do
    let (x, c) ← e.eval σ
    pure (σ.setReg r x, c + 1)
  | _, .alloc r n, σ => do
    let (m, c) ← n.eval σ
    pure ({ σ.setReg r σ.heap.size.toUInt64 with heap := σ.heap.push (Array.replicate m.toNat 0) },
      c + max 1 m.toNat)
  | _, .write r i e, σ => do
    let (j, c) ← i.eval σ
    let (x, d) ← e.eval σ
    let a ← σ.arr (σ.regs r)
    if j.toNat < a.size then
      pure ({ σ with heap := σ.heap.set! (σ.regs r).toNat (a.set! j.toNat x) }, c + d + 1)
    else none
  | fuel, .seq s t, σ => do
    let (σ₁, c) ← s.exec fuel σ
    let (σ₂, d) ← t.exec fuel σ₁
    pure (σ₂, c + d)
  | fuel, .ite b s t, σ => do
    let (x, c) ← b.eval σ
    let (σ', d) ← if x ≠ 0 then s.exec fuel σ else t.exec fuel σ
    pure (σ', c + d + 1)
  | 0, .loop _ _, _ => none
  | fuel + 1, .loop b s, σ => do
    let (x, c) ← b.eval σ
    if x = 0 then pure (σ, c + 1)
    else do
      let (σ₁, d) ← s.exec (fuel + 1) σ
      let (σ₂, e) ← (Stmt.loop b s).exec fuel σ₁
      pure (σ₂, c + d + e + 1)
termination_by fuel s => (fuel, sizeOf s)

/-! ## One rule per construct: the steps a certifying compiler's proofs chain -/

section Rules

variable {σ : State} {F : ℕ}

theorem eval_lit (x : UInt64) : (Expr.lit x).eval σ = some (x, 1) := rfl

theorem eval_var (r : ℕ) : (Expr.var r).eval σ = some (σ.regs r, 1) := rfl

theorem eval_bin {op : BinOp} {a b : Expr} {x y : UInt64} {c d : ℕ} (ha : a.eval σ = some (x, c))
    (hb : b.eval σ = some (y, d)) : (Expr.bin op a b).eval σ = some (op.eval x y, c + d + op.price) :=
  by simp [Expr.eval, ha, hb]

theorem eval_len {r : ℕ} {a : Array UInt64} (h : σ.arr (σ.regs r) = some a) :
    (Expr.len r).eval σ = some (a.size.toUInt64, 1) := by simp [Expr.eval, h]

theorem eval_read {r : ℕ} {i : Expr} {j x : UInt64} {c : ℕ} {a : Array UInt64}
    (hi : i.eval σ = some (j, c)) (h : σ.arr (σ.regs r) = some a) (hx : a[j.toNat]? = some x) :
    (Expr.read r i).eval σ = some (x, c + 1) := by simp [Expr.eval, hi, h, hx]

theorem exec_skip : Stmt.skip.exec F σ = some (σ, 1) := by simp [Stmt.exec]

theorem exec_set {r : ℕ} {e : Expr} {x : UInt64} {c : ℕ} (he : e.eval σ = some (x, c)) :
    (Stmt.set r e).exec F σ = some (σ.setReg r x, c + 1) := by simp [Stmt.exec, he]

theorem exec_seq {s t : Stmt} {σ₁ σ₂ : State} {c d : ℕ} (hs : s.exec F σ = some (σ₁, c))
    (ht : t.exec F σ₁ = some (σ₂, d)) : (Stmt.seq s t).exec F σ = some (σ₂, c + d) := by
  simp [Stmt.exec, hs, ht]

theorem exec_ite_true {b : Expr} {s t : Stmt} {x : UInt64} {c d : ℕ} {σ' : State}
    (hb : b.eval σ = some (x, c)) (hx : x ≠ 0) (hs : s.exec F σ = some (σ', d)) :
    (Stmt.ite b s t).exec F σ = some (σ', c + d + 1) := by simp [Stmt.exec, hb, hx, hs]

theorem exec_ite_false {b : Expr} {s t : Stmt} {c d : ℕ} {σ' : State}
    (hb : b.eval σ = some (0, c)) (ht : t.exec F σ = some (σ', d)) :
    (Stmt.ite b s t).exec F σ = some (σ', c + d + 1) := by simp [Stmt.exec, hb, ht]

theorem exec_write {r : ℕ} {i e : Expr} {j x : UInt64} {c d : ℕ} {a : Array UInt64}
    (hi : i.eval σ = some (j, c)) (he : e.eval σ = some (x, d)) (h : σ.arr (σ.regs r) = some a)
    (hj : j.toNat < a.size) :
    (Stmt.write r i e).exec F σ =
      some ({ σ with heap := σ.heap.set! (σ.regs r).toNat (a.set! j.toNat x) }, c + d + 1) := by
  simp [Stmt.exec, hi, he, h, hj]

theorem exec_alloc {r : ℕ} {n : Expr} {m : UInt64} {c : ℕ} (hn : n.eval σ = some (m, c)) :
    (Stmt.alloc r n).exec F σ = some ({ σ.setReg r σ.heap.size.toUInt64 with
      heap := σ.heap.push (Array.replicate m.toNat 0) }, c + max 1 m.toNat) := by
  simp [Stmt.exec, hn]

end Rules

end

end LeanVM.Cost
