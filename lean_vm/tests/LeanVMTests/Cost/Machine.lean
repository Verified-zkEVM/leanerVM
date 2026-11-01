import LeanVM.Cost.Encoding

/-!
# Tests: the cost machine

* each primitive on sample values, with its price;
* misuse fails: a primitive on the wrong kind of value, a variable or a field that does not exist,
  a call of a missing function, too little fuel;
* Keccak-f[1600] written in the language (one function per round, a recursive loop over the 24
  round constants) equals the statement's `keccakF1600`, at `23745 ≈ 2^14.5` per permutation.
-/

namespace LeanVMTests.Cost

open LeanVM.Cost LeanVM.Semantics LeanVM.Parameters

/-! ## Primitives -/

#guard Op.wadd.apply [.word 3, .word (2 ^ 64 - 1)] == some (.word 2, 1)
#guard Op.wsub.apply [.word 3, .word 5] == some (.word (2 ^ 64 - 2), 1)
#guard Op.wmul.apply [.word (2 ^ 63), .word 2] == some (.word 0, 1)
#guard Op.wand.apply [.word 12, .word 10] == some (.word 8, 1)
#guard Op.wor.apply [.word 12, .word 10] == some (.word 14, 1)
#guard Op.wxor.apply [.word 12, .word 10] == some (.word 6, 1)
#guard Op.wnot.apply [.word 0] == some (.word (2 ^ 64 - 1), 1)
#guard Op.wshl.apply [.word 1, .word 65] == some (.word 2, 1)
#guard Op.wshr.apply [.word 8, .word 3] == some (.word 1, 1)
#guard Op.weq.apply [.word 8, .word 8] == some (.ofBool true, 1)
#guard Op.wlt.apply [.word 9, .word 8] == some (.ofBool false, 1)
#guard Op.wle.apply [.word 8, .word 8] == some (.ofBool true, 1)
#guard Op.gfmul.apply [.word 2, .word 3] == some (.word 6, 256)
#guard Op.wtoNat.apply [.word 7] == some (.nat 7, 1)
#guard Op.wofNat.apply [.nat (2 ^ 64 + 5)] == some (.word 5, 1)
-- Natural numbers: priced by 64-bit limbs.
#guard Op.nadd.apply [.nat (2 ^ 64), .nat 1] == some (.nat (2 ^ 64 + 1), 3)
#guard Op.nsub.apply [.nat 3, .nat 5] == some (.nat 0, 2)
#guard Op.nmul.apply [.nat (2 ^ 64), .nat (2 ^ 128)] == some (.nat (2 ^ 192), 7)
#guard Op.ndiv.apply [.nat 17, .nat 5] == some (.nat 3, 2)
#guard Op.nmod.apply [.nat 17, .nat 5] == some (.nat 2, 2)
#guard Op.neq.apply [.nat 5, .nat 5] == some (.ofBool true, 2)
#guard Op.nlt.apply [.nat 5, .nat 5] == some (.ofBool false, 2)
#guard Op.nle.apply [.nat 5, .nat 5] == some (.ofBool true, 2)
#guard Op.nshl.apply [.nat 1, .nat 128] == some (.nat (2 ^ 128), 5)
#guard Op.nshr.apply [.nat (2 ^ 128), .nat 127] == some (.nat 2, 5)
-- Arrays: a new array of `n` entries costs `n + 1`.
#guard Op.asize.apply [.arr #[.word 1, .word 2]] == some (.nat 2, 1)
#guard Op.aget.apply [.arr #[.word 1, .word 2], .nat 1, .word 0] == some (.word 2, 1)
#guard Op.aget.apply [.arr #[.word 1, .word 2], .nat 5, .word 0] == some (.word 0, 1)
#guard Op.aset.apply [.arr #[.word 1, .word 2], .nat 0, .word 7] == some (.arr #[.word 7, .word 2], 3)
#guard Op.apush.apply [.arr #[.word 1], .word 7] == some (.arr #[.word 1, .word 7], 3)
#guard Op.aofList.apply [.ofList [.word 1, .word 2]] == some (.arr #[.word 1, .word 2], 3)
#guard Op.atoList.apply [.arr #[.word 1, .word 2]] == some (.ofList [.word 1, .word 2], 7)
#guard Op.aappend.apply [.arr #[.word 1], .arr #[.word 2]] == some (.arr #[.word 1, .word 2], 3)
#guard Op.aextract.apply [.arr #[.word 1, .word 2, .word 3], .nat 1, .nat 9] ==
  some (.arr #[.word 2, .word 3], 3)
#guard Op.areplicate.apply [.nat 2, .word 0] == some (.arr #[.word 0, .word 0], 3)

/-! ## Misuse fails -/

#guard Op.wadd.apply [.nat 1, .word 2] == none
#guard Op.wadd.apply [.word 1] == none
#guard Op.aget.apply [.word 1, .nat 0, .word 0] == none
#guard Op.aofList.apply [.ctor 1 [.word 1, .word 2]] == none
#guard eval #[] 5 [] (.var 0) == none
#guard eval #[] 5 [] (.proj 2 (.ctor 0 [.val (.word 1)])) == none
#guard eval #[] 5 [] (.case (.val (.word 1)) [.val (.word 2)]) == none
#guard eval #[] 5 [] (.case (.ctor 3 []) [.val (.word 2)]) == none
#guard eval #[] 5 [] (.call 0 []) == none
#guard eval #[] 5 [] (.app (.val (.word 0)) []) == none
-- A function that calls itself forever runs out of fuel.
#guard run #[.call 0 [.var 0]] 1000 (.word 0) == none
-- Prices: a variable `1`, a constructor of `n` values `n + 1`, a field `1`, a `let` `1`.
#guard run #[.letE (.ctor 4 [.var 0, .var 0]) (.proj 1 (.var 0))] 1 (.word 9) == some (.word 9, 8)
#guard outputWithin #[.letE (.ctor 4 [.var 0, .var 0]) (.proj 1 (.var 0))] (.word 9) 8 ==
  some (.word 9)
#guard outputWithin #[.letE (.ctor 4 [.var 0, .var 0]) (.proj 1 (.var 0))] (.word 9) 7 == none

/-! ## Keccak-f[1600] in the language -/

/-- A term at an environment of a given length: variables named by the length at which they were
bound, turned into positions. -/
abbrev B := ℕ → Term

/-- Argument `j` of `n`. -/
def arg (n j : ℕ) : B := fun d ↦ .var (d - n + j)

/-- `let x := t; body x`. -/
def letB (t : B) (body : B → B) : B := fun d ↦ .letE (t d) (body (fun d' ↦ .var (d' - d - 1)) (d + 1))

/-- `let`s of a list of terms, in order. -/
def letsB : List B → (List B → B) → B
  | [], k => k []
  | t :: ts, k => letB t fun x ↦ letsB ts fun xs ↦ k (x :: xs)

def opB (o : Op) (args : List B) : B := fun d ↦ .op o (args.map (· d))

def wlit (x : UInt64) : B := fun _ ↦ .val (.word x)

def nlit (n : ℕ) : B := fun _ ↦ .val (.nat n)

def xorB (a b : B) : B := opB .wxor [a, b]

/-- `rot(x, n)`. -/
def rotB (x : B) (n : ℕ) : B :=
  if n = 0 then x else opB .wor [opB .wshl [x, wlit n.toUInt64], opB .wshr [x, wlit (64 - n).toUInt64]]

/-- A list value of the terms. -/
def listB : List B → B
  | [] => fun _ ↦ .ctor 0 []
  | t :: ts => fun d ↦ .ctor 1 [t d, listB ts d]

/-- One round on the state (argument `0`) with the round constant (argument `1`). -/
def roundB : B :=
  letsB ((List.range 25).map fun i ↦ opB .aget [arg 2 0, nlit i, wlit 0]) fun a ↦
  letsB ((List.range 5).map fun x ↦
      xorB (a[x]!) (xorB (a[x + 5]!) (xorB (a[x + 10]!) (xorB (a[x + 15]!) (a[x + 20]!))))) fun c ↦
  letsB ((List.range 25).map fun i ↦
      xorB (a[i]!) (xorB (c[(i + 4) % 5]!) (rotB (c[(i + 1) % 5]!) 1))) fun a ↦
  let src := fun j ↦ ((List.range 25).find? fun i ↦ keccakPi i = j).getD 0
  letsB ((List.range 25).map fun j ↦ rotB (a[src j]!) (keccakRho.getD (src j) 0)) fun b ↦
  letsB ((List.range 25).map fun i ↦
      xorB (b[i]!) (opB .wand [opB .wnot [b[i - i % 5 + (i + 1) % 5]!],
        b[i - i % 5 + (i + 2) % 5]!])) fun a ↦
  opB .aofList [listB ((a.set 0 (xorB (a[0]!) (arg 2 1))))]

/-- The program: `0` runs the rounds from round `0`; `1` the rounds from round `i` (argument `1`);
`2` one round. -/
def keccakProgram : LeanVM.Cost.Program := #[
  .call 1 [.var 0, .val (.nat 0)],
  .case (.op .nlt [.var 1, .val (.nat 24)]) [
    .var 0,
    .call 1 [.call 2 [.var 0, .op .aget [.val (.arr (keccakRC.toArray.map .word)), .var 1,
      .val (.word 0)]], .op .nadd [.var 1, .val (.nat 1)]]],
  roundB 2]

def stateA : KeccakState := Vector.ofFn fun i ↦ (i.val * 0x9E3779B97F4A7C15 + 7).toUInt64

#guard (run keccakProgram 100 (Enc.enc (0 : KeccakState))).map (·.1) ==
  some (Enc.enc (keccakF1600 0))
#guard (run keccakProgram 100 (Enc.enc stateA)).map (·.1) == some (Enc.enc (keccakF1600 stateA))
-- The price of one permutation: `23745`, between `2^14` and `2^15`.
#guard (run keccakProgram 100 (Enc.enc stateA)).map (·.2) == some 23745

end LeanVMTests.Cost
