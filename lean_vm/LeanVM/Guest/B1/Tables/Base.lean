/-
  LeanVM.Guest.B1.Tables.Base

  The vocabulary of the B1 lemmas of the bus, the tables, the selectors and the placement: memory
  runs, and runs of the specification's programs on the duplex sponge that the guest carries
  between functions as its five capacity cells.
-/

module

public import LeanVM.Guest.CoreData
public import LeanVM.Guest.CoreLemmas
public import LeanVM.Guest.Value.Keccak
public import LeanVM.Guest.Value.Bits

/-!
# B1 of the bus and the tables: vocabulary

These are local to `B1/{Gkr, Tables, Selectors, Placement}` (prefixed `Tb`, `tb`), until the
shared `B1/Common` has them.

* `TbReadsAt rd p xs`: the words `xs` lie in memory from the pointer `p`, word `k` at `p·g^k`.
* `capCells S`: the five cells `8 .. 12` of the state `S` in the even layout, its lanes
  `16 .. 24`, the capacity (`fs0 .. fs4`, G:595-622) that travels between the guest's functions.
* `SpRuns p cap xs a cap'`: from any sponge whose state has the capacity cells `cap` and no
  waiting scalar, the program `p` (`Spec/Verifier.lean`'s language, run with Keccak-256 and
  Keccak-f[1600]) reads exactly the stream words `xs` and returns `a`, leaving a sponge with the
  capacity cells `cap'` and no waiting scalar, on any stream continuing `xs`, any openings and
  any roots. A sponge with no waiting scalar acts on the next permutation only through its lanes
  `16 .. 24` (`duplexInput`), so the capacity is all a caller needs to hand over.
* `BytecodeAt ev words point value`: the evaluations `ev` take `value` for the fixed polynomial
  at `point`, consuming nothing.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The words `xs` lie in memory from `p`: word `k` at `p·g^k`. -/
def TbReadsAt (rd : Reader) (p : E) (xs : List E) : Prop :=
  ∀ k (hk : k < xs.length), LoadHolds rd p k xs[k]

/-- `Compile.run` with the deployed hash and permutation. -/
abbrev tbRun {α : Type} (p : Prog α) (s : St) : Option (α × St) :=
  Compile.run (m := Id) keccak256 keccakF p s

/-- The capacity cells of a state: cells `8 .. 12` of the even layout, lanes `16 .. 24`. -/
def capCells (S : KState) : List E :=
  (List.finRange 5).map fun j ↦ cellsOfState S false ⟨8 + j.val, by omega⟩

/-- **A run on the carried capacity**: from every state with the capacity cells `cap` and no
waiting scalar, `p` reads exactly `xs` and returns `a`, ending at a state with the capacity cells
`cap'` and no waiting scalar. -/
def SpRuns {α : Type} (p : Prog α) (cap xs : List E) (a : α) (cap' : List E) : Prop :=
  ∀ S : KState, capCells S = cap → ∃ S' : KState, capCells S' = cap' ∧
    ∀ (rest : List E) (os : List Opening) (roots : List (Digest × ℕ × ℕ)),
      tbRun p ⟨⟨S, []⟩, xs ++ rest, os, roots⟩ = some (a, ⟨⟨S', []⟩, rest, os, roots⟩)

/-- `ev` takes `value` for the fixed polynomial of `words` at `point`, consuming nothing. -/
def BytecodeAt (ev : Evaluations) (words : List K) (point : List E) (value : E) : Prop :=
  ∀ s, tbRun (ev.bytecode words point) s = some (value, s)

/-- The order of `g`. -/
abbrev tbOrdG : ℕ := 2 ^ 64 - 1

/-- `g_squares` (`exponent_tables`, G:652-668): `g^(2^j)` at `g^j`, `j < SIZE_BITS = 34`. -/
def gSquaresList : List E := (List.range 34).map fun j ↦ gen ^ 2 ^ j

end
end LeanVM.Guest.B1.Tables
