module

public import LeanVM.Cost.Bounds.FastPath

/-!
# Bounds: the candidate runner

* **`haltLoopVec_cost`**: the halting loop (`haltLoopVec.c389`) with fuel `n` pays at most
  `(S + 45)·n + 20`, `S` a bound of one step's price (`stepVec.c390`).

Open: the memory vector (`memoryVec.c386`: `2^logMemory` words from three columns, an
`ofFnFrom` of a constant-price closure), one step (`stepVec`: the code table's search `gLogTable`, `executeWith`'s instructions,
Keccak-f), `boundaryOfStack`, the tables (`powTable`: a merge sort of `2^logMemory` pairs,
`pcFinal`, `stepCapLite`).
-/

namespace LeanVM.Cost.Bounds

open LeanVM.Cost LeanVM.Cost.Extractor LeanVM.Cost.Library LeanVM.Parameters LeanVM.Extraction
open LeanVM.Extraction.Fast LeanVM.Semantics

public section

variable (P : LeanVM.Cost.Program)

/-- **The halting loop** (`haltLoopVec.c389`): `n` steps at most, each one step's price (at most
`S`) and `45`; `20` at the end. The step counter `a` stays a word. -/
theorem haltLoopVec_cost (hP : Includes P Auto.LeanVM.Extraction.Fast.haltLoopVec.c389.costDeps)
    (memT codeT : Array (ℕ × ℕ)) (prog : LeanVM.Semantics.Program) {κ : ℕ} (mem : Vector E (2 ^ κ))
    (fin : Registers K) (S : ℕ)
    (hS : ∀ r : Registers K, machineCost P Auto.LeanVM.Extraction.Fast.stepVec.c390.costIdx
      [enc memT, enc codeT, enc prog, enc κ, enc mem, enc r] ≤ S) :
    ∀ (n a : ℕ) (r : Registers K), n + a < 2 ^ 64 →
      machineCost P Auto.LeanVM.Extraction.Fast.haltLoopVec.c389.costIdx
        [enc memT, enc codeT, enc prog, enc κ, enc mem, enc fin, enc n, enc a, enc r] ≤
        (S + 45) * n + 20 := by
  intro n
  induction n with
  | zero =>
    intro a r _
    rw [Auto.LeanVM.Extraction.Fast.haltLoopVec.c389.costEq_zero P hP]
    split_ifs <;> omega
  | succ n ih =>
    intro a r hna
    rw [Auto.LeanVM.Extraction.Fast.haltLoopVec.c389.costEq_succ P hP,
      limbs_of_lt (by omega : n + 1 < 2 ^ 64)]
    have hs := hS r
    generalize hst : stepVec memT codeT prog mem r = o
    cases o with
    | none => split_ifs <;> (try dsimp only) <;> nlinarith
    | some r' =>
      have := ih (a + 1) r' (by omega)
      rw [limbs_of_lt (by omega : a < 2 ^ 64)]
      split_ifs <;> (try dsimp only) <;> nlinarith

end

end LeanVM.Cost.Bounds
