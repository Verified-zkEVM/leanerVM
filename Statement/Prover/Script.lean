module

public import Statement.LeanVmVerifier

/-!
# The prover's language

An honest prover written as a program of its own moves, in the order the verifier reads them: it
sends a scalar (`send`), receives a challenge (`sample`), passes a proof of work (`grind`),
commits a matrix (`commit`) and receives the opened rows (`query`), carrying whatever state it
needs in ordinary bindings. `Run.lean` runs a script against the verifier's program (`Prog`,
`LeanVmVerifier.lean`) through the Fiat-Shamir sponge, committing each matrix by its Merkle tree.

A script cannot see a hash or permutation answer other than through the challenges the sponge
gives it: the run (`Run.lean`) feeds it the challenge at each `sample` and the rows of its own
matrices at each `query`, nothing else.
-/

@[expose] public section

namespace LeanVM.Protocol.Compile

open LeanVM.Parameters

/-- A committed matrix: the row at each position. A matrix of `2^height` rows is read at its first
`2^height` positions; the Merkle path of a position reads its low `height` bits
(`verifier.py:396`). -/
abbrev Word : Type := ℕ → List K

end LeanVM.Protocol.Compile

namespace LeanVM.Prover

open LeanVM.Parameters LeanVM.Protocol.Compile

/-- An honest prover as a program of its own moves. -/
inductive Script (α : Type) : Type where
  /-- Stop with a value. -/
  | ret (a : α)
  /-- Send the scalar `x`. -/
  | send (x : E) (k : Script α)
  /-- Receive a challenge. -/
  | sample (k : E → Script α)
  /-- Pass a proof of work. -/
  | grind (k : Script α)
  /-- Commit a matrix. -/
  | commit (word : Word) (k : Script α)
  /-- Receive the opened rows. -/
  | query (k : List (List K) → Script α)

namespace Script

variable {α β : Type}

/-- Sequencing. -/
def bind : Script α → (α → Script β) → Script β
  | ret a, f => f a
  | send x k, f => send x (k.bind f)
  | sample k, f => sample fun c ↦ (k c).bind f
  | grind k, f => grind (k.bind f)
  | commit w k, f => commit w (k.bind f)
  | query k, f => query fun r ↦ (k r).bind f

instance : Monad Script where
  pure := ret
  bind := bind

/-- Send one scalar. -/
def sendE (x : E) : Script Unit := send x (ret ())

/-- Send a list of scalars, in order. -/
def sendList : List E → Script Unit
  | [] => ret ()
  | x :: xs => send x (sendList xs)

/-- Receive one challenge. -/
def sampleE : Script E := sample ret

/-- Receive `n` challenges, in order. -/
def sampleN : ℕ → Script (List E)
  | 0 => ret []
  | n + 1 => do
    let x ← sampleE
    let xs ← sampleN n
    return x :: xs

/-- Pass a proof of work. -/
def grindS : Script Unit := grind (ret ())

/-- Commit a matrix. -/
def commitS (word : Word) : Script Unit := commit word (ret ())

/-- Receive opened rows. -/
def queryS : Script (List (List K)) := query ret

end Script

end LeanVM.Prover

end
