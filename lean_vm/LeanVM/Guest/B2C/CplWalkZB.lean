/-
  LeanVM.Guest.B2C.CplWalkZB

  The completeness walk by induction (`CplWalkZ.lean`) under any semantics of `BLAKE2S`.
-/

module

public import LeanVM.Guest.B2C.CplWalkZ
public import LeanVM.Guest.B2C.CplWalkTB

/-!
# The walk, by induction, under any `BLAKE2S` semantics

`CplWalkZ.lean`'s `walk_Z` over `WHB` (`walkB_Z`, with `walkB_armsZ`): the walk of every block
from every position gives what `WGoodB` says. The parts of a window are `CplWalkZ.lean`'s.
-/

namespace LeanVM.Guest.B2C

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Exec
open LeanVM.Guest.Check LeanVM.Guest.Memory

@[expose] public section

variable {S : BlakeSem}

section Walk

variable {κ : ℕ} {L : MemImage κ} {j fp : ℕ} {σ : Val} {es : List Ev} {vs : List V}
  {kfps : List ℕ} {hdr : E × E} {ck : List (Opcode → ℕ)} {segs : List Exec.Seg} {X : CX}
  {wJ : ℕ} {wenv : Trie Sym}

mutual
/-- **The completeness walk is sound** for every block and position. -/
theorem walkB_Z (H : WHB S L j fp X segs wJ wenv σ es vs kfps hdr ck) :
    ∀ (ss : List Stmt) (st : CW), WGoodB S H ss st
  | [], st => walkB_nilZ H st
  | .atom a :: ss, st => walkB_atomZ H a ss st (walkB_Z H ss)
  | .ite c z n :: ss, st => walkB_iteZ H c z n ss st (walkB_Z H z) (walkB_Z H n) (walkB_Z H ss)
  | .match_ v [] :: ss, st => walkB_matchNilZ H v ss st
  | .match_ v (a0 :: as) :: ss, st => walkB_matchZ H v a0 as ss st (walkB_armsZ H (a0 :: as)) (walkB_Z H ss)
  | .call f args rets :: ss, st => walkB_callZ H f args rets ss st (walkB_Z H ss)
  | .callIf c f args :: ss, st => walkB_callIfZ H c f args ss st (walkB_Z H ss)
  | .dispatch v fs args rets :: ss, st => walkB_dispatchZ H v fs args rets ss st (walkB_Z H ss)
  | .ret vs' :: ss, st => walkB_retZ H vs' ss st

theorem walkB_armsZ (H : WHB S L j fp X segs wJ wenv σ es vs kfps hdr ck) :
    ∀ (arms : List (List Stmt)) (k : ℕ) (hk : k < arms.length) (st : CW), WGoodB S H arms[k] st
  | [], _, hk, _ => absurd hk (Nat.not_lt_zero _)
  | a :: _, 0, _, st => walkB_Z H a st
  | _ :: as, k + 1, hk, st => walkB_armsZ H as k (by simpa using hk) st
end

end Walk

end
end LeanVM.Guest.B2C
