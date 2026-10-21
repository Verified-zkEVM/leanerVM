/-
  LeanVM.Guest.B1.Comp.Tables.CompletesB

  The deployed completeness of blocks free of `BLAKE2S` carried over to any semantics of
  `BLAKE2S` (`CompletesB`, `Comp/CompletesB.lean`), at the program's relation under it.
-/

module

public import LeanVM.Guest.B1.Comp.CompletesB
public import LeanVM.Guest.B1.Comp.VerifySub.Blocks
public import LeanVM.Guest.B1.Comp.FsBlocks
public import LeanVM.Guest.B1.VerifySub.CBlocks
public import LeanVM.Guest.B1.ModelAux
public import LeanVM.Guest.B1.Sig.Steps
public import LeanVM.Guest.B1.Sig.Walk

/-!
# Deployed completeness carried to any semantics

`CompletesB S C rd lo hi ss σ Post` (`Comp/CompletesB.lean`) from the deployed `Completes`:

* `Completes.toB`: a block without `BLAKE2S` completing deployed completes under every `S` at the
  same call relation;
* `Completes.toRelB`: one calling only functions free of `BLAKE2S` completes at
  `coreProgram.RelB S` from `coreProgram.Rel` (`relB_iff_rel_of_freeOn`);
* `Completes.toBC`: one without `BLAKE2S` and without calls, at every call relation.

The Fiat-Shamir blocks over a completeness model are `completesB_fsNextT_comp`,
`completesB_squeezeT_comp` (`Comp/VerifySub/Blocks.lean`).
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub LeanVM.E2E.Complete

@[expose] public section

variable {S : BlakeSem} {C : CallRel} {rd : Reader}

/-! ## Completeness under any semantics -/

/-- **A block without `BLAKE2S` completing deployed** completes under every semantics, at the same
call relation. -/
theorem Completes.toB {lo hi : Nat} {ss : List Stmt} {σ : Val} {P : Val → Prop}
    (hnb : Stmt.noBlakeList ss = true) (h : Completes C rd lo hi ss σ P) :
    CompletesB S C rd lo hi ss σ P :=
  let ⟨σ', he, hp, hh⟩ := h
  ⟨σ', he, hp, fun next kret hn => (holdsListB_iff_of_noBlake hnb next kret).mpr (hh next kret hn)⟩

/-- **A block free of `BLAKE2S` completing deployed at the program's relation** completes under
every semantics at the program's relation under it: every function it calls is in a set `F` of
functions free of `BLAKE2S`. -/
theorem Completes.toRelB {F : List String} (hP : coreProgram.FreeOn F = true) {lo hi : Nat}
    {ss : List Stmt} {σ : Val} {P : Val → Prop} (hF : Stmt.freeInList F ss = true)
    (h : Completes (coreProgram.Rel rd) rd lo hi ss σ P) :
    CompletesB S (coreProgram.RelB S rd) rd lo hi ss σ P :=
  let ⟨σ', he, hp, hh⟩ := h
  ⟨σ', he, hp, fun next kret hn => by
    have hC : CallRel.AgreeOn F (coreProgram.RelB S rd) (coreProgram.Rel rd) := fun f hf a r =>
      relB_iff_rel_of_freeOn hP (List.contains_iff_mem.mp hf) a r
    exact (holdsListB_freeIn (S' := blakeDeployed) hC ss hF next kret).mpr
      (by rw [holdsListB_deployed]; exact hh next kret hn)⟩

/-- **A block without `BLAKE2S` and without calls completing deployed** completes under every
semantics at every call relation. -/
theorem Completes.toBC {C' : CallRel} {lo hi : Nat} {ss : List Stmt} {σ : Val} {P : Val → Prop}
    (hF : Stmt.freeInList [] ss = true) (h : Completes C rd lo hi ss σ P) :
    CompletesB S C' rd lo hi ss σ P :=
  let ⟨σ', he, hp, hh⟩ := h
  ⟨σ', he, hp, fun next kret hn => by
    have hC : CallRel.AgreeOn [] C' C := fun f hf => absurd hf (by simp)
    exact (holdsListB_freeIn (S' := blakeDeployed) hC ss hF next kret).mpr
      (by rw [holdsListB_deployed]; exact hh next kret hn)⟩

end
end LeanVM.Guest.B1.Sig
