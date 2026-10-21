/-
  LeanVM.Guest.B1.Comp.Whir.Loc.OsFinal3

  `open_stacked`'s body equation over a completeness model (`Whir/OsFinal3.lean`)
-/

module

public import LeanVM.Guest.B1.Whir.OsFinal3
public import LeanVM.Guest.B1.Comp.Whir.Loc.OsFinal2B

/-!
# `open_stacked`'s body equation over a completeness model (`Whir/OsFinal3.lean`)
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub
open LeanVM.Guest.B1.Main (MemL RegionL)
open LeanVM.E2E.Complete
open LeanVM.Protocol.Compile (Bytes)
open LeanVM.Protocol (Digest)

@[expose] public section

variable {Ht : Bytes → Digest} {CM : CompModel}

variable {fs : String → ℕ} {cert : String → V → ℕ} {κ : ℕ}

theorem os_holdsList_of_eqC {C : CallRel} {rd : Reader} {σ : Val} {l l' : List Stmt} {next : Prop}
    {kret : List E → Prop} (he : l = l') (h : Stmt.HoldsListB CM.sem C rd σ l' next kret) : Stmt.HoldsListB CM.sem C rd σ l next kret :=
  he ▸ h

end
end LeanVM.Guest.B1
