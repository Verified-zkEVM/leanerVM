/-
  LeanVM.Guest.B1.Comp.Whir.Loc.OsKids

  The kids of `open_stacked` over a completeness model (`Whir/OsKids.lean`)
-/

module

public import LeanVM.Guest.B1.Whir.OsKids
public import LeanVM.Guest.B1.UniformS
public import LeanVM.Guest.B1.Comp.Whir.OsCapC

/-!
# The kids of `open_stacked` over a completeness model (`Whir/OsKids.lean`)
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)
open LeanVM.E2E.Complete
open LeanVM.Protocol.Compile (Bytes)
open LeanVM.Protocol (Digest)

@[expose] public section

variable {Ht : Bytes → Digest} {CM : CompModel}

variable {fs : String → ℕ} {cert : String → V → ℕ}

private theorem os_regionL_appendC {L L' : Layout} {i : ℕ} (h : RegionL (L ++ L') i) : RegionL L i ∨ RegionL L' i := by
  obtain ⟨q, hq, h1, h2⟩ := h
  rcases List.mem_append.mp hq with hq | hq
  · exact Or.inl ⟨q, hq, h1, h2⟩
  · exact Or.inr ⟨q, hq, h1, h2⟩

end
end LeanVM.Guest.B1
