/-
  LeanVM.Guest.B2C.TableB

  The jump table in `main`'s cells (`Table.lean`) under any semantics of `BLAKE2S`.
-/

module

public import LeanVM.Guest.B2C.Table
public import LeanVM.Guest.MemoryB

/-!
# The jump table in `main`'s cells under any `BLAKE2S` semantics

`Table.lean`'s `jumpTables_honestC` with the tree valid under `S : BlakeSem`
(`jumpTablesB_honestC`): the honest memory holds the jump table. The candidates' order
(`tableC_node`, …) is `Table.lean`'s.
-/

namespace LeanVM.Guest.B2C

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

variable {S : BlakeSem}

/-! ## `main`'s candidates -/

/-- **The honest memory holds the jump table**, at `B2C.C`. -/
theorem jumpTablesB_honestC {hdr : E × E} {T : Memory.Tree} {rd : Reader}
    (hH : HonestB S coreProgram fs H C hdr T rd [] []) (hname : T.name = "main") :
    End.JumpTables (honest coreProgram fs H C hdr T) := by
  intro q hq
  obtain ⟨I, hI, hIt, hfp, -⟩ := root_inst (P := coreProgram) (fs := fs) (H := H) (hdr := hdr) (T := T)
  have hnode : ∃ σ bufs kids, T = .node "main" σ bufs kids := by
    have hv := hH.valid
    cases T with
    | phantom f σ => exact hv.elim
    | node f σ bufs kids =>
      simp only [Tree.name] at hname
      subst hname
      exact ⟨σ, bufs, kids, rfl⟩
  obtain ⟨σ, bufs, kids, hT⟩ := hnode
  have hC := tableC_node (I := I) (by rw [hIt, hT]) hq
  have := hH.read_C hI hC
  rwa [hfp, gpow, pow_zero, one_mul] at this

end
end LeanVM.Guest.B2C
