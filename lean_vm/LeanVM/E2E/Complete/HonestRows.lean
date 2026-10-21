/-
  LeanVM.E2E.Complete.HonestRows

  What the honest decoding (L9, `DecodeHonest`) takes of the honest run: every instance of the
  honest tree holds, located, at its own frame, under the table semantics of the run's own rows.
-/

module

public import LeanVM.Guest.Located.BasicB
public import LeanVM.Guest.Value.OracleModel
public import LeanVM.Guest.MemoryB
public import LeanVM.Guest.B2C.Defs
public import LeanVM.Guest.B2C.ShareSoundB

/-!
# The honest run's own rows

V_I decodes an execution under the table semantics of its own `BLAKE2S` rows
(`Value.tableSem (t.blakeRows blakeFree)`, decision E2E-3), at the frames the idealized proof names
(decision E2E-5): a named frame is used when the callee's code holds there under that semantics
(`Located.frameOfB_of_bodyAt`). The honest tree's instances hold under the model's semantics
`S`; that they hold under the run's own table is a fact about the honest run: every `BLAKE2S` row
an instance checks is one the run executes.

`HonestRowsExecuted`: for a functional semantics `S` whose checked rows are canonical, on the
honest memory of a tree of `main` honest under `S` (`HonestAtB`) and a halting run of `n` steps on
it, every node instance of the tree, valid on the honest memory's reads on some words, holds,
located, at its own frame under the table semantics of the run's rows (`Located.BodyAtB`).
-/

namespace LeanVM.E2E.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-- **Every honest instance holds at its frame under the honest run's own rows.** -/
def HonestRowsExecuted : Prop :=
  ∀ (S : BlakeSem), B2C.SemFunctional S →
    (∀ {m : Fin 4 → E} {cv0 cv1 o0 o1 md : E}, S.check m cv0 cv1 o0 o1 md →
      CanonicalCells m cv0 cv1 o0 o1 md) →
    ∀ (hdr : E × E) (rd : Reader) (T : Tree), T.name = "main" →
      HonestAtB S coreProgram B2C.fs B2C.H B2C.C hdr T B2C.cert rd [] [] →
      ∀ n, runB S guest (honest coreProgram B2C.fs B2C.H B2C.C hdr T) n Regs.initial =
          some (Regs.final guest) →
        ∀ I ∈ honestInsts coreProgram B2C.fs B2C.H hdr T, ∀ f σ bufs kids,
          I.t = .node f σ bufs kids → ∀ args rets,
            I.t.ValidB S coreProgram (honest coreProgram B2C.fs B2C.H B2C.C hdr T).read args rets →
            Located.BodyAtB (Value.tableSem
              (Trace.blakeRows blakeFree (⟨_, honest coreProgram B2C.fs B2C.H B2C.C hdr T, n⟩ :
                Trace guest)))
              (honest coreProgram B2C.fs B2C.H B2C.C hdr T) f args rets I.fp

end
end LeanVM.E2E.Complete
