/-
  LeanVM.Guest.B1.Comp.Whir.CapAgreesW

  The caps' agreement along a run over a total hash: `CapAgrees` over `Ht`.
-/

module

public import LeanVM.Guest.B1.Comp.Whir.OsCapC
public import LeanVM.Guest.B1.Comp.Whir.QueriesOfWith

/-!
# The caps' agreement over a total hash

`CapAgreesW Ht μ r root cv xs os target`: the deployed `CapAgrees` (`Whir/CapAgrees.lean`) over
the total hash `Ht`: at every query step of `whirOpen μ r target` run over `Ht` (`queriesOfW`)
from the chain state `cv`, the words `xs`, the openings `os` and the committed root, the step's
openings agree wherever they meet in the cap over `Ht` (`BatchAgreesW`). It is the `CapOk` at which
`open_stacked`'s placed completeness over a model holds (`CompleteOpenAtBC CM … (CapAgreesW Ht)`).
It is T6-det's form (`capAgreesW_iff_with`: `queriesOfWith`, `BatchAgreesWith`, what
`CapsAgreeWith` reads) and at `blake2sBytes` the deployed `CapAgrees` (`capAgreesW_blake`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub

@[expose] public section

/-- **The shared caps' hypothesis over a total hash** (`CapAgrees`). -/
def CapAgreesW (Ht : Bytes → Digest) (μ r : ℕ) (root cv : Digest) (xs : List E) (os : List Opening)
    (target : E) : Prop :=
  ∀ b ∈ queriesOfW Ht (whirOpen μ r target) ⟨cv, xs, os, [(root, stackShape μ r)]⟩, BatchAgreesW Ht b.1 b.2

theorem batchAgreesW_iff_with (Ht : Bytes → Digest) (depth : ℕ) (qs : List (ℕ × Opening)) :
    BatchAgreesW Ht depth qs ↔ LeanVM.E2E.Complete.BatchAgreesWith Ht depth qs := Iff.rfl

theorem capAgreesW_iff_with (Ht : Bytes → Digest) (μ r : ℕ) (root cv : Digest) (xs : List E)
    (os : List Opening) (target : E) :
    CapAgreesW Ht μ r root cv xs os target ↔
      ∀ b ∈ LeanVM.E2E.Complete.queriesOfWith Ht (whirOpen μ r target) ⟨cv, xs, os, [(root, stackShape μ r)]⟩,
        LeanVM.E2E.Complete.BatchAgreesWith Ht b.1 b.2 := by
  rw [CapAgreesW, queriesOfW_eq_queriesOfWith]; rfl

theorem capAgreesW_blake (μ r : ℕ) (root cv : Digest) (xs : List E) (os : List Opening) (target : E) :
    CapAgreesW blake2sBytes μ r root cv xs os target ↔ CapAgrees μ r root cv xs os target := by
  rw [CapAgreesW, CapAgrees, queriesOfW_blake]; rfl

end
end LeanVM.Guest.B1
