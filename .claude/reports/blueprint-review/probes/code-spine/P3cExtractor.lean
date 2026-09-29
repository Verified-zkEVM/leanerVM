import LeanerVM.Protocol.Spine.Toy
import LeanerVM.Protocol.Spine.Compose
import LeanerVM.Protocol.PublicInput

/-!
Probe P3c (code-spine): the type and the value of the composed extractor when a phase has
rounds. The last declaration is expected to fail.
-/

open LeanerVM.Parameters LeanerVM.Protocol LeanerVM.Protocol.Toy CompPoly CPoly OracleComp

namespace Probe

/-! ## The composed extractor when a phase has rounds -/

/-- The toy's phases with the real public-input phase (two rounds) and four pass-throughs. -/
noncomputable def realPub : Phases toy where
  bus := Phase.passThrough toy fun s ↦ (s, ⟨[], []⟩)
  table := Phase.passThrough toy fun p ↦ (p.1, ⟨[]⟩)
  pub := publicInputPhase toy
  flock := Phase.passThrough toy fun p ↦ (p.1, ⟨[], []⟩)
  opening := Phase.passThrough toy fun _ ↦ ()

example : realPub.toDef.n = 3 := rfl

section

variable (Sb : Phase.Security toy realPub.bus (Seam.commit toy) (Seam.bus toy))
  (St : Phase.Security toy realPub.table (Seam.bus toy) (Seam.table toy))
  (Sf : Phase.Security toy realPub.flock (Seam.pub toy) (Seam.flock toy))
  (So : Phase.Security toy realPub.opening (Seam.flock toy) (Seam.done toy))

/-- A security bundle whose public-input field is the repository's. -/
def realPubSecurity : realPub.Security := ⟨Sb, St, publicInputSecurity toy, Sf, So⟩

-- The output slot of the composed extractor is the public-input phase's last intermediate
-- witness, `Unit`: it is not the stack.
example : (realPubSecurity Sb St Sf So).toDef.witMid (Fin.last 3) = Unit := rfl

-- The stack is what the composed extractor returns at round 0, from the transcript's first
-- message.
example : (realPubSecurity Sb St Sf So).toDef.witMid 0 = Column 3 := rfl

-- At round 0 the composed extractor returns the transcript's first message, whatever the
-- phases' extractors and whatever intermediate witness it is handed.
example (s : K)
    (tr : realPub.toDef.pSpec.Transcript (Fin.succ (⟨0, Nat.zero_lt_succ 2⟩ : Fin 3)))
    (w : (realPubSecurity Sb St Sf So).toDef.witMid (Fin.succ (⟨0, Nat.zero_lt_succ 2⟩ : Fin 3))) :
    (piopExtractor realPub (realPubSecurity Sb St Sf So)).extractMid
      (⟨0, Nat.zero_lt_succ 2⟩ : Fin 3) (s, fun i : Fin 0 ↦ i.elim0) tr w =
        (tr ⟨0, Nat.zero_lt_succ 0⟩ : Column 3) := rfl

-- EXPECTED TO FAIL: the repository's test statement, with the real public-input phase in the
-- bundle. The output slot is `Unit`, so the statement "`extractOut` returns the stack" does not
-- typecheck.
example (tr : realPub.toDef.pSpec.FullTranscript) :
    (piopExtractor realPub (realPubSecurity Sb St Sf So)).extractOut
      ((1 : K), fun i : Fin 0 ↦ i.elim0) tr () = honest := rfl

end

end Probe
