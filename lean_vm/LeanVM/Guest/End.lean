/-
  LeanVM.Guest.End

  The start of a valid execution's memory: the public input's cells as `main` loads them.
-/

module

public import LeanVM.Spec.Guest
public import LeanVM.Guest.Start
public import LeanVM.Guest.Core
public import LeanVM.Protocol.EndToEnd.Complete.Public

/-!
# The public input

`bytecode` and the run's start are `Start.lean`'s. `pub_loads`: a valid execution's memory holds the
two cells of the public input's digest at `g^0`, `g^1`, as `main` loads them through the pointer
`1` (`LoadHolds rd 1 0`, `LoadHolds rd 1 1`).
-/

namespace LeanVM.Guest.End

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Node
open LeanVM.Protocol LeanVM.Protocol.KeccakHash

@[expose] public section

theorem one_eq_ofK : (1 : E) = ofK 1 := rfl

/-- A word of the memory at `g^i` is a load through the pointer `1` at offset `i`. -/
theorem loadHolds_one {rd : Reader} {i : ℕ} {d : E} (h : rd (gpow i) = some d) :
    LoadHolds rd 1 i d := by
  refine ⟨(isInK_iff 1).mpr ⟨1, one_eq_ofK⟩, ?_⟩
  rw [one_eq_ofK, limb_ofK]
  simpa using h

/-- **The public input's cells**: a valid execution's memory holds the two cells of the public
input's digest at `g^0` and `g^1`. -/
theorem pub_loads {input : PublicInput} {t : Trace guest} (hv : ValidExecution guest input t) :
    LoadHolds t.image.read 1 0 (digestScalars (publicDigest input)).1 ∧
      LoadHolds t.image.read 1 1 (digestScalars (publicDigest input)).2 := by
  obtain ⟨⟨-, -, h0, h1⟩, -⟩ := hv
  rw [EndToEnd.Complete.digestScalars_publicDigest input]
  exact ⟨loadHolds_one h0, loadHolds_one h1⟩

end
end LeanVM.Guest.End
