/-
  LeanVM.Guest.EndLoc

  B2, located: a valid execution's memory holds `main`'s body at its frame, its calls located.
-/

module

public import LeanVM.Guest.EndFinal

/-!
# `main` at its frame

`mainRel_of` gives, from a halting run of the guest, `main`'s relation: some valuation satisfies
its body. `mainBodyL_of` gives the one the run gives: the words of `main`'s certificate's cells at
`fp = 1` (`Check.valG L 1 (certOf 1)`), each call located at a frame of the memory (`Check.RL`), the
contracts of every function holding for runs of any length (`funSpec_induction` over
`b2Sound.step`).
-/

namespace LeanVM.Guest.End

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Check LeanVM.Node
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.EndToEnd

@[expose] public section

/-- **B2 at `main`, located, for a halting run from `(g^0, 1)`**. -/
theorem mainBodyL_of_safe {κ : ℕ} {L : MemImage κ} (h16 : minLogMem ≤ κ) (h32 : κ ≤ maxLogMem)
    {k : ℕ} (hs : Safe guest L k ⟨gpow 0, 1⟩) :
    Stmt.HoldsList (RL coreProgram L certByName) L.read (valG L 1 (certOf 1)) (coreOf 1).body
      False (fun rs ↦ rs = []) := by
  obtain ⟨hjt, k', hk'⟩ := safe_jumpTables hs
  have hall : ∀ j, FunSpec guest L (contracts.entry j) (contracts.pre j κ L)
      (contracts.post j κ L) :=
    funSpec_induction (P := fun j ↦ contracts.pre j κ L) (Q := fun j ↦ contracts.post j κ L)
      (b2Sound.step L h16 h32)
  exact b2_mainL L h16 h32 hjt k' (fun j ↦ (hall j).lt k') hk'

/-- **B2 at `main`, located, for a valid execution**: `main`'s body under its frame's valuation,
and the public input's cells at `g^0`, `g^1`. -/
theorem mainBodyL_of {input : PublicInput} {t : Trace guest} (hv : ValidExecution guest input t) :
    Stmt.HoldsList (RL coreProgram t.image certByName) t.image.read (valG t.image 1 (certOf 1))
      (coreOf 1).body False (fun rs ↦ rs = []) ∧
    t.image.read 1 = some (digestScalars (publicDigest input)).1 ∧
    t.image.read g = some (digestScalars (publicDigest input)).2 := by
  have hs := safe_of_validExecution hv
  obtain ⟨⟨h16, h32, h0, h1⟩, -⟩ := hv
  have hd := Complete.digestScalars_publicDigest input
  exact ⟨mainBodyL_of_safe h16 h32 hs, by rw [hd, ← pow_zero g]; exact h0,
    by rw [hd, ← pow_one g]; exact h1⟩

end
end LeanVM.Guest.End
