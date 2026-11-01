module

public import LeanVM.Cost.Decoder.Witness
import all LeanVM.Guest.B1.Main.Interface

/-!
# The guest decoder's compiled chain: the staged functions are the decoder's

The staged forms the chain compiles are the deployed decoder's functions, proved apart from the
compiled modules (their kernel checks stay small):

* `decWitStaged_eq : decWitStaged discreteLogTables = B1.Main.decWit`;
* `decWitNStaged_eq : decWitNStaged discreteLogTables = Guest.Fast.decWitN`, the deployed
  decoder's witness at the frame map keyed by index (`Guest.Fast.decode_eq_numbered`).

The other restated functions' equations at the tables built (`…D_tables`, `kidOfStaged_tables`,
`dvWitND_tables`, `cursorLength_tables`, `gLogD_tables`) are next to them.
-/

namespace LeanVM.Cost.Decoder

open LeanVM.Cost LeanVM.Parameters LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.B1.Main
open LeanVM.Protocol.Verifier LeanVM.Node LeanVM.Extraction.Fast

@[expose] public section

/-- **The staged witness is `decWit`**, at the tables built. -/
theorem decWitStaged_eq : decWitStaged discreteLogTables = decWit := by
  funext σ rd wX wS wD wV wA
  rw [decWitStaged_eq_lists]
  unfold nodeWitnessOf kidsAt xmssHoldersAt sphincsHoldersAt xmssHolder
    xmssHolderAt sphincsHolder sphincsHolderAt daWitness aggArgs decWit
  simp only [nKidsD_tables, decKidD_tables, markOfD_tables, nRawXD_tables, nRawSD_tables,
    lxSlotsD_tables, kidOfStaged_tables, nDirectD_tables, gLogD_tables]

/-- **The staged witness is `decWitN`**, at the tables built. -/
theorem decWitNStaged_eq : decWitNStaged discreteLogTables = LeanVM.Guest.Fast.decWitN := by
  funext σ rd Vn cl
  unfold decWitNStaged LeanVM.Guest.Fast.decWitN daAtFrame
  rw [decWitStaged_eq, dvWitND_tables]
  rfl

end

end LeanVM.Cost.Decoder
