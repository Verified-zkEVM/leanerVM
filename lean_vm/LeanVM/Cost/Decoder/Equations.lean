module

public import LeanVM.Cost.Decoder.Witness
import all LeanVM.Guest.B1.Main.Interface

/-!
# The guest decoder's compiled chain: the staged functions are the decoder's

The staged forms the chain compiles are the deployed decoder's functions, proved apart from the
compiled modules (their kernel checks stay small):

* `decWitStaged_eq : decWitStaged discreteLogTables = B1.Main.decWit`;
* `decWitNStaged_eq : decWitNStaged discreteLogTables readerTabs = Guest.Fast.decWitN`, the
  deployed decoder's witness at the frame map keyed by index (`Guest.Fast.decode_eq_numbered`).

The other restated functions' equations at the tables built (`…D_tables`, `kidOfStaged_tables`,
`dvWitND_tables`, `cursorLength_tables`, `gLogD_tables`; the readers' off arrays,
`xmssSigOfA_tabs`, `sphincsSigOfA_tabs`, `vsPiOfA_tabs`, in `Guest/Fast/`) are next to them.
-/

namespace LeanVM.Cost.Decoder

open LeanVM.Cost LeanVM.Parameters LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.B1.Main
open LeanVM.Protocol.Verifier LeanVM.Node LeanVM.Extraction.Fast

@[expose] public section

/-- **The staged witness is `decWit`**, at the tables built. -/
theorem decWitStaged_eq : decWitStaged discreteLogTables = decWit := by
  funext σ rd wX wS wD wV wA
  unfold decWitStaged decWitAt nodeWitnessOf kidsAt xmssHoldersAt sphincsHoldersAt xmssHolder
    xmssHolderAt sphincsHolder sphincsHolderAt daWitness aggArgs decWit
  simp only [nKidsD_tables, decKidD_tables, markOfD_tables, nRawXD_tables, nRawSD_tables,
    lxSlotsD_tables, kidOfStaged_tables, nDirectD_tables, gLogD_tables]

open LeanVM.Guest.Fast in
/-- **The staged witness is `decWitN`**, at the tables built. -/
theorem decWitNStaged_eq : decWitNStaged discreteLogTables readerTabs = decWitN := by
  funext σ rd Vn cl
  unfold decWitNStaged decWitN daAtFrame xmssAtFrame sphincsAtFrame proofAtFrame
  simp only [show readerTabs.xmss = xmssTabs from rfl, show readerTabs.sphincs = sphincsTabs from rfl,
    show readerTabs.whir = whirTabs from rfl, xmssSigOfA_tabs, sphincsSigOfA_tabs, vsPiOfA_tabs]
  rw [decWitStaged_eq, dvWitND_tables]
  rfl

end

end LeanVM.Cost.Decoder
