module

public import LeanVM.Cost.Decoder.Frames
public import LeanVM.Guest.Located.Replay
public import LeanVM.Guest.Glob
import all LeanVM.Guest.Located.Replay
import all LeanVM.Guest.Glob

/-!
# The guest decoder's compiled chain: the witness and `main`'s valuation

* **`decWitN`, staged** (`decWitNStaged`, the logarithm's tables `D` and the readers' tables `R`
  given; `Equations.lean`: `decWitNStaged discreteLogTables readerTabs = Guest.Fast.decWitN`):
  `decWitStaged` (`Staged.lean`) with each callee's witness off its frame (`Frames.lean`), by
  partial application; `Guest.Fast.decWitN` is the deployed decoder's witness at the frame map
  keyed by index (`decWitN_eq`, `decode_eq_numbered`);
* **`main`'s valuation** off the reader (`mainVal`: `EndFinal.mainValWith`'s word, by the
  certificate's cells); `mainValAt rd mainLocs` (`mainValAt_eq`), the locations an array built
  once (`mainLocs`), for the top level's valuation.
-/

namespace LeanVM.Cost.Decoder

open LeanVM.Cost LeanVM.Parameters LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.B1.Main
open LeanVM.Protocol.Verifier LeanVM.Node

@[expose] public section

open LeanVM.Guest.Fast in
/-- **`decWitN`, staged**: `decWitStaged` with each callee's witness off its frame, by partial
application. -/
noncomputable def decWitNStaged (D : LeanVM.Extraction.Fast.DiscreteLogTables) (R : ReaderTabs)
    (σ : Val) (rd : Reader) (Vn : NFrames) (cl : E → E → ℕ) : NodeWitness :=
  decWitStaged D σ rd (xmssAtFrame R Vn) (sphincsAtFrame R σ Vn) (daAtFrame D Vn)
    (proofAtFrame R rd Vn cl) (hintsAtFrame rd Vn)

set_option maxHeartbeats 4000000 in
-- a frame cell's word, under a name of its own (the bounds name it, not an index)
cost_compile wordWithC := LeanVM.Guest.Located.wordWith
cost_compile decWitNC := decWitNStaged

/-! ## `main`'s valuation -/

/-- The word of `main`'s value `v` at `fp = 1`, read with `rd`. -/
def mainVal (rd : Reader) (v : V) : E :=
  LeanVM.Guest.Located.wordWith rd 1 ((LeanVM.Guest.Data.cert1_w0_0 ++ LeanVM.Guest.Data.cert1_w1_0).getD v.idx 0)


set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
cost_compile mainValC := mainVal

/-- The cells' locations of `main`'s values in its frame (`mainVal`'s two lists), as an array:
built once by the decoder's top level, so that each value is one array read, not a walk of the
appended lists (about `420` entries). -/
def mainLocs : Array ℕ := (LeanVM.Guest.Data.cert1_w0_0 ++ LeanVM.Guest.Data.cert1_w1_0).toArray

/-- The word of `main`'s value `v`, its location read off the array `locs` (`mainVal` at
`locs = mainLocs`, `mainValAt_eq`). -/
def mainValAt (rd : Reader) (locs : Array ℕ) (v : V) : E :=
  LeanVM.Guest.Located.wordWith rd 1 (locs.getD v.idx 0)

/-- **Off the array, `main`'s valuation is `mainVal`.** -/
theorem mainValAt_eq (rd : Reader) : mainValAt rd mainLocs = mainVal rd := by
  funext v
  simp only [mainValAt, mainVal, mainLocs, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
    List.getD_eq_getElem?_getD]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
cost_compile mainLocsC := mainLocs
cost_compile mainValAtC := mainValAt

end

end LeanVM.Cost.Decoder
