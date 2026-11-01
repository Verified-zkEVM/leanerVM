module

public import LeanVM.Cost.Decoder.Frames
public import LeanVM.Guest.Located.Replay
public import LeanVM.Guest.Glob
public import LeanVM.Cost.Decoder.GuestTables
import all LeanVM.Guest.Located.Replay
import all LeanVM.Guest.Glob

/-!
# The guest decoder's compiled chain: the witness and `main`'s valuation

* **`decWitN`, staged** (`decWitNStaged`, the logarithm's tables `D` given; `Equations.lean`:
  `decWitNStaged discreteLogTables = Guest.Fast.decWitN`):
  `decWitStaged` (`Staged.lean`) with each callee's witness off its frame (`Frames.lean`), by
  partial application; `Guest.Fast.decWitN` is the deployed decoder's witness at the frame map
  keyed by index (`decWitN_eq`, `decode_eq_numbered`);
* **`main`'s valuation** off the reader (`mainVal`: `EndFinal.mainValWith`'s word, by the
  certificate's cells, read off the literal table `guestLocs`).
-/

namespace LeanVM.Cost.Decoder

open LeanVM.Cost LeanVM.Parameters LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.B1.Main
open LeanVM.Protocol.Verifier LeanVM.Node

@[expose] public section

open LeanVM.Guest.Fast in
/-- **`decWitN`, staged**: `decWitStaged` with each callee's witness off its frame, by partial
application. -/
noncomputable def decWitNStaged (D : LeanVM.Extraction.Fast.DiscreteLogTables) (σ : Val)
    (rd : Reader) (Vn : NFrames) (cl : E → E → ℕ) : NodeWitness :=
  decWitStaged D σ rd (xmssAtFrame Vn) (sphincsAtFrame σ Vn) (daAtFrame D Vn)
    (proofAtFrame rd Vn cl) (hintsAtFrame rd Vn)

set_option maxHeartbeats 4000000 in
-- a frame cell's word, under a name of its own (the bounds name it, not an index)
cost_compile wordWithC := LeanVM.Guest.Located.wordWith
cost_compile decWitNC := decWitNStaged

/-! ## `main`'s valuation -/

/-- The word of `main`'s value `v` at `fp = 1`, read with `rd`: its cell's location read off
`main`'s row of the guest's table of certificates' cells (`guestLocs`, a literal of the program,
`Rule.literal`), in `O(1)` whatever `v` (`Equations.lean`: `mainVal_eq_cert`, the certificate's
cells `cert1_w0_0 ++ cert1_w1_0`, and `mainVal_eq`). -/
def mainVal (rd : Reader) (v : V) : E :=
  LeanVM.Guest.Located.wordWith rd 1 ((guestLocs.getD 1 #[]).getD v.idx 0)

cost_compile mainValC := mainVal

end

end LeanVM.Cost.Decoder
