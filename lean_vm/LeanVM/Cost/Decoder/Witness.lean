module

public import LeanVM.Cost.Decoder.Frames
public import LeanVM.Guest.Located.Replay
public import LeanVM.Guest.Glob
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
  certificate's cells).
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
cost_compile decWitNC := decWitNStaged

/-! ## `main`'s valuation -/

/-- The word of `main`'s value `v` at `fp = 1`, read with `rd`. -/
def mainVal (rd : Reader) (v : V) : E :=
  LeanVM.Guest.Located.wordWith rd 1 ((LeanVM.Guest.Data.cert1_w0_0 ++ LeanVM.Guest.Data.cert1_w1_0).getD v.idx 0)


set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
cost_compile mainValC := mainVal

end

end LeanVM.Cost.Decoder
