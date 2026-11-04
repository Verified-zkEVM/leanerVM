module

public import LeanVM.Cost.Decoder.Staged
public import LeanVM.Guest.Fast.Main

/-!
# The guest decoder's compiled chain: each callee's witness off its frame

The frame map keyed by the functions' indices (`Guest.Fast.NFrames`, `FunctionNames.lean`), and
each callee's witness a function of its call's words, the compiled readers (`Signatures.lean`,
`Da.lean`, `Hints.lean`) at the frame map's value: `xmssAtFrame` (`verify_lean_xmss`, index `20`),
`sphincsAtFrame` (`verify_sig_lean_sphincs`, `21`), `daAtFrame` (`da_verify`, `26`),
`proofAtFrame` (`verify_sub`, `19`), `hintsAtFrame` (`aggregate_claims`, `32`). The signature
and proof readers read their tables off `R : ReaderTabs` (`Guest/Fast/Main.lean`), which the top
level builds once (`readerTabsC`) and passes.
-/

namespace LeanVM.Cost.Decoder

open LeanVM.Cost LeanVM.Parameters LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.B1.Main
open LeanVM.Protocol.Verifier LeanVM.Node

@[expose] public section

/-! ## Each callee's witness off its frame, keyed by index -/

open LeanVM.Guest.Fast in
/-- The leanXMSS signature checked at slot address `p` (`verify_lean_xmss`, index `20`), the
readers' tables `R` given. -/
noncomputable def xmssAtFrame (R : ReaderTabs) (Vn : NFrames) (p : E) : LeanXmss.Signature :=
  xmssSigOfA R.xmss (Vn 20 [p] [])

open LeanVM.Guest.Fast in
/-- The leanSPHINCS signature checked at slot address `p` (`verify_sig_lean_sphincs`, `21`), the
readers' tables `R` given. -/
noncomputable def sphincsAtFrame (R : ReaderTabs) (σ : Val) (Vn : NFrames) (p : E) :
    Sphincs.Signature :=
  sphincsSigOfA R.sphincs (Vn 21 [p, σ (.n 68)] [])

open LeanVM.Guest.Fast in
/-- The DA matrix `da_verify` (`26`) checks on the call's words, the logarithm's tables `D`
given. -/
noncomputable def daAtFrame (D : LeanVM.Extraction.Fast.DiscreteLogTables) (Vn : NFrames)
    (args rets : List E) : LeanVM.Da.MatrixWitness :=
  dvWitND D (Vn 26 args rets) Vn

open LeanVM.Guest.Fast in
/-- A child's proof at its `verify_sub` (`19`) call's words, the readers' tables `R` given. -/
noncomputable def proofAtFrame (R : ReaderTabs) (rd : Reader) (Vn : NFrames) (cl : E → E → ℕ)
    (args : List E) : LeanVM.Protocol.Compile.Proof :=
  vsPiOfA R.whir rd (Vn 19 args []) Vn cl

open LeanVM.Guest.Fast in
/-- The batching's hints at `aggregate_claims`' (`32`) call's words. -/
noncomputable def hintsAtFrame (rd : Reader) (Vn : NFrames) (args : List E) : BatchingHints :=
  aggHints rd (Vn 32 args [])

cost_enc LeanVM.Guest.Fast.ReaderTabs

-- the readers' tables, built: called once by the decoder's top level
cost_compile readerTabsC := LeanVM.Guest.Fast.readerTabs
cost_compile xmssAtFrameC := xmssAtFrame
cost_compile sphincsAtFrameC := sphincsAtFrame
cost_compile daAtFrameC := daAtFrame
cost_compile proofAtFrameC := proofAtFrame
cost_compile hintsAtFrameC := hintsAtFrame
end

end LeanVM.Cost.Decoder
