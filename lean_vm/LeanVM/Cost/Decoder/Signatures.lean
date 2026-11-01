module

public import LeanVM.Cost.Decoder.Kids
public import LeanVM.Guest.Fast.Xmss
public import LeanVM.Guest.Fast.Sphincs
public import LeanVM.Guest.Fast.Whir

/-!
# The guest decoder's compiled chain: the signatures and the children's proofs

The readers of a callee's witness off its check's frame, restated off arrays (`Guest/Fast/`, each
proved equal to the deployed decoder's reader there at the tables built): a leanXMSS signature off
`verify_lean_xmss`' valuation (`xmssSigOfA`, `xmssSigOfA_tabs`), a leanSPHINCS signature off
`verify_sig_lean_sphincs`' (`sphincsSigOfA`, `sphincsSigOfA_tabs`), a child's proof off
`verify_sub`'s and the frame map keyed by index (`vsPiOfA`, `vsPiOfA_tabs`, the cursor's length
`cl` a parameter). Their tables (`XmssTabs`, `SphincsTabs`, `WhirTabs`: the lanes of `g^k`, the
chain starts, the selectors and path bases, the forest keys' cells, the coordinates' positions,
`open_stacked`'s stream words and calls) are arrays the decoder's top level builds once
(`readerTabsC`, `Frames.lean`) and passes; consecutive cells are read by stepping the address
(`wordsFrom`), each query's position once (`oqQueryAt`), the loop's frames at the next power of
`g` (`oqItersFrom`), each opening's exponents once (`subOpeningAt`, `coordOpeningAt`). The
compiled names stay the readers' (`xmssSigOfNC`, `sphincsSigOfNC`, `vsPiOfNC`, `oqsOfNC`, …).
Their records are encoded by their constructors (`Oq`, `OsCall`, `SCoord`, the tables).
-/

namespace LeanVM.Cost.Decoder

open LeanVM.Cost LeanVM.Parameters LeanVM.Guest.B1 LeanVM.Guest.Fast

@[expose] public section

cost_enc LeanVM.Guest.B1.Oq
cost_enc LeanVM.Guest.Fast.OsCall
cost_enc LeanVM.Guest.Fast.SCoord
cost_enc LeanVM.Guest.Fast.XmssTabs
cost_enc LeanVM.Guest.Fast.SphincsTabs
cost_enc LeanVM.Guest.Fast.WhirTabs

/-! ## The tables -/

cost_compile tabAC := tabA
cost_compile offAtAC := offAtA
cost_compile logGTWithC := logGTWith
set_option maxRecDepth 100000 in
cost_compile xmssTabsC := xmssTabs
set_option maxRecDepth 100000 in
cost_compile sphincsTabsC := sphincsTabs
set_option maxRecDepth 100000 in
cost_compile whirTabsC := whirTabs

/-! ## leanXMSS -/

cost_compile cwCellC := cwCellA
cost_compile xPartNC := xPartA
cost_compile xmssSigOfNC := xmssSigOfA

/-! ## leanSPHINCS -/

cost_compile subOpeningAtC := subOpeningAt
cost_compile subOpeningNC := subOpeningA
cost_compile coordOpeningAtC := coordOpeningAt
cost_compile coordOpeningNC := coordOpeningA
cost_compile sphincsSigOfNC := sphincsSigOfA

/-! ## A child's proof -/

cost_compile wordsFromC measure fun _ _ n ↦ n := wordsFrom
cost_compile bitsWC measure fun l ↦ l.length := bitsW
cost_compile posOfWC := posOfW
cost_compile oqQueryAtC := oqQueryAt
cost_compile oqQueryAC := oqQueryA
cost_compile oqIterAC := oqIterA
cost_compile oqItersFromC measure fun _ _ _ _ _ n _ ↦ n := oqItersFrom
cost_compile oqsOfNC := oqsOfA
cost_compile levelOsAtC := levelOsAt
cost_compile levelOsNC := levelOsA
cost_compile vsPiOfAtC := vsPiOfAt
cost_compile vsPiOfMC := vsPiOfM
cost_compile vsPiOfNC := vsPiOfA

end

end LeanVM.Cost.Decoder
