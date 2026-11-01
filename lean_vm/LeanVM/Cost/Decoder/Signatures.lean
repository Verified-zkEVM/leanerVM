module

public import LeanVM.Cost.Decoder.Kids
public import LeanVM.Guest.Fast.Xmss
public import LeanVM.Guest.Fast.Sphincs
public import LeanVM.Guest.Fast.Whir

/-!
# The guest decoder's compiled chain: the signatures and the children's proofs

The readers of a callee's witness off its check's frame, restated (`Guest/Fast/`, each proved
equal to the deployed decoder's reader there): a leanXMSS signature off `verify_lean_xmss`'
valuation (`xmssSigOfN`), a leanSPHINCS signature off `verify_sig_lean_sphincs`'
(`sphincsSigOfN`), a child's proof off `verify_sub`'s and the frame map keyed by index
(`vsPiOfN`, the cursor's length `cl` a parameter). Their tables' records are encoded by their
constructors (`Oq`, `OsCall`, `SCoord`).
-/

namespace LeanVM.Cost.Decoder

open LeanVM.Cost LeanVM.Parameters LeanVM.Guest.B1 LeanVM.Guest.Fast

@[expose] public section

cost_enc LeanVM.Guest.B1.Oq
cost_enc LeanVM.Guest.Fast.OsCall
cost_enc LeanVM.Guest.Fast.SCoord

/-! ## leanXMSS -/

/-! The tables and helpers the readers call, each under a name of its own (stable across the
chain's reallocations of on-demand indices). -/
cost_compile idxBelowC measure fun _ l _ _ ↦ l.length := idxBelow
cost_compile gLanesC := gLanes
cost_compile xFirstC := xFirst
cost_compile xRestC := xRest
cost_compile xLastC := xLast
cost_compile xSel0C := xSel0
cost_compile xPath0C := xPath0
cost_compile xSel1C := xSel1
cost_compile xPath1C := xPath1
cost_compile sibNC := sibN
cost_compile bitsNC measure fun _ _ n ↦ n := bitsN
set_option maxRecDepth 100000 in
cost_compile fkOffC := fkOff
cost_compile foldPosC := foldPos
set_option maxRecDepth 100000 in
cost_compile sCoordTabC := sCoordTab
cost_compile sCoord0C := sCoord0
cost_compile sSelC := sSel
cost_compile sFirstC := sFirst
cost_compile sRestC := sRest
cost_compile sLastC := sLast
cost_compile sPathC := sPath
cost_compile logGTC := logGT
cost_compile cwCellC := cwCell
cost_compile xPartNC := xPartN
cost_compile xmssSigOfNC := xmssSigOfN

/-! ## leanSPHINCS -/

set_option maxRecDepth 100000 in
cost_compile subOpeningNC := subOpeningN
cost_compile coordOpeningNC := coordOpeningN
cost_compile sphincsSigOfNC := sphincsSigOfN

/-! ## A child's proof -/

cost_compile bitsValC measure fun _ n ↦ n := LeanVM.Guest.Value.bitsVal
cost_compile memReadC := memRead
cost_compile posOfC := posOf
cost_compile oqRowC := oqRow
cost_compile OqRC := Oq.R
cost_compile digestOfCellsWC := LeanVM.Guest.B1.digestOfCells
cost_compile oqSibsOfC := oqSibsOf
cost_compile oqK1C := oqK1
cost_compile OqTszC := Oq.tsz
cost_compile rowLoC := rowLo
cost_compile OqGC := Oq.G
cost_compile OqDC := Oq.D
cost_compile oqKLC := oqKL
cost_compile OqBC := Oq.B
cost_compile OqChainLenC := Oq.chainLen
cost_compile oqCqC := oqCq
cost_compile oqEndC := oqEnd
cost_compile oqQueryWC := oqQueryW
cost_compile oqIterOfC := oqIterOf
cost_compile oqLoopArgsC := oqLoopArgs
cost_compile capSibC := LeanVM.Guest.B1.Whir.capSib
cost_compile capSibsOfC := LeanVM.Guest.B1.Whir.capSibsOf
cost_compile toOpeningC := LeanVM.Guest.B1.Whir.toOpening
cost_compile wordsAtC := LeanVM.Guest.B1.VerifySub.wordsAt
cost_compile vsOsArgsC := LeanVM.Guest.B1.VerifySub.vsOsArgs
cost_compile vsOsRetsC := LeanVM.Guest.B1.VerifySub.vsOsRets
cost_compile osWordsTabC := osWordsTab
set_option maxRecDepth 100000 in
cost_compile osCallsTabC := osCallsTab
cost_compile oqsOfNC := oqsOfN
cost_compile levelOsNC := levelOsN
cost_compile vsPiOfNC := vsPiOfN

end

end LeanVM.Cost.Decoder
