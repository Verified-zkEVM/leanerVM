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
`verify_sig_lean_sphincs`' and its three `sp_wots` frames (`sphincsSigOfA`), a child's proof off
`verify_sub`'s and the frame map keyed by index (`vsPiOfA`, `vsPiOfA_tabs`, the cursor's length
`cl` a parameter). Their tables (`XmssTabs`, `SpTabs`, `WhirTabs`: the lanes of `g^k`, the
chain starts, the selectors and path bases, `open_stacked`'s stream words and calls) are arrays the decoder's top level builds once
(`readerTabsC`, `Frames.lean`) and passes; consecutive cells are read by stepping the address
(`wordsFrom`), each query's position once (`oqQueryAt`), the loop's frames at the next power of
`g` (`oqItersFrom`). The compiled names stay the readers' (`xmssSigOfNC`, `sphincsSigOfNC`,
`vsPiOfNC`, `oqsOfNC`, …). Their records are encoded by their constructors (`Oq`, `OsCall`, the
tables).
-/

namespace LeanVM.Cost.Decoder

open LeanVM.Cost LeanVM.Parameters LeanVM.Guest.B1 LeanVM.Guest.Fast

@[expose] public section

cost_enc LeanVM.Guest.B1.Oq
cost_enc LeanVM.Guest.Fast.OsCall
cost_enc LeanVM.Guest.Fast.XmssTabs
cost_enc LeanVM.Guest.Fast.SpTabs
cost_enc LeanVM.Guest.Fast.WhirTabs

/-- The leanSPHINCS layers as the reader builds them (`depFin3`, a function of `Fin 3`): the array
of their values (`depFinEncoding`), stated at `Fin 3`, which instance search does not unify with
`Sphincs.Layer = Fin layerCount`. -/
instance spLayersEnc : MachineEncoding ((i : Fin 3) → Sphincs.LayerSignature i) :=
  @depFinEncoding 3 (fun i ↦ Sphincs.LayerSignature i) fun i ↦ instMachineEncodingLayerSignature_1 i

/-! ## The tables

The literals and helpers the readers call, each under a name of its own (stable across the
chain's reallocations of on-demand indices), compiled before their callers. -/

cost_compile gLanesC := gLanes
cost_compile xFirstC := xFirst
cost_compile xRestC := xRest
cost_compile xLastC := xLast
cost_compile xSel0C := xSel0
cost_compile xPath0C := xPath0
cost_compile xSel1C := xSel1
cost_compile xPath1C := xPath1
cost_compile spSelC := spSel
cost_compile spFirstC := spFirst
cost_compile spRestC := spRest
cost_compile spLastC := spLast
cost_compile osWordsTabC := osWordsTab
set_option maxRecDepth 100000 in
cost_compile osCallsTabC := osCallsTab
cost_compile tabAC := tabA
cost_compile offAtAC := offAtA
cost_compile idxBelowC measure fun _ l _ _ ↦ l.length := idxBelow
cost_compile logGTWithC := logGTWith
cost_compile xmssTabsC := xmssTabs
cost_compile spTabsC := spTabs
cost_compile whirTabsC := whirTabs

/-! ## leanXMSS -/

cost_compile sibNC := sibN
cost_compile bitsNC measure fun _ _ n ↦ n := bitsN
cost_compile cwCellC := cwCellA
cost_compile xPartNC := xPartA
cost_compile xmssSigOfNC := xmssSigOfA

/-! ## leanSPHINCS -/

cost_compile forsOpeningAC := forsOpeningA
cost_compile spCtrC := spCtr
cost_compile spPathC := spPath
cost_compile spBitC := spBit
cost_compile layerAC := layerA
cost_compile sphincsSigOfNC := sphincsSigOfA
cost_compile spWotsArgsC := spWotsArgs
cost_compile spWotsRetsC := spWotsRets

/-! ## A child's proof -/

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
cost_compile oqChC := oqCh
cost_compile oqCqC := oqCq
cost_compile oqEndC := oqEnd
cost_compile oqE1C := oqE1
cost_compile oqLoopArgsC := oqLoopArgs
cost_compile memReadC := memRead
cost_compile capSibC := LeanVM.Guest.B1.Whir.capSib
cost_compile capSibsOfC := LeanVM.Guest.B1.Whir.capSibsOf
cost_compile toOpeningC := LeanVM.Guest.B1.Whir.toOpening
cost_compile vsOsArgsC := LeanVM.Guest.B1.VerifySub.vsOsArgs
cost_compile vsOsRetsC := LeanVM.Guest.B1.VerifySub.vsOsRets
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
