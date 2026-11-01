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

cost_compile oqsOfNC := oqsOfN
cost_compile levelOsNC := levelOsN
cost_compile vsPiOfNC := vsPiOfN

end

end LeanVM.Cost.Decoder
