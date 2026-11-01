module

public import LeanVM.Cost.Decoder.Hints
public import LeanVM.Guest.Fast.Da

/-!
# The guest decoder's compiled chain: the DA matrix

`da_verify`'s witness off its callees' frames, keyed by the functions' indices
(`Guest.Fast.dvWitN`, equal to `Da.dvWit` at the frame map re-keyed by `decoderFunctionName`,
`Guest.Fast.dvWitN_eq`): the rows of the cells' symbols and the vector of the columns' weights,
compiled part by part.
-/

namespace LeanVM.Cost.Decoder

open LeanVM.Cost LeanVM.Parameters LeanVM.Guest.Fast

@[expose] public section

cost_compile colNumC := colNum
cost_compile rowNumC := rowNum
cost_compile dvColVNC := dvColVN
cost_compile dvRowVNC := dvRowVN
cost_compile dvSymsPNC := dvSymsPN
cost_compile dvWsPNC := dvWsPN
set_option maxHeartbeats 4000000 in
cost_compile dvWitNC := dvWitN

end

end LeanVM.Cost.Decoder
