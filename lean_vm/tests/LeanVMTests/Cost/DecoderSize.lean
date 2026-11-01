import LeanVM.Cost.DecoderSpec

/-!
# Tests: the guest decoder program's size

The compiled guest decoder's program (`LeanVM.Cost.decoderProgram`, `Cost/DecoderSpec.lean`): its
exact size, `785159`, of which the guest's frame cells are `749835`, and its top's index;
`Cost/DecoderSize.lean` proves the size at most
`784277 + 2·(decTopC.costIdx - decTopC.costDeps.length)`, the exact size, within
`guestDecoderSizeBound` (`785500`, slack `341`), as `LeanVMTests/Cost/Efficient.lean` records the extractor's.
-/

namespace LeanVMTests.Cost.DecoderSize

open LeanVM.Cost LeanVM.Cost.Decoder

#guard decoderProgram.size == 785159
#guard decTopC.costIdx == 848
#guard 784277 + 2 * (decTopC.costIdx - decTopC.costDeps.length) == 785159
#guard decoderProgram.size ≤ LeanVM.Node.guestDecoderSizeBound

end LeanVMTests.Cost.DecoderSize
