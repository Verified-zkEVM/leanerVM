import LeanVM.Cost.DecoderSpec

/-!
# Tests: the guest decoder program's size

The compiled guest decoder's program (`LeanVM.Cost.decoderProgram`, `Cost/DecoderSpec.lean`): its
exact size, `785041`, of which the guest's frame cells are `749835`, and its top's index;
`Cost/DecoderSize.lean` proves the size at most `784199 + 2·(decTopC.costIdx + 1)`, within
`guestDecoderSizeBound` (`786000`), as `LeanVMTests/Cost/Efficient.lean` records the extractor's.
-/

namespace LeanVMTests.Cost.DecoderSize

open LeanVM.Cost LeanVM.Cost.Decoder

#guard decoderProgram.size == 785041
#guard decTopC.costIdx == 842
#guard decoderProgram.size ≤ LeanVM.Node.guestDecoderSizeBound

end LeanVMTests.Cost.DecoderSize
