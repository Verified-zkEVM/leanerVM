module

public import LeanVM.Cost.DecoderProgram
public import LeanVM.Cost.Decoder.Top

/-!
# The guest decoder's program: its indices and its size, by evaluation

A firewall (`AGENTS.md`), as `Cost/ExtractorSize.lean` is the extractor's: the kernel
evaluations over the decoder program's bodies, in a module of their own that no proof imports, so
that no edit of a proof rebuilds them. It imports the program's definition and the compiled top,
and through them what the compiled chain imports (`Guest/Located/Replay.lean`,
`Guest/B1/Main/Interface.lean`, the extractor's `Cost/Extractor/Top.lean`), not the proofs that
use them. For the program `decoderProgramOf j deps` (`Cost/DecoderProgram.lean`) of a compiled
top `j` with its bodies `deps`, two evaluations by `decide +kernel`:

* the indices increase from the entry's `0` (`increasingFrom 0 (deps.map (·.1))`): the program
  holds its bodies and its entry (`decoderProgramOf_includes`, `decoderProgramOf_entry`);
* the bound `size_ofList_le` gives, the bodies' sizes and two per index, at most a measured
  number: the program's size (`decoderProgramOf_size_le`), then `guestDecoderSizeBound`.

For the compiled top `decTopC` (`Decoder/Top.lean`): at most the bodies' sizes (`784199`) plus two
per index up to the top's, `decTopC`'s own (the last index allocated; so the bound names no index,
which moves when a module before it in the chain gains a function): `785891` at index `845`. Its
exact size is `785083` (`LeanVMTests/Cost/DecoderSize.lean`), of which the guest's frame cells
(`guestLocs`, a literal held once, `guestLocsTable`) are `749835`. `guestDecoderSizeBound` is
`786000` (`Statement/Theorems.lean`): the exact size and a slack of `917`, room for one or two
leanXMSS signatures' encodings.
-/

namespace LeanVM.Cost

open LeanVM.Cost.Decoder

public section

/-- The bodies' indices increase from the entry's `0`. -/
theorem decoderProgram_indices_increasing :
    increasingFrom 0 (decTopC.costDeps.map (·.1)) = true := by
  decide +kernel

/-- The bound of `size_ofList_le` on the program's size, evaluated. -/
theorem decoderProgramBodies_size_bound :
    ((decoderProgramBodiesOf decTopC.costIdx decTopC.costDeps).map fun p ↦ p.2.size).sum +
      2 * (((decoderProgramBodiesOf decTopC.costIdx decTopC.costDeps).map (·.1)).foldr max 0 + 1) ≤
      784199 + 2 * (decTopC.costIdx + 1) := by
  decide +kernel

/-- **The program's size**, evaluated. -/
theorem decoderProgram_size_le_measured :
    (decoderProgramOf decTopC.costIdx decTopC.costDeps).size ≤
      784199 + 2 * (decTopC.costIdx + 1) :=
  decoderProgramOf_size_le decoderProgramBodies_size_bound

end

end LeanVM.Cost
