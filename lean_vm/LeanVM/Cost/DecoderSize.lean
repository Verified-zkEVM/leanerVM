module

public import LeanVM.Cost.DecoderProgram

/-!
# The guest decoder's program: its indices and its size, by evaluation

A firewall (`AGENTS.md`), as `Cost/ExtractorSize.lean` is the extractor's: the kernel
evaluations over the decoder program's bodies, in a module of their own that imports only the
program's definition, so that no edit of a proof rebuilds them. For the program
`decoderProgramOf j deps` (`Cost/DecoderProgram.lean`) of a compiled top `j` with its bodies
`deps`, two evaluations by `decide +kernel`:

* the indices increase from the entry's `0` (`increasingFrom 0 (deps.map (·.1))`): the program
  holds its bodies and its entry (`decoderProgramOf_includes`, `decoderProgramOf_entry`);
* the bound `size_ofList_le` gives, the bodies' sizes and two per index, at most a measured
  number: the program's size (`decoderProgramOf_size_le`), then `guestDecoderSizeBound`.

**Skeleton.** The decoder's top is not compiled yet: the evaluations below measure the program
of the compiled replay (`replayStatesOfC`, `Decoder/Replay.lean`, the largest piece so far) in its
place: at most the bodies' sizes (`1764`) plus two per index up to the top's, `replayStatesOfC`'s
own (the last index allocated; so the bound names no index, which moves when a module before it in
the chain gains a function); its exact size is `3156` at index `768`. Once the top `decTopC` is compiled, its program replaces the replay's
(`decTopC.costIdx`, `decTopC.costDeps`), the measured number with it, and `guestDecoderSizeBound` is set to
the size rounded up to a power of two (`Statement/Theorems.lean`).
-/

namespace LeanVM.Cost

open LeanVM.Cost.Decoder

public section

/-- The bodies' indices increase from the entry's `0`. -/
theorem replayProgram_indices_increasing :
    increasingFrom 0 (replayStatesOfC.costDeps.map (·.1)) = true := by
  decide +kernel

/-- The bound of `size_ofList_le` on the program's size, evaluated. -/
theorem replayProgramBodies_size_bound :
    ((decoderProgramBodiesOf replayStatesOfC.costIdx replayStatesOfC.costDeps).map
        fun p ↦ p.2.size).sum +
      2 * (((decoderProgramBodiesOf replayStatesOfC.costIdx replayStatesOfC.costDeps).map
        (·.1)).foldr max 0 + 1) ≤ 1764 + 2 * (replayStatesOfC.costIdx + 1) := by
  decide +kernel

/-- **The program's size**, evaluated. -/
theorem replayProgram_size_le_measured :
    (decoderProgramOf replayStatesOfC.costIdx replayStatesOfC.costDeps).size ≤
      1764 + 2 * (replayStatesOfC.costIdx + 1) :=
  decoderProgramOf_size_le replayProgramBodies_size_bound

end

end LeanVM.Cost
