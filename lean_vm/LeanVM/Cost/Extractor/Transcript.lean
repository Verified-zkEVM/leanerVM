module

public import LeanVM.Cost.FastLib
public import LeanVM.Cost.Samples.CommittedLeaves
public import LeanVM.Protocol.Extraction.Fast.Transcript
import all LeanVM.Protocol.Extraction.Fast.Transcript
import all LeanVM.Protocol.Extraction.Fast.Replay
import all LeanVM.Protocol.Extraction.Fast.Lookup
import all LeanVM.Protocol.Extraction.Fast.SortedMap
import all Statement.Extractor

/-!
# The transcript's index and the committed word, compiled

`transcriptIndex qs L` (`Fast/Transcript.lean`: the replay in sorted maps, the evaluations of at
most `L` bytes, their first answers and the preimage index) and `leafAt` (a position of the
committed word). The committed leaves (`subtreeLeavesWith (preimageIn idx)`) are the sample
`committedLeavesC` (`Cost/Samples/CommittedLeaves.lean`).
-/

namespace LeanVM.Cost.Extractor

open LeanVM.Cost LeanVM.Parameters LeanVM.Extraction LeanVM.Extraction.Fast
open LeanVM.Protocol.Compile LeanVM.Protocol.KeccakHash LeanVM.Semantics LeanVM.Cost.FastLib

public section

attribute [local instance] lexOrd

cost_compile replayStepC := ReplayFast.step

cost_compile keccakUnpaddedC := keccakUnpaddedFast

cost_compile keccakEvaluationsC := keccakEvaluationsFast

cost_compile firstAnswersC := firstAnswers

cost_compile preimageIndexC := preimageIndex

cost_compile answerPairsC := @answerPairs

cost_compile transcriptIndexC := transcriptIndex

cost_compile leafAtC := leafAt

end

end LeanVM.Cost.Extractor
