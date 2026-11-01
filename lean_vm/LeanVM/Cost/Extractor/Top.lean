module

public import LeanVM.Cost.Extractor.Replay
public import LeanVM.Protocol.Extraction.Fast.Compiled
import all LeanVM.Protocol.Extraction.Fast.Compiled
import all Statement.Extractor
import all Statement.LeanIsa

/-!
# The extractor, compiled

`extractorTop` (`Fast/Compiled.lean`, equal to the statement's `transcriptExtractor` at the
permutation queries: `extractorTop_eq`), compiled on top of the chain of its parts (the decoder,
the transcript side, the candidate runner, the replay; each module reusing the earlier ones'
functions): only its own body and what no earlier module compiled (the bytecode's words) are
compiled here.
-/

namespace LeanVM.Cost.Extractor

open LeanVM.Cost LeanVM.Parameters LeanVM.Extraction LeanVM.Extraction.Fast LeanVM.Cost.FastLib

public section

-- The bytecode's words (`bytecodeWords`): sixteen slots of every instruction.
cost_compile bytecodeWordsC := LeanVM.bytecodeWords

-- The extractor, compiled.
set_option maxHeartbeats 20000000 in
cost_compile extractorC := extractorTop

end

end LeanVM.Cost.Extractor
