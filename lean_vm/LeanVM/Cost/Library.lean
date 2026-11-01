module

public import LeanVM.Cost.Compiler

/-!
# The compiler's library

Init's functions the extractor uses, compiled once for all types (their specs quantified over the
types' encodings); each recursive one with the measure its recursion decreases.
-/

namespace LeanVM.Cost.Library

open LeanVM.Cost

cost_compile listZipWith measure fun _ _ _ _ as _ ↦ as.length := @List.zipWith.{0, 0, 0}

cost_compile listFoldl measure fun _ _ _ _ l ↦ l.length := @List.foldl.{0, 0}

end LeanVM.Cost.Library
