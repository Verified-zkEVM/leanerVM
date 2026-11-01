module

public import LeanVM.Cost.Bounds.Basic
public import LeanVM.Cost.DecoderSpec

/-!
# The decoder program's inclusions the budget's proof uses

`includes` on the decoder's top's list of bodies (a membership proof per body) takes about a second
each: each inclusion the budget's proof (`Budget.lean`) uses is a lemma of its own, here, as the
extractor's (`Bounds/TopIncludes.lean`).
-/

namespace LeanVM.Cost.Bounds.Guest

open LeanVM.Cost LeanVM.Cost.Decoder

public section

theorem includes_budget_readerClosure : Includes decoderProgram Decoder.decTopTablesC.lam0.costDeps := by
  have := decoderProgram_includes
  includes

theorem includes_budget_discreteLogWith : Includes decoderProgram Decoder.discreteLogWithC.costDeps := by
  have := decoderProgram_includes
  includes

theorem includes_budget_powBelow : Includes decoderProgram powBelowC.costDeps := by
  have := decoderProgram_includes
  includes

theorem includes_budget_preTestLam : Includes decoderProgram Decoder.decTopStatesC.lam1.costDeps := by
  have := decoderProgram_includes
  includes

theorem includes_budget_preTestAt : Includes decoderProgram preTestAtC.costDeps := by
  have := decoderProgram_includes
  includes

theorem includes_budget_entryTableT : Includes decoderProgram entryTableTC.costDeps := by
  have := decoderProgram_includes
  includes

theorem includes_budget_getPc : Includes decoderProgram getPcC.costDeps := by
  have := decoderProgram_includes
  includes

theorem includes_budget_frameAt : Includes decoderProgram Decoder.frameAtC.costDeps := by
  have := decoderProgram_includes
  includes

theorem includes_budget_mainValLam : Includes decoderProgram Decoder.decTopStatesC.lam0.costDeps := by
  have := decoderProgram_includes
  includes

theorem includes_budget_mainVal : Includes decoderProgram Decoder.mainValC.costDeps := by
  have := decoderProgram_includes
  includes

theorem includes_budget_decWitN : Includes decoderProgram Decoder.decWitNC.costDeps := by
  have := decoderProgram_includes
  includes

theorem includes_budget_frameLam : Includes decoderProgram Decoder.decTopFramesC.lam0.costDeps := by
  have := decoderProgram_includes
  includes

theorem includes_budget_cursorLam : Includes decoderProgram Decoder.decTopFramesC.lam1.costDeps := by
  have := decoderProgram_includes
  includes

theorem includes_budget_gLogD : Includes decoderProgram Decoder.gLogDC.costDeps := by
  have := decoderProgram_includes
  includes

theorem includes_budget_cursorLength : Includes decoderProgram cursorLengthC.costDeps := by
  have := decoderProgram_includes
  includes

theorem includes_budget_preTable : Includes decoderProgram Decoder.preTableC.costDeps := by
  have := decoderProgram_includes
  includes

theorem includes_budget_pcTableT : Includes decoderProgram Decoder.pcTableTC.costDeps := by
  have := decoderProgram_includes
  includes

end

end LeanVM.Cost.Bounds.Guest
