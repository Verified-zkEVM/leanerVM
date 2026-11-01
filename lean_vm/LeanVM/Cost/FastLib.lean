module

public import LeanVM.Cost.CompPolyLib
public import LeanVM.Protocol.Extraction.Fast.Transcript
import all LeanVM.Protocol.Extraction.Fast.SortedMap
import all LeanVM.Protocol.Extraction.Fast.Lookup
import all LeanVM.Protocol.Extraction.Fast.Replay

/-!
# The fast extractor's data, for the compiler

The encodings of the fast extractor's types (constructors of their data fields), and the measures
its well-founded recursions decrease, registered for the compiler (`cost_measure`).
-/

namespace LeanVM.Cost.FastLib

open LeanVM.Cost LeanVM.Extraction.Fast

public section

instance : Enc Hits where
  enc | .none => .ctor 0 [] | .one x => .ctor 1 [enc x] | .many => .ctor 2 []

instance {α β : Type} [Ord α] [Enc α] [Enc β] : Enc (Level α β) :=
  ⟨fun l ↦ .ctor 0 [enc l.weight, enc l.entries]⟩

instance {α β : Type} [Ord α] [Enc α] [Enc β] : Enc (SortedMap α β) :=
  ⟨fun m ↦ .ctor 0 [enc m.levels]⟩

instance : Enc ReplayFast := ⟨fun τ ↦ .ctor 0 [enc τ.fwd, enc τ.inv, enc τ.caps, enc τ.paths]⟩

instance {R : Type} [Zero R] [Enc R] : Enc (CompPoly.CBivariate R) :=
  inferInstanceAs (Enc (CompPoly.CPolynomial (CompPoly.CPolynomial R)))

cost_enc CompPoly.GuruswamiSudan.GSInterpParams
cost_enc CompPoly.GuruswamiSudan.GSExecParams
cost_enc CompPoly.GuruswamiSudan.GSReceivedWord
cost_enc CompPoly.PolynomialMatrix.RowChoice
cost_enc CompPoly.GuruswamiSudan.LeeOSullivan.RowChoice

cost_measure searchIn := fun _ _ _ _ _ lo hi ↦ hi - lo

cost_measure mergeNewer := fun _ _ _ a b ↦ a.length + b.length

cost_measure findLane := fun _ _ lo hi ↦ hi - lo

end

end LeanVM.Cost.FastLib
