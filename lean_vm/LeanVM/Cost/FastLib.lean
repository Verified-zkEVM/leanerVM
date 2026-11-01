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

open LeanVM.Cost LeanVM.Extraction.Fast LeanVM.Parameters

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
cost_enc CompPoly.CBivariate.Monomial
cost_enc LeanVM.Protocol.Compile.Sponge
cost_enc LeanVM.Protocol.Compile.ProgState
cost_enc LeanVM.Protocol.Verifier.Placement
cost_enc LeanVM.Protocol.Verifier.Form
cost_enc LeanVM.Protocol.Verifier.BusBlock
cost_enc LeanVM.Protocol.Verifier.Layout
cost_enc LeanVM.Parameters.Whir.Level
cost_enc LeanVM.Semantics.Registers

/-- Equality of registers: of both fields. -/
theorem decideEqRegisters {F : Type} [DecidableEq F] (x y : LeanVM.Semantics.Registers F)
    {inst : Decidable (x = y)} : @decide (x = y) inst = (decide (x.pc = y.pc) && decide (x.fp = y.fp)) := by
  obtain ⟨_, _⟩ := x; obtain ⟨_, _⟩ := y; simp

cost_rewrite decideEqRegisters

/-- Membership in `K`: the two upper limbs zero. -/
theorem decideIsInK (x : E) {inst : Decidable (IsInK x)} :
    @decide (IsInK x) inst = decide (x.limb 1 = 0 ∧ x.limb 2 = 0) :=
  decide_eq_decide.2 Iff.rfl

cost_rewrite decideIsInK

/-- Canonical 128-bit values: the top limb zero. -/
theorem decideIsCanonical128 (x : E) {inst : Decidable (IsCanonical128 x)} :
    @decide (IsCanonical128 x) inst = decide (x.limb 2 = 0) :=
  decide_eq_decide.2 Iff.rfl

cost_rewrite decideIsCanonical128

open LeanVM.Semantics in
/-- The Keccak relation: its two conditions. -/
theorem decideKeccakCells (input : Fin 13 → E) (inOdd : Bool) (output : Fin 13 → E) (outOdd : Bool)
    {inst : Decidable (KeccakCellsRelation input inOdd output outOdd)} :
    @decide (KeccakCellsRelation input inOdd output outOdd) inst =
      decide ((∀ c, IsCanonical128 (input c)) ∧
        ∀ c, output c = cellsOfState (keccakF1600 (stateOfCells input inOdd)) outOdd c) :=
  decide_eq_decide.2 Iff.rfl

cost_rewrite decideKeccakCells

cost_measure searchIn := fun _ _ _ _ _ lo hi ↦ hi - lo

cost_measure mergeNewer := fun _ _ _ a b ↦ a.length + b.length

cost_measure findLane := fun _ _ lo hi ↦ hi - lo

end

end LeanVM.Cost.FastLib
