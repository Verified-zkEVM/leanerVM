module

public import LeanVM.Cost.Machine
public import Statement.LeanVm
public import LeanVM.Parameters.Field
public import CompPoly.Univariate.Basic

/-!
# Values of the cost machine for the extractor's data

`Enc α` encodes an `α` as a machine value. The encoding the end statement reads (`Enc`, its
instances for the extractor's input and output, `encode`, `decodeExecution`) is the statement's,
`Statement/CostMachine.lean`; here, the instances only the compiler needs (`UInt8`, `Unit`,
`Char`, `String`, `Ordering`, `Option`, `Array`, CompPoly's polynomials, `Id`, subtypes) and the
proof that decoding inverts encoding (`decodeExecution_enc`).
-/

namespace LeanVM.Cost

open LeanVM LeanVM.Parameters LeanVM.Semantics Common LeanVM.Protocol.Compile

@[expose] public section

instance : Enc UInt8 := ⟨fun x ↦ .word x.toUInt64⟩
instance : Enc Unit := ⟨fun _ ↦ .ctor 0 []⟩

/-- A character: its code point. -/
instance : Enc Char := ⟨fun c ↦ .nat c.toNat⟩

/-- A string: the list of its characters. -/
instance : Enc String := ⟨fun s ↦ enc s.toList⟩

instance : Enc Ordering where
  enc | .lt => .ctor 0 [] | .eq => .ctor 1 [] | .gt => .ctor 2 []

instance {α : Type} [Enc α] : Enc (Option α) where
  enc | none => .ctor 0 [] | some a => .ctor 1 [enc a]

instance {α : Type} [Enc α] : Enc (Array α) := ⟨fun a ↦ .arr (a.map enc)⟩

instance {α : Type} [Enc α] : Enc (CompPoly.CPolynomial.Raw α) := inferInstanceAs (Enc (Array α))

/-- The identity monad: the value. -/
instance {α : Type} [Enc α] : Enc (Id α) := inferInstanceAs (Enc α)

/-- A subtype: its value. -/
instance {α : Type} [Enc α] {p : α → Prop} : Enc (Subtype p) := ⟨fun x ↦ enc x.val⟩

instance {α : Type} [Zero α] [Enc α] : Enc (CompPoly.CPolynomial α) :=
  inferInstanceAs (Enc { p : CompPoly.CPolynomial.Raw α // CompPoly.CPolynomial.Raw.IsCanonical p })

theorem decodeE_enc (x : E) : decodeE (enc x) = some x := by
  simp only [enc, decodeE, show ∀ a : K, K.ofLane a.lane = a from fun _ ↦ rfl, ofLimbs_limb]

theorem mapM_decodeE (l : List E) : (l.map enc).mapM decodeE = some l := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [List.mapM_cons, decodeE_enc, ih]

/-- **Decoding inverts encoding.** -/
theorem decodeExecution_enc (prog : Semantics.Program) (t : Execution prog) :
    decodeExecution prog (enc t) = some t := by
  obtain ⟨κ, mem, steps⟩ := t
  have hm : ((Array.ofFn fun i ↦ enc (mem i)).toList.mapM decodeE) = some (List.ofFn mem) := by
    have : (List.ofFn fun i ↦ enc (mem i)) = (List.ofFn mem).map enc := by
      rw [List.map_ofFn]; rfl
    rw [Array.toList_ofFn, this, mapM_decodeE]
  show decodeExecution prog (.ctor 0 [.nat κ, .arr (Array.ofFn fun i ↦ enc (mem i)), .nat steps]) = _
  simp only [decodeExecution]
  rw [hm]
  simp only [List.length_ofFn, ↓reduceDIte, Option.some.injEq, Execution.mk.injEq, true_and,
    and_true, heq_eq_eq]
  funext i
  simp

end

end LeanVM.Cost
