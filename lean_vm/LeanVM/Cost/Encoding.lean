module

public import LeanVM.Cost.Machine
public import Statement.LeanVm
public import LeanVM.Parameters.Field

/-!
# Values of the cost machine for the extractor's data

`Enc α` encodes an `α` as a machine value: words for `UInt64`, `UInt8` and `K`, natural numbers
for `ℕ` and `Fin n`, a constructor for each inductive type (its constructor's index as the tag,
its fields in order), arrays for `Array`, `Vector` and the functions of a finite domain the
statement uses (`Program.code`, `PublicInput.lanes`, an execution's memory).

* `encode prog input T proof`: the extractor's input, a constructor of the program, the public
  input, the transcript's permutation queries (§4.5: coins are dropped) and the proof;
* `decodeExecution prog`: a linear parse of an execution, the inverse of its encoding
  (`decodeExecution_enc`).
-/

namespace LeanVM.Cost

open LeanVM LeanVM.Parameters LeanVM.Semantics Common LeanVM.Protocol.Compile

@[expose] public section

/-- A machine encoding of `α`. -/
class Enc (α : Type) where
  /-- The value of `a`. -/
  enc : α → Val

export Enc (enc)

instance : Enc UInt64 := ⟨.word⟩
instance : Enc UInt8 := ⟨fun x ↦ .word x.toUInt64⟩
instance : Enc ℕ := ⟨.nat⟩
instance {n : ℕ} : Enc (Fin n) := ⟨fun i ↦ .nat i.val⟩
instance : Enc Bool := ⟨Val.ofBool⟩
instance : Enc Unit := ⟨fun _ ↦ .ctor 0 []⟩
instance : Enc K := ⟨fun a ↦ .word a.lane⟩
instance : Enc E := ⟨fun x ↦ .ctor 0 [enc (x.limb 0), enc (x.limb 1), enc (x.limb 2)]⟩

instance {α : Type} [Enc α] : Enc (Option α) where
  enc | none => .ctor 0 [] | some a => .ctor 1 [enc a]

instance {α : Type} [Enc α] : Enc (List α) := ⟨fun l ↦ .ofList (l.map enc)⟩

instance {α β : Type} [Enc α] [Enc β] : Enc (α × β) := ⟨fun p ↦ .ctor 0 [enc p.1, enc p.2]⟩

instance {α : Type} [Enc α] : Enc (Array α) := ⟨fun a ↦ .arr (a.map enc)⟩

instance {α : Type} [Enc α] {n : ℕ} : Enc (Vector α n) := ⟨fun v ↦ .arr (v.toArray.map enc)⟩

/-- A function of a finite domain, as the array of its values. -/
def encFun {α : Type} [Enc α] {n : ℕ} (f : Fin n → α) : Val := .arr (Array.ofFn fun i ↦ enc (f i))

instance {S : Type} [Enc S] : Enc (PermutationQuery S) where
  enc | .forward x => .ctor 0 [enc x] | .inverse y => .ctor 1 [enc y]

instance : Enc PublicInput := ⟨fun p ↦ .ctor 0 [encFun p.lanes]⟩

instance : Enc DerefMode where
  enc | .cell => .ctor 0 [] | .pc => .ctor 1 [] | .fp => .ctor 2 []

instance : Enc Instr where
  enc
    | .xor a b c => .ctor 0 [enc a, enc b, enc c]
    | .mulNative a b c => .ctor 1 [enc a, enc b, enc c]
    | .setConstant o k => .ctor 2 [enc o, enc k]
    | .deref a b c m => .ctor 3 [enc a, enc b, enc c, enc m]
    | .jump c d f => .ctor 4 [enc c, enc d, enc f]
    | .keccak om t b c o i j => .ctor 5 [encFun om, enc t, enc b, enc c, enc o, enc i, enc j]

instance : Enc Semantics.Program := ⟨fun p ↦ .ctor 0 [enc p.logSize, encFun p.code]⟩

instance : Enc Opening := ⟨fun o ↦ .ctor 0 [enc o.leaf, enc o.path]⟩

instance : Enc Proof := ⟨fun π ↦ .ctor 0 [enc π.stream, enc π.openings]⟩

instance {prog : Semantics.Program} : Enc (Execution prog) :=
  ⟨fun t ↦ .ctor 0 [enc t.logMemorySize, encFun t.memory, enc t.steps]⟩

/-- **The extractor's input.** -/
def encode (prog : Semantics.Program) (input : PublicInput) (T : OracleQueryLog) (proof : Proof) : Val :=
  .ctor 0 [enc prog, enc input, enc (permutationQueries T), enc proof]

/-! ## Decoding an execution -/

/-- A word of `E` from its encoding. -/
def decodeE : Val → Option E
  | .ctor 0 [.word a, .word b, .word c] => some (E.ofLimbs (K.ofLane a) (K.ofLane b) (K.ofLane c))
  | _ => none

/-- **An execution from its encoding**: the memory's size, its `2^κ` words, the steps; `none` on
anything else. -/
def decodeExecution (prog : Semantics.Program) : Val → Option (Execution prog)
  | .ctor 0 [.nat κ, .arr mem, .nat steps] =>
    match (mem.toList.mapM decodeE) with
    | some words =>
      if h : words.length = 2 ^ κ then
        some ⟨κ, fun i ↦ words[i.val]'(by rw [h]; exact i.isLt), steps⟩
      else none
    | none => none
  | _ => none

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
