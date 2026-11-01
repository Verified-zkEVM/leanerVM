module

public import LeanVM.Cost.Encoding
public import Statement.Theorems

/-!
# Decoding a guest decoding inverts its encoding

`decodeDecoded` (`Statement/Theorems.lean`) parses the guest decoder program's output: a seed,
a statement and a witness, each type by its `MachineDecoding` instance. Here `LawfulMachineDecoding α`, that `MachineDecoding α`
inverts `MachineEncoding α`, for every type of a decoding, and **`decodeDecoded_enc`**:
`decodeDecoded (encodeValue d) = some d`.
-/

namespace LeanVM.Cost

open LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node

@[expose] public section

/-- **`MachineDecoding α` inverts `MachineEncoding α`.** -/
class LawfulMachineDecoding (α : Type) [MachineEncoding α] [MachineDecoding α] : Prop where
  decodeValue_encodeValue : ∀ a : α, decodeValue (encodeValue a) = some a

export LawfulMachineDecoding (decodeValue_encodeValue)

attribute [simp] decodeValue_encodeValue

instance : LawfulMachineDecoding UInt64 := ⟨fun _ ↦ rfl⟩
instance : LawfulMachineDecoding ℕ := ⟨fun _ ↦ rfl⟩
instance {n : ℕ} : LawfulMachineDecoding (Fin n) := ⟨fun i ↦ by
  show (if h : i.val < n then some (⟨i.val, h⟩ : Fin n) else none) = some i
  simp [i.isLt]⟩
instance : LawfulMachineDecoding Bool := ⟨fun b ↦ by cases b <;> rfl⟩

instance {w : ℕ} : LawfulMachineDecoding (BitVec w) :=
  ⟨fun v ↦ by show some (BitVec.ofNat w v.toNat) = some v; simp⟩

instance : LawfulMachineDecoding K := ⟨fun _ ↦ rfl⟩
instance : LawfulMachineDecoding E := ⟨decodeE_enc⟩

theorem mapM_decodeValue_map_encodeValue {α : Type} [MachineEncoding α] [MachineDecoding α] [LawfulMachineDecoding α] (l : List α) :
    (l.map encodeValue).mapM (decodeValue (α := α)) = some l := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [List.mapM_cons, ih]

theorem toList?_ofList (l : List MachineValue) : MachineValue.toList? (MachineValue.ofList l) = some l := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [MachineValue.ofList, MachineValue.toList?, ih]

instance {α : Type} [MachineEncoding α] [MachineDecoding α] [LawfulMachineDecoding α] : LawfulMachineDecoding (List α) :=
  ⟨fun l ↦ by
    show (MachineValue.toList? (MachineValue.ofList (l.map encodeValue))).bind (·.mapM decodeValue) = some l
    rw [toList?_ofList, Option.bind_some, mapM_decodeValue_map_encodeValue]⟩

instance {α β : Type} [MachineEncoding α] [MachineDecoding α] [LawfulMachineDecoding α] [MachineEncoding β] [MachineDecoding β] [LawfulMachineDecoding β] :
    LawfulMachineDecoding (α × β) :=
  ⟨fun ⟨a, b⟩ ↦ by
    show (do pure ((← decodeValue (encodeValue a)), (← decodeValue (encodeValue b))) : Option (α × β)) = _
    simp⟩

@[simp] theorem decodeOption_encodeOption {α : Type} [MachineEncoding α] [MachineDecoding α] [LawfulMachineDecoding α]
    (o : Option α) :
    decodeOption (encodeOption o) = some o := by
  cases o with
  | none => rfl
  | some a => show (decodeValue (encodeValue a)).map some = _; simp

theorem mapM_decodeValue_toList_map {α : Type} [MachineEncoding α] [MachineDecoding α] [LawfulMachineDecoding α] (xs : Array α) :
    (xs.map encodeValue).toList.mapM (decodeValue (α := α)) = some xs.toList := by
  rw [Array.toList_map, mapM_decodeValue_map_encodeValue]

instance {α : Type} [MachineEncoding α] [MachineDecoding α] [LawfulMachineDecoding α] {n : ℕ} : LawfulMachineDecoding (Vector α n) :=
  ⟨fun ⟨xs, h⟩ ↦ by
    show (match (xs.map encodeValue).toList.mapM decodeValue with
      | some ys => if h : ys.length = n then some ⟨ys.toArray, by simpa using h⟩ else none
      | none => none : Option (Vector α n)) = _
    rw [mapM_decodeValue_toList_map]
    simp [h]⟩

instance {α : Type} [MachineEncoding α] [MachineDecoding α] [LawfulMachineDecoding α] {n : ℕ} : LawfulMachineDecoding (Fin n → α) :=
  ⟨fun f ↦ by
    have hm : (Array.ofFn fun i ↦ encodeValue (f i)).toList.mapM (decodeValue (α := α)) = some (List.ofFn f) := by
      have : (List.ofFn fun i ↦ encodeValue (f i)) = (List.ofFn f).map encodeValue := by
        rw [List.map_ofFn]; rfl
      rw [Array.toList_ofFn, this, mapM_decodeValue_map_encodeValue]
    show decodeFiniteFunction (.arr (Array.ofFn fun i ↦ encodeValue (f i))) = some f
    simp only [decodeFiniteFunction]
    rw [hm]
    simp only [List.length_ofFn, ↓reduceDIte, Option.some.injEq]
    funext i
    simp⟩

instance : LawfulMachineDecoding Opening := ⟨fun ⟨l, p⟩ ↦ by
  show (do pure ⟨← decodeValue (encodeValue l), ← decodeValue (encodeValue p)⟩ : Option Opening) = _; simp⟩

instance : LawfulMachineDecoding Proof := ⟨fun ⟨s, o⟩ ↦ by
  show (do pure ⟨← decodeValue (encodeValue s), ← decodeValue (encodeValue o)⟩ : Option Proof) = _; simp⟩

instance : LawfulMachineDecoding HashSig.PublicKey := ⟨fun ⟨r, p⟩ ↦ by
  show (do pure ⟨← decodeValue (encodeValue r), ← decodeValue (encodeValue p)⟩ : Option HashSig.PublicKey) = _; simp⟩

instance : LawfulMachineDecoding LeanXmss.LayerSignature := ⟨fun ⟨r, c, p⟩ ↦ by
  show (do pure ⟨← decodeValue (encodeValue r), ← decodeValue (encodeValue c), ← decodeValue (encodeValue p)⟩ :
    Option LeanXmss.LayerSignature) = _
  simp⟩

instance : LawfulMachineDecoding LeanXmss.Signature := ⟨fun ⟨i, l⟩ ↦ by
  show (do pure ⟨← decodeValue (encodeValue i), ← decodeValue (encodeValue l)⟩ : Option LeanXmss.Signature) = _; simp⟩

instance : LawfulMachineDecoding Sphincs.SubOpening := ⟨fun ⟨v, p⟩ ↦ by
  show (do pure ⟨← decodeValue (encodeValue v), ← decodeValue (encodeValue p)⟩ : Option Sphincs.SubOpening) = _; simp⟩

instance : LawfulMachineDecoding Sphincs.CoordOpening := ⟨fun ⟨s, t⟩ ↦ by
  show (do pure ⟨← decodeValue (encodeValue s), ← decodeValue (encodeValue t)⟩ : Option Sphincs.CoordOpening) = _; simp⟩

instance : LawfulMachineDecoding Sphincs.Signature := ⟨fun ⟨r, f, c, v, p⟩ ↦ by
  show (do pure ⟨← decodeValue (encodeValue r), ← decodeValue (encodeValue f), ← decodeValue (encodeValue c), ← decodeValue (encodeValue v),
    ← decodeValue (encodeValue p)⟩ : Option Sphincs.Signature) = _
  simp⟩

instance : LawfulMachineDecoding BytecodeClaim := ⟨fun ⟨p, v⟩ ↦ by
  show (do pure ⟨← decodeValue (encodeValue p), ← decodeValue (encodeValue v)⟩ : Option BytecodeClaim) = _; simp⟩

instance : LawfulMachineDecoding DaClaim := ⟨fun ⟨r, v⟩ ↦ by
  show (do pure ⟨← decodeValue (encodeValue r), ← decodeValue (encodeValue v)⟩ : Option DaClaim) = _; simp⟩

instance : LawfulMachineDecoding Da.MatrixWitness := ⟨fun ⟨r, v⟩ ↦ by
  show (do pure ⟨← decodeValue (encodeValue r), ← decodeValue (encodeValue v)⟩ : Option Da.MatrixWitness) = _; simp⟩

instance : LawfulMachineDecoding Claims := ⟨fun ⟨x, s, d⟩ ↦ by
  show (do pure ⟨← decodeValue (encodeValue x), ← decodeValue (encodeValue s), ← decodeValue (encodeValue d)⟩ : Option Claims) = _
  simp⟩

instance : LawfulMachineDecoding NodeStatement := ⟨fun ⟨c, d⟩ ↦ by
  show (do pure ⟨← decodeValue (encodeValue c), ← decodeValue (encodeValue d)⟩ : Option NodeStatement) = _; simp⟩

instance : LawfulMachineDecoding Child := ⟨fun ⟨s, f, p⟩ ↦ by
  show (do pure ⟨← decodeValue (encodeValue s), ← decodeValue (encodeValue f), ← decodeValue (encodeValue p)⟩ : Option Child) = _
  simp⟩

instance {W : Type} [MachineEncoding W] [MachineDecoding W] [LawfulMachineDecoding W] : LawfulMachineDecoding (ClaimHolder W) :=
  ⟨fun h ↦ by
    cases h with
    | direct w => show (decodeValue (encodeValue w)).map ClaimHolder.direct = _; simp
    | child i => show (decodeValue (encodeValue i)).map (ClaimHolder.child (W := W)) = _; simp⟩

instance : LawfulMachineDecoding BatchingHints := ⟨fun ⟨m, v⟩ ↦ by
  show (do pure ⟨← decodeValue (encodeValue m), ← decodeValue (encodeValue v)⟩ : Option BatchingHints) = _; simp⟩

instance : LawfulMachineDecoding NodeWitness := ⟨fun ⟨c, x, s, d, h⟩ ↦ by
  show (do pure ⟨← decodeValue (encodeValue c), ← decodeValue (encodeValue x), ← decodeValue (encodeValue s),
    ← decodeOption (encodeOption d), ← decodeValue (encodeValue h)⟩ : Option NodeWitness) = _
  simp⟩

instance : LawfulMachineDecoding Decoded := ⟨fun ⟨s, t, w⟩ ↦ by
  show (do pure ⟨← decodeValue (encodeValue s), ← decodeValue (encodeValue t), ← decodeValue (encodeValue w)⟩ : Option Decoded) = _
  simp⟩

/-- **Decoding a decoding inverts its encoding.** -/
theorem decodeDecoded_enc (d : Decoded) : decodeDecoded (encodeValue d) = some d := decodeValue_encodeValue d

end

end LeanVM.Cost
