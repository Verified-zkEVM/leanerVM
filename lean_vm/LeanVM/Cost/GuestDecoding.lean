module

public import LeanVM.Cost.Encoding
public import Statement.Theorems

/-!
# Decoding a guest decoding inverts its encoding

`decodeDecoded` (`Statement/Theorems.lean`) parses the guest decoder program's output: a seed,
a statement and a witness, each type by its `Dec` instance. Here `LawfulDec α`, that `Dec α`
inverts `Enc α`, for every type of a decoding, and **`decodeDecoded_enc`**:
`decodeDecoded (enc d) = some d`.
-/

namespace LeanVM.Cost

open LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node

@[expose] public section

/-- **`Dec α` inverts `Enc α`.** -/
class LawfulDec (α : Type) [Enc α] [Dec α] : Prop where
  dec_enc : ∀ a : α, Dec.dec (enc a) = some a

export LawfulDec (dec_enc)

attribute [simp] dec_enc

instance : LawfulDec UInt64 := ⟨fun _ ↦ rfl⟩
instance : LawfulDec ℕ := ⟨fun _ ↦ rfl⟩
instance {n : ℕ} : LawfulDec (Fin n) := ⟨fun i ↦ by
  show (if h : i.val < n then some (⟨i.val, h⟩ : Fin n) else none) = some i
  simp [i.isLt]⟩
instance : LawfulDec Bool := ⟨fun b ↦ by cases b <;> rfl⟩

instance {w : ℕ} : LawfulDec (BitVec w) :=
  ⟨fun v ↦ by show some (BitVec.ofNat w v.toNat) = some v; simp⟩

instance : LawfulDec K := ⟨fun _ ↦ rfl⟩
instance : LawfulDec E := ⟨decodeE_enc⟩

theorem mapM_dec_map_enc {α : Type} [Enc α] [Dec α] [LawfulDec α] (l : List α) :
    (l.map enc).mapM (Dec.dec (α := α)) = some l := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [List.mapM_cons, ih]

theorem toList?_ofList (l : List Val) : Val.toList? (Val.ofList l) = some l := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [Val.ofList, Val.toList?, ih]

instance {α : Type} [Enc α] [Dec α] [LawfulDec α] : LawfulDec (List α) :=
  ⟨fun l ↦ by
    show (Val.toList? (Val.ofList (l.map enc))).bind (·.mapM Dec.dec) = some l
    rw [toList?_ofList, Option.bind_some, mapM_dec_map_enc]⟩

instance {α β : Type} [Enc α] [Dec α] [LawfulDec α] [Enc β] [Dec β] [LawfulDec β] :
    LawfulDec (α × β) :=
  ⟨fun ⟨a, b⟩ ↦ by
    show (do pure ((← Dec.dec (enc a)), (← Dec.dec (enc b))) : Option (α × β)) = _
    simp⟩

@[simp] theorem decodeOption_encodeOption {α : Type} [Enc α] [Dec α] [LawfulDec α]
    (o : Option α) :
    decodeOption (encodeOption o) = some o := by
  cases o with
  | none => rfl
  | some a => show (Dec.dec (enc a)).map some = _; simp

theorem mapM_dec_toList_map {α : Type} [Enc α] [Dec α] [LawfulDec α] (xs : Array α) :
    (xs.map enc).toList.mapM (Dec.dec (α := α)) = some xs.toList := by
  rw [Array.toList_map, mapM_dec_map_enc]

instance {α : Type} [Enc α] [Dec α] [LawfulDec α] {n : ℕ} : LawfulDec (Vector α n) :=
  ⟨fun ⟨xs, h⟩ ↦ by
    show (match (xs.map enc).toList.mapM Dec.dec with
      | some ys => if h : ys.length = n then some ⟨ys.toArray, by simpa using h⟩ else none
      | none => none : Option (Vector α n)) = _
    rw [mapM_dec_toList_map]
    simp [h]⟩

instance {α : Type} [Enc α] [Dec α] [LawfulDec α] {n : ℕ} : LawfulDec (Fin n → α) :=
  ⟨fun f ↦ by
    have hm : (Array.ofFn fun i ↦ enc (f i)).toList.mapM (Dec.dec (α := α)) = some (List.ofFn f) := by
      have : (List.ofFn fun i ↦ enc (f i)) = (List.ofFn f).map enc := by
        rw [List.map_ofFn]; rfl
      rw [Array.toList_ofFn, this, mapM_dec_map_enc]
    show decFun (.arr (Array.ofFn fun i ↦ enc (f i))) = some f
    simp only [decFun]
    rw [hm]
    simp only [List.length_ofFn, ↓reduceDIte, Option.some.injEq]
    funext i
    simp⟩

instance : LawfulDec Opening := ⟨fun ⟨l, p⟩ ↦ by
  show (do pure ⟨← Dec.dec (enc l), ← Dec.dec (enc p)⟩ : Option Opening) = _; simp⟩

instance : LawfulDec Proof := ⟨fun ⟨s, o⟩ ↦ by
  show (do pure ⟨← Dec.dec (enc s), ← Dec.dec (enc o)⟩ : Option Proof) = _; simp⟩

instance : LawfulDec HashSig.PublicKey := ⟨fun ⟨r, p⟩ ↦ by
  show (do pure ⟨← Dec.dec (enc r), ← Dec.dec (enc p)⟩ : Option HashSig.PublicKey) = _; simp⟩

instance : LawfulDec LeanXmss.LayerSignature := ⟨fun ⟨r, c, p⟩ ↦ by
  show (do pure ⟨← Dec.dec (enc r), ← Dec.dec (enc c), ← Dec.dec (enc p)⟩ :
    Option LeanXmss.LayerSignature) = _
  simp⟩

instance : LawfulDec LeanXmss.Signature := ⟨fun ⟨i, l⟩ ↦ by
  show (do pure ⟨← Dec.dec (enc i), ← Dec.dec (enc l)⟩ : Option LeanXmss.Signature) = _; simp⟩

instance : LawfulDec Sphincs.SubOpening := ⟨fun ⟨v, p⟩ ↦ by
  show (do pure ⟨← Dec.dec (enc v), ← Dec.dec (enc p)⟩ : Option Sphincs.SubOpening) = _; simp⟩

instance : LawfulDec Sphincs.CoordOpening := ⟨fun ⟨s, t⟩ ↦ by
  show (do pure ⟨← Dec.dec (enc s), ← Dec.dec (enc t)⟩ : Option Sphincs.CoordOpening) = _; simp⟩

instance : LawfulDec Sphincs.Signature := ⟨fun ⟨r, f, c, v, p⟩ ↦ by
  show (do pure ⟨← Dec.dec (enc r), ← Dec.dec (enc f), ← Dec.dec (enc c), ← Dec.dec (enc v),
    ← Dec.dec (enc p)⟩ : Option Sphincs.Signature) = _
  simp⟩

instance : LawfulDec BytecodeClaim := ⟨fun ⟨p, v⟩ ↦ by
  show (do pure ⟨← Dec.dec (enc p), ← Dec.dec (enc v)⟩ : Option BytecodeClaim) = _; simp⟩

instance : LawfulDec DaClaim := ⟨fun ⟨r, v⟩ ↦ by
  show (do pure ⟨← Dec.dec (enc r), ← Dec.dec (enc v)⟩ : Option DaClaim) = _; simp⟩

instance : LawfulDec Da.MatrixWitness := ⟨fun ⟨r, v⟩ ↦ by
  show (do pure ⟨← Dec.dec (enc r), ← Dec.dec (enc v)⟩ : Option Da.MatrixWitness) = _; simp⟩

instance : LawfulDec Claims := ⟨fun ⟨x, s, d⟩ ↦ by
  show (do pure ⟨← Dec.dec (enc x), ← Dec.dec (enc s), ← Dec.dec (enc d)⟩ : Option Claims) = _
  simp⟩

instance : LawfulDec NodeStatement := ⟨fun ⟨c, d⟩ ↦ by
  show (do pure ⟨← Dec.dec (enc c), ← Dec.dec (enc d)⟩ : Option NodeStatement) = _; simp⟩

instance : LawfulDec Child := ⟨fun ⟨s, f, p⟩ ↦ by
  show (do pure ⟨← Dec.dec (enc s), ← Dec.dec (enc f), ← Dec.dec (enc p)⟩ : Option Child) = _
  simp⟩

instance {W : Type} [Enc W] [Dec W] [LawfulDec W] : LawfulDec (ClaimHolder W) :=
  ⟨fun h ↦ by
    cases h with
    | direct w => show (Dec.dec (enc w)).map ClaimHolder.direct = _; simp
    | child i => show (Dec.dec (enc i)).map (ClaimHolder.child (W := W)) = _; simp⟩

instance : LawfulDec BatchingHints := ⟨fun ⟨m, v⟩ ↦ by
  show (do pure ⟨← Dec.dec (enc m), ← Dec.dec (enc v)⟩ : Option BatchingHints) = _; simp⟩

instance : LawfulDec NodeWitness := ⟨fun ⟨c, x, s, d, h⟩ ↦ by
  show (do pure ⟨← Dec.dec (enc c), ← Dec.dec (enc x), ← Dec.dec (enc s),
    ← decodeOption (encodeOption d), ← Dec.dec (enc h)⟩ : Option NodeWitness) = _
  simp⟩

instance : LawfulDec Decoded := ⟨fun ⟨s, t, w⟩ ↦ by
  show (do pure ⟨← Dec.dec (enc s), ← Dec.dec (enc t), ← Dec.dec (enc w)⟩ : Option Decoded) = _
  simp⟩

/-- **Decoding a decoding inverts its encoding.** -/
theorem decodeDecoded_enc (d : Decoded) : decodeDecoded (enc d) = some d := dec_enc d

end

end LeanVM.Cost
