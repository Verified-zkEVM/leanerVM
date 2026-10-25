/-
  LeanVM.Facts.DaWith

  The DA claims with any hash and permutation (`Statement/LeanVmGuest.lean`) at Keccak-256
  and Keccak-f[1600] are the deployed ones: the `*_id` lemmas.
  The definitions are the statement's; these are proofs.
-/

module

public import Statement.LeanVmGuest
public import LeanDa.Scheme
public import LeanVM.Fast.Da
public import LeanVM.Fast.Keccak
public import LeanVM.Fast.CubicExt
public import LeanVM.Fast.FieldWords

namespace LeanVM.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash

@[expose] public section

/-- `mapM` in `Id` is `map`. -/
theorem mapM_id {α β : Type} (f : α → Id β) : ∀ l : List α,
    (l.mapM (m := Id) f : List β) = l.map fun a ↦ Id.run (f a)
  | [] => rfl
  | a :: l => by rw [List.mapM_cons, List.map_cons, ← mapM_id f l]; rfl

section Id

variable (H : List UInt8 → LeanDa.Digest) (P : LeanDa.Lanes → LeanDa.Lanes)

/-- A tree level with the pure hash is `LeanDa.treeLevel`. -/
theorem treeLevelWith_id (nodes : List LeanDa.Digest) :
    Id.run (treeLevelWith (m := Id) H nodes) = LeanDa.treeLevel H nodes := by
  simp only [treeLevelWith, mapM_id, LeanDa.treeLevel]
  rfl

/-- A tree level halves the nodes. -/
theorem length_treeLevel (nodes : List LeanDa.Digest) :
    (LeanDa.treeLevel H nodes).length = nodes.length / 2 := by
  simp [LeanDa.treeLevel]

/-- Enough fuel builds the tree. -/
theorem treeRootFuel_id : ∀ (fuel : ℕ) (nodes : List LeanDa.Digest), nodes.length ≤ fuel →
    Id.run (treeRootFuel (m := Id) H fuel nodes) = LeanDa.treeRoot H nodes
  | 0, nodes, h => by
    rw [LeanDa.treeRoot]
    simp only [show nodes.length ≤ 1 by omega, ↓reduceIte]
    rfl
  | fuel + 1, nodes, h => by
    rw [treeRootFuel, LeanDa.treeRoot]
    split
    · rfl
    · rename_i hn
      have hl := length_treeLevel H nodes
      show Id.run (treeRootFuel (m := Id) H fuel (Id.run (treeLevelWith (m := Id) H nodes))) = _
      rw [treeLevelWith_id, treeRootFuel_id fuel _ (by omega)]

/-- The tree's root with the pure hash is `LeanDa.treeRoot`. -/
theorem treeRootWith_id (nodes : List LeanDa.Digest) :
    Id.run (treeRootWith (m := Id) H nodes) = LeanDa.treeRoot H nodes :=
  treeRootFuel_id H _ nodes le_rfl

/-- A row's digest with the pure hash is `LeanDa.rowDigest`. -/
theorem rowDigestWith_id (row : List K) :
    Id.run (rowDigestWith (m := Id) H row) = LeanDa.rowDigest H row := by
  simp only [rowDigestWith, listCellDigestWith, LeanDa.rowDigest, LeanDa.listCellDigest]
  rfl

/-- The commitment with the pure hash and LeanDA's padding digests is `LeanDa.commitCodewords`. -/
theorem commitCodewordsWith_id (rows : List (List K)) :
    Id.run (commitCodewordsWith (m := Id) H (LeanDa.paddingCell H) (LeanDa.paddingRow H) rows) =
      LeanDa.commitCodewords H rows := by
  simp only [commitCodewordsWith, LeanDa.commitCodewords]
  show H (LeanDa.pairBytes (Id.run (treeRootWith (m := Id) H _))
    (Id.run (treeRootWith (m := Id) H _))) = _
  rw [treeRootWith_id, treeRootWith_id]
  congr 3
  · rw [mapM_id]
    exact congrArg (· ++ _) (List.map_congr_left fun row _ ↦ rowDigestWith_id H row)
  · rw [mapM_id, List.map_flatMap]
    congr 1
    funext j
    rw [List.map_map]
    congr 1

/-- The sponge's samples with the pure permutation are `LeanDa.Sponge.samples`. -/
theorem spongeSamplesWith_id : ∀ (n : ℕ) (s : LeanDa.Sponge),
    Id.run (spongeSamplesWith (m := Id) P n s) = LeanDa.Sponge.samples P n s
  | 0, _ => rfl
  | n + 1, s => by
    show _ :: Id.run (spongeSamplesWith (m := Id) P n _) = _
    rw [spongeSamplesWith_id n]
    rfl

/-- Observing with the pure permutation is `LeanDa.Sponge.observe`. -/
theorem spongeObserveWith_id (s : LeanDa.Sponge) (x : E) :
    Id.run (spongeObserveWith (m := Id) P s x) = LeanDa.Sponge.observe P s x := by
  simp only [spongeObserveWith, spongeAbsorbWith, LeanDa.Sponge.observe, LeanDa.Sponge.absorb]
  split <;> rfl

/-- The membership vector with the pure hash and permutation is `LeanDa.membershipVector`. -/
theorem membershipVectorWith_id (root : LeanDa.Digest) :
    Id.run (membershipVectorWith (m := Id) H P root) = LeanDa.membershipVector H P root := by
  show LeanDa.dualCodeword (Id.run (spongeSamplesWith (m := Id) P _
    (Id.run (spongeObserveWith (m := Id) P (Id.run (spongeObserveWith (m := Id) P
      (Id.run (spongeFromLabelWith (m := Id) H P LeanDa.label)) _)) _)))) = _
  rw [spongeObserveWith_id, spongeObserveWith_id, spongeSamplesWith_id]
  rfl

/-- The vector digest with the pure hash is `LeanDa.vectorDigest`. -/
theorem vectorDigestWith_id (vector : List E) :
    Id.run (vectorDigestWith (m := Id) H vector) = LeanDa.vectorDigest H vector := by
  show H ((Id.run ((List.range LeanDa.cellsPerRow).mapM (m := Id)
    (columnDigestWith (m := Id) H vector))).flatMap fun d ↦ d.toList) = _
  rw [mapM_id]
  rfl

end Id

/-- Keccak-256, as LeanDA's hash, is `keccak`. -/
theorem daHash_id : daHash (m := Id) keccak256 = keccak := rfl

/-- Keccak-f[1600], as LeanDA's permutation, is `keccakLanes`. -/
theorem daPerm_id : daPerm (m := Id) keccakF = keccakLanes := rfl

/-- The vector digest of a root with Keccak is `vectorDigestOf`. -/
theorem vectorDigestOfWith_id (root : Digest) :
    Id.run (vectorDigestOfWith (m := Id) keccak256 keccakF root) = vectorDigestOf root := by
  unfold vectorDigestOfWith
  rw [daHash_id, daPerm_id]
  show Id.run (vectorDigestWith (m := Id) keccak
    (Id.run (membershipVectorWith (m := Id) keccak keccakLanes (toBytes root)))) = _
  rw [membershipVectorWith_id, vectorDigestWith_id]
  rfl

end
end LeanVM.Da
