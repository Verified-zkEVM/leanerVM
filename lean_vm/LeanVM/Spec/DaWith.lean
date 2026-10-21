/-
  LeanVM.Spec.DaWith

  The DA claim for any hash: LeanDA's commitment, membership challenges and vector digest with the
  hash a parameter in any monad and the padding digests parameters, the deployed ones recovered.
-/

module

public import LeanVM.Spec.Da

/-!
# The DA claim, for any hash

LeanDA (`formal/lean_da`) defines its algorithms with a pure hash `H : List UInt8 → Digest`. The
end-to-end security theorem (`docs/roadmap/e2e-security.md`) needs them answered by a log: every
hash made, then the value. So the algorithms the DA claim uses are transcribed here in any monad
(`…With`), and the deployed padding digests are parameters (`pc`, `pr`; deployed: the hashes of
the zero cell and the zero row, which the guest bakes as constants, design D5). At `m = Id` they
are LeanDA's own (`commitCodewordsWith_id`, `membershipVectorWith_id`, `vectorDigestWith_id`).
`Witness.OpensWith` is `Witness.Opens` over an `Option`-valued hash. The tree is built with
`nodes.length` as fuel, which is enough (`treeRootFuel_id`).
-/

namespace LeanVM.Da

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Blake2sHash

@[expose] public section

section With

variable {m : Type → Type} [Monad m] (HD : List UInt8 → m LeanDa.Digest)

/-- `LeanDa.listCellDigest` with the hash `HD`. -/
def listCellDigestWith (row : List K) (j : ℕ) : m LeanDa.Digest :=
  HD ((LeanDa.listCell row j).flatMap LeanDa.kBytes)

/-- `LeanDa.rowDigest` with the hash `HD`. -/
def rowDigestWith (row : List K) : m LeanDa.Digest := do
  let ds ← (List.range LeanDa.payloadCells).mapM fun j ↦ listCellDigestWith HD row j
  HD (ds.flatMap fun d ↦ d.toList)

/-- `LeanDa.treeLevel` with the hash `HD`. -/
def treeLevelWith (nodes : List LeanDa.Digest) : m (List LeanDa.Digest) :=
  (List.range (nodes.length / 2)).mapM fun i ↦
    HD (LeanDa.pairBytes (nodes.getD (2 * i) default) (nodes.getD (2 * i + 1) default))

/-- `LeanDa.treeRoot` with the hash `HD`, at most `fuel` levels. -/
def treeRootFuel : ℕ → List LeanDa.Digest → m LeanDa.Digest
  | 0, nodes => pure (nodes.headD default)
  | fuel + 1, nodes =>
    if nodes.length ≤ 1 then pure (nodes.headD default) else do
      let next ← treeLevelWith HD nodes
      treeRootFuel fuel next

/-- `LeanDa.treeRoot` with the hash `HD`. -/
def treeRootWith (nodes : List LeanDa.Digest) : m LeanDa.Digest :=
  treeRootFuel HD nodes.length nodes

/-- **`LeanDa.commitCodewords` with the hash `HD`** and the padding digests `pc` (a zero cell) and
`pr` (a zero row). -/
def commitCodewordsWith (pc pr : LeanDa.Digest) (rows : List (List K)) : m LeanDa.Digest := do
  let n := LeanDa.nPad rows.length
  let rds ← rows.mapM (rowDigestWith HD)
  let rowTree ← treeRootWith HD (rds ++ List.replicate (n - rows.length) pr)
  let cols ← ((List.range LeanDa.cellsPerRow).flatMap fun j ↦ (List.range n).map fun i ↦ (i, j)).mapM
    fun ij ↦ if h : ij.1 < rows.length then listCellDigestWith HD rows[ij.1] ij.2 else pure pc
  let columnTree ← treeRootWith HD cols
  HD (LeanDa.pairBytes rowTree columnTree)

/-- `LeanDa.compressWords` with the hash `HD`. -/
def compressWordsWith (state : LeanDa.Digest) (words : List K) : m LeanDa.Digest :=
  HD (state.toList ++ words.flatMap LeanDa.kBytes)

/-- `LeanDa.squeezes` with the hash `HD`. -/
def squeezesWith : ℕ → LeanDa.Digest → m (List E)
  | 0, _ => pure []
  | n + 1, state => do
    let state ← compressWordsWith HD state [0, 0, 0, LeanDa.K.ofBits 2]
    let rest ← squeezesWith n state
    pure (LeanDa.ofLimbs (LeanDa.word state 0) (LeanDa.word state 1) (LeanDa.word state 2) :: rest)

/-- `LeanDa.membershipChallenges` with the hash `HD`. -/
def membershipChallengesWith (root : LeanDa.Digest) : m (List E) := do
  let state ← HD LeanDa.label
  let state ← compressWordsWith HD state [LeanDa.word root 0, LeanDa.word root 1, 0, LeanDa.K.ofBits 1]
  let state ← compressWordsWith HD state [LeanDa.word root 2, LeanDa.word root 3, 0, LeanDa.K.ofBits 1]
  squeezesWith HD LeanDa.logK state

/-- `LeanDa.membershipVector` with the hash `HD`. -/
def membershipVectorWith (root : LeanDa.Digest) : m (List E) :=
  LeanDa.dualCodeword <$> membershipChallengesWith HD root

/-- `LeanDa.vectorDigest` with the hash `HD`. -/
def vectorDigestWith (vector : List E) : m LeanDa.Digest :=
  HD ((vector.flatMap fun e ↦ [LeanDa.limb e 0, LeanDa.limb e 1, LeanDa.limb e 2]).flatMap
    LeanDa.kBytes)

end With

/-- The hash of a log of this project's digests as LeanDA's: `toBytes` of the answer. -/
def daHash {m : Type → Type} [Monad m] (H : List UInt8 → m Digest) (x : List UInt8) :
    m LeanDa.Digest :=
  toBytes <$> H x

/-- **The vector digest of a root, with the hash `H`** (`vectorDigestOf`). -/
def vectorDigestOfWith {m : Type → Type} [Monad m] (H : List UInt8 → m Digest) (root : Digest) :
    m LeanDa.Digest := do
  vectorDigestWith (daHash H) (← membershipVectorWith (daHash H) (toBytes root))

/-- **`Witness.Opens` over an `Option`-valued hash**, the padding digests `pc`, `pr` parameters:
every hash answered, and the claim true of the answers. -/
def Witness.OpensWith (H : List UInt8 → Option Digest) (pc pr : LeanDa.Digest) (root vd : Digest)
    (w : Witness) : Prop :=
  1 ≤ w.rows.length ∧ w.rows.length ≤ LeanDa.maxRows ∧
    (∀ row ∈ w.rows, row.length = 2 ^ LeanDa.logM) ∧
    commitCodewordsWith (daHash H) pc pr w.rows = some (toBytes root) ∧
    w.vector.length = 2 ^ LeanDa.logM ∧
    vectorDigestWith (daHash H) w.vector = some (toBytes vd) ∧
    ∀ row ∈ w.rows, LeanDa.dot (fun b ↦ w.vector.getD b 0) (fun b ↦ row.getD b 0) = 0

/-! ## The deployed algorithms, recovered -/

theorem mapM_id {α β : Type} (f : α → Id β) : ∀ l : List α,
    (l.mapM (m := Id) f : List β) = l.map fun a ↦ Id.run (f a)
  | [] => rfl
  | a :: l => by rw [List.mapM_cons, List.map_cons, ← mapM_id f l]; rfl

section Id

variable (H : List UInt8 → LeanDa.Digest)

theorem treeLevelWith_id (nodes : List LeanDa.Digest) :
    Id.run (treeLevelWith (m := Id) H nodes) = LeanDa.treeLevel H nodes := by
  simp only [treeLevelWith, mapM_id, LeanDa.treeLevel]
  rfl

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

theorem treeRootWith_id (nodes : List LeanDa.Digest) :
    Id.run (treeRootWith (m := Id) H nodes) = LeanDa.treeRoot H nodes :=
  treeRootFuel_id H _ nodes le_rfl

theorem rowDigestWith_id (row : List K) :
    Id.run (rowDigestWith (m := Id) H row) = LeanDa.rowDigest H row := by
  simp only [rowDigestWith, listCellDigestWith, LeanDa.rowDigest, LeanDa.listCellDigest]
  rfl

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

theorem membershipVectorWith_id (root : LeanDa.Digest) :
    Id.run (membershipVectorWith (m := Id) H root) = LeanDa.membershipVector H root := by
  have hsq : ∀ (n : ℕ) (st : LeanDa.Digest),
      Id.run (squeezesWith (m := Id) H n st) = LeanDa.squeezes H n st := by
    intro n
    induction n with
    | zero => intro st; rfl
    | succ n ih =>
      intro st
      simp only [squeezesWith, LeanDa.squeezes, compressWordsWith, LeanDa.compressWords]
      show _ :: Id.run (squeezesWith (m := Id) H n _) = _
      rw [ih]
  simp only [membershipVectorWith, membershipChallengesWith, LeanDa.membershipVector,
    LeanDa.membershipChallenges, compressWordsWith, LeanDa.compressWords]
  show LeanDa.dualCodeword (Id.run (squeezesWith (m := Id) H _ _)) = _
  rw [hsq]

theorem vectorDigestWith_id (vector : List E) :
    Id.run (vectorDigestWith (m := Id) H vector) = LeanDa.vectorDigest H vector :=
  rfl

theorem vectorDigestOfWith_id (root : Digest) :
    Id.run (vectorDigestOfWith (m := Id) blake2sBytes root) = vectorDigestOf root := by
  simp only [vectorDigestOfWith, vectorDigestOf]
  show Id.run (vectorDigestWith (m := Id) blake2s
    (Id.run (membershipVectorWith (m := Id) blake2s _))) = _
  rw [membershipVectorWith_id, vectorDigestWith_id]

end Id

end
end LeanVM.Da
