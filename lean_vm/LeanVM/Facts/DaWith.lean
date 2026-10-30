/-
  LeanVM.Facts.DaWith

  LeanDA's algorithms with any hash and permutation in any monad (`…With`), the vector digest the
  outer verifier derives from a root (`vectorDigestOf`), and, at Keccak-256 and Keccak-f[1600],
  the deployed ones: the `*_id` lemmas. Moved here from `Statement/LeanVmGuest.lean`, names kept:
  no end statement names them.

  LeanDA (`lean_da`, `LeanDa.Scheme`) defines its algorithms with a pure hash and a pure sponge
  permutation; the guest's proofs also need them answered by a log. The deployed padding digests
  are parameters (`pc`, `pr`; deployed: the hashes of the zero cell and the zero row, which the
  guest bakes as constants, `DA_PAD_CELL_*`, `DA_PAD_ROW_*`,
  `crates/rec_aggregation/src/aggregation.rs:2525-2528`). The tree is built with `nodes.length` as
  fuel, which is enough (`treeRootFuel_id`).
-/

module

public import Statement.LeanVmGuest
public import LeanDa.Scheme
public import Statement.Fast.Keccak
public import Statement.Fast.CubicExt
public import Statement.Fast.FieldWords

namespace LeanVM.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash

@[expose] public section

/-- **The vector digest of a root**, as the outer verifier derives it
(`vector_digest(membership_vector(root))`, `crates/verifier/src/da.rs:87-103`). -/
def vectorDigestOf (root : Digest) : Common.KDigest :=
  LeanDa.vectorDigest keccak (LeanDa.membershipVector keccak keccakF root.toBytes)

section With

variable {m : Type → Type} [Monad m] (HD : List UInt8 → m Common.KDigest)
  (PD : KState → m KState)

/-! ### The commitment -/

/-- `LeanDa.listCellDigest` with the hash `HD`. -/
def listCellDigestWith (row : List K) (j : ℕ) : m Common.KDigest :=
  HD ((LeanDa.listCell row j).flatMap LeanDa.kBytes)

/-- `LeanDa.rowDigest` with the hash `HD`. -/
def rowDigestWith (row : List K) : m Common.KDigest := do
  let ds ← (List.range LeanDa.payloadCells).mapM fun j ↦ listCellDigestWith HD row j
  HD (ds.flatMap fun d ↦ d.toList)

/-- `LeanDa.treeLevel` with the hash `HD`. -/
def treeLevelWith (nodes : List Common.KDigest) : m (List Common.KDigest) :=
  (List.range (nodes.length / 2)).mapM fun i ↦
    HD (LeanDa.pairBytes (nodes.getD (2 * i) default) (nodes.getD (2 * i + 1) default))

/-- `LeanDa.treeRoot` with the hash `HD`, at most `fuel` levels. -/
def treeRootFuel : ℕ → List Common.KDigest → m Common.KDigest
  | 0, nodes => pure (nodes.headD default)
  | fuel + 1, nodes =>
    if nodes.length ≤ 1 then pure (nodes.headD default) else do
      let next ← treeLevelWith HD nodes
      treeRootFuel fuel next

/-- `LeanDa.treeRoot` with the hash `HD`. -/
def treeRootWith (nodes : List Common.KDigest) : m Common.KDigest :=
  treeRootFuel HD nodes.length nodes

/-- **`LeanDa.commitCodewords` with the hash `HD`** and the padding digests `pc` (a zero cell) and
`pr` (a zero row). -/
def commitCodewordsWith (pc pr : Common.KDigest) (rows : List (List K)) : m Common.KDigest := do
  let n := LeanDa.nPad rows.length
  let rds ← rows.mapM (rowDigestWith HD)
  let rowTree ← treeRootWith HD (rds ++ List.replicate (n - rows.length) pr)
  let cols ← ((List.range LeanDa.cellsPerRow).flatMap fun j ↦
      (List.range n).map fun i ↦ (i, j)).mapM fun ij ↦
    if h : ij.1 < rows.length then listCellDigestWith HD rows[ij.1] ij.2 else pure pc
  let columnTree ← treeRootWith HD cols
  HD (LeanDa.pairBytes rowTree columnTree)

/-! ### The challenges' sponge -/

/-- `LeanDa.Sponge.newM` with the permutation `PD`. -/
def spongeNewWith (iv publicInput : Common.KDigest) : m LeanDa.Sponge := do
  let state ← PD (Vector.ofFn fun i : Fin 25 ↦
    if (i : ℕ) < 4 then (LeanDa.word iv i).lane
    else if (i : ℕ) < 8 then (LeanDa.word publicInput (i - 4)).lane else 0)
  pure ⟨state, []⟩

/-- `LeanDa.Sponge.fromLabelM` with the hash `HD` and the permutation `PD`. -/
def spongeFromLabelWith (label : List UInt8) : m LeanDa.Sponge := do
  spongeNewWith PD (← HD label) (Vector.replicate 32 0)

/-- `LeanDa.Sponge.duplexM` with the permutation `PD`. -/
def spongeDuplexWith (s : LeanDa.Sponge) : m LeanDa.Sponge := do
  let state ← PD (Vector.ofFn fun i : Fin 25 ↦
    if (i : ℕ) < LeanDa.rateLanes then ((LeanDa.rateWords s.pending).getD i 0).lane
    else s.state[i])
  pure ⟨state, []⟩

/-- `LeanDa.Sponge.absorbM` with the permutation `PD`. -/
def spongeAbsorbWith (s : LeanDa.Sponge) (x : E) (tag : K) : m LeanDa.Sponge := do
  let s ← if s.pending.length = LeanDa.rateScalars then spongeDuplexWith PD s else pure s
  pure ⟨s.state, s.pending ++ [(x, tag)]⟩

/-- `LeanDa.Sponge.observeM` with the permutation `PD`. -/
def spongeObserveWith (s : LeanDa.Sponge) (x : E) : m LeanDa.Sponge :=
  spongeAbsorbWith PD s x LeanDa.dsObserve

/-- `LeanDa.Sponge.sampleM` with the permutation `PD`. -/
def spongeSampleWith (s : LeanDa.Sponge) : m (E × LeanDa.Sponge) := do
  let s ← spongeDuplexWith PD s
  pure (LeanDa.ofLimbs (K.ofLane s.state[0]) (K.ofLane s.state[1]) (K.ofLane s.state[2]), s)

/-- `LeanDa.Sponge.samplesM` with the permutation `PD`. -/
def spongeSamplesWith : ℕ → LeanDa.Sponge → m (List E)
  | 0, _ => pure []
  | n + 1, s => do
    let (c, s) ← spongeSampleWith PD s
    let rest ← spongeSamplesWith n s
    pure (c :: rest)

/-- `LeanDa.membershipChallengesM` with the hash `HD` and the permutation `PD`. -/
def membershipChallengesWith (root : Common.KDigest) : m (List E) := do
  let s ← spongeFromLabelWith HD PD LeanDa.label
  let s ← spongeObserveWith PD s (LeanDa.ofLimbs (LeanDa.word root 0) (LeanDa.word root 1) 0)
  let s ← spongeObserveWith PD s (LeanDa.ofLimbs (LeanDa.word root 2) (LeanDa.word root 3) 0)
  spongeSamplesWith PD LeanDa.logK s

/-- `LeanDa.membershipVector` with the hash `HD` and the permutation `PD`. -/
def membershipVectorWith (root : Common.KDigest) : m (List E) :=
  LeanDa.dualCodeword <$> membershipChallengesWith HD PD root

/-! ### The vector digest -/

/-- `LeanDa.columnDigest` with the hash `HD`. -/
def columnDigestWith (vector : List E) (j : ℕ) : m Common.KDigest :=
  HD (LeanDa.limbBytes ((vector.drop (j * LeanDa.cellSymbols)).take LeanDa.cellSymbols))

/-- `LeanDa.vectorDigest` with the hash `HD`: the hash of the column digests. -/
def vectorDigestWith (vector : List E) : m Common.KDigest := do
  let ds ← (List.range LeanDa.cellsPerRow).mapM (columnDigestWith HD vector)
  HD (ds.flatMap fun d ↦ d.toList)

end With

/-- This project's hash as LeanDA's: the answer's bytes (`Digest.toBytes`). -/
def daHash {m : Type → Type} [Monad m] (H : List UInt8 → m Digest) (x : List UInt8) :
    m Common.KDigest :=
  Digest.toBytes <$> H x

/-- **The vector digest of a root, with the hash `H` and the permutation `F`**
(`vectorDigestOf`). -/
def vectorDigestOfWith {m : Type → Type} [Monad m] (H : List UInt8 → m Digest)
    (F : KState → m KState) (root : Digest) : m Common.KDigest := do
  vectorDigestWith (daHash H) (← membershipVectorWith (daHash H) F root.toBytes)

/-- `mapM` in `Id` is `map`. -/
theorem mapM_id {α β : Type} (f : α → Id β) : ∀ l : List α,
    (l.mapM (m := Id) f : List β) = l.map fun a ↦ Id.run (f a)
  | [] => rfl
  | a :: l => by rw [List.mapM_cons, List.map_cons, ← mapM_id f l]; rfl

section Id

variable (H : List UInt8 → Common.KDigest) (P : KState → KState)

/-- A tree level with the pure hash is `LeanDa.treeLevel`. -/
theorem treeLevelWith_id (nodes : List Common.KDigest) :
    Id.run (treeLevelWith (m := Id) H nodes) = LeanDa.treeLevel H nodes := by
  simp only [treeLevelWith, mapM_id, LeanDa.treeLevel]
  rfl

/-- A tree level halves the nodes. -/
theorem length_treeLevel (nodes : List Common.KDigest) :
    (LeanDa.treeLevel H nodes).length = nodes.length / 2 := by
  simp [LeanDa.treeLevel]

/-- Enough fuel builds the tree. -/
theorem treeRootFuel_id : ∀ (fuel : ℕ) (nodes : List Common.KDigest), nodes.length ≤ fuel →
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
theorem treeRootWith_id (nodes : List Common.KDigest) :
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

/-- The sponge's samples with the pure permutation are `LeanDa.Sponge.samplesM` over `Id`. -/
theorem spongeSamplesWith_id : ∀ (n : ℕ) (s : LeanDa.Sponge),
    Id.run (spongeSamplesWith (m := Id) P n s) =
      Id.run (LeanDa.Sponge.samplesM (m := Id) (fun L ↦ pure (P L)) n s)
  | 0, _ => rfl
  | n + 1, s => by
    show _ :: Id.run (spongeSamplesWith (m := Id) P n _) = _
    rw [spongeSamplesWith_id n]
    rfl

/-- Observing with the pure permutation is `LeanDa.Sponge.observeM` over `Id`. -/
theorem spongeObserveWith_id (s : LeanDa.Sponge) (x : E) :
    Id.run (spongeObserveWith (m := Id) P s x) =
      Id.run (LeanDa.Sponge.observeM (m := Id) (fun L ↦ pure (P L)) s x) := by
  simp only [spongeObserveWith, spongeAbsorbWith, LeanDa.Sponge.observeM, LeanDa.Sponge.absorbM]
  split <;> rfl

/-- The membership vector with the pure hash and permutation is `LeanDa.membershipVector`. -/
theorem membershipVectorWith_id (root : Common.KDigest) :
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

/-- The vector digest of a root with Keccak is `vectorDigestOf`. -/
theorem vectorDigestOfWith_id (root : Digest) :
    Id.run (vectorDigestOfWith (m := Id) keccak256 keccakF root) = vectorDigestOf root := by
  unfold vectorDigestOfWith
  rw [daHash_id]
  show Id.run (vectorDigestWith (m := Id) keccak
    (Id.run (membershipVectorWith (m := Id) keccak keccakF root.toBytes))) = _
  rw [membershipVectorWith_id, vectorDigestWith_id]
  rfl

end
end LeanVM.Da
