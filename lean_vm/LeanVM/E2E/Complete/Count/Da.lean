/-
  LeanVM.E2E.Complete.Count.Da

  The block prefixes a DA opening logs: its cells, its row digests and its vector, for at most
  `1024` rows and a vector of `2^15` scalars.
-/

module

public import LeanVM.E2E.Complete.Count.Prog

/-!
# A DA opening

`daLog H pc pr w` (`NodeLog.lean`) is the log of the commitment to `w.rows`
(`commitCodewordsWith`) and of the vector's digest. Its long strings are the cells (at most `256`
symbols, `2048` bytes, `31` blocks, whatever the row: `listCell` is a `drop` and a `take`), the
row digests (`64` digests, `2048` bytes) and the vector (`24` bytes a scalar); every tree node
is one `64`-byte pair. So for `r ≤ 1024` rows, padded to `nPad r ≤ 1024`, and a vector of
`2^15` scalars, the log has at most `daOpenBlocks = 1024 · (64 · 31 + 31) + 128 · 1024 · 31 +
12288` block prefixes (`prefixCount_daLog_le`).
-/

namespace LeanVM.E2E.Complete

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Blake2sHash LeanVM.Node

@[expose] public section

variable (H : Bytes → Digest)

/-- A `mapM` in the logging monad returns one value per element. -/
theorem length_mapM_val_logM {α β : Type} (f : α → LogM β) :
    ∀ l : List α, (l.mapM f).val.length = l.length
  | [] => rfl
  | a :: l => by
    rw [List.mapM_cons, LogM.bind_val, LogM.bind_val, LogM.pure_val, List.length_cons,
      length_mapM_val_logM f l, List.length_cons]

/-- A DA hash logs its input. -/
theorem prefixCount_daHash (x : List UInt8) :
    prefixCount (Da.daHash (LogM.hash H) x).log = nBlocks x := by
  rw [Da.daHash, LogM.map_log, prefixCount_hash]

/-- A DA hash of one block. -/
theorem logShort_daHash {x : List UInt8} (hx : x.length ≤ 64) :
    LogShort (Da.daHash (LogM.hash H) x) :=
  LogShort.map _ (LogShort.hash H hx)

theorem length_flatMap_daKBytes (ws : List K) :
    (ws.flatMap LeanDa.kBytes).length = 8 * ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    rw [List.flatMap_cons, List.length_append, ih, List.length_cons]
    simp only [LeanDa.kBytes, List.length_map, List.length_range]
    ring

/-- A cell is at most `31` blocks past its first. -/
theorem prefixCount_listCellDigestWith_le (row : List K) (j : ℕ) :
    prefixCount (Da.listCellDigestWith (Da.daHash (LogM.hash H)) row j).log ≤ 31 := by
  rw [Da.listCellDigestWith, prefixCount_daHash]
  refine nBlocks_le_of_length_le ?_
  rw [length_flatMap_daKBytes]
  have : (LeanDa.listCell row j).length ≤ 256 := by
    unfold LeanDa.listCell
    exact List.length_take_le _ _
  omega

/-- A row's digest: its `64` payload cells and their digests. -/
theorem prefixCount_rowDigestWith_le (row : List K) :
    prefixCount (Da.rowDigestWith (Da.daHash (LogM.hash H)) row).log ≤ 64 * 31 + 31 := by
  rw [Da.rowDigestWith, prefixCount_bind, prefixCount_daHash]
  refine Nat.add_le_add ?_ (nBlocks_le_of_length_le ?_)
  · have := prefixCount_mapM_le_mul _ 31 (List.range LeanDa.payloadCells)
      fun j _ ↦ prefixCount_listCellDigestWith_le H row j
    rwa [List.length_range] at this
  · have hl : ∀ ds : List LeanDa.Digest, (ds.flatMap fun d ↦ d.toList).length = 32 * ds.length := by
      intro ds
      induction ds with
      | nil => rfl
      | cons d ds ih =>
        rw [List.flatMap_cons, List.length_append, ih, List.length_cons, Vector.length_toList]
        ring
    rw [hl, length_mapM_val_logM, List.length_range]
    decide

/-- A tree level hashes pairs. -/
theorem logShort_treeLevelWith (nodes : List LeanDa.Digest) :
    LogShort (Da.treeLevelWith (Da.daHash (LogM.hash H)) nodes) :=
  LogShort.mapM _ _ fun _ _ ↦ logShort_daHash H (by
    simp [LeanDa.pairBytes])

/-- A tree hashes pairs. -/
theorem logShort_treeRootFuel :
    ∀ (fuel : ℕ) (nodes : List LeanDa.Digest),
      LogShort (Da.treeRootFuel (Da.daHash (LogM.hash H)) fuel nodes)
  | 0, _ => LogShort.pure _
  | fuel + 1, nodes => by
    simp only [Da.treeRootFuel]
    split
    · exact LogShort.pure _
    · exact LogShort.bind (logShort_treeLevelWith H nodes) fun _ ↦ logShort_treeRootFuel fuel _

/-- The padded row count of at most `1024` rows. -/
theorem daNPad_le {r : ℕ} (hr : r ≤ LeanDa.maxRows) : LeanDa.nPad r ≤ 1024 := by
  unfold LeanDa.nPad LeanDa.logPad
  have h : Nat.clog 2 r ≤ 10 := by
    have := Nat.clog_mono_right 2 (show r ≤ 2 ^ 10 by unfold LeanDa.maxRows at hr; omega)
    rwa [Nat.clog_pow 2 10 (by norm_num)] at this
  calc 2 ^ Nat.clog 2 r ≤ 2 ^ 10 := Nat.pow_le_pow_right (by norm_num) h
    _ = 1024 := by norm_num

/-- The commitment to at most `1024` rows. -/
theorem prefixCount_commitCodewordsWith_le (pc pr : LeanDa.Digest) (rows : List (List K))
    (hr : rows.length ≤ LeanDa.maxRows) :
    prefixCount (Da.commitCodewordsWith (Da.daHash (LogM.hash H)) pc pr rows).log ≤
      1024 * (64 * 31 + 31) + 128 * 1024 * 31 := by
  unfold Da.commitCodewordsWith Da.treeRootWith
  simp only [prefixCount_bind]
  rw [(logShort_treeRootFuel H _ _).prefixCount_eq, (logShort_treeRootFuel H _ _).prefixCount_eq,
    prefixCount_daHash, nBlocks_eq_zero_of_length_le (by simp [LeanDa.pairBytes])]
  have hrows := prefixCount_mapM_le_mul _ _ rows fun row _ ↦ prefixCount_rowDigestWith_le H row
  have hcols := prefixCount_mapM_le_mul (fun ij : ℕ × ℕ ↦
      if h : ij.1 < rows.length then Da.listCellDigestWith (Da.daHash (LogM.hash H)) rows[ij.1] ij.2
      else (pure pc : LogM LeanDa.Digest)) 31
    ((List.range LeanDa.cellsPerRow).flatMap fun j ↦
      (List.range (LeanDa.nPad rows.length)).map fun i ↦ (i, j)) fun ij _ ↦ by
    split
    · exact prefixCount_listCellDigestWith_le H _ _
    · exact Nat.zero_le _
  have hlen : ((List.range LeanDa.cellsPerRow).flatMap fun j ↦
      (List.range (LeanDa.nPad rows.length)).map fun i ↦ (i, j)).length =
      LeanDa.cellsPerRow * LeanDa.nPad rows.length := by
    simp [List.length_flatMap, List.sum_replicate]
  rw [hlen] at hcols
  have hn := daNPad_le hr
  have hr' : rows.length ≤ 1024 := hr
  have h1 : rows.length * (64 * 31 + 31) ≤ 1024 * (64 * 31 + 31) := Nat.mul_le_mul_right _ hr'
  have h2 : LeanDa.cellsPerRow * LeanDa.nPad rows.length * 31 ≤ 128 * 1024 * 31 :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul (le_of_eq rfl) hn)
  omega

/-- The vector's digest, `2^15` scalars. -/
theorem prefixCount_vectorDigestWith_le (v : List E) (hv : v.length = 2 ^ LeanDa.logM) :
    prefixCount (Da.vectorDigestWith (Da.daHash (LogM.hash H)) v).log ≤ 12288 := by
  rw [Da.vectorDigestWith, prefixCount_daHash]
  refine nBlocks_le_of_length_le ?_
  rw [length_flatMap_daKBytes]
  have hl : ∀ v : List E, (v.flatMap fun e ↦ [LeanDa.limb e 0, LeanDa.limb e 1, LeanDa.limb e 2]).length =
      3 * v.length := by
    intro v
    induction v with
    | nil => rfl
    | cons e v ih =>
      rw [List.flatMap_cons, List.length_append, ih, List.length_cons]
      simp only [List.length_cons, List.length_nil]
      ring
  rw [hl, hv]
  unfold LeanDa.logM
  norm_num

/-- The block prefixes of a DA opening, at most. -/
def daOpenBlocks : ℕ := 1024 * (64 * 31 + 31) + 128 * 1024 * 31 + 12288

theorem daOpenBlocks_le : daOpenBlocks ≤ 2 ^ 30 := by
  unfold daOpenBlocks
  norm_num

/-- **The count of a DA opening** of at most `1024` rows and a vector of `2^15` scalars. -/
theorem prefixCount_daLog_le (pc pr : LeanDa.Digest) (w : Da.Witness)
    (hr : w.rows.length ≤ LeanDa.maxRows) (hv : w.vector.length = 2 ^ LeanDa.logM) :
    prefixCount (daLog H pc pr w) ≤ daOpenBlocks := by
  rw [daLog, prefixCount_append]
  exact Nat.add_le_add (prefixCount_commitCodewordsWith_le H pc pr w.rows hr)
    (prefixCount_vectorDigestWith_le H w.vector hv)

end
end LeanVM.E2E.Complete
