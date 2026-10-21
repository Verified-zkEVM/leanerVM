/-
  LeanVM.E2E.Da.Tree

  The column tree of a DA commitment answered by a log: its rows are determined by its root when
  the log has no collision and no answer is the padding digest, and they are fixed by the log
  before the commitment's root.
-/

module

public import LeanVM.E2E.Da.Log

/-!
# The DA leg: the column tree

A DA commitment (`Da.commitCodewordsWith`) hashes the row tree's root and the column tree's
(`colTreeWith`): the Merkle tree over the cells' digests, column by column, the rows padded to a
power of two with the padding digest `pc`. The DA leg reads two facts off a log `ℓ` answering it
through LeanDA's hash `daHash (look ℓ)`.

**Uniqueness** (`rows_eq_of_colTree`). If the answers have no collision and none is `pc`, the
column root determines the rows. A node of the tree has a height (`Ht`): a leaf (`pc`, or the
digest of an input that is not 64 bytes long, a cell's being 2048) has height `0`, the digest of
two nodes of height `h` has height `h + 1`; without collisions a digest has at most one height
(`ht_unique`). So two column trees with one root have one number of leaves, so the same leaves
(`treeRootFuel_inj`), so the same cells, so the same rows.

**Order** (`colTree_take`). If no entry of `ℓ` from `i` on is a chunk of its input or of an
earlier one, a column tree answered by `ℓ` whose root is a chunk of an input answered by
`ℓ.take i` is answered by `ℓ.take i`: a digest the tree uses is a chunk of the input of its
parent, so an entry after the root's would predict it (`treeRootFuel_step`).
-/

namespace LeanVM.E2E

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Rom

@[expose] public section

/-! ## Option-valued maps -/

/-- An `Option`-valued map succeeds exactly when every entry does. -/
theorem mapM_option_eq_some_iff {α β : Type} (f : α → Option β) :
    ∀ (l : List α) (M : List β), l.mapM f = some M ↔
      M.length = l.length ∧ ∀ i (h : i < l.length) (h' : i < M.length), f l[i] = some M[i]
  | [], M => by
    cases M <;> simp
  | a :: l, M => by
    rw [List.mapM_cons]
    cases M with
    | nil =>
      simp only [List.length_nil, List.length_cons, Nat.right_eq_add, Nat.add_one_ne_zero,
        false_and, iff_false]
      intro h
      simp only [bind, Option.bind_eq_some_iff, pure] at h
      obtain ⟨_, _, _, _, h⟩ := h
      cases h
    | cons b M =>
      simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq, List.cons.injEq,
        List.length_cons, Nat.add_right_cancel_iff]
      constructor
      · rintro ⟨b', hb', M', hM', rfl, rfl⟩
        obtain ⟨hl, hi⟩ := (mapM_option_eq_some_iff f l M').mp hM'
        refine ⟨hl, fun i h h' ↦ ?_⟩
        cases i with
        | zero => exact hb'
        | succ i => exact hi i (by simpa using h) (by simpa using h')
      · rintro ⟨hl, hi⟩
        refine ⟨b, hi 0 (by simp) (by simp), M, ?_, rfl, rfl⟩
        exact (mapM_option_eq_some_iff f l M).mpr
          ⟨hl, fun i h h' ↦ hi (i + 1) (by simpa using h) (by simpa using h')⟩

/-! ## Merkle levels and roots -/

section Tree

variable (HD : List UInt8 → Option LeanDa.Digest)

/-- A pair of digests has 64 bytes. -/
theorem pairBytes_length (a b : LeanDa.Digest) : (LeanDa.pairBytes a b).length = 64 := by
  simp [LeanDa.pairBytes]

/-- A pair of digests is determined by its bytes. -/
theorem pairBytes_inj {a b a' b' : LeanDa.Digest}
    (h : LeanDa.pairBytes a b = LeanDa.pairBytes a' b') : a = a' ∧ b = b' := by
  obtain ⟨h1, h2⟩ := List.append_inj h (by simp)
  exact ⟨Vector.toList_inj.mp h1, Vector.toList_inj.mp h2⟩

/-- The first chunk of a pair is its first digest. -/
theorem chunk0_pairBytes (a b : LeanDa.Digest) : chunk0 (LeanDa.pairBytes a b) = a.toList := by
  simp [chunk0, LeanDa.pairBytes]

/-- The second chunk of a pair is its second digest. -/
theorem chunk1_pairBytes (a b : LeanDa.Digest) : chunk1 (LeanDa.pairBytes a b) = b.toList := by
  simp [chunk1, LeanDa.pairBytes]

/-- A Merkle level answered: its nodes are the hashes of the pairs below. -/
theorem treeLevelWith_eq_some {nodes next : List LeanDa.Digest} :
    Da.treeLevelWith HD nodes = some next ↔ next.length = nodes.length / 2 ∧
      ∀ i, i < nodes.length / 2 → ∀ (h' : i < next.length),
        HD (LeanDa.pairBytes (nodes.getD (2 * i) default) (nodes.getD (2 * i + 1) default)) =
          some next[i] := by
  rw [Da.treeLevelWith, mapM_option_eq_some_iff]
  simp only [List.length_range, List.getElem_range]

/-- The tree without fuel: the first node. -/
theorem treeRootFuel_zero (nodes : List LeanDa.Digest) :
    Da.treeRootFuel HD 0 nodes = some (nodes.headD default) := rfl

/-- The tree with fuel: the first node of at most one, otherwise one level up. -/
theorem treeRootFuel_succ (fuel : ℕ) (nodes : List LeanDa.Digest) :
    Da.treeRootFuel HD (fuel + 1) nodes = if nodes.length ≤ 1 then some (nodes.headD default)
      else (Da.treeLevelWith HD nodes).bind (Da.treeRootFuel HD fuel) := rfl

/-- The root of a single node is the node. -/
theorem treeRootFuel_single {nodes : List LeanDa.Digest} (hn : nodes.length = 1) (fuel : ℕ)
    {v : LeanDa.Digest} (hv : Da.treeRootFuel HD fuel nodes = some v) :
    v = nodes[0]'(by omega) := by
  obtain ⟨x, rfl⟩ : ∃ x, nodes = [x] := List.length_eq_one_iff.mp hn
  cases fuel <;> simpa [treeRootFuel_zero, treeRootFuel_succ] using hv.symm

/-- A level of `2^(a+1)` nodes, answered. -/
theorem treeRootFuel_level {a fuel : ℕ} {nodes : List LeanDa.Digest}
    (hn : nodes.length = 2 ^ (a + 1)) {v : LeanDa.Digest}
    (hv : Da.treeRootFuel HD (fuel + 1) nodes = some v) :
    ∃ next, Da.treeLevelWith HD nodes = some next ∧ next.length = 2 ^ a ∧
      Da.treeRootFuel HD fuel next = some v := by
  rw [treeRootFuel_succ,
    ite_eq_right (by rw [hn, pow_succ]; have := Nat.one_le_two_pow (n := a); omega),
    Option.bind_eq_some_iff] at hv
  obtain ⟨next, hnext, hv⟩ := hv
  refine ⟨next, hnext, ?_, hv⟩
  rw [((treeLevelWith_eq_some HD).mp hnext).1, hn, pow_succ, Nat.mul_div_cancel _ (by norm_num)]

/-- **Two answered Merkle trees with one root and one number of leaves have the same leaves**,
if the answers have no collision. -/
theorem treeRootFuel_inj (hinj : ∀ x y v, HD x = some v → HD y = some v → x = y) :
    ∀ (a : ℕ) (nodes nodes' : List LeanDa.Digest) (fuel fuel' : ℕ) (v : LeanDa.Digest),
      nodes.length = 2 ^ a → nodes'.length = 2 ^ a → a ≤ fuel → a ≤ fuel' →
      Da.treeRootFuel HD fuel nodes = some v → Da.treeRootFuel HD fuel' nodes' = some v →
      nodes = nodes'
  | 0, nodes, nodes', fuel, fuel', v, hn, hn', _, _, hv, hv' => by
    have e := treeRootFuel_single HD hn fuel hv
    have e' := treeRootFuel_single HD hn' fuel' hv'
    obtain ⟨x, rfl⟩ : ∃ x, nodes = [x] := List.length_eq_one_iff.mp hn
    obtain ⟨x', rfl⟩ : ∃ x, nodes' = [x] := List.length_eq_one_iff.mp hn'
    simp only [List.getElem_cons_zero] at e e'
    rw [← e, ← e']
  | a + 1, nodes, nodes', fuel + 1, fuel' + 1, v, hn, hn', hf, hf', hv, hv' => by
    obtain ⟨next, hl, hlen, hr⟩ := treeRootFuel_level HD hn hv
    obtain ⟨next', hl', hlen', hr'⟩ := treeRootFuel_level HD hn' hv'
    have heq := treeRootFuel_inj hinj a next next' fuel fuel' v hlen hlen' (by omega) (by omega)
      hr hr'
    subst heq
    obtain ⟨-, hi⟩ := (treeLevelWith_eq_some HD).mp hl
    obtain ⟨-, hi'⟩ := (treeLevelWith_eq_some HD).mp hl'
    refine List.ext_getElem (by rw [hn, hn']) fun p hp hp' ↦ ?_
    have hq : p / 2 < nodes.length / 2 := by omega
    have hq' : p / 2 < nodes'.length / 2 := by omega
    have hpair := pairBytes_inj (hinj _ _ _ (hi (p / 2) hq (by omega)) (hi' (p / 2) hq' (by omega)))
    have hgd : nodes.getD p default = nodes'.getD p default := by
      rcases Nat.mod_two_eq_zero_or_one p with h2 | h2
      · have := hpair.1
        rwa [show 2 * (p / 2) = p by omega] at this
      · have := hpair.2
        rwa [show 2 * (p / 2) + 1 = p by omega] at this
    rwa [List.getD_eq_getElem _ _ hp, List.getD_eq_getElem _ _ hp'] at hgd
  | a + 1, _, _, 0, _, _, _, _, hf, _, _, _ => absurd hf (by omega)
  | a + 1, _, _, _ + 1, 0, _, _, _, _, hf', _, _ => absurd hf' (by omega)

/-- **The height of a node**: a leaf (`pc`, or the hash of an input that is not 64 bytes long)
has height `0`; the hash of two nodes of height `h` has height `h + 1`. -/
inductive Ht (pc : LeanDa.Digest) : ℕ → LeanDa.Digest → Prop
  /-- The padding digest. -/
  | pad : Ht pc 0 pc
  /-- The hash of an input that is not a pair. -/
  | leaf {x : Bytes} {v : LeanDa.Digest} : x.length ≠ 64 → HD x = some v → Ht pc 0 v
  /-- The hash of a pair of nodes. -/
  | node {h : ℕ} {a b v : LeanDa.Digest} : Ht pc h a → Ht pc h b →
      HD (LeanDa.pairBytes a b) = some v → Ht pc (h + 1) v

/-- **Without collisions, and no answer being `pc`, a node has one height.** -/
theorem ht_unique {pc : LeanDa.Digest} (hinj : ∀ x y v, HD x = some v → HD y = some v → x = y)
    (hpc : ∀ x, HD x ≠ some pc) {h : ℕ} {v : LeanDa.Digest} (hv : Ht HD pc h v) :
    ∀ {h' : ℕ}, Ht HD pc h' v → h = h' := by
  induction hv with
  | pad =>
    intro h' hv'
    cases hv' with
    | pad => rfl
    | leaf _ hx => exact absurd hx (hpc _)
    | node _ _ hx => exact absurd hx (hpc _)
  | leaf hlen hx =>
    intro h' hv'
    cases hv' with
    | pad => exact absurd hx (hpc _)
    | leaf _ _ => rfl
    | node _ _ hy => exact absurd (hinj _ _ _ hx hy ▸ pairBytes_length _ _) hlen
  | node ha hb hx iha ihb =>
    intro h' hv'
    cases hv' with
    | pad => exact absurd hx (hpc _)
    | leaf hlen hy => exact absurd (hinj _ _ _ hy hx ▸ pairBytes_length _ _) hlen
    | node ha' hb' hy =>
      obtain ⟨rfl, rfl⟩ := pairBytes_inj (hinj _ _ _ hx hy)
      rw [iha ha']

/-- The root of `2^a` nodes of height `h` has height `h + a`. -/
theorem ht_treeRootFuel {pc : LeanDa.Digest} :
    ∀ (a : ℕ) (nodes : List LeanDa.Digest) (fuel h : ℕ) (v : LeanDa.Digest),
      nodes.length = 2 ^ a → a ≤ fuel → (∀ x ∈ nodes, Ht HD pc h x) →
      Da.treeRootFuel HD fuel nodes = some v → Ht HD pc (h + a) v
  | 0, nodes, fuel, h, v, hn, _, hx, hv => by
    rw [treeRootFuel_single HD hn fuel hv]
    exact hx _ (List.getElem_mem _)
  | a + 1, nodes, fuel + 1, h, v, hn, hf, hx, hv => by
    obtain ⟨next, hl, hlen, hr⟩ := treeRootFuel_level HD hn hv
    obtain ⟨hl', hi⟩ := (treeLevelWith_eq_some HD).mp hl
    have := ht_treeRootFuel a next fuel (h + 1) v hlen (by omega) (fun x hxm ↦ by
      obtain ⟨i, hi', rfl⟩ := List.getElem_of_mem hxm
      have hq : i < nodes.length / 2 := by omega
      refine Ht.node (hx _ ?_) (hx _ ?_) (hi i hq hi')
      · rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
      · rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _) hr
    rwa [Nat.add_right_comm, Nat.add_assoc] at this
  | _ + 1, _, 0, _, _, _, hf, _, _ => absurd hf (by omega)

end Tree

/-! ## The column tree -/

/-- The column tree's leaves' positions: cell `j` of padded row `i`, column by column. -/
def colIdx (n : ℕ) : List (ℕ × ℕ) :=
  (List.range LeanDa.cellsPerRow).flatMap fun j ↦ (List.range n).map fun i ↦ (i, j)

/-- A leaf of the column tree: the digest of cell `j` of row `i`, or the padding digest. -/
def colLeaf {m : Type → Type} [Monad m] (HD : List UInt8 → m LeanDa.Digest) (pc : LeanDa.Digest)
    (rows : List (List K)) (ij : ℕ × ℕ) : m LeanDa.Digest :=
  if h : ij.1 < rows.length then Da.listCellDigestWith HD rows[ij.1] ij.2 else pure pc

/-- **The column tree's root** of a commitment (`Da.commitCodewordsWith`). -/
def colTreeWith {m : Type → Type} [Monad m] (HD : List UInt8 → m LeanDa.Digest)
    (pc : LeanDa.Digest) (rows : List (List K)) : m LeanDa.Digest := do
  let cols ← (colIdx (LeanDa.nPad rows.length)).mapM (colLeaf HD pc rows)
  Da.treeRootWith HD cols

/-- The column tree's positions: the cells of the padded rows. -/
theorem mem_colIdx {n : ℕ} {ij : ℕ × ℕ} : ij ∈ colIdx n ↔ ij.1 < n ∧ ij.2 < LeanDa.cellsPerRow := by
  obtain ⟨i, j⟩ := ij
  simp only [colIdx, List.mem_flatMap, List.mem_range, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨j', hj', i', hi', rfl, rfl⟩; exact ⟨hi', hj'⟩
  · rintro ⟨hi, hj⟩; exact ⟨j, hj, i, hi, rfl, rfl⟩

/-- The column tree has `128` leaves per padded row. -/
theorem length_colIdx (n : ℕ) : (colIdx n).length = LeanDa.cellsPerRow * n := by
  simp [colIdx, List.length_flatMap, List.map_const', List.sum_replicate]

/-- The padded row count is at least the row count. -/
theorem le_nPad (r : ℕ) : r ≤ LeanDa.nPad r :=
  (Nat.clog_le_iff_le_pow (by norm_num)).mp le_rfl

/-- The column tree has a power of two of leaves. -/
theorem cellsPerRow_mul_nPad (r : ℕ) :
    LeanDa.cellsPerRow * LeanDa.nPad r = 2 ^ (7 + LeanDa.logPad r) := by
  simp [LeanDa.cellsPerRow, LeanDa.nPad, pow_add]

/-- **A commitment answered gives its column tree's root**, hashed after a row root into the
commitment. -/
theorem commitCodewordsWith_eq_some {HD : List UInt8 → Option LeanDa.Digest}
    {pc pr : LeanDa.Digest} {rows : List (List K)} {ρ : LeanDa.Digest}
    (h : Da.commitCodewordsWith HD pc pr rows = some ρ) :
    ∃ rt c, colTreeWith HD pc rows = some c ∧ HD (LeanDa.pairBytes rt c) = some ρ := by
  simp only [Da.commitCodewordsWith, bind, Option.bind_eq_some_iff] at h
  obtain ⟨_, _, rt, _, cols, hcols, c, hc, hρ⟩ := h
  refine ⟨rt, c, ?_, hρ⟩
  simp only [colTreeWith, bind, Option.bind_eq_some_iff]
  exact ⟨cols, hcols, hc⟩

section Unique

variable {HD : List UInt8 → Option LeanDa.Digest} {pc : LeanDa.Digest}

/-- A column tree answered: its leaves and its root. -/
theorem colTreeWith_eq_some {rows : List (List K)} {c : LeanDa.Digest} :
    colTreeWith HD pc rows = some c ↔ ∃ cols,
      (colIdx (LeanDa.nPad rows.length)).mapM (colLeaf HD pc rows) = some cols ∧
        Da.treeRootFuel HD cols.length cols = some c := by
  simp only [colTreeWith, bind, Option.bind_eq_some_iff, Da.treeRootWith]

/-- A cell's bytes are not a pair's: 2048 bytes. -/
theorem length_cellBytes {row : List K} (h : row.length = 2 ^ LeanDa.logM) {j : ℕ}
    (hj : j < LeanDa.cellsPerRow) :
    ((LeanDa.listCell row j).flatMap LeanDa.kBytes).length ≠ 64 := by
  simp only [List.length_flatMap, daKBytes_length, List.map_const', List.sum_replicate,
    smul_eq_mul, length_listCell h hj, LeanDa.cellSymbols]
  norm_num

/-- The leaves of an answered column tree have height `0`. -/
theorem ht_colLeaf {rows : List (List K)} (hrows : ∀ row ∈ rows, row.length = 2 ^ LeanDa.logM)
    {ij : ℕ × ℕ} (hij : ij.2 < LeanDa.cellsPerRow) {v : LeanDa.Digest}
    (hv : colLeaf HD pc rows ij = some v) : Ht HD pc 0 v := by
  unfold colLeaf at hv
  split at hv
  · exact Ht.leaf (length_cellBytes (hrows _ (List.getElem_mem _)) hij) hv
  · cases hv
    exact Ht.pad

/-- **The column root determines the rows**, if the answers have no collision and none is the
padding digest. -/
theorem rows_eq_of_colTree (hinj : ∀ x y v, HD x = some v → HD y = some v → x = y)
    (hpc : ∀ x, HD x ≠ some pc) {rows rows' : List (List K)}
    (hr : ∀ row ∈ rows, row.length = 2 ^ LeanDa.logM)
    (hr' : ∀ row ∈ rows', row.length = 2 ^ LeanDa.logM) {c : LeanDa.Digest}
    (h : colTreeWith HD pc rows = some c) (h' : colTreeWith HD pc rows' = some c) :
    rows = rows' := by
  obtain ⟨cols, hcols, hc⟩ := colTreeWith_eq_some.mp h
  obtain ⟨cols', hcols', hc'⟩ := colTreeWith_eq_some.mp h'
  obtain ⟨hl, hi⟩ := (mapM_option_eq_some_iff _ _ _).mp hcols
  obtain ⟨hl', hi'⟩ := (mapM_option_eq_some_iff _ _ _).mp hcols'
  have hlen : cols.length = 2 ^ (7 + LeanDa.logPad rows.length) := by
    rw [hl, length_colIdx, cellsPerRow_mul_nPad]
  have hlen' : cols'.length = 2 ^ (7 + LeanDa.logPad rows'.length) := by
    rw [hl', length_colIdx, cellsPerRow_mul_nPad]
  have hht : ∀ x ∈ cols, Ht HD pc 0 x := by
    intro x hx
    obtain ⟨i, hi₁, rfl⟩ := List.getElem_of_mem hx
    have hi₂ : i < (colIdx (LeanDa.nPad rows.length)).length := by omega
    exact ht_colLeaf hr (mem_colIdx.mp (List.getElem_mem hi₂)).2 (hi i hi₂ hi₁)
  have hht' : ∀ x ∈ cols', Ht HD pc 0 x := by
    intro x hx
    obtain ⟨i, hi₁, rfl⟩ := List.getElem_of_mem hx
    have hi₂ : i < (colIdx (LeanDa.nPad rows'.length)).length := by omega
    exact ht_colLeaf hr' (mem_colIdx.mp (List.getElem_mem hi₂)).2 (hi' i hi₂ hi₁)
  have hf : 7 + LeanDa.logPad rows.length ≤ cols.length := by
    rw [hlen]; exact Nat.lt_two_pow_self.le
  have hf' : 7 + LeanDa.logPad rows'.length ≤ cols'.length := by
    rw [hlen']; exact Nat.lt_two_pow_self.le
  -- One height, so one number of leaves, so the same leaves.
  have hd := ht_unique HD hinj hpc (ht_treeRootFuel HD _ cols _ 0 c hlen hf hht hc)
    (ht_treeRootFuel HD _ cols' _ 0 c hlen' hf' hht' hc')
  simp only [Nat.zero_add, Nat.add_left_cancel_iff] at hd
  have hcc : cols = cols' := treeRootFuel_inj HD hinj _ cols cols' _ _ c hlen
    (by rw [hlen', hd]) hf (by rw [hd]; exact hf') hc hc'
  subst hcc
  have hn : LeanDa.nPad rows.length = LeanDa.nPad rows'.length := by
    have := hl.symm.trans hl'
    rw [length_colIdx, length_colIdx] at this
    simp only [LeanDa.cellsPerRow] at this
    omega
  rw [← hn] at hcols'
  obtain ⟨_, hi'⟩ := (mapM_option_eq_some_iff _ _ _).mp hcols'
  set n := LeanDa.nPad rows.length
  -- The leaves agree, and are answered.
  have hagree : ∀ ij ∈ colIdx n, colLeaf HD pc rows ij = colLeaf HD pc rows' ij ∧
      ∃ v, colLeaf HD pc rows ij = some v := by
    intro ij hij
    obtain ⟨p, hp, rfl⟩ := List.getElem_of_mem hij
    exact ⟨(hi p hp (by omega)).trans (hi' p hp (by omega)).symm, _, hi p hp (by omega)⟩
  have hrn : rows.length ≤ n := le_nPad _
  have hrn' : rows'.length ≤ n := hn ▸ le_nPad _
  -- No row of one beyond the rows of the other: its cell would be the padding digest.
  have hshort : ∀ (A B : List (List K)), (∀ ij ∈ colIdx n,
      colLeaf HD pc A ij = colLeaf HD pc B ij) → A.length < B.length → B.length ≤ n → False := by
    intro A B hAB hlt hle
    have := hAB (A.length, 0) (mem_colIdx.mpr ⟨by omega, by simp [LeanDa.cellsPerRow]⟩)
    simp only [colLeaf, lt_irrefl, ↓reduceDIte, hlt] at this
    exact hpc _ this.symm
  have hk : rows.length = rows'.length := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · exact hshort rows rows' (fun ij hij ↦ (hagree ij hij).1) hlt hrn'
    · exact hshort rows' rows (fun ij hij ↦ (hagree ij hij).1.symm) hlt hrn
  refine List.ext_getElem hk fun i hi₁ hi₂ ↦ ?_
  refine eq_of_listCell (hr _ (List.getElem_mem _)) (hr' _ (List.getElem_mem _)) fun j hj ↦ ?_
  obtain ⟨heq, v, hv⟩ := hagree (i, j) (mem_colIdx.mpr ⟨by omega, hj⟩)
  simp only [colLeaf, hi₁, hi₂, ↓reduceDIte, Da.listCellDigestWith] at heq hv
  exact flatMap_daKBytes_inj (hinj _ _ _ hv (heq ▸ hv))

end Unique

/-! ## The order of a column tree's entries -/

section Step

variable {ℓ : Log} {t : Bytes} {u : Digest}

/-- An answer of LeanDA's hash on a log persists in a longer log. -/
theorem daHash_append_of_some {x : Bytes} {v : LeanDa.Digest}
    (h : Da.daHash (look ℓ) x = some v) (ℓ' : Log) : Da.daHash (look (ℓ ++ ℓ')) x = some v := by
  simp only [Da.daHash, Option.map_eq_map, Option.map_eq_some_iff] at h ⊢
  obtain ⟨w, hw, rfl⟩ := h
  exact ⟨w, look_append_of_some hw ℓ', rfl⟩

/-- An answer of LeanDA's hash on a prefix is an answer on the log. -/
theorem daHash_of_prefix {ℓ ℓ' : Log} (hp : ℓ <+: ℓ') {x : Bytes} {v : LeanDa.Digest}
    (h : Da.daHash (look ℓ) x = some v) : Da.daHash (look ℓ') x = some v := by
  obtain ⟨r, rfl⟩ := hp
  exact daHash_append_of_some h r

/-- An input LeanDA's hash on a log answers is an input of the log. -/
theorem mem_of_daHash {x : Bytes} {v : LeanDa.Digest} (h : Da.daHash (look ℓ) x = some v) :
    x ∈ ℓ.map Prod.fst := by
  simp only [Da.daHash, Option.map_eq_map, Option.map_eq_some_iff] at h
  obtain ⟨w, hw, -⟩ := h
  by_contra hx
  rw [← logLookup_eq_none_iff] at hx
  exact absurd hw (by simp [look, hx])

/-- LeanDA's hash on a log with one more entry: an old answer, or the new entry. -/
theorem daHash_append_single {x : Bytes} {v : LeanDa.Digest}
    (h : Da.daHash (look (ℓ ++ [(t, u)])) x = some v) :
    Da.daHash (look ℓ) x = some v ∨ (x = t ∧ v = Da.toBytes u) := by
  simp only [Da.daHash, Option.map_eq_map, Option.map_eq_some_iff] at h ⊢
  obtain ⟨w, hw, rfl⟩ := h
  rw [look_append_single] at hw
  rcases hx : look ℓ x with _ | w'
  · rw [hx, Option.none_or] at hw
    split at hw
    · right; exact ⟨by assumption, by cases hw; rfl⟩
    · cases hw
  · rw [hx, Option.some_or] at hw
    exact Or.inl ⟨w, hw ▸ rfl, rfl⟩

/-- The single node's root, for any hash. -/
theorem treeRootFuel_singleton (HD : List UInt8 → Option LeanDa.Digest) (x : LeanDa.Digest)
    (fuel : ℕ) : Da.treeRootFuel HD fuel [x] = some x := by
  cases fuel <;> rfl

/-- **One more entry in a Merkle tree**: if the new answer is no chunk of an input, a tree of
`2^a` nodes answered with it is answered without it and has no node the new answer, unless its
root is the new answer. -/
theorem treeRootFuel_step
    (hp : ∀ x ∈ t :: ℓ.map Prod.fst, chunk0 x ≠ digestBytes u ∧ chunk1 x ≠ digestBytes u) :
    ∀ (a : ℕ) (nodes : List LeanDa.Digest) (fuel : ℕ) (c : LeanDa.Digest),
      nodes.length = 2 ^ a → a ≤ fuel →
      Da.treeRootFuel (Da.daHash (look (ℓ ++ [(t, u)]))) fuel nodes = some c →
      (Da.treeRootFuel (Da.daHash (look ℓ)) fuel nodes = some c ∧ Da.toBytes u ∉ nodes) ∨
        c = Da.toBytes u
  | 0, nodes, fuel, c, hn, _, hc => by
    have e := treeRootFuel_single _ hn fuel hc
    obtain ⟨x, rfl⟩ : ∃ x, nodes = [x] := List.length_eq_one_iff.mp hn
    simp only [List.getElem_cons_zero] at e
    subst e
    by_cases hU : c = Da.toBytes u
    · exact Or.inr hU
    · exact Or.inl ⟨treeRootFuel_singleton _ c fuel, by simpa [eq_comm] using hU⟩
  | a + 1, nodes, fuel + 1, c, hn, hf, hc => by
    obtain ⟨next, hl, hlen, hr⟩ := treeRootFuel_level _ hn hc
    rcases treeRootFuel_step hp a next fuel c hlen (by omega) hr with ⟨hr0, hU⟩ | hU
    · left
      obtain ⟨hl₁, hl₂⟩ := (treeLevelWith_eq_some _).mp hl
      -- Every pair hashed is an old input.
      have hold : ∀ i (hi : i < nodes.length / 2) (hi' : i < next.length),
          Da.daHash (look ℓ) (LeanDa.pairBytes (nodes.getD (2 * i) default)
            (nodes.getD (2 * i + 1) default)) = some next[i] := by
        intro i hi hi'
        rcases daHash_append_single (hl₂ i hi hi') with h | ⟨-, h⟩
        · exact h
        · exact absurd (h ▸ List.getElem_mem hi') hU
      have hl0 : Da.treeLevelWith (Da.daHash (look ℓ)) nodes = some next :=
        (treeLevelWith_eq_some _).mpr ⟨hl₁, hold⟩
      refine ⟨?_, fun hm ↦ ?_⟩
      · rw [treeRootFuel_succ, ite_eq_right (by
          rw [hn, pow_succ]; have := Nat.one_le_two_pow (n := a); omega), hl0, Option.bind_some]
        exact hr0
      · obtain ⟨p, hp', hpe⟩ := List.getElem_of_mem hm
        have hq : p / 2 < nodes.length / 2 := by omega
        have hin := mem_of_daHash (hold (p / 2) hq (by omega))
        obtain ⟨h0, h1⟩ := hp _ (List.mem_cons_of_mem _ hin)
        rw [chunk0_pairBytes, ← toBytes_toList] at h0
        rw [chunk1_pairBytes, ← toBytes_toList] at h1
        rcases Nat.mod_two_eq_zero_or_one p with h2 | h2
        · rw [show 2 * (p / 2) = p by omega, List.getD_eq_getElem _ _ hp', hpe] at h0
          exact h0 rfl
        · rw [show 2 * (p / 2) + 1 = p by omega, List.getD_eq_getElem _ _ hp', hpe] at h1
          exact h1 rfl
    · exact Or.inr hU
  | _ + 1, _, 0, _, _, hf, _ => absurd hf (by omega)

/-- **One more entry in a column tree**: if the new answer is no chunk of an input, a column
tree answered with it, whose root is the second chunk of an old input, is answered without
it. -/
theorem colTreeWith_step {pc : LeanDa.Digest} {rows : List (List K)} {c rt ρ : LeanDa.Digest}
    (hp : ∀ x ∈ t :: ℓ.map Prod.fst, chunk0 x ≠ digestBytes u ∧ chunk1 x ≠ digestBytes u)
    (hroot : Da.daHash (look ℓ) (LeanDa.pairBytes rt c) = some ρ)
    (h : colTreeWith (Da.daHash (look (ℓ ++ [(t, u)]))) pc rows = some c) :
    colTreeWith (Da.daHash (look ℓ)) pc rows = some c := by
  have hcU : c ≠ Da.toBytes u := by
    intro hcU
    have := (hp _ (List.mem_cons_of_mem _ (mem_of_daHash hroot))).2
    rw [chunk1_pairBytes, hcU, toBytes_toList] at this
    exact this rfl
  obtain ⟨cols, hcols, hc⟩ := colTreeWith_eq_some.mp h
  obtain ⟨hl, hi⟩ := (mapM_option_eq_some_iff _ _ _).mp hcols
  have hlen : cols.length = 2 ^ (7 + LeanDa.logPad rows.length) := by
    rw [hl, length_colIdx, cellsPerRow_mul_nPad]
  rcases treeRootFuel_step hp _ cols cols.length c hlen
      (by rw [hlen]; exact Nat.lt_two_pow_self.le) hc with ⟨hc0, hU⟩ | hU
  · refine colTreeWith_eq_some.mpr ⟨cols, (mapM_option_eq_some_iff _ _ _).mpr ⟨hl, ?_⟩, hc0⟩
    intro i h₁ h₂
    have := hi i h₁ h₂
    unfold colLeaf at this ⊢
    split
    · rename_i hlt
      rw [dite_eq_left hlt] at this
      rcases daHash_append_single this with h' | ⟨-, h'⟩
      · exact h'
      · exact absurd (h' ▸ List.getElem_mem h₂) hU
    · rename_i hlt
      rw [dite_eq_right hlt] at this
      exact this
  · exact absurd hU hcU

end Step

/-- **A column tree answered by a log is answered by the prefix answering its root's pair**, if
no entry from there on fails for DA. -/
theorem colTree_take {pc : LeanDa.Digest} {ℓ : Log} (h : ¬ FailDA pc ℓ) {i : ℕ}
    (hi : i ≤ ℓ.length) {rows : List (List K)} {c rt ρ : LeanDa.Digest}
    (hroot : Da.daHash (look (ℓ.take i)) (LeanDa.pairBytes rt c) = some ρ)
    (hc : colTreeWith (Da.daHash (look ℓ)) pc rows = some c) :
    colTreeWith (Da.daHash (look (ℓ.take i))) pc rows = some c := by
  suffices key : ∀ m, i + m ≤ ℓ.length →
      colTreeWith (Da.daHash (look (ℓ.take (i + m)))) pc rows = some c →
      colTreeWith (Da.daHash (look (ℓ.take i))) pc rows = some c by
    refine key (ℓ.length - i) (by omega) ?_
    rwa [show i + (ℓ.length - i) = ℓ.length by omega, List.take_length]
  intro m
  induction m with
  | zero => intro _ hc; simpa using hc
  | succ m ih =>
    intro hm hc
    have hj : i + m < ℓ.length := by omega
    rw [show i + (m + 1) = i + m + 1 by omega, List.take_add_one, List.getElem?_eq_getElem hj,
      Option.toList_some] at hc
    exact ih (by omega) (colTreeWith_step (rt := rt) (ρ := ρ) (not_chunk_of_not_failDA h hj)
      (daHash_of_prefix (List.take_prefix_take_left (by omega)) hroot) hc)

end
end LeanVM.E2E
