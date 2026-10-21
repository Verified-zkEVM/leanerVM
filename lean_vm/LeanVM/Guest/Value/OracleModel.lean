/-
  LeanVM.Guest.Value.OracleModel

  The oracle hash model of the end-to-end security theorem: `BLAKE2S` rows are an execution's
  table, a hash is a log's answer, and the table check binds the two; the chain lemma; the
  execution bridge from the Flock-blind machine to the table's; the deployed direction of the
  table check.
-/

module

public import LeanVM.Guest.Value.HashModel
public import LeanVM.Spec.Ideal.Table
public import LeanVM.Protocol.Compile.Rom.Log

/-!
# The oracle hash model

The idealized system (`docs/roadmap/e2e-security.md` D4, T2) runs the guest under the Flock-blind
semantics, whose `BLAKE2S` rows are free canonical cells, and binds them to a random oracle through
the table check (`Spec/Ideal/Table.lean`, `TableOK`): every standard BLAKE2s chain among the rows
of a byte string `x` ends at the oracle's answer for `x`. This module makes that a `HashModel`:

* `tableSem rows`: a row checks when its cells are canonical and it is one of `rows`;
* `TablePrefix rows bs st`: the whole blocks `bs` are absorbed from the IV by a chain of rows of the
  table (`BlockChain`: non-final rows, each from its predecessor's output), ending at the cells
  `st` (`chainState`);
* **the chain lemma** (`stdChain_snoc`, C5): a prefix chain and a final row form the standard
  chain of `bs.flatten ++ r`; so `HashModel.oracle rows ℓ h`, at a log `ℓ` whose lookup passes the
  table check, answers every string the guest hashes by `look ℓ`.

The execution bridge (`validExecutionB_tableSem_iff`): a valid Flock-blind execution is a valid
execution under its own table (`Trace.blakeRows`), since each `BLAKE2S` instruction the run
executes is a row of the table (`row_of_mem_runRows`, `runB_of_runRows`).

The deployed direction (`tableOK_blake2s`, the table part of T7′): rows of the compression
function pass the table check at BLAKE2s-256, every standard chain computing `blake2sBytes`.
-/

namespace LeanVM.Guest.Value

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Compile.Rom

@[expose] public section

/-! ## The table's semantics -/

/-- **The table's semantics**: a `BLAKE2S` instruction checks when its cells are canonical and its
row is one of `rows`. -/
noncomputable def tableSem (rows : List BlakeRow) : BlakeSem where
  check m cv0 cv1 out0 out1 md :=
    CanonicalCells m cv0 cv1 out0 out1 md ∧ ⟨m, cv0, cv1, out0, out1, md⟩ ∈ rows
  dec _ _ _ _ _ _ := Classical.dec _

/-! ## Prefix chains -/

/-- Each row's chaining value is the IV for the first, its predecessor's output after
(`StdChain`'s second clause). -/
def Linked (c : List BlakeRow) : Prop :=
  ∀ (i : ℕ) (hi : i < c.length),
    c[i].cv = if h : i = 0 then paramIv else (c[i - 1]'(by omega)).out

/-- **`c` absorbs the whole blocks `bs` from the IV**: one row a block, linked, row `i` reading
block `i`'s bytes at the counter `64(i + 1)` with no flag (a standard chain's non-final rows). -/
def BlockChain (bs : List (List UInt8)) (c : List BlakeRow) : Prop :=
  bs = c.map (fun b ↦ blockBytes b.m) ∧ Linked c ∧
    ∀ (i : ℕ) (hi : i < c.length), unpackMetadata c[i].md = ((64 * (i + 1)).toUInt64, 0, 0)

/-- The chaining-value cells after a chain: the IV's for none, the last row's output after. -/
def chainState (c : List BlakeRow) : E × E :=
  match c.getLast? with
  | none => ivCells
  | some b => (b.out0, b.out1)

/-- **A prefix of the table**: whole blocks `bs`, absorbed from the IV by a chain of rows of
`rows`, reaching the cells `st`. -/
def TablePrefix (rows : List BlakeRow) (bs : List (List UInt8)) (st : E × E) : Prop :=
  ∃ c, (∀ b ∈ c, b ∈ rows) ∧ BlockChain bs c ∧ st = chainState c

/-- The digest of the cells after a chain: the IV for none, the last row's output after. -/
theorem cellWords_chainState (c : List BlakeRow) :
    cellWords (chainState c).1 ++ cellWords (chainState c).2 =
      if h : c.length = 0 then paramIv else (c[c.length - 1]'(by omega)).out := by
  rcases List.eq_nil_or_concat c with rfl | ⟨c, b, rfl⟩
  · exact cellWords_digestScalars paramIv
  · simp [chainState, BlakeRow.out]

/-- A row from the cells after a linked chain extends it. -/
theorem Linked.snoc {c : List BlakeRow} (hc : Linked c) {b : BlakeRow}
    (hb : b.cv = cellWords (chainState c).1 ++ cellWords (chainState c).2) : Linked (c ++ [b]) := by
  intro i hi
  rw [List.length_append, List.length_singleton] at hi
  rcases Nat.lt_or_ge i c.length with h | h
  · rw [List.getElem_append_left h, hc i h]
    split
    · rfl
    · rw [List.getElem_append_left (by omega)]
  · obtain rfl : i = c.length := by omega
    rw [List.getElem_concat_length rfl, hb, cellWords_chainState]
    split
    · rfl
    · rw [List.getElem_append_left (by omega)]

/-- The bytes `64i .. 64i + 63` of whole blocks and more are block `i`. -/
theorem take_drop_flatten_append {bs : List (List UInt8)} (hbs : ∀ b ∈ bs, b.length = 64)
    (r : List UInt8) {i : ℕ} (hi : i < bs.length) :
    ((bs.flatten ++ r).drop (64 * i)).take 64 = bs[i] := by
  induction bs generalizing i with
  | nil => exact absurd hi (Nat.not_lt_zero _)
  | cons b bs ih =>
    have hb : b.length = 64 := hbs b (by simp)
    rw [List.flatten_cons, List.append_assoc]
    rcases i with _ | i
    · rw [Nat.mul_zero, List.drop_zero, List.take_left' hb, List.getElem_cons_zero]
    · rw [show 64 * (i + 1) = b.length + 64 * i by rw [hb]; ring, ← List.drop_drop,
        List.drop_left, List.getElem_cons_succ]
      exact ih (fun c hc ↦ hbs c (by simp [hc])) (by simpa using hi)

/-- **The chain lemma** (C5): a chain absorbing whole blocks `bs` from the IV, then a row from its
cells over the rest `r` zero-filled, at the counter of the whole string with the last-block flag,
is the standard chain of `bs.flatten ++ r`. -/
theorem stdChain_snoc {bs : List (List UInt8)} {c : List BlakeRow} (hc : BlockChain bs c)
    {b : BlakeRow} (hb : b.cv = cellWords (chainState c).1 ++ cellWords (chainState c).2)
    {r : List UInt8} (hr : r.length ≤ 64) (hr' : bs = [] ∨ r ≠ [])
    (hm : blockBytes b.m = r ++ List.replicate (64 - r.length) 0)
    (hmd : b.md = metadataCell (64 * bs.length + r.length) true) :
    StdChain (bs.flatten ++ r) (c ++ [b]) := by
  obtain ⟨rfl, hl, hmd'⟩ := hc
  have h64 : ∀ x ∈ c.map (fun b ↦ blockBytes b.m), x.length = 64 := by simp
  have hlen := length_flatten_of_64 _ h64
  rw [List.length_map] at hlen
  have hx : (((c.map fun b ↦ blockBytes b.m).flatten ++ r).length - 1) / 64 = c.length := by
    rw [List.length_append, hlen]
    rcases hr' with h | h
    · obtain rfl : c = [] := List.map_eq_nil_iff.mp h
      simp only [List.length_nil]
      omega
    · have := List.length_pos_of_ne_nil h
      omega
  refine ⟨by rw [hx, List.length_append, List.length_singleton], hl.snoc hb, ?_, ?_⟩
  · intro i hi
    rw [List.length_append, List.length_singleton] at hi
    rw [List.getElem_append_left (by omega), messageWords_eq_blockWords,
      take_drop_flatten_append h64 r (by simpa using hi), List.getElem_map]
    exact ⟨rfl, hmd' i (by omega)⟩
  · intro _
    simp only [List.length_append, List.length_singleton, Nat.add_sub_cancel,
      List.getElem_concat_length]
    rw [messageWords_eq_blockWords, hm, blockWords_append_zeros, hmd, unpackMetadata_metadataCell,
      List.length_map, ← hlen, List.drop_left]
    exact ⟨rfl, rfl⟩

/-- The empty prefix is the IV. -/
theorem tablePrefix_nil (rows : List BlakeRow) : TablePrefix rows [] ivCells :=
  ⟨[], fun _ h ↦ absurd h List.not_mem_nil,
    ⟨rfl, fun _ h ↦ absurd h (by simp), fun _ h ↦ absurd h (by simp)⟩, by simp [chainState]⟩

/-- A non-final row of the table, at the counter of the bytes up to it, extends a prefix. -/
theorem tablePrefix_step {rows : List BlakeRow} {bs : List (List UInt8)} {st st' : E × E}
    {m : Fin 4 → E} (hp : TablePrefix rows bs st)
    (hc : (tableSem rows).check m st.1 st.2 st'.1 st'.2
      (metadataCell (64 * (bs.length + 1)) false)) :
    TablePrefix rows (bs ++ [blockBytes m]) st' := by
  obtain ⟨c, hrows, ⟨rfl, hl, hmd⟩, rfl⟩ := hp
  obtain ⟨_, hmem⟩ := hc
  rw [List.length_map] at hmem
  let b : BlakeRow := ⟨m, (chainState c).1, (chainState c).2, st'.1, st'.2,
    metadataCell (64 * (c.length + 1)) false⟩
  refine ⟨c ++ [b], ?_, ⟨by simp [b], hl.snoc rfl, ?_⟩, by simp [chainState, b]⟩
  · intro b' hb
    rcases List.mem_append.mp hb with hb | hb
    · exact hrows b' hb
    · exact List.mem_singleton.mp hb ▸ hmem
  · intro i hi
    rw [List.length_append, List.length_singleton] at hi
    rcases Nat.lt_or_ge i c.length with h | h
    · rw [List.getElem_append_left h]; exact hmd i h
    · obtain rfl : i = c.length := by omega
      rw [List.getElem_concat_length rfl, unpackMetadata_metadataCell]
      simp

/-- **The last row of a prefix** gives the log's answer for the whole string, when the table
passes the check at the log. -/
theorem tablePrefix_final {rows : List BlakeRow} {ℓ : Log} (h : TableOK (look ℓ) rows)
    {bs : List (List UInt8)} {st : E × E} {m : Fin 4 → E} {r : List UInt8} {out0 out1 : E}
    (hp : TablePrefix rows bs st) (hr : r.length ≤ 64) (hr' : bs = [] ∨ r ≠ [])
    (hm : blockBytes m = r ++ List.replicate (64 - r.length) 0)
    (hc : (tableSem rows).check m st.1 st.2 out0 out1
      (metadataCell (64 * bs.length + r.length) true)) :
    ∃ d, look ℓ (bs.flatten ++ r) = some d ∧ (out0, out1) = digestScalars d := by
  obtain ⟨c, hrows, hc', rfl⟩ := hp
  obtain ⟨hcan, hmem⟩ := hc
  have hs := stdChain_snoc hc' (b := ⟨m, (chainState c).1, (chainState c).2, out0, out1,
    metadataCell (64 * bs.length + r.length) true⟩) rfl hr hr' hm rfl
  have hrows' : ∀ b ∈ c ++ [⟨m, (chainState c).1, (chainState c).2, out0, out1,
      metadataCell (64 * bs.length + r.length) true⟩], b ∈ rows := by
    intro b hb
    rcases List.mem_append.mp hb with hb | hb
    · exact hrows b hb
    · exact List.mem_singleton.mp hb ▸ hmem
  have := h _ _ (by simp) hrows' hs
  rw [List.getElem_concat_length (by simp)] at this
  exact ⟨_, this, pair_eq_digestScalars_iff.mpr ⟨hcan.2.2.2.1, hcan.2.2.2.2.1, rfl⟩⟩

/-! ## The oracle model -/

/-- **The oracle model**: the table's semantics, every string the log answers answered by it; a
prefix's chaining value is free, only the table's standard chains are bound to the log, which
`TableOK` asks. -/
noncomputable def HashModel.oracle (rows : List BlakeRow) (ℓ : Log)
    (h : TableOK (look ℓ) rows) : HashModel where
  sem := tableSem rows
  canonical hc := hc.1
  H := look ℓ
  Prefix := TablePrefix rows
  prefix_nil := tablePrefix_nil rows
  prefix_step := tablePrefix_step
  final := tablePrefix_final h

/-! ## The execution bridge -/

/-- A step checks under `S'` what it checks under `S` when `S'` accepts the row it reads. -/
theorem executeWithB_of {S S' : BlakeSem} {read : K → Option E} {r r' : Regs K} {i : Instr}
    (hS : ∀ b, blakeRowAt read r i = some b → S.row b → S'.row b)
    (h : executeWithB S read r i = some r') : executeWithB S' read r i = some r' := by
  cases i with
  | blake2s om ocv oout omd =>
    simp only [executeWithB, Option.bind_eq_bind, Option.bind_eq_some_iff] at h ⊢
    obtain ⟨m0, h0, m1, h1, m2, h2, m3, h3, cv0, h4, cv1, h5, o0, h6, o1, h7, md, h8, u, hg, hr⟩ :=
      h
    have hc := hS ⟨![m0, m1, m2, m3], cv0, cv1, o0, o1, md⟩
      (by simp [blakeRowAt, h0, h1, h2, h3, h4, h5, h6, h7, h8])
      (show S.check _ _ _ _ _ _ by simpa [guard] using hg)
    exact ⟨m0, h0, m1, h1, m2, h2, m3, h3, cv0, h4, cv1, h5, o0, h6, o1, h7, md, h8, (),
      by simpa [guard] using (show S'.check _ _ _ _ _ _ from hc), hr⟩
  | _ => exact h

/-- The row a step reads checks, when the step succeeds. -/
theorem row_of_executeWithB {S : BlakeSem} {read : K → Option E} {r r' : Regs K} {i : Instr}
    {b : BlakeRow} (hb : blakeRowAt read r i = some b) (h : executeWithB S read r i = some r') :
    S.row b := by
  cases i with
  | blake2s om ocv oout omd =>
    simp only [executeWithB, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨m0, h0, m1, h1, m2, h2, m3, h3, cv0, h4, cv1, h5, o0, h6, o1, h7, md, h8, u, hg, -⟩ := h
    simp only [blakeRowAt, h0, h1, h2, h3, h4, h5, h6, h7, h8, Option.bind_eq_bind,
      Option.bind_some, Option.pure_def, Option.some.injEq] at hb
    subst hb
    show S.check _ _ _ _ _ _
    simpa [guard] using hg
  | _ => simp [blakeRowAt] at hb

/-- One step of `runRows`: a non-final step that succeeds contributes its row. -/
theorem runRows_succ {S : BlakeSem} {κ : ℕ} {prog : Program} {L : MemImage κ} {n : ℕ}
    {r r' : Regs K} {i : Instr} (hpc : r.pc ≠ prog.finalPc) (hf : prog.fetch r.pc = some i)
    (hs : stepB S prog L r = some r') :
    runRows S prog L (n + 1) r = (blakeRowAt L.read r i).toList ++ runRows S prog L n r' := by
  simp only [runRows, hpc, ↓reduceIte, hf, hs]

/-- **Every row of a run checks**: `runRows` lists only the rows of the steps that succeed. -/
theorem row_of_mem_runRows {S : BlakeSem} {κ : ℕ} {prog : Program} {L : MemImage κ} :
    ∀ {n : ℕ} {r : Regs K} {b : BlakeRow}, b ∈ runRows S prog L n r → S.row b
  | 0, _, _, h => absurd h List.not_mem_nil
  | n + 1, r, b, h => by
    by_cases hpc : r.pc = prog.finalPc
    · simp [runRows, hpc] at h
    cases hf : prog.fetch r.pc with
    | none => simp [runRows, hpc, hf] at h
    | some i =>
      cases hs : stepB S prog L r with
      | none => simp [runRows, hpc, hf, hs] at h
      | some r' =>
        rw [runRows_succ hpc hf hs] at h
        rcases List.mem_append.mp h with h | h
        · simp only [stepB, hf, Option.bind_eq_bind, Option.bind_some] at hs
          exact row_of_executeWithB (Option.mem_toList.mp h) hs
        · exact row_of_mem_runRows h

/-- **A run under `S` is a run under `S'`** when `S'` accepts every row the run performs. -/
theorem runB_of_runRows {S S' : BlakeSem} {κ : ℕ} {prog : Program} {L : MemImage κ} :
    ∀ {n : ℕ} {r rf : Regs K}, (∀ b ∈ runRows S prog L n r, S.row b → S'.row b) →
      runB S prog L n r = some rf → runB S' prog L n r = some rf
  | 0, _, _, _, h => h
  | n + 1, r, rf, hS, h => by
    by_cases hpc : r.pc = prog.finalPc
    · simp [runB, hpc] at h
    simp only [runB, hpc, ↓reduceIte, Option.bind_eq_bind, Option.bind_eq_some_iff] at h ⊢
    obtain ⟨r', hs, hrun⟩ := h
    obtain ⟨i, hf, he⟩ := Option.bind_eq_some_iff.mp hs
    rw [runRows_succ hpc hf hs] at hS
    refine ⟨r', ?_, runB_of_runRows (fun b hb ↦ hS b (List.mem_append_right _ hb)) hrun⟩
    simp only [stepB, hf, Option.bind_eq_bind, Option.bind_some]
    exact executeWithB_of (fun b hb ↦ hS b (List.mem_append_left _ (Option.mem_toList.mpr hb))) he

/-- A valid Flock-blind execution is valid under any table holding its rows. -/
theorem validExecutionB_tableSem {prog : Program} {input : PublicInput} {t : Trace prog}
    {rows : List BlakeRow} (h : ValidExecutionB blakeFree prog input t)
    (hrows : ∀ b ∈ t.blakeRows blakeFree, b ∈ rows) :
    ValidExecutionB (tableSem rows) prog input t :=
  ⟨h.1, runB_of_runRows (S := blakeFree) (fun b hb hc ↦ ⟨hc, hrows b hb⟩) h.2⟩

/-- **A deployed execution is a Flock-blind one**: the compression's cells are canonical. -/
theorem validExecutionB_blakeFree_of_valid {prog : Program} {input : PublicInput} {t : Trace prog}
    (h : ValidExecution prog input t) : ValidExecutionB blakeFree prog input t := by
  rw [← validExecutionB_deployed] at h
  exact ⟨h.1, runB_of_runRows (S := blakeDeployed)
    (fun _ _ hc ↦ canonicalCells_of_compressCells hc) h.2⟩

/-- **The execution bridge**: a Flock-blind execution is valid exactly when it is valid under
its own table. -/
theorem validExecutionB_tableSem_iff (prog : Program) (input : PublicInput) (t : Trace prog) :
    ValidExecutionB (tableSem (t.blakeRows blakeFree)) prog input t ↔
      ValidExecutionB blakeFree prog input t :=
  ⟨fun h ↦ ⟨h.1, runB_of_runRows (S := tableSem (t.blakeRows blakeFree)) (S' := blakeFree)
      (fun _ _ hc ↦ hc.1) h.2⟩,
    fun h ↦ validExecutionB_tableSem h fun _ hb ↦ hb⟩

/-- The bridge at the oracle model of an execution's table. -/
theorem validExecutionB_oracle {prog : Program} {input : PublicInput} {t : Trace prog} {ℓ : Log}
    (hok : TableOK (look ℓ) (t.blakeRows blakeFree)) (h : ValidExecutionB blakeFree prog input t) :
    ValidExecutionB (HashModel.oracle (t.blakeRows blakeFree) ℓ hok).sem prog input t :=
  (validExecutionB_tableSem_iff prog input t).mpr h

/-! ## The deployed direction -/

/-- A row of the compression function: its output is the compression of its inputs. -/
theorem out_eq_compress {b : BlakeRow} (h : blakeDeployed.row b) :
    b.out = compress b.cv (messageWords b.m) (unpackMetadata b.md).1 (unpackMetadata b.md).2.1
      (unpackMetadata b.md).2.2 :=
  h.2.2.2.2.2.2

/-- A standard chain of compressions, from row `j`, computes `absorb` of the bytes from `64j`. -/
theorem stdChain_out_eq_absorb {x : List UInt8} {c : List BlakeRow} (hc : StdChain x c)
    (hcomp : ∀ b ∈ c, blakeDeployed.row b) (hpos : 0 < c.length) :
    ∀ (k j : ℕ) (hj : j + k = c.length - 1),
      (c[c.length - 1]'(by omega)).out = absorb (c[j]'(by omega)).cv (64 * j) k (x.drop (64 * j))
  | 0, j, hj => by
    obtain rfl : j = c.length - 1 := hj
    have hb := out_eq_compress (hcomp _ (List.getElem_mem (show c.length - 1 < c.length by omega)))
    obtain ⟨hm, hmd⟩ := hc.2.2.2 hpos
    rw [hm, hmd] at hb
    have := hc.1
    rw [hb, absorb, List.length_drop,
      show 64 * (c.length - 1) + (x.length - 64 * (c.length - 1)) = x.length by omega]
  | k + 1, j, hj => by
    have hb := out_eq_compress (hcomp _ (List.getElem_mem (show j < c.length by omega)))
    obtain ⟨hm, hmd⟩ := hc.2.2.1 j (by omega)
    rw [hm, hmd] at hb
    have hl := hc.2.1 (j + 1) (by omega)
    simp only [Nat.add_one_ne_zero, ↓reduceDIte, Nat.add_sub_cancel] at hl
    rw [stdChain_out_eq_absorb hc hcomp hpos k (j + 1) (by omega), hl, hb, absorb,
      List.drop_drop, Nat.mul_add, Nat.mul_one]

/-- **A standard chain of compressions computes BLAKE2s-256.** -/
theorem stdChain_out_eq_blake2sBytes {x : List UInt8} {c : List BlakeRow} (hc : StdChain x c)
    (hcomp : ∀ b ∈ c, blakeDeployed.row b) (hpos : 0 < c.length) :
    (c[c.length - 1]'(by omega)).out = blake2sBytes x := by
  have h0 := hc.2.1 0 hpos
  simp only [↓reduceDIte] at h0
  rw [stdChain_out_eq_absorb hc hcomp hpos (c.length - 1) 0 (by omega), h0, blake2sBytes, hc.1]
  rfl

/-- **The deployed table check** (T7′'s table part): rows of the compression function pass the
table check at BLAKE2s-256. -/
theorem tableOK_blake2s {rows : List BlakeRow} (h : ∀ b ∈ rows, blakeDeployed.row b) :
    TableOK (fun x ↦ some (blake2sBytes x)) rows :=
  fun _ _ hpos hc hs ↦
    congrArg some (stdChain_out_eq_blake2sBytes hs (fun b hb ↦ h b (hc b hb)) hpos).symm

/-- The rows of a deployed run pass the table check at BLAKE2s-256. -/
theorem tableOK_blakeRows_deployed {prog : Program} (t : Trace prog) :
    TableOK (fun x ↦ some (blake2sBytes x)) (t.blakeRows blakeDeployed) :=
  tableOK_blake2s fun _ hb ↦ row_of_mem_runRows hb

end
end LeanVM.Guest.Value
