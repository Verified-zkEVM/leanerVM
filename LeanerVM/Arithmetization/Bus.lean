/-
  LeanerVM.Arithmetization.Bus

  Soundness of the two lookups of the leanISA bus: in a witness of the constraint statement,
  every pulled memory tuple is a correct read of the committed image and every pulled bytecode
  tuple is an entry of the public program at the pulled counter.
-/

module

public import LeanerVM.Arithmetization.Rows

@[expose] public section

/-!
# Lookup soundness

Specification §6.2 "The lookup protocol" (`doc/leanvm/body/06-bus-interactions.tex:34-82` at
leanVM pin `a386121f84292f6fa663aaa3e570c15bc0240ea2`: Lemma 6.3 `:51`, Theorem 6.4 `:59`,
Corollary 6.5 `:70`, "Instance caps" `:80`). Category A for the argument, which is
the specification's; Category B for what it is applied to, the memory and bytecode pairs as
the components transcribe them (`LeanerVM.Arithmetization.Rows`). Artifact: the accept
relation `SatisfiedBy`. Direction: soundness, from an accepted witness to facts about its
pulls. Contribution: T1-S through BC (`docs/architecture.md`), the lookup half of constraint
soundness.

**Lemma 6.3** (`eq_zero_of_perm_map_mul_g`). A list of counts `C` that is a permutation of
`C.map (g * ·)` and has fewer than `2^64 - 1` elements holds only `0`: multiplication by `g`
keeps every multiplicity, so a nonzero count `c` brings its whole orbit `g^k · c`,
`k < 2^64 - 1`, which is `2^64 - 1` distinct elements because `g` has full order.

**Theorem 6.4, generic** (`lookup_sound`). Messages are anything with a key (the address and
the value), a count and a bump (the push of a read, its count multiplied by `g`, its key
unchanged). If the pushes, the bumped reads and the seeds, are a permutation of the pulls, the
reads and the finalizes, every read count is nonzero, there are fewer than `2^64 - 1` reads,
and every seed and finalize has a good key, then every read has a good key: the messages with
a bad key are reads on both sides, and their counts satisfy Lemma 6.3.

**The two lookups.** `mem_channel_sound` and `bytecode_channel_sound` apply it to a witness of
`SatisfiedBy`, with the messages as coordinate lists, the key every coordinate but the count,
the reads the six opcode tables' pulls, and the seeds and finalizes the rows of the memory
block, respectively the bytecode block. The verifier's facts are those of `SatisfiedBy` alone:
the balance of the pair, `CountsNonzero`, the heights of `Caps` (each table has at most
`2^32` rows and a row reads at most nine cells and one entry, so at most `9 · 6 · 2^32`
memory reads and `6 · 2^32` bytecode reads, §6.2 "Instance caps"), and the block conjuncts:
`SeedRowsAreTheImage` with `IndexColumnsAreRowIndices` make every memory block message's key
`(g^i, mem[i])`, and `BytecodeRowsAreTheProgram prog` every bytecode block message's
`(g^i, entry (prog.code i))`. The conclusions cover every pull on the channel, the blocks'
finalizes included. A memory pull's conclusion is its channel guarantee
(`MemPull.Guarantees`, which is Corollary 6.5 as well: the address is in range); a bytecode
pull's is the strong form, the entry is the program's at the pulled counter, which implies the
decoding guarantee `BytecodePull.Guarantees` (`decode_entry`).

**Messages, table by table.** `messagesOn_split` splits a witness's messages on a channel into
the verifier's, the six opcode tables' and the two blocks' (`rowsOn`, `tables_eq_take_append`),
and `rowsOn_single_nil` drops a table that sends nothing on the channel.

## Wrong readings excluded

* Lemma 6.3 concludes that every count is `0`, not that the list is empty: a read with count
  `0` pulls and pushes the same tuple and balances itself, whatever its address and value, and
  only the count product rejects it (the tests).
* Balance is a permutation counted in `ℕ`: a field sum over `K`, of characteristic `2`, would
  cancel any message pushed twice.
* The block rows' keys are what the verifier fixes: with the index column free, a memory block
  row that seeds and finalizes `(g^j, mem[i])` for some `j ≠ i` balances by itself, and its
  pull is a wrong read (the tests).
-/

namespace LeanerVM.Arithmetization

open LeanerVM.Parameters LeanerVM.Semantics
open Air.Flat (Component EnsembleWitness)

/-! ## Invariant count lists -/

/-- Specification Lemma 6.3 (invariant count multisets): a list of counts that is a permutation
of itself multiplied by `g`, with fewer than `2^64 - 1` elements, holds only `0`. -/
theorem eq_zero_of_perm_map_mul_g {C : List K} (h : (C.map (g * ·)).Perm C)
    (hlen : C.length < 2 ^ 64 - 1) : ∀ c ∈ C, c = 0 := by
  have hcount : ∀ x, C.count (g * x) = C.count x := fun x ↦ by
    rw [← h.count_eq (g * x), List.count_map_of_injective _ _ (mul_right_injective₀ g_ne_zero)]
  have hpow : ∀ k x, C.count (g ^ k * x) = C.count x := by
    intro k
    induction k with
    | zero => intro x; rw [pow_zero, one_mul]
    | succ k ih => intro x; rw [pow_succ', mul_assoc, hcount, ih]
  intro c hc
  by_contra hc0
  have hnodup : ((List.range (2 ^ 64 - 1)).map fun k ↦ g ^ k * c).Nodup :=
    List.Nodup.map_on (fun a ha b hb hab ↦ gpow_injOn (List.mem_range.mp ha)
      (List.mem_range.mp hb) (mul_right_cancel₀ hc0 hab)) List.nodup_range
  have hsub : ((List.range (2 ^ 64 - 1)).map fun k ↦ g ^ k * c) ⊆ C := by
    intro y hy
    obtain ⟨k, -, rfl⟩ := List.mem_map.mp hy
    rw [← List.count_pos_iff, hpow]
    exact List.count_pos_iff.mpr hc
  have hle := (List.subperm_of_subset hnodup hsub).length_le
  rw [List.length_map, List.length_range] at hle
  omega

/-! ## The generic lookup theorem -/

/-- Specification Theorem 6.4 (lookup correctness), for any messages with a key, a count and a
bump that keeps the key and multiplies the count by `g`: if the pushes (the bumped reads and
the seeds) are a permutation of the pulls (the reads and the finalizes), every read count is
nonzero, there are fewer than `2^64 - 1` reads, and every seed and finalize has a good key,
then every read has a good key. -/
theorem lookup_sound {M κ : Type} [DecidableEq κ] {key : M → κ} {count : M → K}
    {bump : M → M} (key_bump : ∀ m, key (bump m) = key m)
    (count_bump : ∀ m, count (bump m) = g * count m) {Good : κ → Prop}
    {reads seeds fins : List M} (balanced : (reads.map bump ++ seeds).Perm (reads ++ fins))
    (seeds_good : ∀ m ∈ seeds, Good (key m)) (fins_good : ∀ m ∈ fins, Good (key m))
    (counts_ne : ∀ m ∈ reads, count m ≠ 0) (length_lt : reads.length < 2 ^ 64 - 1) :
    ∀ m ∈ reads, Good (key m) := by
  intro m hm
  by_contra hbad
  let p : M → Bool := fun m' ↦ decide (key m' = key m)
  have hnil : ∀ l : List M, (∀ m' ∈ l, Good (key m')) → l.filter p = [] := fun l hl ↦
    List.filter_eq_nil_iff.mpr fun m' hm' hpm ↦ hbad (by
      rw [← of_decide_eq_true hpm]; exact hl m' hm')
  have hbal := balanced.filter p
  rw [List.filter_append, List.filter_append, hnil seeds seeds_good, hnil fins fins_good,
    List.append_nil, List.append_nil, List.filter_map,
    show p ∘ bump = p from funext fun m' ↦ by simp only [Function.comp_apply, p, key_bump]]
    at hbal
  have hC := hbal.map count
  rw [List.map_map, show count ∘ bump = (g * ·) ∘ count from funext count_bump,
    ← List.map_map] at hC
  have hzero := eq_zero_of_perm_map_mul_g hC
    (by rw [List.length_map]; exact lt_of_le_of_lt (List.length_filter_le _ _) length_lt)
  exact counts_ne m hm (hzero _ (List.mem_map_of_mem (List.mem_filter.mpr ⟨hm, by simp [p]⟩)))

/-! ## A witness's messages, table by table -/

variable {prog : Program} {input : PublicInput}

/-- The messages of a list of tables on a channel, row by row. -/
def rowsOn (ts : List (Air.Flat.Table K)) (c : RawChannel K) : List (Array K) :=
  ts.flatMap fun t ↦ t.table.flatMap fun row ↦ rowMessagesOn t row c

/-- A witness's tables are the six opcode tables and the two blocks. -/
theorem tables_eq_take_append (w : EnsembleWitness (leanIsaEnsemble prog)) :
    w.tables = w.tables.take 6 ++ [tableAt w 6, tableAt w 7] := by
  have hlen : w.tables.length = 8 := w.same_length.symm
  conv_lhs => rw [← List.take_append_drop 6 w.tables]
  rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons (by omega),
    List.drop_eq_nil_of_le (by omega)]
  rfl

/-- A witness's messages on a channel: the verifier's, the six opcode tables', the memory
block's and the bytecode block's. -/
theorem messagesOn_split (w : EnsembleWitness (leanIsaEnsemble prog)) (c : RawChannel K) :
    messagesOn w c = rowsOn [w.verifierTable] c ++ rowsOn (w.tables.take 6) c ++
      rowsOn [tableAt w 6] c ++ rowsOn [tableAt w 7] c := by
  rw [messagesOn_eq_flatMap, EnsembleWitness.allTables]
  conv_lhs => rw [tables_eq_take_append w]
  simp only [rowsOn, List.flatMap_cons, List.flatMap_append, List.flatMap_nil, List.append_nil,
    List.append_assoc]

/-- A table whose every row sends nothing on `c` contributes nothing. -/
theorem rowsOn_single_nil {t : Air.Flat.Table K} {c : RawChannel K}
    (h : ∀ row, rowMessagesOn t row c = []) : rowsOn [t] c = [] := by
  simp only [rowsOn, List.flatMap_cons, List.flatMap_nil, List.append_nil, h]
  exact List.flatMap_eq_nil_iff.mpr fun _ _ ↦ rfl

/-- The memory block's component is `memTable`. -/
theorem tableAt_six_component (w : EnsembleWitness (leanIsaEnsemble prog)) :
    (tableAt w 6).component = ⟨memTable⟩ :=
  (tableAt_component w 6).trans rfl

/-- The bytecode block's component is `bytecodeTable`. -/
theorem tableAt_seven_component (w : EnsembleWitness (leanIsaEnsemble prog)) :
    (tableAt w 7).component = ⟨bytecodeTable⟩ :=
  (tableAt_component w 7).trans rfl

/-! ## Proof helpers -/

/-- The key of a bus message as a coordinate list: every coordinate but the count. -/
private def readKey (l : List K) : List K := l.eraseIdx 1

/-- The count of a bus message as a coordinate list, coordinate `1`. -/
private def readCount (l : List K) : K := l.getD 1 0

/-- The push of a read as a coordinate list: the count multiplied by `g`. -/
private def readBump (l : List K) : List K := l.modify 1 (g * ·)

private theorem readKey_readBump (l : List K) : readKey (readBump l) = readKey l := by
  rcases l with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> rfl

private theorem readCount_readBump (l : List K) : readCount (readBump l) = g * readCount l := by
  rcases l with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> first | rfl | exact (mul_zero g).symm

/-- A memory read's push, as coordinates. -/
private theorem memMsg_bump_toList (m : MemMsg K) :
    (toElements m.bump).toArray.toList = readBump (toElements m).toArray.toList := by
  rw [Vector.toList_toArray, Vector.toList_toArray, memMsg_toElements, memMsg_toElements]
  rfl

/-- A bytecode read's push, as coordinates. -/
private theorem bytecodeMsg_bump_toList (m : BytecodeMsg K) :
    (toElements m.bump).toArray.toList = readBump (toElements m).toArray.toList := by
  rw [Vector.toList_toArray, Vector.toList_toArray, bytecodeMsg_toElements,
    bytecodeMsg_toElements]
  rfl

/-- The verifier sends nothing on a lookup channel. -/
private theorem rowsOn_verifier (w : EnsembleWitness (leanIsaEnsemble prog)) {c : RawChannel K}
    (h1 : c.name ≠ StatePush.name) (h2 : c.name ≠ StatePull.name) :
    rowsOn [w.verifierTable] c = [] :=
  rowsOn_single_nil fun row ↦ by
    rw [verifier_rowMessagesOn (prog := prog) rfl, ite_eq_right h1, ite_eq_right h2]

/-- On a memory channel, a witness's messages are the six opcode tables' and the memory
block's. -/
private theorem messagesOn_memChannel (w : EnsembleWitness (leanIsaEnsemble prog))
    {c : RawChannel K} (hc : c.name = MemPull.name ∨ c.name = MemPush.name) :
    messagesOn w c = rowsOn (w.tables.take 6) c ++ rowsOn [tableAt w 6] c := by
  rcases hc with hc | hc <;>
  rw [messagesOn_split, rowsOn_verifier w (by rw [hc]; decide) (by rw [hc]; decide),
    rowsOn_single_nil (t := tableAt w 7) fun row ↦ by
      rw [bytecodeBlock_rowMessagesOn (tableAt_seven_component w) row rfl, hc,
        ite_eq_right (by decide), ite_eq_right (by decide)], List.nil_append, List.append_nil]

/-- On a bytecode channel, a witness's messages are the six opcode tables' and the bytecode
block's. -/
private theorem messagesOn_bytecodeChannel (w : EnsembleWitness (leanIsaEnsemble prog))
    {c : RawChannel K} (hc : c.name = BytecodePull.name ∨ c.name = BytecodePush.name) :
    messagesOn w c = rowsOn (w.tables.take 6) c ++ rowsOn [tableAt w 7] c := by
  rcases hc with hc | hc <;>
  rw [messagesOn_split, rowsOn_verifier w (by rw [hc]; decide) (by rw [hc]; decide),
    rowsOn_single_nil (t := tableAt w 6) fun row ↦ by
      rw [memBlock_rowMessagesOn (tableAt_six_component w) row rfl, hc,
        ite_eq_right (by decide), ite_eq_right (by decide)], List.nil_append, List.append_nil]

/-- At most `L · n` messages from a list of tables of at most `L` rows each sending at most `n`
messages. -/
private theorem length_rowsOn_le {ts : List (Air.Flat.Table K)} {c : RawChannel K} {L n : ℕ}
    (hL : ∀ t ∈ ts, t.table.length ≤ L) (hn : ∀ t ∈ ts, ∀ row, (rowMessagesOn t row c).length ≤ n) :
    (rowsOn ts c).length ≤ ts.length * (L * n) := by
  rw [rowsOn, List.length_flatMap]
  refine (List.sum_le_length_nsmul _ _ ?_).trans (by rw [List.length_map, smul_eq_mul])
  simp only [List.mem_map]
  rintro _ ⟨t, ht, rfl⟩
  rw [List.length_flatMap]
  refine (List.sum_le_length_nsmul _ n ?_).trans ?_
  · simp only [List.mem_map]
    rintro _ ⟨row, -, rfl⟩
    exact hn t ht row
  · rw [List.length_map, smul_eq_mul]
    exact Nat.mul_le_mul_right n (hL t ht)

/-- Every table of a witness satisfying the caps has at most `2^32` rows. -/
private theorem length_table_le {w : EnsembleWitness (leanIsaEnsemble prog)} (h : Caps w) :
    ∀ t ∈ w.tables, t.table.length ≤ 2 ^ 32 := by
  intro t ht
  obtain ⟨τ, hτ, hlen⟩ := h.heights t ht
  rw [hlen]
  exact Nat.pow_le_pow_right (by norm_num) hτ

/-- A row of the opcode tables pushes its pulls on a lookup pair, bumped. -/
private theorem rowsOn_push_eq {w : EnsembleWitness (leanIsaEnsemble prog)}
    {pull push : RawChannel K}
    (hrow : ∀ t ∈ w.tables.take 6, ∀ row, (rowMessagesOn t row push).map Array.toList =
      (rowMessagesOn t row pull).map (readBump ∘ Array.toList)) :
    (rowsOn (w.tables.take 6) push).map Array.toList =
      ((rowsOn (w.tables.take 6) pull).map Array.toList).map readBump := by
  simp only [rowsOn, List.map_flatMap, List.map_map]
  exact List.flatMap_congr fun t ht ↦ List.flatMap_congr fun row _ ↦ hrow t ht row

/-- The reads of a lookup pair, their counts nonzero, given each pulled message has at least
two coordinates. -/
private theorem readCount_ne {w : EnsembleWitness (leanIsaEnsemble prog)} (h : CountsNonzero w)
    {pull : RawChannel K} (hname : pull.name = MemPull.name ∨ pull.name = BytecodePull.name)
    (hsize : ∀ t ∈ w.tables.take 6, ∀ row, ∀ a ∈ rowMessagesOn t row pull, 1 < a.size) :
    ∀ l ∈ (rowsOn (w.tables.take 6) pull).map Array.toList, readCount l ≠ 0 := by
  intro l hl
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hl
  obtain ⟨t, ht, ha⟩ := List.mem_flatMap.mp ha
  obtain ⟨row, hrow, ha⟩ := List.mem_flatMap.mp ha
  obtain ⟨i, hi, hiname, rfl⟩ := exists_interaction_of_mem_rowMessagesOn hrow ha
  have hs := hsize t ht row _ ha
  have hne := h t ht i hi (by rw [hiname]; exact hname) hs
  rwa [readCount, List.getD_eq_getElem _ _ (by rwa [Array.length_toList]), Array.getElem_toList]

/-! ## The memory lookup -/

/-- A memory message's key is its address and its value. -/
private theorem readKey_memMsg (m : MemMsg K) :
    readKey (toElements m).toArray.toList = m.addr :: m.v.toList := by
  rw [Vector.toList_toArray, memMsg_toElements]
  rfl

/-- The good memory keys: an address `g^i` of the image and the word there. -/
private def MemGood (w : EnsembleWitness (leanIsaEnsemble prog)) (k : List K) : Prop :=
  ∃ i : Fin (2 ^ (imageOf w.data).1), k = gpow i ::
    [((imageOf w.data).2 i).limb 0, ((imageOf w.data).2 i).limb 1, ((imageOf w.data).2 i).limb 2]

/-- Every message of the memory block has a good key. -/
private theorem memBlock_good {w : EnsembleWitness (leanIsaEnsemble prog)}
    (h : SatisfiedBy prog input w) {c : RawChannel K} :
    ∀ l ∈ (rowsOn [tableAt w 6] c).map Array.toList, MemGood w (readKey l) := by
  obtain ⟨idx, cntFin, hrows⟩ := h.seed_rows
  intro l hl
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hl
  simp only [rowsOn, List.flatMap_cons, List.flatMap_nil, List.append_nil] at ha
  obtain ⟨row, hrow, ha⟩ := List.mem_flatMap.mp ha
  have hrow' : row ∈ memBlockRows w := hrow
  rw [hrows, List.mem_ofFn] at hrow'
  obtain ⟨i, rfl⟩ := hrow'
  have hidx := h.index_columns i (by rw [hrows, List.length_ofFn]; exact i.isLt)
  simp only [hrows, List.getElem_ofFn, Fin.eta, memRowAt_toElements] at hidx
  rw [memBlock_rowMessagesOn (tableAt_six_component w) _ (rowAt_toElements _ _)] at ha
  refine ⟨i, ?_⟩
  split_ifs at ha <;> simp only [List.mem_singleton, List.not_mem_nil] at ha <;> subst ha <;>
    rw [readKey_memMsg] <;> exact congrArg₂ _ hidx rfl

/-- In a witness of the statement, every read of the six opcode tables reads the image: the
memory pair, the counts and the caps, through Theorem 6.4. -/
private theorem memReads_good {w : EnsembleWitness (leanIsaEnsemble prog)}
    (h : SatisfiedBy prog input w) :
    ∀ l ∈ (rowsOn (w.tables.take 6) MemPull.toRaw).map Array.toList, MemGood w (readKey l) := by
  have hsends := exists_sendsOpcode w
  have hbal := List.Perm.map Array.toList h.mem_balanced
  rw [messagesOn_memChannel w (Or.inr rfl), messagesOn_memChannel w (Or.inl rfl), List.map_append,
    List.map_append, rowsOn_push_eq (pull := MemPull.toRaw) fun t ht row ↦ by
    obtain ⟨s, hs, -⟩ := hsends t ht row
    simp only [hs.mem_push, hs.mem_pull, List.map_map]
    exact List.map_congr_left fun m _ ↦ memMsg_bump_toList m] at hbal
  refine lookup_sound readKey_readBump readCount_readBump hbal (memBlock_good h) (memBlock_good h)
    (readCount_ne h.counts_nonzero (Or.inl rfl) fun t ht row a ha ↦ ?_) ?_
  · obtain ⟨s, hs, -⟩ := hsends t ht row
    rw [hs.mem_pull, List.mem_map] at ha
    obtain ⟨m, -, rfl⟩ := ha
    rw [Vector.size_toArray]
    decide
  · rw [List.length_map]
    refine lt_of_le_of_lt (length_rowsOn_le (L := 2 ^ 32) (n := 9) (fun t ht ↦
      length_table_le h.caps t (List.mem_of_mem_take ht)) fun t ht row ↦ ?_) ?_
    · obtain ⟨s, hs, hlen⟩ := hsends t ht row
      rw [hs.mem_pull, List.length_map]
      exact hlen
    · exact lt_of_le_of_lt (Nat.mul_le_mul_right _ (List.length_take_le _ _)) (by norm_num)

/-- Specification Theorem 6.4 and Corollary 6.5 on the memory pair: in a witness of the
constraint statement, every pulled memory tuple, the six tables' reads and the memory block's
finalizes, is a correct read of the image the data names; in particular its address is in
range. -/
theorem mem_channel_sound {w : EnsembleWitness (leanIsaEnsemble prog)}
    (h : SatisfiedBy prog input w) :
    ∀ i ∈ w.interactions, i.channel.name = MemPull.name →
      ∀ m : MemMsg K, i.msg = (toElements m).toArray → MemPull.Guarantees m w.data := by
  intro i hi hname m hm
  have hmem : i.msg ∈ messagesOn w MemPull.toRaw :=
    List.mem_map_of_mem (List.mem_filter.mpr ⟨hi, decide_eq_true hname⟩)
  rw [messagesOn_memChannel w (Or.inl rfl), List.mem_append] at hmem
  have hgood : MemGood w (readKey i.msg.toList) := by
    rcases hmem with hmem | hmem
    · exact memReads_good h _ (List.mem_map_of_mem hmem)
    · exact memBlock_good h _ (List.mem_map_of_mem hmem)
  obtain ⟨j, hj⟩ := hgood
  rw [hm, readKey_memMsg, List.cons.injEq] at hj
  obtain ⟨haddr, hv⟩ := hj
  have hv' : m.v = #v[((imageOf w.data).2 j).limb 0, ((imageOf w.data).2 j).limb 1,
      ((imageOf w.data).2 j).limb 2] := Vector.toList_inj.mp hv
  show (imageOf w.data).2.read m.addr = some (E.ofLimbs m.v[0] m.v[1] m.v[2])
  have hκ : (imageOf w.data).1 < 64 := lt_of_le_of_lt (Nat.min_le_right _ _) (by decide)
  rw [haddr, hv', MemImage.read_gpow hκ]
  exact congrArg some (ofLimbs_limb _).symm

/-! ## The bytecode lookup -/

/-- A bytecode message's key is its counter and its entry. -/
private theorem readKey_bytecodeMsg (m : BytecodeMsg K) :
    readKey (toElements m).toArray.toList = m.pc :: (#v[m.opcode] ++ m.op).toList := by
  rw [Vector.toList_toArray, bytecodeMsg_toElements, Vector.toList_append]
  rfl

/-- The good bytecode keys: a counter `g^i` of the program and the entry there. -/
private def BytecodeGood (prog : Program) (k : List K) : Prop :=
  ∃ i : Fin (2 ^ prog.logSize), k = gpow i :: (entry (prog.code i)).toList

/-- Every message of the bytecode block has a good key. -/
private theorem bytecodeBlock_good {w : EnsembleWitness (leanIsaEnsemble prog)}
    (h : SatisfiedBy prog input w) {c : RawChannel K} :
    ∀ l ∈ (rowsOn [tableAt w 7] c).map Array.toList, BytecodeGood prog (readKey l) := by
  obtain ⟨cntFin, hrows⟩ := h.bytecode_rows
  intro l hl
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hl
  simp only [rowsOn, List.flatMap_cons, List.flatMap_nil, List.append_nil] at ha
  obtain ⟨row, hrow, ha⟩ := List.mem_flatMap.mp ha
  have hrow' : row ∈ bytecodeBlockRows w := hrow
  rw [hrows, List.mem_ofFn] at hrow'
  obtain ⟨i, rfl⟩ := hrow'
  have hr := rowAt_toElements (tableAt w 7).data (bytecodeRowOf prog i (cntFin i))
  rw [bytecodeBlock_rowMessagesOn (tableAt_seven_component w) _ hr] at ha
  refine ⟨i, ?_⟩
  have he : #v[(bytecodeRowOf prog i (cntFin i)).opcode] ++ (bytecodeRowOf prog i (cntFin i)).op =
      entry (prog.code i) := by
    ext j hj
    interval_cases j <;> rfl
  split_ifs at ha <;> simp only [List.mem_singleton, List.not_mem_nil] at ha <;> subst ha <;>
    rw [readKey_bytecodeMsg] <;> exact congrArg _ (congrArg Vector.toList he)

/-- In a witness of the statement, every bytecode read of the six opcode tables reads the
program: the bytecode pair, the counts and the caps, through Theorem 6.4. -/
private theorem bytecodeReads_good {w : EnsembleWitness (leanIsaEnsemble prog)}
    (h : SatisfiedBy prog input w) :
    ∀ l ∈ (rowsOn (w.tables.take 6) BytecodePull.toRaw).map Array.toList,
      BytecodeGood prog (readKey l) := by
  have hsends := exists_sendsOpcode w
  have hbal := List.Perm.map Array.toList h.bytecode_balanced
  rw [messagesOn_bytecodeChannel w (Or.inr rfl), messagesOn_bytecodeChannel w (Or.inl rfl),
    List.map_append, List.map_append, rowsOn_push_eq (pull := BytecodePull.toRaw) fun t ht row ↦ by
    obtain ⟨s, hs, -⟩ := hsends t ht row
    rw [hs.bytecode_push, hs.bytecode_pull, List.map_singleton, List.map_singleton,
      Function.comp_apply, bytecodeMsg_bump_toList]] at hbal
  refine lookup_sound readKey_readBump readCount_readBump hbal (bytecodeBlock_good h)
    (bytecodeBlock_good h)
    (readCount_ne h.counts_nonzero (Or.inr rfl) fun t ht row a ha ↦ ?_) ?_
  · obtain ⟨s, hs, -⟩ := hsends t ht row
    rw [hs.bytecode_pull, List.mem_singleton] at ha
    subst ha
    rw [Vector.size_toArray]
    decide
  · rw [List.length_map]
    refine lt_of_le_of_lt (length_rowsOn_le (L := 2 ^ 32) (n := 1) (fun t ht ↦
      length_table_le h.caps t (List.mem_of_mem_take ht)) fun t ht row ↦ ?_) ?_
    · obtain ⟨s, hs, -⟩ := hsends t ht row
      rw [hs.bytecode_pull, List.length_singleton]
    · exact lt_of_le_of_lt (Nat.mul_le_mul_right _ (List.length_take_le _ _)) (by norm_num)

/-- Specification Theorem 6.4 on the bytecode pair, in the strong form: in a witness of the
constraint statement, every pulled bytecode tuple, the six tables' reads and the bytecode
block's finalizes, is the public program's entry at the pulled counter `g^k`. It implies the
pull's guarantee, that the entry decodes (`decode_entry`). -/
theorem bytecode_channel_sound {w : EnsembleWitness (leanIsaEnsemble prog)}
    (h : SatisfiedBy prog input w) :
    ∀ i ∈ w.interactions, i.channel.name = BytecodePull.name →
      ∀ m : BytecodeMsg K, i.msg = (toElements m).toArray →
        ∃ k : Fin (2 ^ prog.logSize), m.pc = gpow k ∧
          #v[m.opcode] ++ m.op = entry (prog.code k) := by
  intro i hi hname m hm
  have hmem : i.msg ∈ messagesOn w BytecodePull.toRaw :=
    List.mem_map_of_mem (List.mem_filter.mpr ⟨hi, decide_eq_true hname⟩)
  rw [messagesOn_bytecodeChannel w (Or.inl rfl), List.mem_append] at hmem
  have hgood : BytecodeGood prog (readKey i.msg.toList) := by
    rcases hmem with hmem | hmem
    · exact bytecodeReads_good h _ (List.mem_map_of_mem hmem)
    · exact bytecodeBlock_good h _ (List.mem_map_of_mem hmem)
  obtain ⟨k, hk⟩ := hgood
  rw [hm, readKey_bytecodeMsg, List.cons.injEq] at hk
  exact ⟨k, hk.1, Vector.toList_inj.mp hk.2⟩

end LeanerVM.Arithmetization
