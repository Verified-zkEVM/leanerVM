/-
  LeanerVM.Protocol.LeanIsa.Relation

  The clauses of the M3 relation against leanISA's conjuncts, on a stack and a witness that
  agree: the constraints, the bus and the read counts.
-/

module

public import LeanerVM.Protocol.LeanIsa.Bus

/-!
# The relations, clause by clause

On a stack `q` and a witness `w` that agree (`Agrees`: the opcode tables are the stack's rows
within their widths, the memory and bytecode blocks the stack's), three clauses of the M3
relation are three conjuncts of leanISA's, in both directions:

* `opcode_constraints_iff`: an opcode table's Clean constraints hold on every row exactly when
  the instance's constraint polynomials vanish on the stack's rows of that table. Clean reads a
  row only within the component's width, and the table has no lookups.
* `balanced_iff_channels`: the instance's bus balances exactly when each of leanISA's three
  channels does, pushes against pulls; `balanced_multiset_iff` reads Clean's multiset balance as
  those three permutations and a bound on each channel's interactions, which the caps give
  (`interactionsWith_length_lt`).
* `countsNonzero_iff`: every read count of the six opcode tables is nonzero exactly when every
  cell of the instance's count columns is: a count column is the coordinate-`1` variable of a
  memory or bytecode pull, and every such pull has one.
-/

namespace LeanerVM.Protocol.LeanIsa

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Arithmetization
open Air.Flat (Component EnsembleWitness Ensemble)

@[expose] public section

variable {prog : Program} {F : FlockSpec} {s : Sizes} {q : Column (leanIsaμ prog s)}
  {κ : ℕ} {w : EnsembleWitness (leanIsaEnsemble prog κ)}

/-! ## Facts of the opcode components -/

/-- No opcode table has a lookup. -/
private theorem opcode_lookups : ∀ j : Fin 6,
    (opcodeComponent j).rowOperations.lookups.isEmpty := by
  decide +kernel

/-- Every assert expression of an opcode table reads within its width. -/
private theorem opcode_constraints_withinWidth : ∀ j : Fin 6,
    ∀ e ∈ (opcodeComponent j).rowOperations.constraints,
        e.WithinWidth (opcodeComponent j).width := by
  decide +kernel

/-- Every read count of an opcode table is a column. -/
private theorem opcode_countsAreVariables : ∀ j : Fin 6,
    CountsAreVariables (opcodeComponent j) counted := by
  decide +kernel

/-- Coordinate `1` of a counted interaction, evaluated on any row, is the row's cell at its count
column, `0` when missing. -/
private theorem msg_one_of_countVar' {n : ℕ} {i : AbstractInteraction K} {k : Fin n}
    (h : countVar n i = some k) (row : Array K) (data : ProverData K) :
    (i.eval (Environment.fromArray row data)).msg[1]? = some (row[(k : ℕ)]?.getD 0) := by
  unfold countVar at h
  simp only [AbstractInteraction.eval, Vector.toArray_map, Array.getElem?_map]
  split at h
  · next v hv =>
    split_ifs at h with hn
    obtain rfl := Option.some.inj h
    rw [hv]
    simp [Expression.eval, Environment.fromArray]
  · exact absurd h (by simp)

/-- A row of a table of known length, by its index. -/
private theorem forall_mem_table {t : Air.Flat.Table K} {n : ℕ} (hn : t.table.length = n)
    {P : Array K → Prop} :
    (∀ row ∈ t.table, P row) ↔ ∀ x : Fin n, P (t.table[x.val]'(by rw [hn]; exact x.isLt)) := by
  constructor
  · exact fun h x ↦ h _ (List.getElem_mem _)
  · intro h row hrow
    obtain ⟨x, hx, rfl⟩ := List.getElem_of_mem hrow
    exact h ⟨x, hn ▸ hx⟩

/-! ## The constraints -/

/-- On a row agreeing with `r` within the width, an opcode table's Clean constraints hold exactly
when its constraint polynomials vanish at `r`. -/
private theorem opcode_constraintsHold_iff (j : Fin 6) (row : Array K)
    (r : Fin (opcodeComponent j).width → K) (hr : ∀ i : Fin (opcodeComponent j).width,
      row[(i : ℕ)]?.getD 0 = r i) (data : ProverData K) :
    (opcodeComponent j).operations.ConstraintsHold (Environment.fromArray row data) ↔
      ∀ C ∈ (opcodeTable j).constraints, C.eval r = 0 := by
  have hl := List.isEmpty_iff.mp (opcode_lookups j)
  refine Iff.trans ?_ (toM3_constraints_iff (opcodeComponent j) channelSep (·.direction) counted hl
    r data).symm
  rw [Air.Flat.Component.constraintsHold_iff, Air.Flat.Component.constraintsHold_iff,
    Operations.ConstraintsHold, Operations.ConstraintsHold, hl]
  have hrow : (Array.ofFn fun i : Fin (opcodeComponent j).width ↦ row[(i : ℕ)]?.getD 0) =
      Array.ofFn r := congrArg Array.ofFn (funext hr)
  simp only [List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  refine forall₂_congr fun e he ↦ ?_
  rw [Expression.eval_fromArray_truncate row data (opcode_constraints_withinWidth j e he), hrow]

/-- Opcode table `j`'s Clean constraints hold on every row exactly when the instance's constraint
polynomials of that table vanish on every row of the stack. -/
theorem opcode_constraints_iff (h : Agrees F s q w) (j : Fin 6) :
    (opTable w j).Constraints ↔
      ∀ x : Fin (2 ^ s.τ j), ∀ C ∈ (opcodeTable j).constraints,
        C.eval ((leanIsaInstance F prog s).row q (opIdx j) x) = 0 := by
  rw [Air.Flat.Table.Constraints, forall_mem_table (h.length j)]
  refine forall_congr' fun x ↦ ?_
  rw [Air.Flat.Table.environment, opTable_component]
  refine opcode_constraintsHold_iff j _ _ (fun i ↦ ?_) _
  rw [← h.cells j x i, cellOf, List.getElem?_eq_getElem]
  rfl

/-! ## The bus -/

/-- The instance's bus balances exactly when each of leanISA's three channels does. -/
theorem balanced_iff_channels (h : Agrees F s q w) :
    (leanIsaInstance F prog s).Balanced q ↔ ∀ k : Fin 3,
      (messagesOn w (channelAt k) .push).Perm (messagesOn w (channelAt k) .pull) := by
  rw [← balanced_iff]
  exact ⟨fun hb ↦ (tuples_perm h .push).symm.trans (hb.trans (tuples_perm h .pull)),
    fun hb ↦ (tuples_perm h .push).trans (hb.trans (tuples_perm h .pull).symm)⟩

/-- The three channels of the ensemble. -/
theorem channelAt_mem (k : Fin 3) : channelAt k ∈ (leanIsaEnsemble prog κ).channels := by
  fin_cases k <;> simp [leanIsaEnsemble, channelAt]

/-- Every channel of the ensemble is one of the three. -/
private theorem exists_channelAt {c : RawChannel K} (hc : c ∈ (leanIsaEnsemble prog κ).channels) :
    ∃ k : Fin 3, c = channelAt k := by
  simp only [leanIsaEnsemble, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩]

/-- Clean's active messages of a channel of the ensemble are `messagesOn`. -/
private theorem activeMessages_interactionsWith (w : EnsembleWitness (leanIsaEnsemble prog κ))
    (k : Fin 3) (d : BusDir) :
    activeMessages (w.interactionsWith (channelAt k)) d = messagesOn w (channelAt k) d := by
  rw [EnsembleWitness.interactionsWith_eq_filter_name (channelAt_mem k), messagesOn]

/-- **The balance.** Clean's multiset balance holds exactly when each channel has fewer than
`2^64` interactions and its pushes and pulls carry the same messages: every multiplicity is `1`. -/
theorem balanced_multiset_iff (w : EnsembleWitness (leanIsaEnsemble prog κ)) :
    w.Balanced .multiset ↔ (∀ k : Fin 3, (w.interactionsWith (channelAt k)).length < 2 ^ 64) ∧
      ∀ k : Fin 3, (messagesOn w (channelAt k) .push).Perm (messagesOn w (channelAt k) .pull) := by
  constructor
  · intro h
    refine ⟨fun k ↦ (h _ (channelAt_mem k)).1, fun k ↦ ?_⟩
    rw [← activeMessages_interactionsWith, ← activeMessages_interactionsWith]
    exact (h _ (channelAt_mem k)).2.2
  · rintro ⟨hl, hp⟩ c hc
    obtain ⟨k, rfl⟩ := exists_channelAt hc
    refine ⟨hl k, fun i hi ↦ .inr ?_, ?_⟩
    · rw [EnsembleWitness.interactionsWith_eq_filter_name hc] at hi
      exact interactions_mult_eq_one _ _ (List.mem_filter.mp hi).1
    · rw [activeMessages_interactionsWith, activeMessages_interactionsWith]
      exact hp k

/-- The opcode components emit at most thirty-two interactions a row. -/
private theorem opcode_interactions_le :
    ∀ j : Fin 6, (opcodeComponent j).rowOperations.interactions.length ≤ 32 := by
  decide +kernel

/-- Every component of the ensemble emits at most thirty-two interactions a row. -/
private theorem tables_interactions_le :
    ∀ c ∈ (leanIsaEnsemble prog κ).tables, c.rowOperations.interactions.length ≤ 32 := by
  intro c hc
  simp only [leanIsaEnsemble, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact opcode_interactions_le 0
  · exact opcode_interactions_le 1
  · exact opcode_interactions_le 2
  · exact opcode_interactions_le 3
  · exact opcode_interactions_le 4
  · exact opcode_interactions_le 5
  · exact (by decide +kernel : (memComponent 0).rowOperations.interactions.length ≤ 32)
  · exact (by decide +kernel : (bytecodeComponent ⟨0, Nat.zero_le _, fun _ ↦ .jump 0 0 0⟩
      ).rowOperations.interactions.length ≤ 32)

/-- Within the caps, a witness has fewer than `2^64` interactions on each channel: at most
thirty-two a row of eight tables of at most `2^32` rows, and the verifier's two. -/
theorem interactionsWith_length_lt (hc : Caps w) (k : Fin 3) :
    (w.interactionsWith (channelAt k)).length < 2 ^ 64 := by
  rw [EnsembleWitness.interactionsWith_eq_filter_name (channelAt_mem k)]
  refine lt_of_le_of_lt (List.length_filter_le _ _) ?_
  have ht : ∀ t ∈ w.tables, t.interactions.length ≤ 2 ^ maxLogRows * 32 := by
    intro t ht
    obtain ⟨τ, hτ, hlen⟩ := hc.heights t ht
    rw [Air.Flat.Table.interactions, List.length_flatMap]
    refine (List.sum_le_length_nsmul _ 32 fun n hn ↦ ?_).trans ?_
    · obtain ⟨row, -, rfl⟩ := List.mem_map.mp hn
      simp only [Operations.interactionValues, List.length_map,
        Air.Flat.Component.interactions_eq]
      exact tables_interactions_le _ (EnsembleWitness.component_mem_tables_of_mem ht)
    · rw [List.length_map, hlen, smul_eq_mul]
      exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hτ)
  have h8 : w.tables.length = 8 := w.same_length.symm
  rw [EnsembleWitness.interactions, List.length_append, Operations.interactionValues,
    List.length_map, verifier_interactions, List.length_flatMap]
  have hs := List.sum_le_length_nsmul (w.tables.map fun t ↦ t.interactions.length)
    (2 ^ maxLogRows * 32) (fun n hn ↦ by
      obtain ⟨t, htm, rfl⟩ := List.mem_map.mp hn
      exact ht t htm)
  rw [List.length_map, h8, smul_eq_mul] at hs
  have : 2 + 8 * (2 ^ maxLogRows * 32) < 2 ^ 64 := by decide
  simp only [List.length_cons, List.length_nil] at *
  omega

/-! ## The read counts -/

/-- A counted interaction of an opcode table has at least two coordinates. -/
private theorem opcode_counted_arity :
    ∀ j : Fin 6, ∀ ai ∈ (opcodeComponent j).rowOperations.interactions,
    counted ai → 1 < ai.channel.arity := by
  decide +kernel

/-- The first six tables of a witness are its opcode tables. -/
private theorem take_six_tables (w : EnsembleWitness (leanIsaEnsemble prog κ)) :
    w.tables.take 6 = (List.finRange 6).map (opTable w) := by
  rw [tables_eq, show List.finRange 8 = (List.finRange 6).map (fun j : Fin 6 ↦
      (⟨j, by omega⟩ : Fin 8)) ++ [6, 7] by decide, List.map_append, List.map_map,
    List.take_left' (by simp)]
  rfl

/-- The instance's count cells are nonzero exactly when, on every opcode table, every count column
is nonzero on the stack's rows. -/
private theorem m3_countsNonzero_iff :
    (leanIsaInstance F prog s).CountsNonzero q ↔
      ∀ j : Fin 6, ∀ k ∈ (opcodeTable j).count, ∀ x : Fin (2 ^ s.τ j),
        (leanIsaInstance F prog s).row q (opIdx j) x k ≠ 0 := by
  constructor
  · exact fun hc j k hk x ↦ hc (opIdx j) k hk x
  · intro hc j'
    rcases j' with ⟨_ | _ | _ | j, hj⟩
    · exact fun i hi ↦ absurd hi List.not_mem_nil
    · exact fun i hi ↦ absurd hi List.not_mem_nil
    · exact fun i hi ↦ absurd hi List.not_mem_nil
    · have h9 : (leanIsaInstance F prog s).ntab = 9 := rfl
      exact hc ⟨j, by omega⟩

/-- An interaction of a table of known length: one of its component's, on one of its rows. -/
private theorem forall_mem_interactions {t : Air.Flat.Table K} {n : ℕ} (hn : t.table.length = n)
    {P : Interaction K → Prop} :
    (∀ i ∈ t.interactions, P i) ↔
      ∀ x : Fin n, ∀ ai ∈ t.component.rowOperations.interactions,
        P (ai.eval (t.environment (t.table[x.val]'(by rw [hn]; exact x.isLt)))) := by
  constructor
  · intro hP x ai hai
    refine hP _ ?_
    simp only [Air.Flat.Table.interactions, List.mem_flatMap, Operations.interactionValues,
      List.mem_map, Air.Flat.Component.interactions_eq]
    exact ⟨_, List.getElem_mem _, ai, hai, rfl⟩
  · intro hP i hi
    simp only [Air.Flat.Table.interactions, List.mem_flatMap, Operations.interactionValues,
      List.mem_map, Air.Flat.Component.interactions_eq] at hi
    obtain ⟨row, hrow, ai, hai, rfl⟩ := hi
    obtain ⟨x, hx, rfl⟩ := List.getElem_of_mem hrow
    exact hP ⟨x, hn ▸ hx⟩ ai hai

/-- A counted interaction is a pull on the memory or bytecode channel. -/
private theorem counted_iff {i : AbstractInteraction K} :
    counted i = true ↔
      (i.channel.name = MemChannel.name ∨ i.channel.name = BytecodeChannel.name) ∧
        i.direction = .pull := by
  simp [counted]

/-- **The read counts.** Every read count of the six opcode tables is nonzero exactly when every
cell of the instance's count columns is. -/
theorem countsNonzero_iff (h : Agrees F s q w) :
    CountsNonzero w ↔ (leanIsaInstance F prog s).CountsNonzero q := by
  rw [m3_countsNonzero_iff, CountsNonzero, take_six_tables, List.forall_mem_map]
  refine forall_congr' fun j ↦ ?_
  simp only [List.mem_finRange, true_implies]
  rw [forall_mem_interactions (h.length j), opTable_component]
  have hcell : ∀ (x : Fin (2 ^ s.τ j)) (k : Fin (opcodeComponent j).width),
      ((opTable w j).table[x.val]'(by rw [h.length j]; exact x.isLt))[k.val]?.getD 0 =
        (leanIsaInstance F prog s).row q (opIdx j) x k := fun x k ↦ by
    rw [← h.cells j x k, cellOf, List.getElem?_eq_getElem]
    rfl
  constructor
  · intro hc k hk x
    obtain ⟨ai, hai, hcnt, hk'⟩ := (mem_toM3_count_iff _ _ _ _ k).mp hk
    have hm := msg_one_of_countVar' hk' ((opTable w j).table[x.val]'(by
      rw [h.length j]; exact x.isLt)) (opTable w j).data
    have hsize : 1 < (ai.eval (Environment.fromArray ((opTable w j).table[x.val]'(by
        rw [h.length j]; exact x.isLt)) (opTable w j).data)).msg.size := by
      rw [Interaction.same_size]
      exact opcode_counted_arity j ai hai hcnt
    have hne := hc x ai hai (counted_iff.mp hcnt).1 (counted_iff.mp hcnt).2 hsize
    rw [Array.getElem?_eq_getElem hsize] at hm
    rw [← (Option.some.inj hm).trans (hcell x k)]
    exact hne
  · intro hc x ai hai hname hdir hsize
    change 1 < (ai.eval (Environment.fromArray _ (opTable w j).data)).msg.size at hsize
    change (ai.eval (Environment.fromArray _ (opTable w j).data)).msg[1] ≠ 0
    have hcnt : counted ai = true := counted_iff.mpr ⟨hname, hdir⟩
    obtain ⟨k, hk'⟩ := Option.isSome_iff_exists.mp (opcode_countsAreVariables j ai hai hcnt)
    have hm := msg_one_of_countVar' hk' ((opTable w j).table[x.val]'(by
      rw [h.length j]; exact x.isLt)) (opTable w j).data
    rw [Array.getElem?_eq_getElem hsize] at hm
    rw [(Option.some.inj hm).trans (hcell x k)]
    exact hc k ((mem_toM3_count_iff _ _ _ _ k).mpr ⟨ai, hai, hcnt, hk'⟩) x

end

end LeanerVM.Protocol.LeanIsa
