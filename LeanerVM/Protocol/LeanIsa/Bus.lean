/-
  LeanerVM.Protocol.LeanIsa.Bus

  The bus of a leanISA witness read as the M3 model's one bus: the sixteen-slot tuples of its
  interactions, side by side, and the three channels' balances as one permutation.
-/

module

public import LeanerVM.Protocol.LeanIsa.Read
public import LeanerVM.Arithmetization.Completeness.Messages

/-!
# The leanISA bus as one bus

leanISA's constraint system has three channels and balances each as a multiset of messages,
pushes against pulls, the direction an interaction's tag (Clean's `Balance.multiset`, read by
`messagesOn`). The M3 model has one bus of sixteen-slot tuples, the separator first, pushes
against pulls (`M3Instance.Balanced`). This module relates the two on any witness of the
ensemble.

* `interaction_channel`: every interaction of a witness is on one of the three channels, with
  that channel's arity; `interaction_mult`: with multiplicity `1`, so every interaction is
  active.
* `sideTuples w side`: the tuples a witness flushes on one side: every interaction whose
  direction is that side, as `flushTuple`, leanISA's `busTuple`.
* `balanced_iff`: the two sides are one multiset exactly when each of the three channels
  balances. A tuple's separator names its channel, and on one channel the tuple determines the
  message, since no message has more than fifteen coordinates.
-/

namespace LeanerVM.Protocol.LeanIsa

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Arithmetization
open Air.Flat (Component EnsembleWitness Ensemble)

@[expose] public section

/-! ## The three channels -/

/-- The three channels by name, with their arities. -/
def channelTable : List (String × ℕ) :=
  [(StateChannel.name, 2), (MemChannel.name, 5), (BytecodeChannel.name, 10)]

variable {prog : Program} {κ : ℕ}

/-- Every interaction of a witness is on one of the three channels, with its arity. -/
theorem interaction_channel {w : EnsembleWitness (leanIsaEnsemble prog κ)} {i : Interaction K}
    (hi : i ∈ w.interactions) : (i.channel.name, i.channel.arity) ∈ channelTable := by
  have h := EnsembleWitness.channel_mem_of_mem_interactions hi
  simp only [leanIsaEnsemble, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h <;> rw [h] <;> decide

/-- The opcode components have unit multiplicities. -/
private theorem opcode_unit : ∀ j : Fin 6, UnitMultiplicities (opcodeComponent j) := by
  decide +kernel

/-- Every component of the ensemble has unit multiplicities. -/
private theorem tables_unit (prog : Program) (κ : ℕ) :
    ∀ c ∈ (leanIsaEnsemble prog κ).tables, UnitMultiplicities c := by
  intro c hc
  simp only [leanIsaEnsemble, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact opcode_unit 0
  · exact opcode_unit 1
  · exact opcode_unit 2
  · exact opcode_unit 3
  · exact opcode_unit 4
  · exact opcode_unit 5
  · exact (by decide +kernel : UnitMultiplicities (memComponent 0))
  · exact (by decide +kernel :
      UnitMultiplicities (bytecodeComponent ⟨0, Nat.zero_le _, fun _ ↦ .jump 0 0 0⟩))

/-- The verifier's two interactions: the initial state pushed, the final state pulled. -/
theorem verifier_interactions (prog : Program) (κ : ℕ) :
    (leanIsaEnsemble prog κ).verifierOperations.interactions =
      [(StateChannel.pushed (⟨1, 1⟩ : Regs (Expression K))).toRaw,
        (StateChannel.pulled (⟨.const prog.finalPc, 1⟩ : Regs (Expression K))).toRaw] :=
  rfl

/-- Every interaction of a witness has multiplicity `1`. -/
theorem interaction_mult {w : EnsembleWitness (leanIsaEnsemble prog κ)} {i : Interaction K}
    (hi : i ∈ w.interactions) : i.mult = 1 := by
  simp only [EnsembleWitness.interactions, List.mem_append, List.mem_flatMap,
    Air.Flat.Table.interactions, Operations.interactionValues, List.mem_map,
    Air.Flat.Component.interactions_eq] at hi
  rcases hi with ⟨ai, hai, rfl⟩ | ⟨t, ht, row, -, ai, hai, rfl⟩
  · rw [verifier_interactions] at hai
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hai
    rcases hai with rfl | rfl <;> rfl
  · exact Expression.eval_of_constValue
      (tables_unit prog κ _ (EnsembleWitness.component_mem_tables_of_mem ht) ai hai) _

/-- On interactions of multiplicity `1`, the active messages of a direction are all of its
messages. -/
private theorem activeMessages_eq {l : List (Interaction K)} (h : ∀ i ∈ l, i.mult = 1)
    (d : BusDir) :
    activeMessages l d = (l.filter fun i ↦ decide (i.direction = d)).map (·.msg) := by
  unfold activeMessages
  congr 1
  refine List.filter_congr fun i hi ↦ ?_
  simp [h i hi]

/-- The messages of a witness on a channel in a direction: every interaction on the channel in
that direction. -/
theorem messagesOn_eq (w : EnsembleWitness (leanIsaEnsemble prog κ)) (c : RawChannel K)
    (d : BusDir) :
    messagesOn w c d = ((w.interactions.filter fun i ↦ decide (i.channel.name = c.name)).filter
      fun i ↦ decide (i.direction = d)).map (·.msg) :=
  activeMessages_eq (fun _ hi ↦ interaction_mult (List.mem_filter.mp hi).1) d

/-! ## Tuples and separators -/

/-- Channel `k`: state, memory, bytecode. -/
def channelAt (k : Fin 3) : RawChannel K :=
  ![StateChannel.toRaw, MemChannel.toRaw, BytecodeChannel.toRaw] k

/-- The direction of a side of the bus. -/
def dirOf : Side → BusDir
  | .push => .push
  | .pull => .pull

/-- The arity of channel `k`'s messages. -/
def arityOf (k : Fin 3) : ℕ := ![2, 5, 10] k

/-- A direction flushes on a side exactly when it is the side's. -/
private theorem sideOf_eq_iff (d : BusDir) (side : Side) : sideOf d = side ↔ d = dirOf side := by
  cases d <;> cases side <;> simp [sideOf, dirOf]

/-- The three separators are distinct and nonzero. -/
private theorem gpow_facts : gpow 0 ≠ gpow 1 ∧ gpow 0 ≠ gpow 2 ∧ gpow 1 ≠ gpow 2 ∧ gpow 0 ≠ 0 ∧
    gpow 1 ≠ 0 ∧ gpow 2 ≠ 0 := by
  decide +kernel

/-- A channel's separator is channel `k`'s exactly when its name is: the bus reads the channel
off the separator. -/
private theorem channelSep_eq_iff (ch : RawChannel K) (k : Fin 3) :
    channelSep ch = gpow k ↔ ch.name = (channelAt k).name := by
  obtain ⟨h01, h02, h12, h0, h1, h2⟩ := gpow_facts
  unfold channelSep
  fin_cases k <;>
    simp only [channelAt, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val,
      Channel.toRaw, Fin.isValue] <;>
    split_ifs with ha hb hc <;>
    simp_all [StateChannel, MemChannel, BytecodeChannel, Ne.symm]

/-- A channel of the table named as channel `k` has channel `k`'s arity. -/
private theorem arity_of_mem {ch : RawChannel K} (h : (ch.name, ch.arity) ∈ channelTable)
    {k : Fin 3} (hn : ch.name = (channelAt k).name) : ch.arity = arityOf k := by
  simp only [channelTable, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  fin_cases k <;>
    simp only [channelAt, arityOf, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val,
      Channel.toRaw, Fin.isValue] at hn ⊢ <;>
    rcases h with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;>
    simp_all [StateChannel, MemChannel, BytecodeChannel]

/-- A channel of the table has the separator of one of the three channels. -/
private theorem channelSep_of_mem {ch : RawChannel K} (h : (ch.name, ch.arity) ∈ channelTable) :
    ∃ k : Fin 3, channelSep ch = gpow k := by
  simp only [channelTable, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  rcases h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
  exacts [⟨0, (channelSep_eq_iff ch 0).mpr h⟩, ⟨1, (channelSep_eq_iff ch 1).mpr h⟩,
    ⟨2, (channelSep_eq_iff ch 2).mpr h⟩]

/-- The sixteen-slot tuple of a message with the separator `σ`. -/
def tupleOf (σ : K) (m : Array K) : Vector K 16 :=
  Vector.ofFn fun k ↦ if k.val = 0 then σ else m[k.val - 1]?.getD 0

/-- A tuple's first slot is its separator. -/
private theorem tupleOf_zero (σ : K) (m : Array K) : (tupleOf σ m)[0] = σ := by
  simp [tupleOf]

/-- A message of at most fifteen coordinates is read back off its tuple. -/
theorem tupleMsg_tupleOf (σ : K) (m : Array K) (h : m.size ≤ 15) :
    tupleMsg m.size (tupleOf σ m) = m := by
  apply Array.ext (by simp [tupleMsg])
  intro k _ hk
  simp only [tupleMsg, Array.getElem_ofFn]
  rw [Vector.getElem?_eq_getElem (by omega), Option.getD_some]
  simp only [tupleOf, Vector.getElem_ofFn, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel]
  rw [Array.getElem?_eq_getElem hk, Option.getD_some]

/-- Messages of one length at most fifteen are read back off their tuples. -/
theorem map_tupleMsg_tupleOf {σ : K} {a : ℕ} (l : List (Array K)) (hl : ∀ m ∈ l, m.size = a)
    (ha : a ≤ 15) : (l.map (tupleOf σ)).map (tupleMsg a) = l := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_id l]
  refine List.map_congr_left fun m hm ↦ ?_
  rw [Function.comp_apply, ← hl m hm, tupleMsg_tupleOf _ _ (by rw [hl m hm]; exact ha), id]

/-- The side and tuple of an interaction on the bus. -/
def busView (i : Interaction K) : Side × Vector K 16 :=
  (sideOf i.direction, flushTuple channelSep i)

/-- The tuples a list of interactions flushes on one side. -/
def tuplesOn (l : List (Interaction K)) (side : Side) : List (Vector K 16) :=
  ((l.map busView).filter fun v ↦ decide (v.1 = side)).map (·.2)

/-- The tuples a witness flushes on one side of the bus. -/
abbrev sideTuples (w : EnsembleWitness (leanIsaEnsemble prog κ)) (side : Side) :
    List (Vector K 16) :=
  tuplesOn w.interactions side

/-- The tuples one side flushes with channel `k`'s separator are the messages on channel `k` in
that side's direction, as tuples. -/
theorem filter_tuplesOn (l : List (Interaction K)) (side : Side) (k : Fin 3) :
    (tuplesOn l side).filter (fun v : Vector K 16 ↦ decide (v[0] = gpow k)) =
      (((l.filter fun i ↦ decide (i.channel.name = (channelAt k).name)).filter
        fun i ↦ decide (i.direction = dirOf side)).map (·.msg)).map (tupleOf (gpow k)) := by
  have hv : tuplesOn l side = (l.filter fun i ↦ decide (sideOf i.direction = side)).map
      fun i ↦ tupleOf (channelSep i.channel) i.msg := by
    simp only [tuplesOn, List.filter_map, List.map_map]
    rfl
  rw [hv, List.filter_map, List.filter_filter, List.filter_filter, List.map_map]
  have hp : ∀ i : Interaction K,
      (((fun v : Vector K 16 ↦ decide (v[0] = gpow k)) ∘
          fun i : Interaction K ↦ tupleOf (channelSep i.channel) i.msg) i &&
        decide (sideOf i.direction = side)) =
      (decide (i.direction = dirOf side) && decide (i.channel.name = (channelAt k).name)) := by
    intro i
    simp only [Function.comp_apply, tupleOf_zero, channelSep_eq_iff, sideOf_eq_iff]
    rw [Bool.and_comm]
  rw [List.filter_congr fun i _ ↦ hp i]
  refine List.map_congr_left fun i hi ↦ ?_
  simp only [List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hi
  simp only [Function.comp_apply, (channelSep_eq_iff i.channel k).mpr hi.2.2]

/-- Every tuple of a witness's bus has the separator of one of the three channels. -/
private theorem sideTuples_sep {w : EnsembleWitness (leanIsaEnsemble prog κ)} {side : Side}
    {v : Vector K 16} (hv : v ∈ sideTuples w side) : ∃ k : Fin 3, v[0] = gpow k := by
  simp only [sideTuples, tuplesOn, List.mem_map, List.mem_filter] at hv
  obtain ⟨_, ⟨⟨i, hi, rfl⟩, -⟩, rfl⟩ := hv
  obtain ⟨k, hk⟩ := channelSep_of_mem (interaction_channel hi)
  exact ⟨k, by simp [busView, flushTuple, hk]⟩

/-- A message on channel `k` has channel `k`'s arity. -/
private theorem size_of_mem_messagesOn {w : EnsembleWitness (leanIsaEnsemble prog κ)} {k : Fin 3}
    {d : BusDir} {m : Array K} (hm : m ∈ messagesOn w (channelAt k) d) : m.size = arityOf k := by
  rw [messagesOn_eq] at hm
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hm
  simp only [List.mem_filter, decide_eq_true_eq] at hi
  rw [i.same_size]
  exact arity_of_mem (interaction_channel hi.1.1) hi.1.2

/-- Channel `k` balances exactly when the two sides' tuples with its separator are one
multiset. -/
theorem channel_perm_iff (w : EnsembleWitness (leanIsaEnsemble prog κ)) (k : Fin 3) :
    (messagesOn w (channelAt k) .push).Perm (messagesOn w (channelAt k) .pull) ↔
      ((sideTuples w .push).filter fun v : Vector K 16 ↦ decide (v[0] = gpow k)).Perm
        ((sideTuples w .pull).filter fun v : Vector K 16 ↦ decide (v[0] = gpow k)) := by
  have hpush := filter_tuplesOn w.interactions .push k
  have hpull := filter_tuplesOn w.interactions .pull k
  rw [← messagesOn_eq] at hpush hpull
  rw [hpush, hpull]
  constructor
  · exact fun h ↦ h.map _
  · intro h
    have hk : arityOf k ≤ 15 := by fin_cases k <;> decide
    have h' := h.map (tupleMsg (arityOf k))
    rwa [map_tupleMsg_tupleOf _ (fun m hm ↦ size_of_mem_messagesOn hm) hk,
      map_tupleMsg_tupleOf _ (fun m hm ↦ size_of_mem_messagesOn hm) hk] at h'

/-- The two sides of the bus are one multiset exactly when each of the three channels
balances. -/
theorem balanced_iff (w : EnsembleWitness (leanIsaEnsemble prog κ)) :
    (sideTuples w .push).Perm (sideTuples w .pull) ↔ ∀ k : Fin 3,
        (messagesOn w (channelAt k) .push).Perm (messagesOn w (channelAt k) .pull) := by
  simp only [channel_perm_iff]
  constructor
  · exact fun h k ↦ h.filter _
  · intro h
    rw [List.perm_iff_count]
    intro v
    by_cases hv : ∃ k : Fin 3, v[0] = gpow k
    · obtain ⟨k, hk⟩ := hv
      have := (List.perm_iff_count.mp (h k)) v
      simpa only [List.count_filter, hk, decide_true, ite_true] using this
    · rw [List.count_eq_zero_of_not_mem fun hm ↦ hv (sideTuples_sep hm),
        List.count_eq_zero_of_not_mem fun hm ↦ hv (sideTuples_sep hm)]

/-! ## A component's tuples -/

/-- The separator of the channel named `n`, as `channelSep` reads it. -/
private def nameSep (n : String) : K :=
  if n = StateChannel.name then gpow 0
  else if n = MemChannel.name then gpow 1
  else if n = BytecodeChannel.name then gpow 2
  else 0

/-- The side and tuple of a message on the channel of a name, in a direction. -/
private def nameView (p : String × BusDir × Array K) : Side × Vector K 16 :=
  (sideOf p.2.1, tupleOf (nameSep p.1) p.2.2)

/-- The tuples of a list of interactions depend only on their channels' names, their directions
and their messages. -/
private theorem tuplesOn_eq (l : List (Interaction K)) (side : Side) :
    tuplesOn l side = ((((l.map fun i ↦ (i.channel.name, i.direction, i.msg)).map nameView).filter
      fun v ↦ decide (v.1 = side)).map (·.2)) := by
  rw [tuplesOn, List.map_map]
  rfl

/-- The memory block's two messages on a row: the seed push `(idx, 1, m)` and the finalize pull
`(idx, cntFin, m)`. -/
theorem memTable_messages (idx cnt a b c : K) (data : ProverData K) :
    ((memComponent κ).operations.interactionValues
      (Environment.fromArray (toElements (⟨idx, cnt, #v[a, b, c]⟩ : MemRow K)).toArray data)).map
        (fun i ↦ (i.channel.name, i.direction, i.msg)) =
      [(MemChannel.name, .push, #[idx, 1, a, b, c]),
        (MemChannel.name, .pull, #[idx, cnt, a, b, c])] := by
  rw [Air.Flat.Component.interactionsValues_eq]
  exact mem_sends_gen _ _ _ _ (eval_rowVar _ data)

/-- The bytecode block's two messages on a row: the seed push `(idx, 1, opcode, op)` and the
finalize pull `(idx, cntFin, opcode, op)`. -/
theorem bytecodeTable_messages (idx cnt opc o₁ o₂ o₃ o₄ o₅ o₆ o₇ : K) (data : ProverData K) :
    ((bytecodeComponent prog).operations.interactionValues
      (Environment.fromArray (toElements (⟨idx, cnt, opc, #v[o₁, o₂, o₃, o₄, o₅, o₆, o₇]⟩ :
        BytecodeRow K)).toArray data)).map (fun i ↦ (i.channel.name, i.direction, i.msg)) =
      [(BytecodeChannel.name, .push, #[idx, 1, opc, o₁, o₂, o₃, o₄, o₅, o₆, o₇]),
        (BytecodeChannel.name, .pull, #[idx, cnt, opc, o₁, o₂, o₃, o₄, o₅, o₆, o₇])] := by
  rw [Air.Flat.Component.interactionsValues_eq]
  exact bytecode_sends_gen _ _ _ _ (eval_rowVar _ data)

/-! ## The opcode tables -/

/-- Opcode table `j` of a witness. -/
abbrev opTable (w : EnsembleWitness (leanIsaEnsemble prog κ)) (j : Fin 6) : Air.Flat.Table K :=
  tableAt w ⟨j, by omega⟩

/-- Opcode table `j` of a witness runs the ensemble's opcode component `j`. -/
theorem opTable_component (w : EnsembleWitness (leanIsaEnsemble prog κ)) (j : Fin 6) :
    (opTable w j).component = opcodeComponent j := by
  rw [opTable, tableAt_component]
  fin_cases j <;> rfl

/-- Every message coordinate of an opcode table reads within its width. -/
theorem opcode_withinWidth : ∀ j : Fin 6, ∀ ai ∈ (opcodeComponent j).rowOperations.interactions,
    ∀ e ∈ ai.msg.toList, e.WithinWidth (opcodeComponent j).width := by
  decide +kernel

/-- The tuples of two lists side by side. -/
private theorem tuplesOn_append (l₁ l₂ : List (Interaction K)) (side : Side) :
    tuplesOn (l₁ ++ l₂) side = tuplesOn l₁ side ++ tuplesOn l₂ side := by
  simp only [tuplesOn, List.map_append, List.filter_append]

/-- The tuples of a list built by rows are the rows' tuples. -/
private theorem tuplesOn_flatMap {α : Type} (l : List α) (f : α → List (Interaction K))
    (side : Side) :
    tuplesOn (l.flatMap f) side = l.flatMap fun a ↦ tuplesOn (f a) side := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, List.flatMap_cons, ← ih]
    simp only [tuplesOn, List.map_append, List.filter_append]

/-- A component whose messages read within its width flushes the same tuples on a row as on the
row's first `width` cells. -/
private theorem tuplesOn_truncate (c : Component K)
    (hw : ∀ ai ∈ c.rowOperations.interactions, ∀ e ∈ ai.msg.toList, e.WithinWidth c.width)
    (row : Array K) (r : Fin c.width → K) (hr : ∀ i : Fin c.width, row[(i : ℕ)]?.getD 0 = r i)
    (data : ProverData K) (side : Side) :
    tuplesOn (c.operations.interactionValues (Environment.fromArray row data)) side =
      tuplesOn (c.operations.interactionValues (Environment.fromArray (Array.ofFn r) data)) side
          := by
  have hrow : (Array.ofFn fun i : Fin c.width ↦ row[(i : ℕ)]?.getD 0) = Array.ofFn r :=
    congrArg Array.ofFn (funext hr)
  rw [Air.Flat.Component.interactionsValues_eq, Air.Flat.Component.interactionsValues_eq]
  simp only [tuplesOn, Operations.interactionValues, List.map_map]
  congr 2
  refine List.map_congr_left fun ai hai ↦ ?_
  have hm : ai.msg.map (fun x ↦ Expression.eval (Environment.fromArray row data) x) =
      ai.msg.map (fun x ↦ Expression.eval (Environment.fromArray (Array.ofFn r) data) x) := by
    refine Vector.ext fun k hk ↦ ?_
    rw [Vector.getElem_map, Vector.getElem_map, Expression.eval_fromArray_truncate row data
      (hw ai hai _ (Vector.mem_toList_iff.mpr (Vector.getElem_mem hk))), hrow]
  simp only [Function.comp_apply, busView, AbstractInteraction.eval, hm]
  rfl

/-- On a row of its width, an opcode table flushes, on one side, its flushes of that side
evaluated on the row. -/
private theorem tuplesOn_opcode_row (j : Fin 6) (r : Fin (opcodeComponent j).width → K)
    (data : ProverData K) (side : Side) :
    tuplesOn ((opcodeComponent j).operations.interactionValues
        (Environment.fromArray (Array.ofFn r) data)) side =
      ((opcodeTable j).flushes.filter fun f ↦ decide (sideOf f.1 = side)).map
        fun f ↦ f.2.map (·.eval r) := by
  have h := toM3_flushes_eq (opcodeComponent j) channelSep (·.direction) counted r data
  have hv : (((opcodeComponent j).operations.interactionValues
      (Environment.fromArray (Array.ofFn r) data)).map busView) =
      ((opcodeTable j).flushes.map fun f ↦ (sideOf f.1, f.2.map (·.eval r))) := by
    have := congrArg (List.map fun p : BusDir × Vector K 16 ↦
      (sideOf p.1, p.2)) h
    simp only [List.map_map] at this
    rw [Air.Flat.Component.interactionsValues_eq, Operations.interactionValues, List.map_map]
    exact this.symm
  rw [tuplesOn, hv, List.filter_map]
  simp only [List.map_map, Function.comp_def]

/-- Swapping the two loops of a product enumeration permutes it. -/
private theorem perm_flatMap_swap {α β γ : Type} (l₁ : List α) (l₂ : List β) (g : α → β → γ) :
    (l₁.flatMap fun a ↦ l₂.map (g a)).Perm (l₂.flatMap fun b ↦ l₁.map fun a ↦ g a b) := by
  rw [← Multiset.coe_eq_coe, ← Multiset.coe_bind, ← Multiset.coe_bind]
  simp only [← Multiset.map_coe]
  exact Multiset.bind_map_comm _ _

/-- A list of known length, enumerated by its indices. -/
private theorem flatMap_eq_finRange {α β : Type} (l : List α) {n : ℕ} (hn : l.length = n)
    (g : α → List β) :
    l.flatMap g =
      (List.finRange n).flatMap fun x : Fin n ↦ g (l[x.val]'(by rw [hn]; exact x.isLt)) := by
  subst hn
  conv_lhs => rw [← List.map_getElem_finRange l]
  rw [List.flatMap_map]

/-! ## A stack and a witness that agree -/

section Agrees

variable (F : FlockSpec) (s : Sizes) (q : Column (leanIsaμ prog s))

/-- A stack and a witness agree: the opcode tables have the announced heights and, within their
widths, the stack's rows; the memory and bytecode blocks are the stack's. -/
structure Agrees (w : EnsembleWitness (leanIsaEnsemble prog κ)) : Prop where
  /-- Opcode table `j` has `2 ^ τ_j` rows. -/
  length : ∀ j : Fin 6, (opTable w j).table.length = 2 ^ s.τ j
  /-- Its cells within its width are the stack's row. -/
  cells : ∀ (j : Fin 6) (x : Fin (2 ^ s.τ j)) (i : Fin (opcodeComponent j).width),
    cellOf (opTable w j) x i = (leanIsaInstance F prog s).row q (opIdx j) x i
  /-- The memory block's rows are the stack's. -/
  memRows : memBlockRows w = memBlockRowsOf F prog s q
  /-- The bytecode block's rows are the stack's. -/
  bytecodeRows : bytecodeBlockRows w = bytecodeBlockRowsOf F prog s q

variable {F s q}

/-- Opcode table `j` flushes, on one side, its flushes of that side on every row of the stack. -/
theorem tuplesOn_opTable {w : EnsembleWitness (leanIsaEnsemble prog κ)} (h : Agrees F s q w)
    (j : Fin 6) (side : Side) :
    tuplesOn (opTable w j).interactions side =
      (List.finRange (2 ^ s.τ j)).flatMap fun x ↦
        ((opcodeTable j).flushes.filter fun f ↦ decide (sideOf f.1 = side)).map
          fun f ↦ f.2.map (·.eval ((leanIsaInstance F prog s).row q (opIdx j) x)) := by
  rw [Air.Flat.Table.interactions, tuplesOn_flatMap, flatMap_eq_finRange _ (h.length j)]
  refine List.flatMap_congr fun x _ ↦ ?_
  rw [Air.Flat.Table.environment, opTable_component]
  refine (tuplesOn_truncate (opcodeComponent j) (opcode_withinWidth j) _
    ((leanIsaInstance F prog s).row q (opIdx j) x) (fun i ↦ ?_) _ side).trans
    (tuplesOn_opcode_row j _ _ side)
  rw [← h.cells j x i, cellOf, List.getElem?_eq_getElem]
  rfl

/-! ## The boundary blocks -/

/-- A boundary block's coordinates, the separator first, are the tuple of the rest. -/
private theorem coords_coordCell (I : M3Instance) {κ : ℕ} (σ : K) (rest : List (Coord I.toShape κ))
    (q : Column I.μ) (x : Fin (2 ^ κ)) :
    (coords (.const σ :: rest)).map (fun co ↦ I.coordCell q co x) =
      tupleOf σ (rest.map fun co ↦ I.coordCell q co x).toArray := by
  apply Vector.ext
  intro k hk
  simp only [coords, tupleOf, Vector.getElem_map, Vector.getElem_ofFn]
  rcases k with _ | k
  · rfl
  · simp only [List.getD_cons_succ, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel,
      List.getElem?_toArray, List.getElem?_map]
    by_cases hr : k < rest.length
    · rw [List.getD_eq_getElem _ _ hr, List.getElem?_eq_getElem hr]
      rfl
    · rw [List.getD_eq_default _ _ (by omega), List.getElem?_eq_none (by omega)]
      rfl

variable (F : FlockSpec) (s : Sizes) (q : Column (leanIsaμ prog s))

/-- The memory columns' cells of row `x`: the three limbs. -/
abbrev memLimbs (x : Fin (2 ^ s.logMem)) : List K :=
  [cell F prog s q (memCol 0) x, cell F prog s q (memCol 1) x, cell F prog s q (memCol 2) x]

/-- The program's entry at slot `i`, its eight coordinates. -/
abbrev entryList (i : Fin (2 ^ prog.logSize)) : List K :=
  (List.finRange 8).map fun k ↦ (entry (prog.code i))[k]

/-- The push side's boundary tuples: the initial state, the memory seed, the bytecode seed. -/
theorem boundaryTuples_push :
    (leanIsaInstance F prog s).boundaryTuples q .push =
      [tupleOf (gpow 0) #[1, 1]] ++
      ((List.finRange (2 ^ s.logMem)).map fun x : Fin (2 ^ s.logMem) ↦
        tupleOf (gpow 1) (#[gpow x, 1] ++ (memLimbs F s q x).toArray)) ++
      ((List.finRange (2 ^ prog.logSize)).map fun i : Fin (2 ^ prog.logSize) ↦
        tupleOf (gpow 2) (#[gpow i, 1] ++ (entryList i).toArray)) := by
  simp only [M3Instance.boundaryTuples, boundary, List.filter_cons, List.filter_nil,
    reduceCtorEq, decide_true, decide_false, ite_true, Bool.false_eq_true, ite_false,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]
  refine congrArg₂ (fun a b : List (Vector K 16) ↦ a ++ b) ?_
    (congrArg₂ (fun a b : List (Vector K 16) ↦ a ++ b) ?_ ?_)
  · rw [show List.finRange (2 ^ 0) = [0] from rfl, List.map_singleton]
    refine congrArg (· :: []) ((coords_coordCell (leanIsaInstance F prog s) _ _ q 0).trans ?_)
    rfl
  · refine List.map_congr_left fun x _ ↦ (coords_coordCell (leanIsaInstance F prog s) _ _ q
        x).trans ?_
    simp [M3Instance.coordCell, idxColumn, powersTable, Vector.get_ofFn]
    rfl
  · refine List.map_congr_left fun i _ ↦ (coords_coordCell (leanIsaInstance F prog s) _ _ q
        i).trans ?_
    have hl : ((Coord.known (idxColumn prog.logSize) :: Coord.const 1 ::
        (List.finRange 8).map fun k ↦ (Coord.known (entryColumn prog k) :
          Coord (shape prog s) prog.logSize)).map
        fun co ↦ (leanIsaInstance F prog s).coordCell q co i) = gpow i :: 1 :: entryList i := by
      simp only [List.map_cons, List.map_map]
      refine congrArg₂ _ (Vector.get_ofFn _ _) (congrArg _ (List.map_congr_left fun k _ ↦ ?_))
      exact Vector.get_ofFn _ _
    exact (congrArg (fun l : List K ↦ tupleOf (gpow 2) l.toArray) hl).trans rfl

/-- The pull side's boundary tuples: the final state, the memory finalize, the bytecode finalize. -/
theorem boundaryTuples_pull :
    (leanIsaInstance F prog s).boundaryTuples q .pull =
      [tupleOf (gpow 0) #[prog.finalPc, 1]] ++
      ((List.finRange (2 ^ s.logMem)).map fun x : Fin (2 ^ s.logMem) ↦
        tupleOf (gpow 1) (#[gpow x, cell F prog s q (memCol 3) x] ++ (memLimbs F s q x).toArray)) ++
      ((List.finRange (2 ^ prog.logSize)).map fun i : Fin (2 ^ prog.logSize) ↦
        tupleOf (gpow 2) (#[gpow i, cell F prog s q bfcntCol i] ++ (entryList i).toArray)) := by
  simp only [M3Instance.boundaryTuples, boundary, List.filter_cons, List.filter_nil,
    reduceCtorEq, decide_true, decide_false, ite_true, Bool.false_eq_true, ite_false,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]
  refine congrArg₂ (fun a b : List (Vector K 16) ↦ a ++ b) ?_
    (congrArg₂ (fun a b : List (Vector K 16) ↦ a ++ b) ?_ ?_)
  · rw [show List.finRange (2 ^ 0) = [0] from rfl, List.map_singleton]
    refine congrArg (· :: []) ((coords_coordCell (leanIsaInstance F prog s) _ _ q 0).trans ?_)
    rfl
  · refine List.map_congr_left fun x _ ↦ (coords_coordCell (leanIsaInstance F prog s) _ _ q
        x).trans ?_
    simp [M3Instance.coordCell, idxColumn, powersTable, Vector.get_ofFn]
    rfl
  · refine List.map_congr_left fun i _ ↦ (coords_coordCell (leanIsaInstance F prog s) _ _ q
        i).trans ?_
    have hl : ((Coord.known (idxColumn prog.logSize) :: Coord.committed bfcntCol rfl ::
        (List.finRange 8).map fun k ↦ (Coord.known (entryColumn prog k) :
          Coord (shape prog s) prog.logSize)).map
        fun co ↦ (leanIsaInstance F prog s).coordCell q co i) =
          gpow i :: cell F prog s q bfcntCol i :: entryList i := by
      simp only [List.map_cons, List.map_map]
      refine congrArg₂ _ (Vector.get_ofFn _ _) (congrArg₂ _ rfl (List.map_congr_left fun k _ ↦ ?_))
      exact Vector.get_ofFn _ _
    exact (congrArg (fun l : List K ↦ tupleOf (gpow 2) l.toArray) hl).trans rfl
/-- The separators of the three channels, by name. -/
private theorem nameSep_three :
    nameSep StateChannel.name = gpow 0 ∧ nameSep MemChannel.name = gpow 1 ∧
      nameSep BytecodeChannel.name = gpow 2 :=
  ⟨rfl, rfl, rfl⟩

/-- The tuples of a push and a pull message on one channel, on each side. -/
private theorem tuplesOn_pair {l : List (Interaction K)} {n : String} {mPull mPush : Array K}
    {σ : K} (h : l.map (fun i ↦ (i.channel.name, i.direction, i.msg)) =
      [(n, .push, mPush), (n, .pull, mPull)]) (hn : nameSep n = σ) (side : Side) :
    tuplesOn l side = [tupleOf σ (if side = .push then mPush else mPull)] := by
  rw [tuplesOn_eq, h]
  cases side <;> simp [nameView, sideOf, hn]

variable {F s q}

/-- The memory block flushes its seed and finalize tuples, on the stack's memory columns. -/
theorem tuplesOn_memBlock {w : EnsembleWitness (leanIsaEnsemble prog κ)} (h : Agrees F s q w)
    (side : Side) :
    tuplesOn (tableAt w 6).interactions side =
      (List.finRange (2 ^ s.logMem)).map fun x : Fin (2 ^ s.logMem) ↦
        tupleOf (gpow 1) ((if side = .push then #[gpow x, 1]
          else #[gpow x, cell F prog s q (memCol 3) x]) ++ (memLimbs F s q x).toArray) := by
  rw [Air.Flat.Table.interactions, tuplesOn_flatMap,
    show (tableAt w 6).table = memBlockRowsOf F prog s q from h.memRows, memBlockRowsOf,
    List.ofFn_eq_map, List.flatMap_map, tableAt_component]
  rw [← List.flatMap_pure_eq_map]
  refine List.flatMap_congr fun x _ ↦ ?_
  refine (tuplesOn_pair (memTable_messages _ _ _ _ _ (tableAt w 6).data) nameSep_three.2.1
    side).trans ?_
  cases side <;> rfl

/-- The bytecode block flushes the program's seed and finalize tuples, with the stack's finalize
counts. -/
theorem tuplesOn_bytecodeBlock {w : EnsembleWitness (leanIsaEnsemble prog κ)} (h : Agrees F s q w)
    (side : Side) :
    tuplesOn (tableAt w 7).interactions side =
      (List.finRange (2 ^ prog.logSize)).map fun i : Fin (2 ^ prog.logSize) ↦
        tupleOf (gpow 2) ((if side = .push then #[gpow i, 1]
          else #[gpow i, cell F prog s q bfcntCol i]) ++ (entryList i).toArray) := by
  rw [Air.Flat.Table.interactions, tuplesOn_flatMap,
    show (tableAt w 7).table = bytecodeBlockRowsOf F prog s q from h.bytecodeRows,
    bytecodeBlockRowsOf, List.ofFn_eq_map, List.flatMap_map, tableAt_component]
  rw [← List.flatMap_pure_eq_map]
  refine List.flatMap_congr fun i _ ↦ ?_
  refine (tuplesOn_pair (bytecodeTable_messages _ _ _ _ _ _ _ _ _ _ (tableAt w 7).data)
    nameSep_three.2.2 side).trans ?_
  cases side <;> simp [entryList, List.finRange_succ]

/-- The verifier pushes the initial state and pulls the final state. -/
theorem tuplesOn_verifier (env : Environment K) (side : Side) :
    tuplesOn ((leanIsaEnsemble prog κ).verifierOperations.interactionValues env) side =
      [tupleOf (gpow 0) (if side = .push then #[1, 1] else #[prog.finalPc, 1])] :=
  tuplesOn_pair (verifier_sends prog κ env) nameSep_three.1 side

/-- The instance's tables: the three column groups, then the six opcode tables. -/
private theorem finRange_nine : List.finRange 9 = [0, 1, 2] ++ (List.finRange 6).map opIdx := by
  decide

/-- The witness's tables, in order. -/
theorem tables_eq (w : EnsembleWitness (leanIsaEnsemble prog κ)) :
    w.tables = (List.finRange 8).map (tableAt w) := by
  apply List.ext_getElem
  · rw [List.length_map, List.length_finRange, ← w.same_length]
    rfl
  · intro n h₁ h₂
    rw [List.getElem_map, List.getElem_finRange]
    rfl

/-- Filtering a mapped list before a loop is filtering and mapping inside it. -/
private theorem filter_map_flatMap {α β γ : Type} (l : List α) (f : α → β) (p : β → Bool)
    (g : β → List γ) : ((l.map f).filter p).flatMap g = (l.filter (p ∘ f)).flatMap (g ∘ f) := by
  rw [List.filter_map, List.flatMap_map]
  rfl

/-- The instance's flush tuples, table by table. -/
private theorem flushTuples_eq (side : Side) :
    (leanIsaInstance F prog s).flushTuples q side =
      (List.finRange 9).flatMap fun j ↦ ((flushes j).filter fun f ↦ decide (f.1 = side)).flatMap
        fun f ↦ (List.finRange (2 ^ height prog s j)).map fun x ↦
          f.2.map fun P ↦ P.eval ((leanIsaInstance F prog s).row q j x) := rfl

/-- The flushes of opcode table `j`, on one side: a permutation of what the table's rows emit
there. -/
private theorem flushTuples_opIdx_perm {w : EnsembleWitness (leanIsaEnsemble prog κ)}
    (h : Agrees F s q w)
    (j : Fin 6) (side : Side) :
    (((flushes (opIdx j)).filter fun f ↦ decide (f.1 = side)).flatMap
        fun f ↦ (List.finRange (2 ^ height prog s (opIdx j))).map fun x ↦
          f.2.map fun P ↦ P.eval ((leanIsaInstance F prog s).row q (opIdx j) x)).Perm
      (tuplesOn (opTable w j).interactions side) := by
  rw [tuplesOn_opTable h]
  refine List.Perm.trans ?_ (perm_flatMap_swap _ _ _)
  show (((opcodeTable j).flushes.map fun f ↦ (sideOf f.1, f.2)).filter _).flatMap _ |>.Perm _
  exact List.Perm.of_eq (filter_map_flatMap _ _ _ _)

/-- **The bus, read off a stack, is the bus of a witness that agrees with it**: on each side, the
instance's tuples (the opcode tables' flushes and the six boundary blocks) are a permutation of
the tuples the witness's interactions flush. -/
theorem tuples_perm {w : EnsembleWitness (leanIsaEnsemble prog κ)} (h : Agrees F s q w)
    (side : Side) : ((leanIsaInstance F prog s).tuples q side).Perm (sideTuples w side) := by
  have hb : (leanIsaInstance F prog s).boundaryTuples q side =
      tuplesOn ((leanIsaEnsemble prog κ).verifierOperations.interactionValues
          (.fromInput w.publicInput w.data)) side ++ tuplesOn (tableAt w 6).interactions side ++
        tuplesOn (tableAt w 7).interactions side := by
    rw [tuplesOn_verifier, tuplesOn_memBlock h, tuplesOn_bytecodeBlock h]
    cases side
    · rw [boundaryTuples_push]
      simp
    · rw [boundaryTuples_pull]
      simp
  have hf : ((leanIsaInstance F prog s).flushTuples q side).Perm
      ((List.finRange 6).flatMap fun j ↦ tuplesOn (opTable w j).interactions side) := by
    rw [flushTuples_eq, finRange_nine, List.flatMap_append, List.flatMap_map]
    have h0 : ([0, 1, 2] : List (Fin 9)).flatMap (fun j ↦
        ((flushes j).filter fun f ↦ decide (f.1 = side)).flatMap fun f ↦
          (List.finRange (2 ^ height prog s j)).map fun x ↦
            f.2.map fun P ↦ P.eval ((leanIsaInstance F prog s).row q j x)) = [] := rfl
    rw [h0, List.nil_append]
    exact List.Perm.flatMap_left _ fun j _ ↦ flushTuples_opIdx_perm h j side
  rw [M3Instance.tuples, hb, sideTuples, EnsembleWitness.interactions, tables_eq, List.flatMap_map,
    show List.finRange 8 = (List.finRange 6).map (fun j : Fin 6 ↦ (⟨j, by omega⟩ : Fin 8)) ++
      [6, 7] by decide, List.flatMap_append, List.flatMap_map, tuplesOn_append, tuplesOn_append,
    tuplesOn_flatMap,
    tuplesOn_flatMap]
  refine (hf.append_right _).trans ?_
  rw [List.perm_iff_count]
  intro v
  simp only [List.count_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, opTable]
  omega

end Agrees

end

end LeanerVM.Protocol.LeanIsa
