/-
  LeanerVM.Arithmetization.Soundness

  Constraint soundness of leanISA: a witness of the constraint statement represents a valid
  execution of its program, and a computable walk of the witness's rows finds it.
-/

module

public import LeanerVM.Arithmetization.Steps
public import LeanerVM.Semantics.Walk
public import Std.Data.HashMap

@[expose] public section

/-!
# Constraint soundness

The soundness half of T1 (`docs/architecture.md`): from `SatisfiedBy prog input w`, a trace
`t` with `AssignmentRepresents w t` and `ValidExecution prog input t`, for a program whose
sentinel slot is not a `JUMP` (`SentinelSafe prog`, the `sentinelSafe` field of the roadmap's
`WellFormedBytecode`). Specification Proposition 6.1 (`doc/leanvm/body/06-bus-interactions.tex:9`
at leanVM pin `a386121f84292f6fa663aaa3e570c15bc0240ea2`) cut at the first arrival at the final
registers. Category A. Artifact: the accept relation `SatisfiedBy`; the execution relation
`ValidExecution`. Direction: soundness. Boundary: the hypotheses Clean cannot yet express and
the BLAKE2s validity are conjuncts of `SatisfiedBy`.

**The walk.** Every row of the six opcode tables pulls one state and pushes one
(`statePairs`), every such row is a step of the program (`rowSteps_of_satisfiedBy`) away from
the sentinel (`no_row_at_sentinel`), the blocks send no state, and the verifier pushes `(1, 1)`
and pulls `(g^(N_prog - 1), 1)`; so the balance of the state pair is the balance of a graph of
steps from `(1, 1)` to the final registers, and the generic Euler-walk lemma
(`exists_walksIn`) gives a walk of steps between them through pulled states, which, every
state on it being away from the sentinel, is a `run` (`exists_run_of_balanced`). Each step of
the walk is a row of the witness, so the witness represents the trace of that run.

**The trace, computably.** `traceOf prog w` finds the run without a discrete logarithm and
without `step`: it maps each row's pulled state to its pushed state (`stateMap`, a hash map
keyed by the two words of a state) and walks the map from `(1, 1)` until the final registers,
with the number of opcode rows as fuel (`walkSteps`); the trace is the image the data names
and the number of steps. `traceOf_valid` says it succeeds on every witness of `SatisfiedBy`
and returns a trace the witness represents and that is a valid execution;
`constraintSoundness` is its existential form, and `leanIsaTraceExtraction` is the
`TraceExtraction` interface of the proof system's headline.

## Wrong readings excluded

* The run is not every row: the rows off the walk are closed walks of steps (the fill blocks),
  about which nothing is claimed beyond being steps.
* `traceOf` reads no hint and decides nothing about memory: the map it walks is the rows' own
  pairs, and `traceOf_valid` is what makes the walk a run; on a witness that is not satisfying
  it may return anything or nothing.
* The fuel is the number of opcode rows: the walk takes at most one step per row.
-/

namespace LeanerVM.Arithmetization

open LeanerVM.Parameters LeanerVM.Semantics
open Air.Flat (Component EnsembleWitness)

variable {prog : Program} {input : PublicInput}

/-! ## The trace of a witness -/

/-- A state message as registers: coordinates `0` and `1`, a missing one `0`. -/
def regsOfMsg (a : Array K) : Regs K := ⟨a[0]?.getD 0, a[1]?.getD 0⟩

/-- The pulled and pushed state of every row of the six opcode tables, in table and row
order. -/
def statePairs (w : EnsembleWitness (leanIsaEnsemble prog)) : List (Regs K × Regs K) :=
  (w.tables.take 6).flatMap fun t ↦ t.table.flatMap fun row ↦
    ((rowMessagesOn t row StatePull.toRaw).zip (rowMessagesOn t row StatePush.toRaw)).map
      fun p ↦ (regsOfMsg p.1, regsOfMsg p.2)

/-- The key of a state in the state map: its two words. -/
def stateKey (r : Regs K) : BitVec 64 × BitVec 64 := (r.pc.toBitVec, r.fp.toBitVec)

/-- The state map of a witness: each pulled state to the state its row pushes. -/
def stateMap (w : EnsembleWitness (leanIsaEnsemble prog)) :
    Std.HashMap (BitVec 64 × BitVec 64) (Regs K) :=
  (statePairs w).foldl (fun m p ↦ m.insert (stateKey p.1) p.2) ∅

/-- The number of steps the map `m` walks from `r` to `final`, within `fuel` steps. -/
def walkSteps (m : Std.HashMap (BitVec 64 × BitVec 64) (Regs K)) (final : Regs K) :
    ℕ → Regs K → Option ℕ
  | 0, r => if r = final then some 0 else none
  | fuel + 1, r =>
    if r = final then some 0
    else (m[stateKey r]?).bind fun r' ↦ (walkSteps m final fuel r').map (· + 1)

/-- The trace a witness represents: the image its data names, and the number of steps its rows'
states walk from `(1, 1)` to the final registers, with the number of opcode rows as fuel. -/
def traceOf (prog : Program) (w : EnsembleWitness (leanIsaEnsemble prog)) :
    Option (Trace prog) :=
  (walkSteps (stateMap w) (Regs.final prog) (statePairs w).length Regs.initial).map
    fun n ↦ ⟨(imageOf w.data).1, (imageOf w.data).2, n⟩

/-! ## Proof helpers -/

/-- A state message read back as registers. -/
private theorem regsOfMsg_pair (r : Regs K) : regsOfMsg #[r.pc, r.fp] = r := rfl

/-- Distinct states have distinct keys. -/
private theorem stateKey_injective : Function.Injective stateKey := by
  rintro ⟨⟨a⟩, ⟨b⟩⟩ ⟨⟨c⟩, ⟨d⟩⟩ h
  simp only [stateKey, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  rfl

/-- A witness's tables are the six opcode tables and the two blocks. -/
private theorem tables_eq (w : EnsembleWitness (leanIsaEnsemble prog)) :
    w.tables = w.tables.take 6 ++ [tableAt w 6, tableAt w 7] := by
  have hlen : w.tables.length = 8 := w.same_length.symm
  conv_lhs => rw [← List.take_append_drop 6 w.tables]
  rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons (by omega),
    List.drop_eq_nil_of_le (by omega)]
  rfl

/-- The messages a list of tables sends on a channel, row by row. -/
private def rowsOn (ts : List (Air.Flat.Table K)) (c : RawChannel K) : List (Array K) :=
  ts.flatMap fun t ↦ t.table.flatMap fun row ↦ rowMessagesOn t row c

/-- A witness's state messages: the verifier's, then the six opcode tables'; the blocks send
none. -/
private theorem messagesOn_state (w : EnsembleWitness (leanIsaEnsemble prog)) {c : RawChannel K}
    (hc : c.name = StatePull.name ∨ c.name = StatePush.name) :
    messagesOn w c = rowsOn [w.verifierTable] c ++ rowsOn (w.tables.take 6) c := by
  have h6 := (tableAt_component w 6).trans (rfl : _ = (⟨memTable⟩ : Component K))
  have h7 := (tableAt_component w 7).trans (rfl : _ = (⟨bytecodeTable⟩ : Component K))
  have hne : ∀ n : String, n ≠ StatePull.name → n ≠ StatePush.name → c.name ≠ n := by
    rintro n h1 h2 rfl
    rcases hc with hc | hc
    · exact h1 hc
    · exact h2 hc
  have hnil6 : (tableAt w 6).table.flatMap (fun row ↦ rowMessagesOn (tableAt w 6) row c) = [] :=
    List.flatMap_eq_nil_iff.mpr fun row _ ↦ by
      rw [memBlock_rowMessagesOn h6 row rfl, ite_eq_right (hne _ (by decide) (by decide)),
        ite_eq_right (hne _ (by decide) (by decide))]
  have hnil7 : (tableAt w 7).table.flatMap (fun row ↦ rowMessagesOn (tableAt w 7) row c) = [] :=
    List.flatMap_eq_nil_iff.mpr fun row _ ↦ by
      rw [bytecodeBlock_rowMessagesOn h7 row rfl, ite_eq_right (hne _ (by decide) (by decide)),
        ite_eq_right (hne _ (by decide) (by decide))]
  rw [messagesOn_eq_flatMap, EnsembleWitness.allTables, List.flatMap_cons]
  conv_lhs => rw [tables_eq w]
  simp only [rowsOn, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    hnil6, hnil7]

/-- The verifier pushes `(1, 1)` and pulls the final registers. -/
private theorem verifier_states (w : EnsembleWitness (leanIsaEnsemble prog)) :
    (rowsOn [w.verifierTable] StatePush.toRaw).map regsOfMsg = [Regs.initial] ∧
      (rowsOn [w.verifierTable] StatePull.toRaw).map regsOfMsg = [Regs.final prog] := by
  have hv : w.verifierTable.component = ⟨leanIsaVerifier prog⟩ := rfl
  simp only [rowsOn, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    EnsembleWitness.verifierTable_table, verifier_rowMessagesOn hv]
  constructor <;> rfl

/-- Every row of the six opcode tables pulls one state and pushes one. -/
private theorem opcode_states {w : EnsembleWitness (leanIsaEnsemble prog)} {t : Air.Flat.Table K}
    (ht : t ∈ w.tables.take 6) (row : Array K) :
    ∃ r r' : Regs K, rowMessagesOn t row StatePull.toRaw = [#[r.pc, r.fp]] ∧
      rowMessagesOn t row StatePush.toRaw = [#[r'.pc, r'.fp]] := by
  obtain ⟨s, hs, -⟩ := exists_sendsOpcode w t ht row
  exact ⟨s.pull, s.push, hs.state_pull, hs.state_push⟩

/-- The state pairs, as the rows' pulls and pushes. -/
private theorem statePairs_fst (w : EnsembleWitness (leanIsaEnsemble prog)) :
    (statePairs w).map Prod.fst = (rowsOn (w.tables.take 6) StatePull.toRaw).map regsOfMsg ∧
      (statePairs w).map Prod.snd = (rowsOn (w.tables.take 6) StatePush.toRaw).map regsOfMsg := by
  simp only [statePairs, rowsOn, List.map_flatMap, List.map_map]
  constructor <;>
  · refine List.flatMap_congr fun t ht ↦ List.flatMap_congr fun row _ ↦ ?_
    obtain ⟨r, r', hp, hq⟩ := opcode_states ht row
    rw [hp, hq]
    rfl

/-- What each state pair is: a step of the program, away from the sentinel, from a row of the
witness. -/
private theorem statePairs_spec (hsafe : SentinelSafe prog)
    {w : EnsembleWitness (leanIsaEnsemble prog)} (h : SatisfiedBy prog input w) :
    ∀ p ∈ statePairs w, step prog (imageOf w.data).2 p.1 = some p.2 ∧
      p.1.pc ≠ prog.finalPc ∧ RowSteps w p.1 p.2 := by
  intro p hp
  simp only [statePairs, List.mem_flatMap, List.mem_map] at hp
  obtain ⟨t, ht, row, hrow, q, hq, rfl⟩ := hp
  obtain ⟨r, r', hpull, hpush⟩ := opcode_states ht row
  rw [hpull, hpush] at hq
  simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at hq
  subst hq
  have ht' := List.mem_of_mem_take ht
  refine ⟨rowSteps_of_satisfiedBy h t ht' row hrow r r' hpull hpush,
    no_row_at_sentinel hsafe h t ht' row hrow r.pc r.fp
      (by rw [hpull]; exact List.mem_singleton_self _),
    t, ht', row, hrow, hpull, hpush⟩

/-- A list of pairs whose first components step to their second: the steps of the first
components are the second components. -/
private theorem filterMap_fst {α : Type} {f : α → Option α} :
    ∀ {l : List (α × α)}, (∀ p ∈ l, f p.1 = some p.2) →
      (l.map Prod.fst).filterMap f = l.map Prod.snd
  | [], _ => rfl
  | p :: l, h => by
    rw [List.map_cons, List.filterMap_cons_some (h p List.mem_cons_self), List.map_cons,
      filterMap_fst fun q hq ↦ h q (List.mem_cons_of_mem p hq)]

/-- The states the rows pull: a balanced graph of steps from `(1, 1)` to the final registers. -/
private theorem states_balanced (hsafe : SentinelSafe prog)
    {w : EnsembleWitness (leanIsaEnsemble prog)} (h : SatisfiedBy prog input w) :
    (Regs.initial :: ((statePairs w).map Prod.fst).filterMap (step prog (imageOf w.data).2)).Perm
      (Regs.final prog :: (statePairs w).map Prod.fst) := by
  have hbal := List.Perm.map regsOfMsg h.state_balanced
  rw [messagesOn_state w (Or.inr rfl), messagesOn_state w (Or.inl rfl), List.map_append,
    List.map_append, (verifier_states w).1, (verifier_states w).2, ← (statePairs_fst w).1,
    ← (statePairs_fst w).2] at hbal
  rwa [filterMap_fst fun p hp ↦ (statePairs_spec hsafe h p hp).1]

/-- A walk of steps through states away from the sentinel is a run. -/
private theorem run_of_walksIn {κ : ℕ} {L : MemImage κ} {E : List (Regs K)}
    (hE : ∀ v ∈ E, v.pc ≠ prog.finalPc) :
    ∀ {n s t}, WalksIn (step prog L) E n s t → run prog L n s = some t
  | 0, _, _, h => congrArg some h
  | _ + 1, _, _, ⟨hs, _, hstep, hw⟩ => by
    rw [run_succ_of_ne (hE _ hs), hstep]
    exact run_of_walksIn hE hw

/-- Along a walk of steps through states away from the sentinel, the run's state after each
step but the last is a state of the list. -/
private theorem walksIn_states {κ : ℕ} {L : MemImage κ} {E : List (Regs K)}
    (hE : ∀ v ∈ E, v.pc ≠ prog.finalPc) :
    ∀ {n s t}, WalksIn (step prog L) E n s t → ∀ k < n, ∃ u ∈ E, run prog L k s = some u
  | 0, _, _, _, _, hk => absurd hk (Nat.not_lt_zero _)
  | _ + 1, _, _, ⟨hs, _, _, _⟩, 0, _ => ⟨_, hs, rfl⟩
  | _ + 1, _, _, ⟨hs, _, hstep, hw⟩, k + 1, hk => by
    obtain ⟨u, hu, hrun⟩ := walksIn_states hE hw k (by omega)
    refine ⟨u, hu, ?_⟩
    rw [run_succ_of_ne (hE _ hs), hstep]
    exact hrun

/-- The state map holds only the pairs' values. -/
private theorem foldl_insert_getElem? {l : List (Regs K × Regs K)}
    {m : Std.HashMap (BitVec 64 × BitVec 64) (Regs K)} {k : BitVec 64 × BitVec 64} {v : Regs K}
    (h : (l.foldl (fun m p ↦ m.insert (stateKey p.1) p.2) m)[k]? = some v) :
    m[k]? = some v ∨ ∃ p ∈ l, stateKey p.1 = k ∧ p.2 = v := by
  induction l generalizing m with
  | nil => exact Or.inl h
  | cons p l ih =>
    rcases ih h with h' | ⟨q, hq, hk, hv⟩
    · rw [Std.HashMap.getElem?_insert] at h'
      split_ifs at h' with hpk
      · exact Or.inr ⟨p, List.mem_cons_self, beq_iff_eq.mp hpk, Option.some.inj h'⟩
      · exact Or.inl h'
    · exact Or.inr ⟨q, List.mem_cons_of_mem p hq, hk, hv⟩

/-- The state map holds a value at every pair's key. -/
private theorem foldl_insert_isSome {l : List (Regs K × Regs K)}
    {m : Std.HashMap (BitVec 64 × BitVec 64) (Regs K)} {k : BitVec 64 × BitVec 64}
    (h : (m[k]?).isSome ∨ ∃ p ∈ l, stateKey p.1 = k) :
    ((l.foldl (fun m p ↦ m.insert (stateKey p.1) p.2) m)[k]?).isSome := by
  induction l generalizing m with
  | nil =>
    rcases h with h | ⟨p, hp, -⟩
    · exact h
    · exact absurd hp List.not_mem_nil
  | cons p l ih =>
    refine ih ?_
    rcases h with h | ⟨q, hq, hk⟩
    · left
      rw [Std.HashMap.getElem?_insert]
      split_ifs
      · rfl
      · exact h
    · rcases List.mem_cons.mp hq with rfl | hq
      · left
        rw [Std.HashMap.getElem?_insert, ite_eq_left (beq_iff_eq.mpr hk)]
        rfl
      · exact Or.inr ⟨q, hq, hk⟩

/-- At a pulled state, the state map holds the state a row pushes from it. -/
private theorem stateMap_getElem? {w : EnsembleWitness (leanIsaEnsemble prog)}
    (hpairs : ∀ p ∈ statePairs w, ∀ q ∈ statePairs w, p.1 = q.1 → p.2 = q.2)
    {p : Regs K × Regs K} (hp : p ∈ statePairs w) : (stateMap w)[stateKey p.1]? = some p.2 := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp
    (foldl_insert_isSome (l := statePairs w) (m := ∅) (Or.inr ⟨p, hp, rfl⟩))
  rcases foldl_insert_getElem? hv with h0 | ⟨q, hq, hk, rfl⟩
  · rw [Std.HashMap.getElem?_empty] at h0
    cases h0
  · rw [stateMap, hv, hpairs q hq p hp (stateKey_injective hk)]

/-- The map's walk follows a walk of steps through the pulled states. -/
private theorem walkSteps_of_walksIn {κ : ℕ} {L : MemImage κ} {E : List (Regs K)}
    {m : Std.HashMap (BitVec 64 × BitVec 64) (Regs K)} {final : Regs K}
    (hfinal : ∀ v ∈ E, v ≠ final)
    (hm : ∀ v ∈ E, ∀ v', step prog L v = some v' → m[stateKey v]? = some v') :
    ∀ {n s fuel}, WalksIn (step prog L) E n s final → n ≤ fuel → walkSteps m final fuel s = some n
  | 0, _, 0, h, _ => by rw [walkSteps, ite_eq_left (show _ = final from h)]
  | 0, _, _ + 1, h, _ => by rw [walkSteps, ite_eq_left (show _ = final from h)]
  | _ + 1, _, 0, _, hn => absurd hn (by omega)
  | n + 1, s, fuel + 1, ⟨hs, s', hstep, hw⟩, hn => by
    rw [walkSteps, ite_eq_right (hfinal s hs), hm s hs s' hstep, Option.bind_some,
      walkSteps_of_walksIn hfinal hm hw (by omega), Option.map_some]

/-- A valid trace's register sequence is its run's states. -/
private theorem run_regs {t : Trace prog} {r : Regs K}
    (h : run prog t.image t.steps Regs.initial = some r) :
    ∀ k (hk : k < t.regs.length), run prog t.image k Regs.initial = some t.regs[k] := by
  have hsome : ∀ j ∈ List.range (t.steps + 1),
      run prog t.image j Regs.initial =
        some ((run prog t.image j Regs.initial).getD Regs.initial) := by
    intro j hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp (List.mem_range.mp hj) with hlt | rfl
    · obtain ⟨r₁, h₁, -⟩ := run_intermediate h hlt
      rw [h₁]
      rfl
    · rw [h]
      rfl
  have hfm : ∀ l : List ℕ, (∀ j ∈ l, run prog t.image j Regs.initial =
      some ((run prog t.image j Regs.initial).getD Regs.initial)) →
      l.filterMap (fun j ↦ run prog t.image j Regs.initial) =
        l.map fun j ↦ (run prog t.image j Regs.initial).getD Regs.initial := by
    intro l hl
    induction l with
    | nil => rfl
    | cons j l ih =>
      rw [List.filterMap_cons_some (f := fun j ↦ run prog t.image j Regs.initial)
        (hl j List.mem_cons_self), List.map_cons,
        ih fun j' hj' ↦ hl j' (List.mem_cons_of_mem j hj')]
  intro k hk
  have hregs : t.regs = (List.range (t.steps + 1)).map
      fun j ↦ (run prog t.image j Regs.initial).getD Regs.initial :=
    hfm _ hsome
  have hk' : k < t.steps + 1 := by rw [hregs, List.length_map, List.length_range] at hk; exact hk
  simp only [hregs, List.getElem_map, List.getElem_range]
  exact hsome k (List.mem_range.mpr hk')

/-! ## Soundness -/

/-- In a witness of the constraint statement of a program whose sentinel slot is not a `JUMP`,
the computable walk of the rows' states succeeds, and returns a trace the witness represents
and that is a valid execution of the program on the input. -/
theorem traceOf_valid (hsafe : SentinelSafe prog) {w : EnsembleWitness (leanIsaEnsemble prog)}
    (h : SatisfiedBy prog input w) :
    ∃ t, traceOf prog w = some t ∧ AssignmentRepresents w t ∧ ValidExecution prog input t := by
  have hspec := statePairs_spec hsafe h
  set E := (statePairs w).map Prod.fst with hEdef
  have hE : ∀ v ∈ E, v.pc ≠ prog.finalPc := by
    intro v hv
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hv
    exact (hspec p hp).2.1
  obtain ⟨n, hn, hw⟩ := exists_walksIn (states_balanced hsafe h) fun v hv ↦ by
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hv
    rw [(hspec p hp).1]
    exact Option.some_ne_none _
  have hpairs : ∀ p ∈ statePairs w, ∀ q ∈ statePairs w, p.1 = q.1 → p.2 = q.2 :=
    fun p hp q hq hpq ↦ Option.some.inj ((hspec p hp).1.symm.trans (hpq ▸ (hspec q hq).1))
  have hwalk : walkSteps (stateMap w) (Regs.final prog) (statePairs w).length Regs.initial =
      some n := by
    refine walkSteps_of_walksIn (fun v hv hvf ↦ hE v hv (by rw [hvf]; rfl)) ?_ hw
      (by rwa [List.length_map] at hn)
    intro v hv v' hstep
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hv
    rw [stateMap_getElem? hpairs hp, ← Option.some.inj ((hspec p hp).1.symm.trans hstep)]
  have hrun := run_of_walksIn hE hw
  let t : Trace prog := ⟨(imageOf w.data).1, (imageOf w.data).2, n⟩
  have hregs : ∀ k (hk : k + 1 < t.regs.length), RowSteps w t.regs[k] t.regs[k + 1] := by
    intro k hk
    have hlen : t.regs.length = n + 1 := Trace.regs_length (t := t) hrun
    have hkn : k < n := by omega
    have hrk := run_regs (t := t) hrun k (by omega)
    have hrk1 := run_regs (t := t) hrun (k + 1) hk
    obtain ⟨u, hu, hu'⟩ := walksIn_states hE hw k hkn
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hu
    have hk_eq : t.regs[k] = p.1 := Option.some.inj (hrk.symm.trans hu')
    have hk1_eq : t.regs[k + 1] = p.2 := by
      have : run prog t.image (k + 1) Regs.initial = some p.2 := by
        rw [run_add, hu']
        show run prog t.image 1 p.1 = some p.2
        rw [run_succ_of_ne (hspec p hp).2.1, (hspec p hp).1]
        rfl
      exact Option.some.inj (hrk1.symm.trans this)
    rw [hk_eq, hk1_eq]
    exact (hspec p hp).2.2
  exact ⟨t, by rw [traceOf, hwalk]; rfl, ⟨rfl, fun _ _ ↦ rfl, hregs⟩,
    ⟨⟨h.caps.minLogMem_le, h.caps.le_maxLogMem, h.word0_eq, h.word1_eq⟩, hrun⟩⟩

/-- Specification Proposition 6.1, cut at the first arrival at the final registers: the
balanced state channel of a witness of the constraint statement contains a run of the program
from `(1, 1)` to the final registers `(g^(N_prog - 1), 1)`. -/
theorem exists_run_of_balanced (hsafe : SentinelSafe prog)
    {w : EnsembleWitness (leanIsaEnsemble prog)} (h : SatisfiedBy prog input w) :
    ∃ n, run prog (imageOf w.data).2 n Regs.initial = some (Regs.final prog) := by
  obtain ⟨t, -, hrep, -, hrun⟩ := traceOf_valid hsafe h
  rw [assignmentRepresents_image hrep]
  exact ⟨t.steps, hrun⟩

/-- Constraint soundness (T1, soundness): a witness of the constraint statement of a program
whose sentinel slot is not a `JUMP` represents a valid execution of the program on the input. -/
theorem constraintSoundness (hsafe : SentinelSafe prog)
    {w : EnsembleWitness (leanIsaEnsemble prog)} (h : SatisfiedBy prog input w) :
    ∃ t, AssignmentRepresents w t ∧ ValidExecution prog input t := by
  obtain ⟨t, -, ht⟩ := traceOf_valid hsafe h
  exact ⟨t, ht⟩

/-- The trace interface of the proof system's headline, for a program whose sentinel slot is not
a `JUMP`: `traceOf`, and `traceOf_valid`. -/
def leanIsaTraceExtraction (hsafe : SentinelSafe prog) : TraceExtraction prog where
  traceOf _ w := traceOf prog w
  valid _ _ h := traceOf_valid hsafe h

end LeanerVM.Arithmetization
