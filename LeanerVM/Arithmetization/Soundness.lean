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
at leanVM pin `a386121f84292f6fa663aaa3e570c15bc0240ea2`, over Clean `9dd71e82`) cut at the
first arrival at the final registers. Category A. Artifact: the accept relation `SatisfiedBy`;
the execution relation `ValidExecution`. Direction: soundness. Boundary: the BLAKE2s validity is
a conjunct of `SatisfiedBy`, discharged by Flock; the two blocks' addresses, words and entries
are Clean's fixed columns and derived data, not hypotheses.

**The walk.** Every row of the six opcode tables pulls one state and pushes one
(`statePairs`), every such row is a step of the program (`rowSteps_of_satisfiedBy`) away from
the sentinel (`no_row_at_sentinel`), the blocks send no state, and the verifier pushes `(1, 1)`
and pulls `(g^(N_prog - 1), 1)`; so the balance of the state channel is the balance of a graph of
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
`TraceExtraction` interface of the proof system's headline, at every memory log-size `κ`.

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

variable {prog : Program} {κ : ℕ} {input : PublicInput}

/-! ## The trace of a witness -/

/-- A state message as registers: coordinates `0` and `1`, a missing one `0`. -/
def regsOfMsg (a : Array K) : Regs K := ⟨a[0]?.getD 0, a[1]?.getD 0⟩

/-- The pulled and pushed state of every row of the six opcode tables, in table and row
order. -/
def statePairs (w : EnsembleWitness (leanIsaEnsemble prog κ)) : List (Regs K × Regs K) :=
  (w.tables.take 6).flatMap fun t ↦ t.table.flatMap fun row ↦
    ((rowMessagesOn t row StateChannel.toRaw .pull).zip
        (rowMessagesOn t row StateChannel.toRaw .push)).map
      fun p ↦ (regsOfMsg p.1, regsOfMsg p.2)

/-- The key of a state in the state map: its two words. -/
def stateKey (r : Regs K) : BitVec 64 × BitVec 64 := (r.pc.toBitVec, r.fp.toBitVec)

/-- The state map of a witness: each pulled state to the state its row pushes. -/
def stateMap (w : EnsembleWitness (leanIsaEnsemble prog κ)) :
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
def traceOf (prog : Program) (w : EnsembleWitness (leanIsaEnsemble prog κ)) :
    Option (Trace prog) :=
  (walkSteps (stateMap w) (Regs.final prog) (statePairs w).length Regs.initial).map
    fun n ↦ ⟨(imageOf w.data).1, (imageOf w.data).2, n⟩

/-! ## Proof helpers -/

/-- Distinct states have distinct keys. -/
private theorem stateKey_injective : Function.Injective stateKey := by
  rintro ⟨⟨a⟩, ⟨b⟩⟩ ⟨⟨c⟩, ⟨d⟩⟩ h
  simp only [stateKey, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  rfl

/-- A witness's state messages: the verifier's, then the six opcode tables'; the blocks send
none. -/
private theorem messagesOn_state (w : EnsembleWitness (leanIsaEnsemble prog κ)) (d : BusDir) :
    messagesOn w StateChannel.toRaw d =
      verifierMessagesOn w StateChannel.toRaw d ++
        rowsOn (w.tables.take 6) StateChannel.toRaw d := by
  rw [messagesOn_split,
    rowsOn_single_nil (t := tableAt w 6) fun row ↦ by
      rw [memBlock_rowMessagesOn (tableAt_six_component w) row rfl, ite_eq_right (by decide)],
    rowsOn_single_nil (t := tableAt w 7) fun row ↦ by
      rw [bytecodeBlock_rowMessagesOn (tableAt_seven_component w) row rfl,
        ite_eq_right (by decide)],
    List.append_nil, List.append_nil]

/-- The verifier pushes `(1, 1)` and pulls the final registers. -/
private theorem verifier_states (w : EnsembleWitness (leanIsaEnsemble prog κ)) :
    (verifierMessagesOn w StateChannel.toRaw .push).map regsOfMsg = [Regs.initial] ∧
      (verifierMessagesOn w StateChannel.toRaw .pull).map regsOfMsg = [Regs.final prog] := by
  simp only [verifier_messagesOn,
    ite_eq_left (show StateChannel.toRaw.name = StateChannel.name from rfl),
    ite_eq_right (show ¬(.pull : BusDir) = .push by decide)]
  constructor <;> rfl

/-- Every row of the six opcode tables pulls one state and pushes one. -/
private theorem opcode_states {w : EnsembleWitness (leanIsaEnsemble prog κ)} {t : Air.Flat.Table K}
    (ht : t ∈ w.tables.take 6) (row : Array K) :
    ∃ r r' : Regs K, rowMessagesOn t row StateChannel.toRaw .pull = [#[r.pc, r.fp]] ∧
      rowMessagesOn t row StateChannel.toRaw .push = [#[r'.pc, r'.fp]] := by
  obtain ⟨s, hs, -⟩ := exists_sendsOpcode w t ht row
  exact ⟨s.pull, s.push, hs.state_pull, hs.state_push⟩

/-- The state pairs, as the rows' pulls and pushes. -/
private theorem statePairs_fst (w : EnsembleWitness (leanIsaEnsemble prog κ)) :
    (statePairs w).map Prod.fst =
        (rowsOn (w.tables.take 6) StateChannel.toRaw .pull).map regsOfMsg ∧
      (statePairs w).map Prod.snd =
        (rowsOn (w.tables.take 6) StateChannel.toRaw .push).map regsOfMsg := by
  simp only [statePairs, rowsOn, List.map_flatMap, List.map_map]
  constructor <;>
  · refine List.flatMap_congr fun t ht ↦ List.flatMap_congr fun row _ ↦ ?_
    obtain ⟨r, r', hp, hq⟩ := opcode_states ht row
    rw [hp, hq]
    rfl

/-- What each state pair is: a step of the program, away from the sentinel, from a row of the
witness. -/
private theorem statePairs_spec (hsafe : SentinelSafe prog)
    {w : EnsembleWitness (leanIsaEnsemble prog κ)} (h : SatisfiedBy prog input w) :
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

/-- The states the rows pull: a balanced graph of steps from `(1, 1)` to the final registers. -/
private theorem states_balanced (hsafe : SentinelSafe prog)
    {w : EnsembleWitness (leanIsaEnsemble prog κ)} (h : SatisfiedBy prog input w) :
    (Regs.initial :: ((statePairs w).map Prod.fst).filterMap (step prog (imageOf w.data).2)).Perm
      (Regs.final prog :: (statePairs w).map Prod.fst) := by
  have hbal := List.Perm.map regsOfMsg (h.perm List.mem_cons_self)
  rw [messagesOn_state w .push, messagesOn_state w .pull, List.map_append,
    List.map_append, (verifier_states w).1, (verifier_states w).2, ← (statePairs_fst w).1,
    ← (statePairs_fst w).2] at hbal
  rwa [List.filterMap_map, (List.filterMap_eq_map_iff_forall_eq_some
    (f := step prog (imageOf w.data).2 ∘ Prod.fst)).mpr fun p hp ↦ (statePairs_spec hsafe h p hp).1]

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
  | nil => simpa using h
  | cons p l ih =>
    refine ih ?_
    simp only [Std.HashMap.isSome_getElem?_iff_mem, Std.HashMap.mem_insert, beq_iff_eq,
      List.mem_cons, or_and_right, exists_or, exists_eq_left] at h ⊢
    tauto

/-- At a pulled state, the state map holds the state a row pushes from it. -/
private theorem stateMap_getElem? {w : EnsembleWitness (leanIsaEnsemble prog κ)}
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
  | 0, _, fuel, h, _ => by cases fuel <;> rw [walkSteps, ite_eq_left (show _ = final from h)]
  | _ + 1, _, 0, _, hn => absurd hn (by omega)
  | n + 1, s, fuel + 1, ⟨hs, s', hstep, hw⟩, hn => by
    rw [walkSteps, ite_eq_right (hfinal s hs), hm s hs s' hstep, Option.bind_some,
      walkSteps_of_walksIn hfinal hm hw (by omega), Option.map_some]

/-! ## Soundness -/

/-- In a witness of the constraint statement of a program whose sentinel slot is not a `JUMP`,
the computable walk of the rows' states succeeds, and returns a trace the witness represents
and that is a valid execution of the program on the input. -/
theorem traceOf_valid (hsafe : SentinelSafe prog) {w : EnsembleWitness (leanIsaEnsemble prog κ)}
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
    obtain ⟨u, hu, hu'⟩ := walksIn_states hE hw k (by omega)
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hu
    have hu1 : run prog t.image (k + 1) Regs.initial = some p.2 := by
      rw [run_add, hu']
      show run prog t.image 1 p.1 = some p.2
      rw [run_succ_of_ne (hspec p hp).2.1, (hspec p hp).1]
      rfl
    rw [Option.some.inj ((Trace.regs_getElem (t := t) hrun k (by omega)).symm.trans hu'),
      Option.some.inj ((Trace.regs_getElem (t := t) hrun (k + 1) hk).symm.trans hu1)]
    exact (hspec p hp).2.2
  have hκ : t.κ = κ := imageOf_data_fst h.caps.le_maxLogMem
  exact ⟨t, by rw [traceOf, hwalk]; rfl, ⟨rfl, fun _ _ ↦ rfl, hregs⟩,
    ⟨⟨hκ ▸ h.caps.minLogMem_le, hκ ▸ h.caps.le_maxLogMem, h.word0_eq, h.word1_eq⟩, hrun⟩⟩

/-- Specification Proposition 6.1, cut at the first arrival at the final registers: the
balanced state channel of a witness of the constraint statement contains a run of the program
from `(1, 1)` to the final registers `(g^(N_prog - 1), 1)`. -/
theorem exists_run_of_balanced (hsafe : SentinelSafe prog)
    {w : EnsembleWitness (leanIsaEnsemble prog κ)} (h : SatisfiedBy prog input w) :
    ∃ n, run prog (imageOf w.data).2 n Regs.initial = some (Regs.final prog) := by
  obtain ⟨t, -, hrep, -, hrun⟩ := traceOf_valid hsafe h
  rw [assignmentRepresents_image hrep]
  exact ⟨t.steps, hrun⟩

/-- Constraint soundness (T1, soundness): a witness of the constraint statement of a program
whose sentinel slot is not a `JUMP` represents a valid execution of the program on the input. -/
theorem constraintSoundness (hsafe : SentinelSafe prog)
    {w : EnsembleWitness (leanIsaEnsemble prog κ)} (h : SatisfiedBy prog input w) :
    ∃ t, AssignmentRepresents w t ∧ ValidExecution prog input t := by
  obtain ⟨t, -, ht⟩ := traceOf_valid hsafe h
  exact ⟨t, ht⟩

/-- The trace interface of the proof system's headline, for a program whose sentinel slot is not
a `JUMP`: `traceOf`, and `traceOf_valid`. -/
def leanIsaTraceExtraction (hsafe : SentinelSafe prog) : TraceExtraction prog where
  traceOf _ _ w := traceOf prog w
  valid _ _ _ h := traceOf_valid hsafe h

end LeanerVM.Arithmetization
