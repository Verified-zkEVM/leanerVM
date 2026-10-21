/-
  LeanVM.E2E.Reduction.Lift

  The game's parts in the schemes' world: coins, hash queries and the schemes' runs of the game,
  translated by `toW`, are the schemes' own computations; the game's key generation is a
  sequence of the schemes' key generations.
-/

module

public import LeanVM.E2E.Reduction.Record
public import Sphincs.StatementMulti

/-!
# The game's parts in the schemes' world

`tw x st` is a computation `x` of the game's monad run from the signers' state `st` and
translated to the schemes' world (`toW`). The parts the reductions reuse:

* coins are the schemes' coins (`tw_coins`), a hash query the schemes' query read as a digest
  (`tw_hashQuery`);
* a leanXMSS or leanSPHINCS computation run against the game's hash (`xmssRun`, `sphincsRun`) is
  the scheme's computation lifted into the schemes' world (`tw_xmssRun`, `tw_sphincsRun`): the
  digest's bits read back are the answer;
* the game's key generation (`Vector.mapM` over the keys) is `sequenceFin` of the per-key
  generations (`vector_mapM_replicate`);
* forgetting the log of a writer simulation is the simulation by the forgetful handler
  (`fst_map_run_simulateQ_writer`).
-/

namespace LeanVM.E2E

open LeanVM.Parameters LeanVM.Semantics LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Rom
open OracleSpec OracleComp
open scoped ENNReal

@[expose] public section

/-! ## Generic facts -/

/-- **Forgetting a writer's log** of a simulation is the simulation by the handler that forgets
it. -/
theorem fst_map_run_simulateQ_writer {ι : Type} {spec : OracleSpec.{0, 0} ι} {M : Type → Type}
    [Monad M] [LawfulMonad M] {W : Type} [Monoid W] (h : QueryImpl spec (WriterT W M)) {α : Type}
    (oa : OracleComp spec α) :
    Prod.fst <$> (simulateQ h oa).run = simulateQ (fun t ↦ Prod.fst <$> (h t).run) oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, WriterT.run_bind, map_bind, bind_map_left]
    refine bind_congr fun p ↦ ?_
    rw [← ih p.1, Functor.map_map]

/-- **Forgetting a writer's log, append flavour** (the logging oracles' writer). -/
theorem fst_map_run_simulateQ_writer' {ι : Type} {spec : OracleSpec.{0, 0} ι} {M : Type → Type}
    [Monad M] [LawfulMonad M] {L : Type} (h : QueryImpl spec (WriterT (List L) M)) {α : Type} (oa : OracleComp spec α) :
    Prod.fst <$> (simulateQ h oa).run = simulateQ (fun t ↦ Prod.fst <$> (h t).run) oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t k ih =>
    rw [simulateQ_query_bind, simulateQ_bind, simulateQ_spec_query, WriterT.fst_map_run_bind']
    exact bind_congr fun p ↦ ih p

/-- **A vector of runs of one computation is a sequence of them.** -/
theorem vector_mapM_replicate {m : Type → Type} [Monad m] [LawfulMonad m] {β : Type} (c : m β) :
    ∀ n : ℕ, (Vector.replicate n ()).mapM (fun _ ↦ c) =
      (fun f ↦ Vector.ofFn f) <$> LeanXmss.Concrete.sequenceFin (fun _ : Fin n ↦ c) := by
  intro n
  rw [← Vector.map_toArray_inj, Vector.toArray_mapM, Array.mapM_eq_mapM_toList, Functor.map_map]
  have h : ∀ n : ℕ, (List.replicate n ()).mapM (fun _ ↦ c) =
      (fun f ↦ List.ofFn f) <$> LeanXmss.Concrete.sequenceFin (fun _ : Fin n ↦ c) := by
    intro n
    induction n with
    | zero => simp [LeanXmss.Concrete.sequenceFin]
    | succ n ih =>
      simp only [List.replicate_succ, List.mapM_cons, ih, LeanXmss.Concrete.sequenceFin, map_bind,
        bind_map_left, map_pure, List.ofFn_succ, Fin.cases_zero, Fin.cases_succ]
  simp only [Vector.toArray_replicate, Array.toList_replicate, h, Functor.map_map]
  congr 1
  funext f
  simp [Vector.toArray_ofFn, List.toArray_ofFn]

/-! ## The game's parts, translated -/

variable {nx ns : ℕ}

/-- A computation of the game's monad from a state, in the schemes' world. -/
noncomputable def tw {α : Type} (x : GameM nx ns α) (st : SignState nx ns) :
    OracleComp OW (α × SignState nx ns) :=
  simulateQ toW (x.run st)

/-- The translation of a bind. -/
theorem tw_bind {α β : Type} (x : GameM nx ns α) (f : α → GameM nx ns β) (st : SignState nx ns) :
    tw (x >>= f) st = tw x st >>= fun p ↦ tw (f p.1) p.2 := by
  simp only [tw, StateT.run_bind, simulateQ_bind]

/-- The translation of `pure`. -/
theorem tw_pure {α : Type} (a : α) (st : SignState nx ns) :
    tw (pure a : GameM nx ns α) st = pure (a, st) := by
  simp [tw]

/-- Coins of the game, translated, are coins. -/
theorem simulateQ_toW_liftM {α : Type} (p : ProbComp α) :
    simulateQ toW (liftM p : OracleComp GameSpec α) = (liftM p : OracleComp OW α) := by
  induction p using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t k ih =>
    rw [liftM_bind, liftM_bind]
    change simulateQ toW (liftM (GameSpec.query (.inl t)) >>= fun a ↦ liftM (k a)) =
      (liftM (OW.query (.inl t)) >>= fun a ↦ liftM (k a) : OracleComp OW α)
    rw [simulateQ_bind, simulateQ_spec_query]
    exact bind_congr fun a ↦ ih a

/-- The game's coins, translated. -/
theorem tw_coins {α : Type} (p : ProbComp α) (st : SignState nx ns) :
    tw (coins p : GameM nx ns α) st = (·, st) <$> (liftM p : OracleComp OW α) := by
  unfold tw coins
  rw [OracleComp.liftM_run_StateT, simulateQ_bind, simulateQ_toW_liftM, map_eq_bind_pure_comp]
  simp only [simulateQ_pure]
  rfl

/-- A hash query of the game, translated. -/
theorem tw_hashQuery (x : Bytes) (st : SignState nx ns) :
    tw (hashQuery x : GameM nx ns Digest) st =
      (·, st) <$> (bitsD <$> (liftM (OW.query (.inr x)) : OracleComp OW LeanXmss.HashOutput)) := by
  unfold tw hashQuery
  change simulateQ toW ((liftM (liftM (GameSpec.query (.inr x)) : OracleComp GameSpec Digest) :
    GameM nx ns Digest).run st) = _
  rw [OracleComp.liftM_run_StateT, simulateQ_bind, simulateQ_spec_query, map_eq_bind_pure_comp]
  simp [toW, map_eq_bind_pure_comp]

/-- The translation of a map. -/
theorem tw_map {α β : Type} (f : α → β) (x : GameM nx ns α) (st : SignState nx ns) :
    tw (f <$> x) st = Prod.map f id <$> tw x st := by
  simp only [tw, StateT.run_map, simulateQ_map]
  rfl

/-- **A stateless simulation, translated**: if every query of `impl` leaves the state and is,
translated, the query of `g`, the simulation is `g`'s. -/
theorem tw_simulateQ {ι : Type} {spec : OracleSpec.{0, 0} ι} (impl : QueryImpl spec (GameM nx ns))
    (g : QueryImpl spec (OracleComp OW)) (st : SignState nx ns)
    (himpl : ∀ t, tw (impl t) st = (·, st) <$> g t) {α : Type} (oa : OracleComp spec α) :
    tw (simulateQ impl oa) st = (·, st) <$> simulateQ g oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp [tw_pure]
  | query_bind t k ih =>
    rw [simulateQ_bind, simulateQ_spec_query, tw_bind, himpl, simulateQ_bind, simulateQ_spec_query,
      bind_map_left, map_bind]
    exact bind_congr fun u ↦ ih u

/-- A hash query read as an output, translated, is the schemes' query. -/
theorem tw_hBits_hashQuery (x : Bytes) (st : SignState nx ns) :
    tw (hBits <$> hashQuery x : GameM nx ns LeanXmss.HashOutput) st =
      (·, st) <$> (liftM (OW.query (.inr x)) : OracleComp OW LeanXmss.HashOutput) := by
  rw [tw_map, tw_hashQuery, Functor.map_map, Functor.map_map]
  congr 1
  funext v
  simp [Prod.map]

/-- The schemes' hash queries, simulated, are the lift into the schemes' world. -/
theorem simulateQ_query_inr {α : Type} (oa : OracleComp LeanXmss.HashSpec α) :
    simulateQ (fun x ↦ (liftM (OW.query (.inr x)) : OracleComp OW LeanXmss.HashOutput)) oa =
      (liftM oa : OracleComp OW α) := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind x k ih =>
    rw [simulateQ_bind, simulateQ_spec_query, liftM_bind]
    exact bind_congr fun u ↦ ih u

/-- **A leanXMSS computation run against the game's hash, translated, is the computation lifted
into the schemes' world.** -/
theorem tw_xmssRun {α : Type} (oa : OracleComp LeanXmss.HashSpec α) (st : SignState nx ns) :
    tw (xmssRun oa : GameM nx ns α) st = (·, st) <$> (liftM oa : OracleComp OW α) := by
  change tw (simulateQ (fun x ↦ hBits <$> hashQuery x : QueryImpl LeanXmss.HashSpec (GameM nx ns))
    oa) st = _
  rw [tw_simulateQ _ _ st (fun x ↦ tw_hBits_hashQuery x st), simulateQ_query_inr]

/-- A digest as leanSPHINCS's hash output. -/
def sBits (d : Digest) : Sphincs.HashOutput := digestBits d

/-- A hash query read as a leanSPHINCS output, translated, is the schemes' query. -/
theorem tw_sBits_hashQuery (x : Bytes) (st : SignState nx ns) :
    tw (sBits <$> hashQuery x : GameM nx ns Sphincs.HashOutput) st =
      (·, st) <$> ((liftM (Sphincs.OracleWorld.query (.inr x)) :
        OracleComp Sphincs.OracleWorld Sphincs.HashOutput) : OracleComp OW Sphincs.HashOutput) := by
  rw [tw_map, tw_hashQuery, Functor.map_map, Functor.map_map]
  congr 1
  funext v
  simp only [Prod.map, id, sBits]
  congr 1
  exact digestBits_bitsDigest v

/-- leanSPHINCS's hash queries, simulated, are the lift into its world. -/
theorem simulateQ_query_inr_sphincs {α : Type} (oa : OracleComp Sphincs.HashSpec α) :
    simulateQ (fun x ↦ (liftM (Sphincs.OracleWorld.query (.inr x)) :
      OracleComp Sphincs.OracleWorld Sphincs.HashOutput)) oa =
      (liftM oa : OracleComp Sphincs.OracleWorld α) := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind x k ih =>
    rw [simulateQ_bind, simulateQ_spec_query, liftM_bind]
    exact bind_congr fun u ↦ ih u

/-- A leanSPHINCS computation in the schemes' world (its world is `OW` up to unfolding). -/
noncomputable def sLift {α : Type} (oa : OracleComp Sphincs.HashSpec α) : OracleComp OW α :=
  (liftM oa : OracleComp Sphincs.OracleWorld α)

/-- **A leanSPHINCS computation run against the game's hash, translated, is the computation
lifted into the schemes' world.** -/
theorem tw_sphincsRun [Sphincs.Params] {α : Type} (oa : OracleComp Sphincs.HashSpec α)
    (st : SignState nx ns) :
    tw (sphincsRun oa : GameM nx ns α) st = (·, st) <$> sLift oa := by
  change tw (simulateQ (fun x ↦ sBits <$> hashQuery x : QueryImpl Sphincs.HashSpec (GameM nx ns))
    oa) st = _
  rw [tw_simulateQ (spec := Sphincs.HashSpec) _ _ st (fun x ↦ tw_sBits_hashQuery x st)]
  exact congrArg _ (simulateQ_query_inr_sphincs oa)

/-- **A sequence of stateless computations, translated**, is the sequence of their
translations. -/
theorem tw_sequenceFin {α : Type} (st : SignState nx ns) :
    ∀ {n : ℕ} (c : Fin n → GameM nx ns α) (d : Fin n → OracleComp OW α),
      (∀ i, tw (c i) st = (·, st) <$> d i) →
      tw (LeanXmss.Concrete.sequenceFin c) st = (·, st) <$> LeanXmss.Concrete.sequenceFin d
  | 0, _, _, _ => by simp [LeanXmss.Concrete.sequenceFin, tw_pure]
  | n + 1, c, d, h => by
    simp only [LeanXmss.Concrete.sequenceFin]
    rw [tw_bind, h 0, bind_map_left, map_bind]
    refine bind_congr fun a ↦ ?_
    rw [tw_bind, tw_sequenceFin st (fun i ↦ c i.succ) (fun i ↦ d i.succ) (fun i ↦ h i.succ),
      bind_map_left, map_bind]
    refine bind_congr fun f ↦ ?_
    simp [tw_pure]

/-- **The signers' logs are unchanged** from `st` to `st'`. -/
def LogsFixed (st st' : SignState nx ns) : Prop := st'.xlog = st.xlog ∧ st'.slog = st.slog

/-- A recorded V_I computation leaves the signers' logs: on every point of its translated run. -/
def KeepsLogs {α : Type} (x : StateT Log (OptionT (GameM nx ns)) α) : Prop :=
  ∀ (tr : Log) (st : SignState nx ns), ∀ p ∈ support (tw ((x.run tr).run) st), LogsFixed st p.2

/-- `KeepsLogs` holds of `pure`. -/
theorem keepsLogs_pure {α : Type} (a : α) :
    KeepsLogs (pure a : StateT Log (OptionT (GameM nx ns)) α) := by
  intro tr st p hp
  simp only [StateT.run_pure, OptionT.run_pure, tw_pure, support_pure, Set.mem_singleton_iff] at hp
  subst hp
  exact ⟨rfl, rfl⟩

/-- `KeepsLogs` is closed under `bind`. -/
theorem keepsLogs_bind {α β : Type} (x : StateT Log (OptionT (GameM nx ns)) α)
    (f : α → StateT Log (OptionT (GameM nx ns)) β) (hx : KeepsLogs x) (hf : ∀ a, KeepsLogs (f a)) :
    KeepsLogs (x >>= f) := by
  intro tr st p hp
  rw [StateT.run_bind, OptionT.run_bind, Option.elimM, tw_bind, mem_support_bind_iff] at hp
  obtain ⟨q, hq, hp⟩ := hp
  obtain ⟨h₁, h₂⟩ := hx tr st q hq
  rcases hq' : q.1 with _ | ⟨a, tr'⟩
  · rw [hq'] at hp
    simp only [Option.elim_none, tw_pure, support_pure, Set.mem_singleton_iff] at hp
    subst hp
    exact ⟨h₁, h₂⟩
  · rw [hq'] at hp
    obtain ⟨h₃, h₄⟩ := hf a tr' q.2 p hp
    exact ⟨h₃.trans h₁, h₄.trans h₂⟩

/-- `KeepsLogs` holds of the recorded query. -/
theorem keepsLogs_recQuery (budget : ℕ) (x : Bytes) :
    KeepsLogs (recQuery (nx := nx) (ns := ns) budget x) := by
  intro tr st p hp
  rw [run_recQuery, tw_map, support_map] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  unfold tw at hq
  by_cases hb : budget ≤ st.spent
  · rw [run_budgetedQuery_of_le hb, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hq
    subst hq
    exact ⟨rfl, rfl⟩
  · rw [run_budgetedQuery_of_lt hb, simulateQ_map, support_map] at hq
    obtain ⟨d, -, rfl⟩ := hq
    exact ⟨rfl, rfl⟩

/-- **V_I's recorded run leaves the signers' logs.** -/
theorem keepsLogs_viRec (budget : ℕ) (guest : Program) (ip : IdealProof) (fuel : ℕ)
    (s : NodeStatement) (st : SignState nx ns) :
    ∀ p ∈ support (tw (viRec budget guest ip fuel s) st), LogsFixed st p.2 :=
  closed_idealVerify (fun x ↦ KeepsLogs x) keepsLogs_pure keepsLogs_bind _
    (keepsLogs_recQuery budget) guest ip fuel s [] st

/-- A leanSPHINCS request of the game, translated, leaves the leanXMSS log. -/
theorem xlog_tw_sphincsSign [Sphincs.Params] (keys : Keys nx ns) (j : Fin ns) (msg : Sphincs.Message)
    (st : SignState nx ns) : ∀ p ∈ support (tw (sphincsSign keys j msg) st), p.2.xlog = st.xlog := by
  intro p hp
  unfold sphincsSign at hp
  by_cases h : Sphincs.signatureLimit ≤ (st.slog j).length
  · simp [h, tw] at hp
    rw [hp]
  · simp only [h, ↓reduceIte, tw, StateT.run_bind, StateT.run_get, pure_bind, simulateQ_bind,
      mem_support_bind_iff] at hp
    obtain ⟨q, hq, hp⟩ := hp
    have hq' := tw_sphincsRun (nx := nx) (ns := ns)
      (Sphincs.Seeded.sign (keys.sphincs j).2 msg : OracleComp Sphincs.HashSpec _) st
    unfold tw at hq'
    rw [hq', support_map] at hq
    obtain ⟨σ, -, rfl⟩ := hq
    simp at hp
    rw [hp]

/-- A leanXMSS request of the game, translated, leaves the leanSPHINCS log. -/
theorem slog_tw_xmssSign [Sphincs.Params] (keys : Keys nx ns) (j : Fin nx) (req : XmssRequest)
    (st : SignState nx ns) : ∀ p ∈ support (tw (xmssSign keys j req) st), p.2.slog = st.slog := by
  intro p hp
  unfold xmssSign at hp
  by_cases h : ((st.xlog j).any fun e ↦ decide (e.1.1 = req.1)) = true
  · simp [h, tw] at hp
    rw [hp]
  · simp only [h, Bool.false_eq_true, ↓reduceIte, tw, StateT.run_bind, StateT.run_get, pure_bind,
      simulateQ_bind, mem_support_bind_iff] at hp
    obtain ⟨q, hq, hp⟩ := hp
    have hq' := tw_xmssRun (nx := nx) (ns := ns) (LeanXmss.Seeded.sign (keys.xmss j).2 req.1 req.2) st
    unfold tw at hq'
    rw [hq', support_map] at hq
    obtain ⟨σ, -, rfl⟩ := hq
    simp at hp
    rw [hp]

end
end LeanVM.E2E
