/-
  LeanerVM.Protocol.ToVCVio.LogReplay

  A computation's queries answered again from a record of their answers: a logged run of a
  computation on a single oracle is reproduced, value and log, by answering every query from any
  partial function that agrees with the log. Candidate for VCVio.
-/

module

public import VCVio.OracleComp.QueryTracking.LoggingOracle.Core
public import VCVio.OracleComp.SimSemantics.StateT.Basic.Native

/-!
# Replaying a logged run

`replayImpl ans` answers a query `t` to the oracle `Q →ₒ D` by `ans t`, failing where `ans` has no
answer, and appends the query with its answer to a log. `run_simulateQ_replayImpl`: if `(x, log)`
is a possible logged run of `oa` (in the support of `oa.withQueryLog`, where a query may be
answered by anything) and `ans` answers every logged query as the log does, the replay of `oa`
returns `x` and appends exactly `log`. The support of a simulation is in the support of the
computation it simulates (`support_simulateQ_subset`, VCVio's `support_simulateQ_run'_subset`),
so the same holds of a logged run under any implementation of the oracle: a stateless one such as
`pure ∘ f` (`replay_of_mem_support_simulateQ`), or a stateful one such as a lazy random oracle
(`replay_of_mem_support_simulateQ_run'`).
-/

namespace LeanerVM.Protocol.QueryLog

open OracleComp OracleSpec

@[expose] public section

variable {Q D : Type}

/-- The oracle `Q →ₒ D` answered by a partial function, each query appended with its answer to a
log: a query `ans` does not answer fails. -/
def replayImpl (ans : Q → Option D) : QueryImpl (Q →ₒ D) (StateT (Q →ₒ D).QueryLog Option) :=
  fun t ↦ do
    let u ← StateT.lift (ans t)
    modify (· ++ [⟨t, u⟩])
    return u

/-- **A logged run, replayed**: if `(x, log)` is a possible logged run of `oa` and `ans` answers
every logged query as the log does, the replay of `oa` from a log `pre` returns `x` and the log
`pre ++ log`. -/
theorem run_simulateQ_replayImpl {α : Type} (ans : Q → Option D) (oa : OracleComp (Q →ₒ D) α)
    {x : α} {log : (Q →ₒ D).QueryLog} (h : (x, log) ∈ support oa.withQueryLog)
    (hans : ∀ e ∈ log, ans e.1 = some e.2) (pre : (Q →ₒ D).QueryLog) :
    (simulateQ (replayImpl ans) oa).run pre = some (x, pre ++ log) := by
  induction oa using OracleComp.inductionOn generalizing x log pre with
  | pure y =>
    rw [withQueryLog_pure, mem_support_pure_iff, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp
  | query_bind t mx ih =>
    rw [withQueryLog_bind, withQueryLog_query, bind_assoc, mem_support_bind_iff] at h
    obtain ⟨u, -, h⟩ := h
    rw [pure_bind, support_map, Set.mem_image] at h
    obtain ⟨⟨y, log'⟩, hy, he⟩ := h
    simp only [Prod.map_apply, id_eq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    have hu : ans t = some u := hans ⟨t, u⟩ (by simp)
    have hrest : ∀ e ∈ log', ans e.1 = some e.2 := fun e he ↦ hans e (by simp [he])
    have hstep : (replayImpl ans t).run pre = pure (u, pre ++ [⟨t, u⟩]) := by
      simp [replayImpl, hu]
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, hstep, pure_bind]
    simp only at hy
    rw [ih u hy hrest]
    simp

/-- The support of a simulation is in the support of the computation it simulates. -/
theorem support_simulateQ_subset {ι : Type} {spec : OracleSpec ι} {α : Type}
    {n : Type → Type} [Monad n] [LawfulMonad n] [MonadAttach n] [ExactMonadAttach n]
    (impl : QueryImpl spec n) (oa : OracleComp spec α) :
    support (simulateQ impl oa) ⊆ support oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t k ih =>
    intro x hx
    simp only [simulateQ_bind, simulateQ_spec_query, MonadAttach.support_bind, Set.mem_iUnion,
      exists_prop] at hx ⊢
    obtain ⟨u, -, hu⟩ := hx
    exact ⟨u, mem_support_query t u, ih u hu⟩

/-- **A run under an oracle, replayed**: a logged run of `oa` under any implementation of the
oracle, ending at `(x, log)`, is reproduced by answering from any `ans` that agrees with the
log. -/
theorem replay_of_mem_support_simulateQ {α : Type} {n : Type → Type} [Monad n] [LawfulMonad n]
    [MonadAttach n] [ExactMonadAttach n] (impl : QueryImpl (Q →ₒ D) n)
    (oa : OracleComp (Q →ₒ D) α) {x : α} {log : (Q →ₒ D).QueryLog}
    (h : (x, log) ∈ support (simulateQ impl oa.withQueryLog)) (ans : Q → Option D)
    (hans : ∀ e ∈ log, ans e.1 = some e.2) :
    (simulateQ (replayImpl ans) oa).run [] = some (x, log) := by
  simpa using run_simulateQ_replayImpl ans oa (support_simulateQ_subset impl _ h) hans []

/-- **A run under a stateful oracle, replayed**: a logged run of `oa` under a stateful
implementation of the oracle, a lazy random oracle say, ending at `(x, log)`, is reproduced by
answering from any `ans` that agrees with the log. -/
theorem replay_of_mem_support_simulateQ_run' {α σ : Type} {n : Type → Type} [Monad n]
    [LawfulMonad n] [MonadAttach n] [ExactMonadAttach n] (impl : QueryImpl (Q →ₒ D) (StateT σ n))
    (oa : OracleComp (Q →ₒ D) α) (s : σ) {x : α} {log : (Q →ₒ D).QueryLog}
    (h : (x, log) ∈ support ((simulateQ impl oa.withQueryLog).run' s)) (ans : Q → Option D)
    (hans : ∀ e ∈ log, ans e.1 = some e.2) :
    (simulateQ (replayImpl ans) oa).run [] = some (x, log) := by
  simpa using run_simulateQ_replayImpl ans oa (support_simulateQ_run'_subset impl _ s h) hans []

end

end LeanerVM.Protocol.QueryLog
