/-
  LeanVM.Protocol.Rpm.Coins

  Knowledge soundness of `LeanVM/Spec/Statement.lean` for adversaries that also have private
  coins: the coins do not help.
-/

import LeanVM.Protocol.LeanVMSound
import LeanRpm.Prob

/-!
# Adversaries with coins

`KnowledgeSoundness` (`LeanVM/Spec/Statement.lean`) quantifies over adversaries querying the two
random oracles only. The random-oracle adversary that the random-permutation transfer produces
(`LeanRpm.advS2`: the adversary with the indifferentiability simulator) also flips coins. Against
the lazily sampled random oracles such an adversary does no better than some deterministic
adversary with the same number of oracle queries (`exists_det`): at a coin, the best of the finitely
many continuations; at an oracle query, the query followed by the best continuation at each answer.
So the bound of `knowledgeSoundness_holds` holds for it (`knowledgeSoundness_coins`), coins not
counted.
-/

open OracleComp OracleSpec
open scoped ENNReal

namespace LeanVM.Rpm

open LeanVM.Protocol.Compile

/-- Oracle calls, coins free. -/
def hashCalls : (unifSpec + HashSpec).Domain → ℕ
  | .inl _ => 0
  | .inr _ => 1

theorem romImpl_inl_run (n : ℕ) (c : HashSpec.QueryCache) :
    (HashSpec.romImpl (.inl n)).run c = (fun x => (x, c)) <$> (unifSpec.query n : ProbComp _) := by
  simp [unifFwdImpl]

/-- The cache after a random-oracle step answering `u` at `t` from `c`. -/
def stepCache (c : HashSpec.QueryCache) (t : HashSpec.Domain) (u : HashSpec.Range t) :
    HashSpec.QueryCache :=
  match c t with
  | some _ => c
  | none => c.cacheQuery t u

theorem snd_eq_stepCache {c : HashSpec.QueryCache} {t : HashSpec.Domain}
    {z : HashSpec.Range t × HashSpec.QueryCache} (hz : z ∈ support ((HashSpec.randomOracle t).run c)) :
    z.2 = stepCache c t z.1 := by
  rw [randomOracle.run_eq] at hz
  unfold stepCache
  cases h : c t with
  | some u =>
    simp only [h, support_pure, Set.mem_singleton_iff] at hz
    subst hz; rfl
  | none =>
    simp only [h, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨u, -, rfl⟩ := hz
    rfl

/-- **Derandomization.** Against the random oracle, an adversary with coins does no better than
some deterministic adversary of the same query budget, for any continuation and any event. -/
theorem exists_det {α γ : Type} (g : α × HashSpec.QueryCache → ProbComp γ) (E : γ → Prop)
    (X : OracleComp (unifSpec + HashSpec) α) :
    ∀ (Q : ℕ), LeanRpm.IsWeightBound X hashCalls Q → ∀ c : HashSpec.QueryCache,
      ∃ A : OracleComp HashSpec α, IsTotalQueryBound A Q ∧
        Pr{let y ← (simulateQ HashSpec.romImpl X).run c >>= g}[E y] ≤
          Pr{let y ← (simulateQ HashSpec.randomOracle A).run c >>= g}[E y] := by
  induction X using OracleComp.inductionOn with
  | pure a =>
    intro Q _ c
    exact ⟨pure a, trivial, by simp⟩
  | query_bind t k ih =>
    intro Q hX c
    rw [LeanRpm.isWeightBound_query_bind_iff] at hX
    obtain ⟨ht, hk⟩ := hX
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind, bind_assoc]
    rcases t with n | t
    · -- a coin: average below the best continuation
      have hk' : ∀ u, LeanRpm.IsWeightBound (k u) hashCalls Q := fun u ↦ by
        simpa [hashCalls] using hk u
      choose A hA hle using fun u ↦ ih u Q (hk' u) c
      let f : Fin (n + 1) → ℝ≥0∞ := fun u ↦
        Pr{let y ← (simulateQ HashSpec.randomOracle (A u)).run c >>= g}[E y]
      obtain ⟨u₀, hu₀⟩ := Finite.exists_max f
      refine ⟨A u₀, hA u₀, ?_⟩
      refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun z hz ↦ ?_
      rw [romImpl_inl_run, support_map] at hz
      obtain ⟨u, -, rfl⟩ := hz
      exact (hle u).trans (hu₀ u)
    · -- a hash query: query it, then follow the best continuation at each answer
      have hQ : 1 ≤ Q := ht
      choose A hA hle using fun u ↦ ih u (Q - 1) (hk u) (stepCache c t u)
      refine ⟨liftM (HashSpec.query t) >>= A, ?_, ?_⟩
      · exact isTotalQueryBound_query_bind_iff.mpr ⟨by omega, hA⟩
      · simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
          OracleQuery.cont_query, id_map, StateT.run_bind, bind_assoc]
        refine prEvent_bind_mono_of_forall_le_of_support _ _ _ _ _ fun z hz ↦ ?_
        have hz' : z.2 = stepCache c t z.1 := snd_eq_stepCache hz
        rw [hz']
        exact hle z.1

/-- The experiment of `Statement.lean` against an adversary that also has private coins. -/
noncomputable def experimentCoins (B : OracleComp (unifSpec + HashSpec) (Statement × Proof)) :
    ProbComp Outcome := do
  let (z, adversaryCache) ← (simulateQ HashSpec.romImpl B).run ∅
  let (verdict, cache) ←
    (simulateQ HashSpec.randomOracle (verifier queryH queryF z.1.1 z.1.2 z.2)).run adversaryCache
  return ((z, verdict), cache, adversaryCache)

/-- **Knowledge soundness against adversaries with coins**: private coins do not help, so the
bound of `knowledgeSoundness_holds` holds for every adversary with coins of at most `Q` oracle
calls. -/
theorem knowledgeSoundness_coins {B : OracleComp (unifSpec + HashSpec) (Statement × Proof)} {Q : ℕ}
    (hB : LeanRpm.IsWeightBound B hashCalls Q) :
    Pr{let z ← experimentCoins B}[Breaks extractor z] ≤ soundnessError Q := by
  obtain ⟨A, hA, hle⟩ := exists_det (fun p ↦ do
      let (verdict, cache) ←
        (simulateQ HashSpec.randomOracle (verifier queryH queryF p.1.1.1 p.1.1.2 p.1.2)).run p.2
      return ((p.1, verdict), cache, p.2)) (Breaks extractor) B Q hB ∅
  exact hle.trans (knowledgeSoundness_holds A Q hA)

end LeanVM.Rpm
