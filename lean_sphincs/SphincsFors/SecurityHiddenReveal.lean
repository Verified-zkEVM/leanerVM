import SphincsFors.Uniform
import VCVio.OracleComp.QueryTracking.RandomOracle.EagerTable
import SphincsBase.Proof.Base.QueryCap

/-! Reveal/guess experiments on independently sampled candidate digest coordinates. The exposed
coordinates form a knowledge cache and `completion` samples the others uniformly; revealing a
coordinate commutes with that sampling, and one guessed value at an unexposed coordinate has exact
probability `2^-128`. This is exact uniform completion of the exposed cache, rather than an
assumption that a coordinate stays uniform after conditioning on earlier failed guesses. -/

open OracleComp OracleSpec ENNReal
namespace SphincsFors.Security.HiddenReveal
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 100000
attribute [local instance] Classical.propDecidable

variable {ι : Type} [Fintype ι]
noncomputable local instance : DecidableEq ι := Classical.decEq ι
noncomputable local instance tableSampleable : SampleableType (ι → Digest) := SampleableType.ofFintype _

abbrev Knowledge (ι : Type) := QueryCache (ι →ₒ Digest)
abbrev ViewSpec (ι : Type) := unifSpec + ((ι →ₒ Digest) + ((ι × Digest) →ₒ Unit))

noncomputable def completion (known : Knowledge ι) : ProbComp (ι → Digest) :=
  tableExtending known <$> ($ᵗ (ι → Digest) : ProbComp (ι → Digest))

omit [Fintype ι] in
theorem completion_known (known : Knowledge ι) (coordinate : ι) (value : Digest)
    (hknown : known coordinate = some value) (table : ι → Digest) :
    tableExtending known table coordinate = value := by simp [tableExtending, hknown]

/-- Revealing any selected coordinate commutes with sampling the remaining uniform table.
This includes the full residual table, so arbitrary adaptive continuations may follow. -/
theorem completion_reveal {α : Type} (known : Knowledge ι) (coordinate : ι)
    (next : Digest → (ι → Digest) → ProbComp α) :
    (completion known >>= fun table => next (table coordinate) table) =ᵈ (do
        let (value, known') ← (randomOracle (spec := ι →ₒ Digest) coordinate).run known
        completion known' >>= next value) := by
  cases hc : known coordinate with
  | some value =>
      rw [QueryImpl.withCaching_run_some _ hc, pure_bind]
      simp only [completion, bind_map_left, completion_known known coordinate value hc, EvalDistEq.refl]
  | none =>
      rw [QueryImpl.withCaching_run_none _ hc]
      simp only [completion, bind_map_left]
      let continuation := fun table : ι → Digest =>
        next (tableExtending known table coordinate) (tableExtending known table)
      change ($ᵗ (ι → Digest)) >>= continuation =ᵈ _
      refine (((uniformSample_bind_update_evalDistEq (D := ι) (R := Digest) coordinate).bind_left
        continuation).symm).trans ?_
      simp only [bind_assoc, pure_bind]
      refine EvalDistEq.bind_right _ fun value => EvalDistEq.bind_right _ fun table => ?_
      have heq : tableExtending known (Function.update table coordinate value) =
          tableExtending (known.cacheQuery coordinate value) table := by
        rw [tableExtending_cacheQuery, tableExtending_update_of_none known table hc]
      simp only [continuation, heq, tableExtending, hc, Function.update_self, Option.getD_none,
        EvalDistEq.refl]

noncomputable def run {α : Type} (table : ι → Digest) (computation : OracleComp (ViewSpec ι) α) :
    Knowledge ι → ProbComp (Option α) :=
  OracleComp.construct (fun value _ => pure (some value))
    (fun input _ next known =>
      match input with
      | .inl draw => do
          let value ← liftM (unifSpec.query draw)
          next value known
      | .inr (.inl coordinate) => next (table coordinate)
          (known.cacheQuery coordinate (table coordinate))
      | .inr (.inr guess) =>
          if known guess.1 = none ∧ table guess.1 = guess.2 then pure none
          else next () known) computation

omit [Fintype ι] in
theorem run_pure {α : Type} (table : ι → Digest) (value : α) (known : Knowledge ι) :
    run table (pure value) known = pure (some value) := rfl

noncomputable def experiment {α : Type} (computation : OracleComp (ViewSpec ι) α)
    (known : Knowledge ι) : ProbComp (Option α) :=
  completion known >>= fun table => run table computation known

end SphincsFors.Security.HiddenReveal
