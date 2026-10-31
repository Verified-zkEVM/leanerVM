import SphincsFors.BridgeSupport

/-! Every canonical WOTS encoding-search input of the candidate key is answered from an
independent pre-sampled table placed in the lazy outside oracle's initial cache. Encoding
targets are then fixed before the run. -/

open OracleComp OracleSpec ENNReal

namespace SphincsFors.Security.HiddenBridge

open Eager Short HiddenCost Concrete

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

/-- Every leaf's canonical WOTS encoding search of its FORS tops, run in order. -/
def searchAll (parameter : PublicParameter) (forsKey : Index → FtsTops) :
    OracleComp HashSpec (Index → Option (Counter × Encoding)) :=
  Concrete.sequenceFin fun leaf => ReferenceChoice.search parameter topLayer rootTree leaf (forsKey leaf)
    encodingAttemptLimit 0

theorem Only.searchAll (parameter : PublicParameter) (forsKey : Index → FtsTops) :
    Short.Only (searchAll parameter forsKey) :=
  Short.Only.sequenceFin _ fun _ => Only.search _ _ _ _ _ _ _

/-- Running any short hash computation on the lazy oracle first, then sampling the remaining
table, is the eager table itself. Only the resulting cache is kept. -/
theorem evalDist_eager_prefix {β γ : Type} (computation : OracleComp HashSpec γ)
    (hshort : Short.Only computation) (cache : QueryCache HashSpec)
    (next : (HashInput → HashOutput) → ProbComp β) :
    (($ᵗ Eager.Table) >>= fun outside => next (extend cache outside)) =ᵈ ((simulateQ randomOracle computation).run cache >>= fun result =>
        ($ᵗ Eager.Table) >>= fun outside => next (extend result.2 outside)) := by
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, pure_bind, EvalDistEq.refl]
  | query_bind input next' ih =>
      rw [Short.Only, isQueryBoundP_query_bind_iff] at hshort
      have hnext : ∀ answer, Short.Only (next' answer) := fun answer => by
        have := hshort.2 answer
        split at this <;> simpa [Short.Only] using this
      have hinput : IsShort input := by
        rcases hshort.1 with hnot | hzero
        · exact Classical.not_not.mp hnot
        · omega
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, bind_assoc]
      change _ =ᵈ (randomOracle (spec := HashSpec) input).run cache >>= _
      cases hc : cache input with
      | some answer =>
          rw [QueryImpl.withCaching_run_some _ hc, pure_bind]
          exact ih answer (hnext answer) cache
      | none =>
          rw [QueryImpl.withCaching_run_none _ hc, bind_map_left]
          have hupdate : ∀ (answer : HashOutput) (outside : Eager.Table),
              next (extend (cache.cacheQuery input answer) outside) =
                (fun table => next (extend cache table)) (Function.update outside ⟨input, hinput⟩ answer) := by
            intro answer outside
            simp only [extend_cacheQuery cache outside hinput hc answer]
          have hassoc : (($ᵗ HashOutput : ProbComp HashOutput) >>= fun answer => ($ᵗ Eager.Table) >>=
                fun outside => pure (Function.update outside ⟨input, hinput⟩ answer)) >>=
                  (fun outside => next (extend cache outside)) =
              ($ᵗ HashOutput : ProbComp HashOutput) >>= fun answer => ($ᵗ Eager.Table) >>= fun outside =>
                next (extend (cache.cacheQuery input answer) outside) := by
            simp only [bind_assoc, pure_bind, hupdate]
          refine ((uniformSample_bind_update_evalDistEq (D := ShortIn) (R := HashOutput)
            ⟨input, hinput⟩).bind_left _).symm.trans ?_
          rw [hassoc]
          change _ =ᵈ uniformSampleImpl (spec := HashSpec) input >>= _
          exact EvalDistEq.bind_right _ fun answer => ih answer (hnext answer) _

section Game

open Completeness SeedModel Graph Assembly Reduce HiddenGraph Internalize GraphView

variable [Params]

attribute [local instance] sampleCellFintypeInst sampleCellDecEq hiddenTableSampleable highsSampleable
  remainingSampleable

/-- The preparation run of one sample: every canonical encoding search, started from the
structural cache. -/
noncomputable def preparation (parameterOutput : HashOutput) (fixed : HiddenGraph.Table)
    (highs : CoordinateHighs) (remaining : RemainingOutputs) :
    ProbComp ((Index → Option (Counter × Encoding)) × QueryCache HashSpec) :=
  (simulateQ randomOracle (searchAll (truncateHash parameterOutput)
    (sampleData parameterOutput fixed highs remaining).forsKey)).run
    (structCache (splitMaterial parameterOutput highs remaining fixed) (splitAnswers highs remaining fixed))

end Game

end SphincsFors.Security.HiddenBridge
