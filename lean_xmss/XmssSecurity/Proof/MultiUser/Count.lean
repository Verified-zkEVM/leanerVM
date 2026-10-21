import XmssSecurity.Proof.MultiUser.Reduction
import XmssSecurity.Proof.Bridge.AttributedSecurity

/-!
# The reductions' counts in the multi-user game

The reduction against key `j` runs, in its single-key game, the multi-user game with key `j`
generated first. With the traces of every key generation and of the rest kept apart, its game is,
in distribution, the multi-user game with every key generation traced (`evalDist_tracedAt`): its
attributable count is the count, over every trace but key `j`'s own generation, of the calls starting
with key `j`'s parameter, and its budget is the length of all of them.
-/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.MultiUser

open Seeded

set_option backward.isDefEq.respectTransparency false

local notation "World" => LeanXmss.OracleWorld

variable {n : Nat}

/-- Key generation with its trace. -/
noncomputable abbrev tracedKeygen : OracleComp OracleWorld (KeyPair × List HashInput) :=
  traceHashes (LeanXmss.MultiUser.keygen : OracleComp OracleWorld KeyPair)

/-- The traces of a sequence of key generations with position `j`'s replaced by none. -/
def blankWith (j : Fin n) (key : KeyPair × List HashInput) (parts : Fin n → KeyPair × List HashInput) :
    Fin n → KeyPair × List HashInput :=
  fun i => if i = j then (key.1, []) else parts i

/-- The traces of a sequence of key generations with position `j`'s emptied. -/
abbrev blank (j : Fin n) (parts : Fin n → KeyPair × List HashInput) : Fin n → KeyPair × List HashInput :=
  blankWith j (parts j) parts

/-- The multi-user game verified under key `j`, every key generation traced: the result, key `j`
with its trace, and the trace of the rest of the run. -/
noncomputable def tracedAt (adversary : LeanXmss.MultiUser.Adversary n) (j : Fin n) :
    OracleComp OracleWorld (Bool × (KeyPair × List HashInput) × List HashInput) :=
  LeanXmss.Concrete.sequenceFin (fun _ : Fin n => tracedKeygen) >>= fun parts =>
    traceHashes (body adversary (fun i => (blank j parts i).1) >>= finish (parts j).1.1 j :
      OracleComp OracleWorld Bool) >>= fun s =>
        pure (s.1, parts j, flatTrace (blank j parts) ++ s.2)

/-- The reduction's single-key game after key generation, with key generation's trace and the
rest's kept apart. -/
noncomputable def tracedReduction (adversary : LeanXmss.MultiUser.Adversary n) (j : Fin n) :
    OracleComp OracleWorld (Bool × (KeyPair × List HashInput) × List HashInput) :=
  tracedKeygen >>= fun keyed =>
    traceHashes (restAt adversary j keyed.1 : OracleComp OracleWorld Bool) >>= fun r =>
      pure (r.1, keyed, r.2)

theorem traceHashes_keyAt (j : Fin n) (key : KeyPair) :
    (fun i : Fin n => traceHashes (if i = j then pure key else
        (LeanXmss.MultiUser.keygen : OracleComp OracleWorld KeyPair))) =
      fun i => if i = j then pure (key, []) else tracedKeygen := by
  funext i
  split <;> rfl

/-- **The reduction's game is the multi-user game with every key generation traced.** -/
theorem evalDist_tracedAt (adversary : LeanXmss.MultiUser.Adversary n) (j : Fin n) :
    romRun (tracedReduction adversary j) ∅ =ᵈ romRun (tracedAt adversary j) ∅ := by
  have hrest : ∀ keyed : KeyPair × List HashInput,
      (traceHashes (restAt adversary j keyed.1 : OracleComp OracleWorld Bool) >>= fun r =>
          (pure (r.1, keyed, r.2) : OracleComp OracleWorld _)) =
        LeanXmss.Concrete.sequenceFin (fun i : Fin n => if i = j then pure keyed else tracedKeygen) >>=
          fun parts => traceHashes (body adversary (fun i => (blankWith j keyed parts i).1) >>=
            finish keyed.1.1 j : OracleComp OracleWorld Bool) >>= fun s =>
              pure (s.1, keyed, flatTrace (blankWith j keyed parts) ++ s.2) := by
    intro keyed
    unfold restAt
    rw [traceHashes_bind, traceHashes_sequenceFin, traceHashes_keyAt]
    simp only [bind_map_left, bind_assoc, pure_bind]
    rw [← sequenceFin_slot j keyed (keyed.1, []) (fun _ => tracedKeygen)]
    rfl
  unfold tracedReduction
  simp only [hrest]
  have hfront := romRun_sequenceFin_front n (fun _ => tracedKeygen) j
    (fun keyed parts => traceHashes (body adversary (fun i => (blankWith j keyed parts i).1) >>=
      finish keyed.1.1 j : OracleComp OracleWorld Bool) >>= fun s =>
        (pure (s.1, keyed, flatTrace (blankWith j keyed parts) ++ s.2) : OracleComp OracleWorld _)) ∅
  exact hfront

/-- The reduction's game, as a run from the empty cache, without the cache. -/
theorem evalDist_tracedAt_run' (adversary : LeanXmss.MultiUser.Adversary n) (j : Fin n) :
    (simulateQ romImpl (tracedReduction adversary j)).run' ∅ =ᵈ
      (simulateQ romImpl (tracedAt adversary j)).run' ∅ := by
  rw [StateT.run'_eq, StateT.run'_eq]
  exact (evalDist_tracedAt adversary j).map Prod.fst

theorem keygen_bind_traced {β : Type} (next : KeyPair → OracleComp OracleWorld β) :
    traceHashes ((LeanXmss.MultiUser.keygen : OracleComp OracleWorld KeyPair) >>= next) =
      tracedKeygen >>= fun keyed => traceHashes (next keyed.1) >>= fun r =>
        pure (r.1, keyed.2 ++ r.2) := traceHashes_bind _ _

/-- **The reduction's attributable count** is the count, in the multi-user game verified under key
`j`, of the calls starting with key `j`'s parameter outside key `j`'s own generation. -/
theorem expectedAttributedQueries_reduction (adversary : LeanXmss.MultiUser.Adversary n) (j : Fin n) :
    LeanXmss.Security.expectedAttributedQueries (reduction adversary j) =
      ∑' x, Pr{let y ← (simulateQ romImpl (tracedAt adversary j)).run' ∅}[y = x] *
        ((x.2.2.countP fun input => decide (IsParameterHashInput x.2.1.1.1.parameter input) : Nat) :
          ℝ≥0∞) := by
  rw [Bridge.expectedAttributedQueries_eq]
  have hcounted : (Bridge.realCounted (reduction adversary j) : OracleComp OracleWorld (Bool × Nat)) =
      (fun x => (x.1, x.2.2.countP fun input =>
        decide (IsParameterHashInput x.2.1.1.1.parameter input))) <$> tracedReduction adversary j := by
    have hkeygen : (Bridge.realCounted (reduction adversary j) : OracleComp OracleWorld (Bool × Nat)) =
        (LeanXmss.MultiUser.keygen : OracleComp OracleWorld KeyPair) >>= fun keys =>
          QueryCounting.counted (IsParameterQuery keys.1.parameter)
            (Bridge.realRest (reduction adversary j) keys.1 keys.2) := by
      unfold Bridge.realCounted Bridge.countedAfterSeed LeanXmss.MultiUser.keygen
      simp only [bind_assoc]
      refine bind_congr fun seed => ?_
      rw [Bridge.keygenFromSeed_eq, liftM_bind, bind_assoc]
      rfl
    rw [hkeygen]
    simp only [← Bridge.realRest_eq_gameRest, gameRest_reduction, counted_eq_traceHashes]
    rw [← traceHashes_forget (LeanXmss.MultiUser.keygen : OracleComp OracleWorld KeyPair), bind_map_left]
    unfold tracedReduction
    simp only [map_bind, map_pure]
    refine bind_congr fun a => ?_
    simp only [map_eq_bind_pure_comp]
    rfl
  unfold Bridge.realAttributedMean Bridge.countMeanFrom
  rw [hcounted, simulateQ_map, StateT.run'_map', OracleComp.tsum_prEvent_map_mul]
  exact tsum_prEvent_mul_congr (evalDist_tracedAt_run' adversary j) _

-- Keep the linters from unfolding the seed's uniform draw and key generation.
attribute [local irreducible] LeanXmss.Seeded.keygenFromSeed LeanXmss.sampleMasterSeed

theorem hasHashQueryBound_iff_gameCore (adversary : LeanXmss.Security.Adversary) (q : Nat) :
    LeanXmss.Security.HasHashQueryBound adversary q ↔
      HashQueryBound (LeanXmss.Security.gameCore adversary : OracleComp OracleWorld Bool) ∅ q := by
  simp only [HashQueryBound, simulateQ_countHashQueries]
  exact Iff.rfl

/-- **The reduction's budget** is the length of every trace of the multi-user game verified under
key `j`. -/
theorem hasHashQueryBound_reduction (adversary : LeanXmss.MultiUser.Adversary n) (j : Fin n) (q : Nat)
    (hbound : ∀ x ∈ support ((simulateQ romImpl (tracedAt adversary j)).run' ∅),
      x.2.1.2.length + x.2.2.length ≤ q) :
    LeanXmss.Security.HasHashQueryBound (reduction adversary j) q := by
  have hgame : HashQueryBound (LeanXmss.Security.gameCore (reduction adversary j) :
      OracleComp OracleWorld Bool) ∅ q := by
    intro r hr
    rw [countHashQueries_eq_traceHashes, gameCore_reduction, keygen_bind_traced] at hr
    have heq : (tracedKeygen >>= fun keyed =>
          traceHashes (restAt adversary j keyed.1 : OracleComp OracleWorld Bool) >>= fun r =>
            (pure (r.1, keyed.2 ++ r.2) : OracleComp OracleWorld _)) =
        (fun x => (x.1, x.2.1.2 ++ x.2.2)) <$> tracedReduction adversary j := by
      unfold tracedReduction
      simp only [map_bind, map_pure]
    rw [heq, Functor.map_map, simulateQ_map, StateT.run'_map', support_map] at hr
    obtain ⟨x, hx, rfl⟩ := hr
    rw [support_eq_of_evalDistEq (evalDist_tracedAt_run' adversary j)] at hx
    change (x.2.1.2 ++ x.2.2).length ≤ q
    rw [List.length_append]
    exact hbound x hx
  exact (hasHashQueryBound_iff_gameCore _ q).mpr hgame

end XmssSecurity.MultiUser
