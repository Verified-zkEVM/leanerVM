import XmssSecurity.Proof.MultiUser.Coincidence
import XmssSecurity.Proof.VerifyQueryBound

/-!
# The multi-user budget

The multi-user game is its prefix, the key generations and the adversary with every key's signing
oracle, every trace kept (`tracedPrefix`), then a verification of at most `verifyHashBound` hash
calls (`length_trace_finish_le`). The budget `q` bounds every prefix's traces (`prefix_length_le`),
and the reduction against key `j` spends the prefix and one verification: `q + verifyHashBound`
(`hasHashQueryBound_reduction_of`).
-/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.MultiUser

open Seeded

set_option backward.isDefEq.respectTransparency false

local notation "World" => LeanXmss.OracleWorld

variable {n : Nat}

/-- The key generations and the adversary, every trace kept. -/
noncomputable def tracedPrefix (adversary : LeanXmss.MultiUser.Adversary n) :
    OracleComp OracleWorld ((Fin n → KeyPair × List HashInput) ×
      ((LeanXmss.MultiUser.Forgery n × QueryLog (LeanXmss.MultiUser.SigningSpec n)) × List HashInput)) :=
  LeanXmss.Concrete.sequenceFin (fun _ : Fin n => tracedKeygen) >>= fun parts =>
    (fun s => (parts, s)) <$>
      traceHashes (body adversary (fun i => (parts i).1) : OracleComp OracleWorld _)

theorem blank_fst (j : Fin n) (parts : Fin n → KeyPair × List HashInput) :
    (fun i => (blank j parts i).1) = fun i => (parts i).1 := by
  funext i
  unfold blank blankWith
  split
  · next h => subst h; rfl
  · rfl

theorem sum_blank (j : Fin n) (parts : Fin n → KeyPair × List HashInput) (g : List HashInput → Nat)
    (hg : g [] = 0) :
    (∑ i, g (blank j parts i).2) + g (parts j).2 = ∑ i, g (parts i).2 := by
  have h : ∀ i, g (blank j parts i).2 = if i = j then 0 else g (parts i).2 := by
    intro i
    unfold blank blankWith
    split <;> simp [hg]
  simp only [h]
  rw [← Finset.sum_erase_add Finset.univ (fun i => g (parts i).2) (Finset.mem_univ j)]
  congr 1
  rw [Finset.sum_ite, Finset.sum_const_zero, zero_add]
  congr 1
  ext i
  simp [Finset.mem_erase, and_comm]

theorem tracedAt_eq (adversary : LeanXmss.MultiUser.Adversary n) (j : Fin n) :
    tracedAt adversary j = tracedPrefix adversary >>= fun p =>
      traceHashes (finish (p.1 j).1.1 j p.2.1 : OracleComp OracleWorld Bool) >>= fun f =>
        pure (f.1, p.1 j, flatTrace (blank j p.1) ++ (p.2.2 ++ f.2)) := by
  unfold tracedAt tracedPrefix
  simp only [bind_assoc, bind_map_left, blank_fst, traceHashes_bind, pure_bind]

theorem traceHashes_prefixRun (adversary : LeanXmss.MultiUser.Adversary n) :
    traceHashes (prefixRun adversary : OracleComp OracleWorld _) =
      (fun x => ((fun i => (x.1 i).1, x.2.1), flatTrace x.1 ++ x.2.2)) <$> tracedPrefix adversary := by
  unfold prefixRun tracedPrefix
  rw [traceHashes_bind, traceHashes_sequenceFin]
  simp only [bind_map_left, map_bind, Functor.map_map, traceHashes_map]
  refine bind_congr fun parts => ?_
  simp only [map_eq_bind_pure_comp]
  rfl

theorem traceHashes_gameCore (adversary : LeanXmss.MultiUser.Adversary n) :
    traceHashes (LeanXmss.MultiUser.gameCore adversary : OracleComp OracleWorld Bool) =
      tracedPrefix adversary >>= fun x =>
        traceHashes (finish (x.1 x.2.1.1.key).1.1 x.2.1.1.key x.2.1 : OracleComp OracleWorld Bool) >>=
          fun s => pure (s.1, (flatTrace x.1 ++ x.2.2) ++ s.2) := by
  rw [gameCore_eq_prefixRun, traceHashes_bind, traceHashes_prefixRun, bind_map_left]

/-! ## Verification -/

theorem length_trace_le_of_isQueryBoundP {α : Type} (computation : OracleComp OracleWorld α)
    {k : Nat} (hbound : computation.IsQueryBoundP IsHashQuery k)
    (cache : QueryCache HashSpec) (r : (α × List HashInput) × QueryCache HashSpec)
    (hr : r ∈ support (romRun (traceHashes computation) cache)) : r.1.2.length ≤ k := by
  induction computation using OracleComp.inductionOn generalizing k cache r with
  | pure value =>
      simp only [traceHashes_pure, romRun, simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hr
      subst hr
      exact Nat.zero_le _
  | query_bind input next ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
      rw [traceHashes_query_bind, romRun_query_bind, mem_support_bind_iff] at hr
      obtain ⟨answer, _, hrest⟩ := hr
      rw [romRun_bind, mem_support_bind_iff] at hrest
      obtain ⟨inner, hinner, hfinal⟩ := hrest
      simp only [romRun, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hfinal
      subst hfinal
      have hih := ih answer.1 (hbound.2 answer.1) answer.2 inner hinner
      cases input with
      | inl m =>
          simpa [prependHash, IsHashQuery] using hih
      | inr x =>
          have hpos : 0 < k := by
            rcases hbound.1 with h | h
            · exact absurd rfl h
            · exact h
          simp only [prependHash, List.length_cons]
          simp only [IsHashQuery, ↓reduceIte] at hih
          omega

theorem finish_isQueryBoundP (publicKey : LeanXmss.PublicKey) (j : Fin n)
    (result : LeanXmss.MultiUser.Forgery n × QueryLog (LeanXmss.MultiUser.SigningSpec n)) :
    (finish publicKey j result : OracleComp OracleWorld Bool).IsQueryBoundP IsHashQuery
      verifyHashBound := by
  have hverify : (liftM (show OracleComp HashSpec Bool from
      LeanXmss.Concrete.verify (m := OracleComp LeanXmss.HashSpec) publicKey result.1.forgery.message
        result.1.forgery.signature) : OracleComp OracleWorld Bool).IsQueryBoundP IsHashQuery
          verifyHashBound := by
    rw [Bridge.verify_real]
    exact scheme_verify_isHashQueryBound _ _ _ _
  unfold finish
  rw [show verifyHashBound = verifyHashBound + 0 from rfl]
  exact OracleComp.isQueryBoundP_bind hverify fun _ _ => OracleComp.isQueryBoundP_pure _ _ _

theorem length_trace_finish_le (publicKey : LeanXmss.PublicKey) (j : Fin n)
    (result : LeanXmss.MultiUser.Forgery n × QueryLog (LeanXmss.MultiUser.SigningSpec n))
    (cache : QueryCache HashSpec) (r : (Bool × List HashInput) × QueryCache HashSpec)
    (hr : r ∈ support (romRun (traceHashes (finish publicKey j result : OracleComp OracleWorld Bool))
      cache)) : r.1.2.length ≤ verifyHashBound :=
  length_trace_le_of_isQueryBoundP _ (finish_isQueryBoundP publicKey j result) cache r hr

/-! ## The budget -/

-- Keep the linters from unfolding the seed's uniform draw and key generation.
attribute [local irreducible] LeanXmss.Seeded.keygenFromSeed LeanXmss.sampleMasterSeed

theorem hashQueryBound_gameCore (adversary : LeanXmss.MultiUser.Adversary n) (q : Nat)
    (hbound : LeanXmss.MultiUser.HasHashQueryBound adversary q) :
    HashQueryBound (LeanXmss.MultiUser.gameCore adversary : OracleComp OracleWorld Bool) ∅ q := by
  simp only [HashQueryBound, simulateQ_countHashQueries]
  exact hbound

/-- The budget bounds the traces of every prefix. -/
theorem prefix_length_le (adversary : LeanXmss.MultiUser.Adversary n) (q : Nat)
    (hbound : LeanXmss.MultiUser.HasHashQueryBound adversary q)
    (x : _ × QueryCache HashSpec) (hx : x ∈ support (romRun (tracedPrefix adversary) ∅)) :
    (flatTrace x.1.1).length + x.1.2.2.length ≤ q := by
  have hgame := hashQueryBound_gameCore adversary q hbound
  obtain ⟨f, hf⟩ := probComp_support_nonempty (romRun (traceHashes
    (finish (x.1.1 x.1.2.1.1.key).1.1 x.1.2.1.1.key x.1.2.1 : OracleComp OracleWorld Bool)) x.2)
  have hmem : (f.1.1, (flatTrace x.1.1 ++ x.1.2.2) ++ f.1.2) ∈
      support ((simulateQ romImpl (traceHashes (LeanXmss.MultiUser.gameCore adversary :
        OracleComp OracleWorld Bool))).run' ∅) := by
    rw [StateT.run'_eq, support_map]
    refine ⟨((f.1.1, (flatTrace x.1.1 ++ x.1.2.2) ++ f.1.2), f.2), ?_, rfl⟩
    rw [traceHashes_gameCore]
    change _ ∈ support (romRun _ ∅)
    rw [romRun_bind, mem_support_bind_iff]
    refine ⟨x, hx, ?_⟩
    rw [romRun_bind, mem_support_bind_iff]
    exact ⟨f, hf, by simp [romRun]⟩
  have h := traceHashes_length_le _ ∅ q hgame _ hmem
  simp only [List.length_append] at h
  omega

/-- **The reduction's budget** in the multi-user budget: one more verification. -/
theorem hasHashQueryBound_reduction_of (adversary : LeanXmss.MultiUser.Adversary n) (j : Fin n)
    (q : Nat) (hbound : LeanXmss.MultiUser.HasHashQueryBound adversary q) :
    LeanXmss.Security.HasHashQueryBound (reduction adversary j) (q + verifyHashBound) := by
  refine hasHashQueryBound_reduction adversary j _ fun x hx => ?_
  rw [tracedAt_eq, StateT.run'_eq, support_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  change y ∈ support (romRun _ ∅) at hy
  rw [romRun_bind, mem_support_bind_iff] at hy
  obtain ⟨p, hp, hy⟩ := hy
  rw [romRun_bind, mem_support_bind_iff] at hy
  obtain ⟨f, hf, hy⟩ := hy
  simp only [romRun, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
  subst hy
  have hprefix := prefix_length_le adversary q hbound p hp
  have hfinish := length_trace_finish_le _ _ _ _ f hf
  have hsum := sum_blank j p.1.1 List.length rfl
  simp only [List.length_append, length_flatTrace] at hprefix ⊢
  omega

end XmssSecurity.MultiUser
