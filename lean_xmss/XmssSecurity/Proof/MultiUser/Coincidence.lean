import XmssSecurity.Proof.MultiUser.Keygen
import XmssSecurity.Proof.AdaptiveFreshTarget

/-!
# Two keys share a parameter rarely

Key generation from a cache that holds at most `L` inputs outputs a fixed parameter with probability
at most `2^-128` plus two guesses of a 256-bit seed per cached input: the key's seed `S_0` would have
to name a cached seed-hash input, the scheme's seed `S` a cached parameter input, or else the
parameter is a fresh uniform truncation (`probEvent_keygen_parameter_le`). A key generation from the
empty cache caches only its own `keygenQueries` inputs (`length_trace_keygen`), so the two keys of any
pair among the `n`, which may be generated first by commuting the key generations, share a parameter
with probability at most `2^-128 + (2 K + 1) / 2^256` (`probEvent_parameter_pair_le`).
-/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.MultiUser

open Seeded

set_option backward.isDefEq.respectTransparency false

local notation "World" => LeanXmss.OracleWorld

/-- A key generation, query by query. -/
noncomputable def keygenExplicit : OracleComp OracleWorld KeyPair := do
  let keySeed ← (liftM LeanXmss.sampleMasterSeed : OracleComp OracleWorld MasterSeed)
  let seed ← (liftM (OracleWorld.query (.inr (LeanXmss.seedHashInput keySeed))) :
    OracleComp OracleWorld HashOutput)
  let output ← (liftM (OracleWorld.query (.inr (LeanXmss.keygenHashInput 0 .parameter seed))) :
    OracleComp OracleWorld HashOutput)
  let root ← (liftM (show OracleComp HashSpec LeanXmss.Digest from
    LeanXmss.Seeded.treeNode (m := OracleComp LeanXmss.HashSpec) (LeanXmss.truncateHash output)
      LeanXmss.topLayer seed LeanXmss.layerHeight 0) : OracleComp OracleWorld LeanXmss.Digest)
  return (⟨root, LeanXmss.truncateHash output⟩, ⟨seed, LeanXmss.truncateHash output, root⟩)

theorem keygen_eq_explicit :
    (LeanXmss.MultiUser.keygen : OracleComp OracleWorld KeyPair) = keygenExplicit := by
  unfold LeanXmss.MultiUser.keygen keygenExplicit
  refine bind_congr fun keySeed => ?_
  rw [Bridge.keygenFromSeed_eq, liftM_bind]
  unfold Bridge.realKeygen LeanXmss.deriveKey
  simp only [liftM_bind, liftM_pure, bind_assoc, pure_bind]
  rfl

theorem romRun_lift_prob_bind {α β : Type} (computation : ProbComp α)
    (next : α → OracleComp OracleWorld β) (cache : QueryCache HashSpec) :
    romRun ((liftM computation : OracleComp OracleWorld α) >>= next) cache =
      computation >>= fun a => romRun (next a) cache := by
  rw [romRun_bind]
  have h : simulateQ romImpl (liftM computation : OracleComp OracleWorld α) =
      simulateQ (unifFwdImpl HashSpec) computation :=
    QueryImpl.simulateQ_add_liftM_left _ _ computation
  rw [romRun, h, unifFwdImpl.simulateQ_run, bind_map_left]

/-! ## The trace's length -/

theorem length_trace_of_queryCount {α : Type} {computation : OracleComp HashSpec α} {k : Nat}
    (hcount : Bridge.QueryCount computation k) (cache : QueryCache HashSpec)
    (r : (α × List HashInput) × QueryCache HashSpec)
    (hr : r ∈ support (romRun (traceHashes (liftM computation : OracleComp OracleWorld α)) cache)) :
    r.1.2.length = k := by
  induction hcount generalizing cache r with
  | pure a =>
      simp only [liftM_pure, traceHashes_pure, romRun, simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hr
      subst hr
      rfl
  | query x next n _ ih =>
      rw [liftM_bind] at hr
      change r ∈ support (romRun (traceHashes (liftM (OracleWorld.query (.inr x)) >>= _)) cache) at hr
      rw [traceHashes_query_bind, romRun_query_bind, mem_support_bind_iff] at hr
      obtain ⟨answer, _, hrest⟩ := hr
      rw [romRun_bind, mem_support_bind_iff] at hrest
      obtain ⟨inner, hinner, hfinal⟩ := hrest
      simp only [romRun, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hfinal
      subst hfinal
      simp [prependHash, ih answer.1 answer.2 inner hinner]

theorem sampleMasterSeed_eq : LeanXmss.sampleMasterSeed = XmssSecurity.sampleMasterSeed := rfl

theorem derivationSeedHit_parameterInput (seed : MasterSeed) :
    DerivationSeedHit (LeanXmss.keygenHashInput 0 .parameter seed) seed := by
  simp [DerivationSeedHit, LeanXmss.keygenHashInput, LeanXmss.fieldBytes, LeanXmss.bytesLE]
  rfl

-- Keep elaboration from unfolding the seed's uniform draw and key generation's literal tree.
attribute [local irreducible] LeanXmss.sampleMasterSeed LeanXmss.Seeded.keygenFromSeed Bridge.realKeygen
  LeanXmss.Seeded.treeNode

/-- Key generation makes exactly `keygenQueries` hash calls. -/
theorem length_trace_keygen (cache : QueryCache HashSpec)
    (r : (KeyPair × List HashInput) × QueryCache HashSpec)
    (hr : r ∈ support (romRun tracedKeygen cache)) : r.1.2.length = Bridge.keygenQueries := by
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_support_traced_bind _ _ cache r hr
  rw [(mem_support_traced_lift_prob _ _ a ha).1, List.nil_append]
  rw [(mem_support_traced_lift_prob _ _ a ha).2] at hb
  have hcount : Bridge.QueryCount (show OracleComp HashSpec KeyPair from
      LeanXmss.Seeded.keygenFromSeed a.1.1) Bridge.keygenQueries := by
    rw [Bridge.keygenFromSeed_eq, show Bridge.keygenQueries = 1 + (Bridge.keygenQueries - 1) by
      rw [Bridge.keygenQueries_eq]]
    exact (Bridge.queryCount_oracleHash _).bind fun seed => Bridge.queryCount_realKeygen seed
  exact length_trace_of_queryCount hcount cache b hb

/-- **One key generation hits a fixed parameter** with probability at most `2^-128` plus a guess of
each seed per cached input. -/
theorem probEvent_keygen_parameter_le (inputs : List HashInput) (cache : QueryCache HashSpec)
    (hcache : ∀ x, cache x ≠ none → x ∈ inputs) (target : PublicParameter) :
    Pr{let r ← romRun (LeanXmss.MultiUser.keygen : OracleComp OracleWorld KeyPair) cache}[
        r.1.1.parameter = target] ≤
      (inputs.length : ℝ≥0∞) / ((2 ^ 256 : Nat) : ℝ≥0∞) +
        (((inputs.length + 1 : Nat) : ℝ≥0∞) / ((2 ^ 256 : Nat) : ℝ≥0∞) +
          ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) := by
  rw [keygen_eq_explicit, keygenExplicit, romRun_lift_prob_bind]
  refine (prEvent_bind_le_prEvent_add _ _ (SeedHitLog Bridge.KeySeedHit inputs) _ ?_).trans
    (add_le_add ?_ le_rfl)
  · intro keySeed hkeySeed
    have hnone : cache (LeanXmss.seedHashInput keySeed) = none := by
      by_contra h
      exact hkeySeed ⟨_, hcache _ h, rfl⟩
    rw [romRun_query_bind, romImpl_hash_run_none _ hnone, bind_map_left]
    refine (prEvent_bind_le_prEvent_add _ _
      (SeedHitLog SeedHit (LeanXmss.seedHashInput keySeed :: inputs)) _ ?_).trans
      (add_le_add ?_ le_rfl)
    · intro seed hseed
      have hnone' : (cache.cacheQuery (LeanXmss.seedHashInput keySeed) seed)
          (LeanXmss.keygenHashInput 0 .parameter seed) = none := by
        by_contra h
        by_cases heq : LeanXmss.keygenHashInput 0 .parameter seed = LeanXmss.seedHashInput keySeed
        · exact hseed ⟨_, List.mem_cons_self .., heq ▸ derivationSeedHit_parameterInput seed⟩
        · rw [QueryCache.cacheQuery_of_ne _ _ heq] at h
          exact hseed ⟨_, List.mem_cons_of_mem _ (hcache _ h), derivationSeedHit_parameterInput seed⟩
      rw [romRun_query_bind, romImpl_hash_run_none _ hnone', bind_map_left]
      refine (prEvent_bind_le_prEvent_of_support _ _
        (fun output => LeanXmss.truncateHash output = target) _ ?_).trans ?_
      · intro output _ houtput
        refine prEvent_eq_zero_of_forall_mem_support _ _ fun r hr hr' => houtput ?_
        rw [romRun_bind, mem_support_bind_iff] at hr
        obtain ⟨root, _, hfinal⟩ := hr
        simp only [romRun, simulateQ_pure, StateT.run_pure, support_pure,
          Set.mem_singleton_iff] at hfinal
        subst hfinal
        exact hr'
      · exact (Rom.uniform_truncate_probability target).le
    · change Pr{let x ← ($ᵗ HashOutput : ProbComp HashOutput)}[_] ≤ _
      rw [← (Bridge.evalDist_sampleMasterSeed).prEvent_eq]
      have h := probEvent_seedHitLog_le guessBound_seedHit (LeanXmss.seedHashInput keySeed :: inputs)
      rw [List.length_cons] at h
      exact h
  · rw [sampleMasterSeed_eq]
    exact probEvent_seedHitLog_le Bridge.guessBound_keySeedHit inputs

/-- The bound on two keys sharing a parameter. -/
noncomputable def pairBound : ℝ≥0∞ :=
  (Bridge.keygenQueries : ℝ≥0∞) / ((2 ^ 256 : Nat) : ℝ≥0∞) +
    (((Bridge.keygenQueries + 1 : Nat) : ℝ≥0∞) / ((2 ^ 256 : Nat) : ℝ≥0∞) +
      ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹)

/-- **Two key generations from the empty cache share a parameter** with probability at most
`pairBound`. -/
theorem probEvent_parameter_pair_le {γ : Type}
    (rest : KeyPair × List HashInput → KeyPair × List HashInput → OracleComp OracleWorld γ)
    (event : γ → Prop)
    (hrest : ∀ a b cache, ∀ r ∈ support (romRun (rest a b) cache), event r.1 →
      a.1.1.parameter = b.1.1.parameter) :
    Pr{let r ← romRun (tracedKeygen >>= fun a => tracedKeygen >>= fun b => rest a b) ∅}[event r.1] ≤
      pairBound := by
  rw [romRun_bind]
  refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun first hfirst => ?_
  rw [romRun_bind]
  refine (prEvent_bind_le_prEvent_of_support _ _
    (fun second => second.1.1.1.parameter = first.1.1.1.parameter) _ ?_).trans ?_
  · intro second _ hsecond
    exact prEvent_eq_zero_of_forall_mem_support _ _ fun r hr hevent =>
      hsecond (hrest _ _ _ r hr hevent).symm
  · have hmap : romRun (LeanXmss.MultiUser.keygen : OracleComp OracleWorld KeyPair) first.2 =
        (fun r => (r.1.1, r.2)) <$> romRun tracedKeygen first.2 := by
      rw [← traceHashes_forget (LeanXmss.MultiUser.keygen : OracleComp OracleWorld KeyPair), romRun,
        simulateQ_map, StateT.run_map]
    have h := probEvent_keygen_parameter_le first.1.2 first.2 (fun x hx => by
      rcases cache_mem_trace _ ∅ first hfirst x hx with h | h
      · exact absurd rfl h
      · exact h) first.1.1.1.parameter
    rw [hmap, prEvent_map, length_trace_keygen ∅ first hfirst] at h
    exact h

/-- A pure position of a sequence holds its value. -/
theorem sequenceFin_pure_slot {α : Type} :
    ∀ {n : Nat} (computation : Fin n → OracleComp OracleWorld α) (j : Fin n) (x : α),
      computation j = pure x → ∀ cache, ∀ r ∈ support (romRun (LeanXmss.Concrete.sequenceFin computation) cache),
        r.1 j = x
  | 0, _, j, _, _, _, _, _ => j.elim0
  | n + 1, computation, j, x, hj, cache, r, hr => by
      simp only [LeanXmss.Concrete.sequenceFin] at hr
      rw [romRun_bind, mem_support_bind_iff] at hr
      obtain ⟨head, hhead, hrest⟩ := hr
      rw [romRun_bind, mem_support_bind_iff] at hrest
      obtain ⟨tail, htail, hfinal⟩ := hrest
      simp only [romRun, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hfinal
      subst hfinal
      cases j using Fin.cases with
      | zero =>
          rw [hj] at hhead
          simp only [romRun, simulateQ_pure, StateT.run_pure, support_pure,
            Set.mem_singleton_iff] at hhead
          subst hhead
          rfl
      | succ j =>
          exact sequenceFin_pure_slot (fun i => computation i.succ) j x hj _ tail htail

/-- **Two of `n` keys share a parameter** with probability at most `pairBound`. -/
theorem probEvent_sequence_pair_le {n : Nat} {γ : Type} (i k : Fin n) (hik : i ≠ k)
    (rest : (Fin n → KeyPair × List HashInput) → OracleComp OracleWorld γ) (event : γ → Prop)
    (hrest : ∀ parts cache, ∀ r ∈ support (romRun (rest parts) cache), event r.1 →
      (parts i).1.1.parameter = (parts k).1.1.parameter) :
    Pr{let r ← romRun (LeanXmss.Concrete.sequenceFin (fun _ : Fin n => tracedKeygen) >>= rest) ∅}[
      event r.1] ≤ pairBound := by
  have hfirst := romRun_sequenceFin_front n (fun _ => tracedKeygen) i (fun _ parts => rest parts) ∅
  rw [← (hfirst).prEvent_eq, romRun_bind]
  have hsecond : ∀ (a : KeyPair × List HashInput) (cache : QueryCache HashSpec),
      romRun (LeanXmss.Concrete.sequenceFin (fun l : Fin n => if l = i then pure a else tracedKeygen) >>=
          rest) cache =ᵈ
        romRun (tracedKeygen >>= fun b => LeanXmss.Concrete.sequenceFin (fun l : Fin n =>
          if l = k then pure b else if l = i then pure a else tracedKeygen) >>= rest) cache := by
    intro a cache
    have h := romRun_sequenceFin_front n (fun l => if l = i then pure a else tracedKeygen) k
      (fun _ parts => rest parts) cache
    simp only [Ne.symm hik, ↓reduceIte] at h
    exact h.symm
  have hjoint : (romRun tracedKeygen ∅ >>= fun r =>
        romRun (LeanXmss.Concrete.sequenceFin (fun l : Fin n => if l = i then pure r.1 else tracedKeygen) >>=
          rest) r.2) =ᵈ
      romRun (tracedKeygen >>= fun a => tracedKeygen >>= fun b =>
        LeanXmss.Concrete.sequenceFin (fun l : Fin n =>
          if l = k then pure b else if l = i then pure a else tracedKeygen) >>= rest) ∅ := by
    rw [romRun_bind]
    exact EvalDistEq.bind_right _ fun r => hsecond r.1 r.2
  rw [hjoint.prEvent_eq]
  refine probEvent_parameter_pair_le _ event fun a b cache r hr hevent => ?_
  rw [romRun_bind, mem_support_bind_iff] at hr
  obtain ⟨parts, hparts, hr⟩ := hr
  have hk := sequenceFin_pure_slot _ k b (by simp) cache parts hparts
  have hi := sequenceFin_pure_slot _ i a (by simp [hik]) cache parts hparts
  have := hrest parts.1 parts.2 r hr hevent
  rwa [hi, hk] at this

end XmssSecurity.MultiUser
