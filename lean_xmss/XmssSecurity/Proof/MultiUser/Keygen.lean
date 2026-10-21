import XmssSecurity.Proof.MultiUser.Count

/-!
# Key generation's trace

Every run of key generation calls the hash at least `2^16` times on inputs starting with the
parameter it outputs, one leaf hash per leaf of the top tree (`own_count_le`), and exactly
`keygenQueries` times in all (`length_trace_keygen`).
-/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.MultiUser

open Seeded

set_option backward.isDefEq.respectTransparency false

/-- The calls of a hash computation satisfying `p`: at least `m` along every run, from every cache. -/
def LowerTrace (p : HashInput → Prop) [DecidablePred p] {α : Type}
    (computation : OracleComp HashSpec α) (m : Nat) : Prop :=
  ∀ cache, ∀ r ∈ support (romRun (traceHashes (liftM computation : OracleComp OracleWorld α)) cache),
    m ≤ r.1.2.countP fun input => decide (p input)

variable {p : HashInput → Prop} [DecidablePred p]

theorem LowerTrace.zero {α : Type} (computation : OracleComp HashSpec α) :
    LowerTrace p computation 0 := fun _ _ _ => Nat.zero_le _

theorem LowerTrace.bind {α β : Type} {computation : OracleComp HashSpec α}
    {next : α → OracleComp HashSpec β} {m m' : Nat} (hfirst : LowerTrace p computation m)
    (hnext : ∀ a, LowerTrace p (next a) m') : LowerTrace p (computation >>= next) (m + m') := by
  intro cache r hr
  rw [liftM_bind, traceHashes_bind, romRun_bind, mem_support_bind_iff] at hr
  obtain ⟨first, hfirst', hrest⟩ := hr
  rw [romRun_bind, mem_support_bind_iff] at hrest
  obtain ⟨second, hsecond, hfinal⟩ := hrest
  simp only [romRun, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hfinal
  subst hfinal
  rw [List.countP_append]
  exact Nat.add_le_add (hfirst cache first hfirst') (hnext first.1.1 first.2 second hsecond)

theorem LowerTrace.mono {α : Type} {computation : OracleComp HashSpec α} {m m' : Nat}
    (h : LowerTrace p computation m) (hle : m' ≤ m) : LowerTrace p computation m' :=
  fun cache r hr => hle.trans (h cache r hr)

theorem LowerTrace.query {x : HashInput} (hx : p x) :
    LowerTrace p (liftM (HashSpec.query x) : OracleComp HashSpec HashOutput) 1 := by
  intro cache r hr
  rw [← bind_pure (liftM (HashSpec.query x) : OracleComp HashSpec HashOutput)] at hr
  rw [liftM_bind] at hr
  change r ∈ support (romRun (traceHashes (liftM (OracleWorld.query (.inr x)) >>= _)) cache) at hr
  rw [traceHashes_query_bind, romRun_query_bind, mem_support_bind_iff] at hr
  obtain ⟨answer, _, hrest⟩ := hr
  simp only [liftM_pure, traceHashes_pure, pure_bind, romRun, simulateQ_pure, StateT.run_pure,
    support_pure, Set.mem_singleton_iff] at hrest
  subst hrest
  simp [prependHash, hx]

theorem LowerTrace.map {α β : Type} {computation : OracleComp HashSpec α} {m : Nat}
    (h : LowerTrace p computation m) (f : α → β) : LowerTrace p (f <$> computation) m := by
  rw [map_eq_bind_pure_comp]
  have h' := h.bind (next := pure ∘ f) (m' := 0) fun a => LowerTrace.zero _
  rwa [Nat.add_zero] at h'

theorem lowerTrace_tweakableHash (parameter : PublicParameter) (domain : LeanXmss.HashDomain)
    (payload : HashInput) :
    LowerTrace (IsParameterHashInput parameter)
      (LeanXmss.Concrete.tweakableHash parameter domain payload : OracleComp LeanXmss.HashSpec LeanXmss.Digest) 1 := by
  unfold LeanXmss.Concrete.tweakableHash
  have hq := LowerTrace.query (p := IsParameterHashInput parameter)
    (x := LeanXmss.tweakableHashInput parameter domain payload) (by
      unfold IsParameterHashInput LeanXmss.tweakableHashInput
      simp only [List.append_assoc]
      exact List.prefix_append _ _)
  exact hq.map LeanXmss.truncateHash

/-- At least one call per leaf of a tree, each starting with the parameter. -/
theorem lowerTrace_treeNode (parameter : PublicParameter) (lay : LeanXmss.Layer) (seed : MasterSeed) :
    ∀ level node, LowerTrace (IsParameterHashInput parameter)
      (LeanXmss.Seeded.treeNode parameter lay seed level node : OracleComp LeanXmss.HashSpec LeanXmss.Digest)
      (2 ^ level)
  | 0, node => by
      rw [LeanXmss.Seeded.treeNode]
      unfold LeanXmss.Concrete.leafHash
      simpa using (LowerTrace.zero _).bind fun endpoints => lowerTrace_tweakableHash parameter _ _
  | level + 1, node => by
      rw [LeanXmss.Seeded.treeNode]
      refine LowerTrace.mono (m := 2 ^ level + (2 ^ level + 0)) ?_ (by rw [pow_succ]; omega)
      exact (lowerTrace_treeNode parameter lay seed level (2 * node)).bind fun _ =>
        (lowerTrace_treeNode parameter lay seed level (2 * node + 1)).bind fun _ => LowerTrace.zero _

theorem mem_support_traced_bind {α β : Type} (computation : OracleComp OracleWorld α)
    (next : α → OracleComp OracleWorld β) (cache : QueryCache HashSpec)
    (r : (β × List HashInput) × QueryCache HashSpec)
    (hr : r ∈ support (romRun (traceHashes (computation >>= next)) cache)) :
    ∃ a ∈ support (romRun (traceHashes computation) cache),
      ∃ b ∈ support (romRun (traceHashes (next a.1.1)) a.2), r = ((b.1.1, a.1.2 ++ b.1.2), b.2) := by
  rw [traceHashes_bind, romRun_bind, mem_support_bind_iff] at hr
  obtain ⟨a, ha, hrest⟩ := hr
  rw [romRun_bind, mem_support_bind_iff] at hrest
  obtain ⟨b, hb, hfinal⟩ := hrest
  simp only [romRun, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hfinal
  exact ⟨a, ha, b, hb, hfinal⟩

theorem mem_support_traced_lift_prob {α : Type} (computation : ProbComp α) (cache : QueryCache HashSpec)
    (r : (α × List HashInput) × QueryCache HashSpec)
    (hr : r ∈ support (romRun (traceHashes (liftM computation : OracleComp OracleWorld α)) cache)) :
    r.1.2 = [] ∧ r.2 = cache := by
  rw [traceHashes_lift_prob, romRun, simulateQ_map, StateT.run_map, support_map] at hr
  obtain ⟨s, hs, rfl⟩ := hr
  have h : simulateQ romImpl (liftM computation : OracleComp OracleWorld α) =
      simulateQ (unifFwdImpl HashSpec) computation :=
    QueryImpl.simulateQ_add_liftM_left _ _ computation
  rw [h, unifFwdImpl.simulateQ_run, support_map] at hs
  obtain ⟨v, _, rfl⟩ := hs
  exact ⟨rfl, rfl⟩

-- Keep elaboration from unfolding the seed's uniform draw and key generation's literal tree.
attribute [local irreducible] LeanXmss.sampleMasterSeed LeanXmss.Seeded.keygenFromSeed Bridge.realKeygen
  LeanXmss.Seeded.treeNode

/-- **Key generation's own calls**: at least `2^16` start with the parameter it outputs. -/
theorem own_count_le (cache : QueryCache HashSpec) (r : (KeyPair × List HashInput) × QueryCache HashSpec)
    (hr : r ∈ support (romRun tracedKeygen cache)) :
    2 ^ 16 ≤ r.1.2.countP fun input => decide (IsParameterHashInput r.1.1.1.parameter input) := by
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_support_traced_bind _ _ cache r hr
  rw [(mem_support_traced_lift_prob _ _ a ha).1, List.nil_append]
  rw [(mem_support_traced_lift_prob _ _ a ha).2] at hb
  have hkey : (liftM (show OracleComp HashSpec KeyPair from LeanXmss.Seeded.keygenFromSeed a.1.1) :
        OracleComp OracleWorld KeyPair) =
      (liftM (show OracleComp HashSpec MasterSeed from
        LeanXmss.schemeSeed (m := OracleComp LeanXmss.HashSpec) a.1.1) :
        OracleComp OracleWorld MasterSeed) >>= fun seed =>
        (liftM (show OracleComp HashSpec LeanXmss.Digest from
          LeanXmss.deriveKey (m := OracleComp LeanXmss.HashSpec) 0 .parameter seed) :
          OracleComp OracleWorld LeanXmss.Digest) >>= fun parameter =>
          (liftM (show OracleComp HashSpec LeanXmss.Digest from
            LeanXmss.Seeded.treeNode (m := OracleComp LeanXmss.HashSpec) parameter LeanXmss.topLayer
              seed LeanXmss.layerHeight 0) : OracleComp OracleWorld LeanXmss.Digest) >>=
            fun root => pure (⟨root, parameter⟩, ⟨seed, parameter, root⟩) := by
    rw [Bridge.keygenFromSeed_eq, liftM_bind]
    unfold Bridge.realKeygen
    simp only [liftM_bind, liftM_pure]
  change b ∈ support (romRun (traceHashes (liftM (show OracleComp HashSpec KeyPair from
    LeanXmss.Seeded.keygenFromSeed a.1.1) : OracleComp OracleWorld KeyPair)) cache) at hb
  rw [hkey] at hb
  obtain ⟨c, _, d, hd, rfl⟩ := mem_support_traced_bind _ _ cache b hb
  obtain ⟨e, _, f, hf, rfl⟩ := mem_support_traced_bind _ _ c.2 d hd
  obtain ⟨g, hg, h, hh, rfl⟩ := mem_support_traced_bind _ _ e.2 f hf
  simp only [traceHashes_pure, romRun, simulateQ_pure, StateT.run_pure, support_pure,
    Set.mem_singleton_iff] at hh
  subst hh
  have htree := lowerTrace_treeNode e.1.1 LeanXmss.topLayer c.1.1 LeanXmss.layerHeight 0 e.2 g hg
  simp only [List.countP_append, List.append_nil]
  exact htree.trans (by omega)

end XmssSecurity.MultiUser
