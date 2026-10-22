/-
  LeanVM.E2E.KS.Trace

  The deployed game before verification, for the reductions: the recorded adversary's queries,
  what its transcript knows (every entry answered alike by the game's final log), the game's
  translation to the schemes' world and its hash queries.
-/

module

public import LeanVM.E2E.KS.Prefix
public import LeanVM.E2E.Reduction.Xmss

/-!
# The adversary's transcript

The per-scheme reductions of the deployed game run `pGameComp` themselves, except the honest
keys of the scheme they attack. A known forgery's signature is valid under the answers of the
adversary's own hash queries (`POutcome.trace`, recorded by `record`); the reductions check it
against the schemes' random oracle, which must answer the transcript alike.

* **Counts** (`isQueryBoundP_record`): recording keeps every query bound of the adversary.
* **What the transcript knows** (`pGame_trace`): on every reachable outcome of `pGame`, every
  entry of the transcript is answered alike by the final log (`TrSub`); so the final log's cache
  holds it (`XmssRed.CacheTr`).
* **The schemes' world** (`prEvent_pGame_eq`): an event of the outcome has, in `pGame`, the
  probability of the event and the transcript held by the cache in the translation of
  `pGameComp` run against the schemes' lazy random oracle; that translation is the leanXMSS key
  generations, the leanSPHINCS key generations, then the rest (`toW_pGameComp`, `pRest`).
* **Hash queries** (`isQueryBoundP_pGameComp`, `isQueryBoundP_pRest`): at most `preQueries`, the
  rest at most the adversary's and its requests'.
-/

namespace LeanVM.E2E.KS

open LeanVM.Parameters LeanVM.Semantics LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Rom
open LeanVM.E2E OracleSpec OracleComp
open scoped ENNReal

@[expose] public section

variable {nx ns : ℕ}

/-! ## The recorded oracles -/

/-- The recorded oracles on a hash query: the query, its input and answer appended. -/
theorem run_recordImpl_hash (x : Bytes) (tr : Log) :
    (recordImpl (nx := nx) (ns := ns) (.inl (.inl (.inr x)))).run tr =
      (liftM ((AdvSpec nx ns).query (.inl (.inl (.inr x)))) : OracleComp (AdvSpec nx ns) Digest) >>=
        fun u ↦ pure (u, tr ++ [(x, u)]) := by
  simp [recordImpl]

/-- The recorded oracles on any other query: the query forwarded, the transcript unchanged. -/
theorem run_recordImpl_of_not_hash (t : (AdvSpec nx ns).Domain) (ht : ¬ AdvHash t) (tr : Log) :
    (recordImpl t).run tr =
      (liftM ((AdvSpec nx ns).query t) : OracleComp (AdvSpec nx ns) _) >>=
        fun u ↦ pure (u, tr) := by
  rcases t with ((n | x) | q) | q
  · exact OracleComp.liftM_run_StateT _ _
  · exact absurd trivial ht
  · exact OracleComp.liftM_run_StateT _ _
  · exact OracleComp.liftM_run_StateT _ _

/-- **Recording keeps every query bound**, from every transcript. -/
theorem isQueryBoundP_record (p : (AdvSpec nx ns).Domain → Prop) [DecidablePred p] {α : Type} :
    ∀ (oa : OracleComp (AdvSpec nx ns) α) (n : ℕ), IsQueryBoundP oa p n → ∀ tr : Log,
      IsQueryBoundP ((simulateQ recordImpl oa).run tr) p n := by
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure a => intro n _ tr; simp
  | query_bind t k ih =>
    intro n h tr
    rw [isQueryBoundP_query_bind_iff] at h
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    by_cases ht : AdvHash t
    · rcases t with ((n' | x) | q) | q
      · exact absurd ht id
      · change IsQueryBoundP ((recordImpl (.inl (.inl (.inr x)))).run tr >>= _) p n
        rw [run_recordImpl_hash, bind_assoc, isQueryBoundP_query_bind_iff]
        exact ⟨h.1, fun u ↦ by simpa using ih u _ (h.2 u) _⟩
      · exact absurd ht id
      · exact absurd ht id
    · change IsQueryBoundP ((recordImpl t).run tr >>= _) p n
      rw [run_recordImpl_of_not_hash t ht, bind_assoc, isQueryBoundP_query_bind_iff]
      exact ⟨h.1, fun u ↦ by simpa using ih u _ (h.2 u) _⟩

/-- **The recorded adversary's bounds**: recording keeps `A`'s hash, leanXMSS and leanSPHINCS
bounds. -/
theorem DAdvBounds.recorded {A : DAdversary nx ns} {qH sX sS : ℕ} (hA : DAdvBounds A qH sX sS)
    (pkx : Fin nx → LeanXmss.PublicKey) (pks : Fin ns → Sphincs.PublicKey) :
    IsQueryBoundP (KS.record (A pkx pks)) AdvHash qH ∧
      IsQueryBoundP (KS.record (A pkx pks)) AdvXmss sX ∧
        IsQueryBoundP (KS.record (A pkx pks)) AdvSphincs sS :=
  ⟨isQueryBoundP_record _ _ _ (hA.hash pkx pks) [], isQueryBoundP_record _ _ _ (hA.xmss pkx pks) [],
    isQueryBoundP_record _ _ _ (hA.sphincs pkx pks) []⟩

/-! ## What the transcript knows -/

/-- **A run against the game's oracle extends the log.** -/
theorem prefix_of_mem_support_gameRun {α : Type} (oa : OracleComp GameSpec α) (ℓ : Log)
    {z : α × Log} (hz : z ∈ support ((simulateQ gameImpl oa).run ℓ)) : ℓ <+: z.2 := by
  induction oa using OracleComp.inductionOn generalizing ℓ with
  | pure x =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    rw [hz]
  | query_bind t k ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨p, hp, hz⟩ := hz
    refine List.IsPrefix.trans ?_ (ih p.1 p.2 hz)
    rcases t with n | x
    · change p ∈ support ((coinImpl n).run ℓ) at hp
      simp only [coinImpl, QueryImpl.liftTarget_apply, StateT.run_monadLift, support_bind,
        support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hp
      obtain ⟨u, -, rfl⟩ := hp
      exact List.prefix_rfl
    · exact (mem_support_gameImpl_hash hp).1

variable [Sphincs.Params]

/-- **The recorded adversary's transcript is answered by the game's log**: from a transcript the
log answers alike, every run of the recorded adversary with the game's oracles extends the log,
and its final transcript is answered alike by the final log. -/
theorem record_trace (keys : Keys nx ns) {α : Type} :
    ∀ (oa : OracleComp (AdvSpec nx ns) α) (tr : Log) (st : SignState nx ns) (ℓ : Log),
      TrSub tr (look ℓ) → ∀ p ∈ support ((simulateQ gameImpl
        ((simulateQ (advImpl keys) ((simulateQ recordImpl oa).run tr)).run st)).run ℓ),
        ℓ <+: p.2 ∧ TrSub p.1.1.2 (look p.2) := by
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro tr st ℓ htr p hp
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
    subst hp
    exact ⟨List.prefix_refl _, htr⟩
  | query_bind t k ih =>
    intro tr st ℓ htr p hp
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, simulateQ_bind] at hp
    obtain ⟨q, hq, hp⟩ := mem_support_run_bind hp
    have hfirst : ℓ <+: q.2 ∧ TrSub q.1.1.2 (look q.2) := by
      by_cases ht : AdvHash t
      · rcases t with ((n' | x) | r) | r
        · exact absurd ht id
        · change q ∈ support ((simulateQ gameImpl ((simulateQ (advImpl keys)
            ((recordImpl (.inl (.inl (.inr x)))).run tr)).run st)).run ℓ) at hq
          rw [run_recordImpl_hash, simulateQ_bind, simulateQ_spec_query] at hq
          obtain ⟨q', hq', hq⟩ := mem_support_run_bind hq
          simp only [simulateQ_pure, StateT.run_pure, support_pure,
            Set.mem_singleton_iff] at hq
          subst hq
          change q' ∈ support ((simulateQ gameImpl ((hashQuery x : GameM nx ns Digest).run
            st)).run ℓ) at hq'
          unfold hashQuery at hq'
          rw [OracleComp.liftM_run_StateT, simulateQ_bind, StateT.run_bind,
            mem_support_bind_iff] at hq'
          obtain ⟨d, hd, hq'⟩ := hq'
          change d ∈ support ((simulateQ gameImpl (liftM (GameSpec.query (.inr x)) :
            OracleComp GameSpec Digest)).run ℓ) at hd
          rw [simulateQ_spec_query] at hd
          simp only [simulateQ_pure, StateT.run_pure, support_pure,
            Set.mem_singleton_iff] at hq'
          subst hq'
          obtain ⟨hpre, hlook⟩ := mem_support_gameImpl_hash hd
          refine ⟨hpre, fun e he ↦ ?_⟩
          rcases List.mem_append.mp he with he | he
          · exact (htr.of_prefix hpre) e he
          · rw [List.mem_singleton.mp he]; exact hlook
        · exact absurd ht id
        · exact absurd ht id
      · change q ∈ support ((simulateQ gameImpl ((simulateQ (advImpl keys)
          ((recordImpl t).run tr)).run st)).run ℓ) at hq
        rw [run_recordImpl_of_not_hash t ht, simulateQ_bind, simulateQ_spec_query] at hq
        obtain ⟨q', hq', hq⟩ := mem_support_run_bind hq
        simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hq
        subst hq
        have hpre := prefix_of_mem_support_gameRun _ _ hq'
        exact ⟨hpre, htr.of_prefix hpre⟩
    obtain ⟨h1, h2⟩ := ih q.1.1.1 q.1.1.2 q.1.2 q.2 hfirst.2 p hp
    exact ⟨hfirst.1.trans h1, h2⟩

/-- **What the transcript knows.** On every reachable outcome of the deployed game before
verification, every entry of the adversary's transcript is answered alike by the final log. -/
theorem pGame_trace {A : DAdversary nx ns} {z : POutcome nx ns × Log}
    (hz : z ∈ support (pGame A)) : TrSub z.1.trace (look z.2) := by
  unfold pGame pGameComp at hz
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨⟨⟨out, st⟩, ℓ⟩, hq, hz⟩ := hz
  simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  subst hz
  obtain ⟨⟨⟨keys, st₁⟩, ℓ₁⟩, -, hq⟩ := mem_support_run_bind hq
  obtain ⟨⟨⟨⟨⟨s, π⟩, tr⟩, st₂⟩, ℓ₂⟩, hr, hq⟩ := mem_support_run_bind hq
  simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff,
    Prod.mk.injEq] at hq
  obtain ⟨⟨h₁, -⟩, h₃⟩ := hq
  subst h₁ h₃
  exact (record_trace keys _ [] st₁ ℓ₁ (fun _ h ↦ absurd h List.not_mem_nil) _ hr).2

omit [Sphincs.Params] in
/-- A transcript answered alike by a log is held by the log's cache. -/
theorem TrSub.cacheTr {tr ℓ : Log} (h : TrSub tr (look ℓ)) : XmssRed.CacheTr (logCache ℓ) tr :=
  fun e he ↦ by rw [logCache_apply, h e he]; rfl

/-! ## The schemes' world -/

/-- **An event of the outcome before verification, in the schemes' world**: its probability in
`pGame` is that of the event and the transcript held by the cache, in the translation of
`pGameComp` run against the schemes' lazy random oracle from the empty cache. -/
theorem prEvent_pGame_eq (A : DAdversary nx ns) (E : POutcome nx ns → Prop) :
    Pr{let z ← pGame A}[E z.1] =
      Pr{let o ← romRun (simulateQ toW (pGameComp A)) ∅}[
        E o.1 ∧ XmssRed.CacheTr o.2 o.1.trace] := by
  let F : POutcome nx ns × QueryCache LeanXmss.HashSpec → Prop :=
    fun o ↦ E o.1 ∧ XmssRed.CacheTr o.2 o.1.trace
  calc Pr{let z ← pGame A}[E z.1] = Pr{let z ← pGame A}[F (z.1, logCache z.2)] :=
        le_antisymm
          (prEvent_mono_of_support _ _ _ fun z hz h ↦ ⟨h, TrSub.cacheTr (pGame_trace hz)⟩)
          (prEvent_mono_of_support _ _ _ fun _ _ h ↦ h.1)
    _ = Pr{let o ← Prod.map id logCache <$> pGame A}[F o] := by
        rw [prEvent_map]; rfl
    _ = Pr{let o ← romRun (simulateQ toW (pGameComp A)) ∅}[F o] :=
        (evalDistEq_run_toW_nil _).prEvent_eq F

/-- **The rest of the deployed game before verification at the keys `keys`**, translated: the
recorded adversary with the game's oracles. -/
noncomputable def pRest (A : DAdversary nx ns) (keys : Keys nx ns) :
    OracleComp OW (POutcome nx ns) :=
  tw (simulateQ (advImpl keys)
      (KS.record (A (fun j ↦ (keys.xmss j).1) (fun j ↦ (keys.sphincs j).1))))
      (SignState.init nx ns) >>= fun q ↦
    pure ⟨keys, q.1.1.1, q.1.1.2, q.1.2, q.2⟩

/-- **The deployed game before verification, translated**: the leanXMSS keys, the leanSPHINCS
keys, then the rest. -/
theorem toW_pGameComp (A : DAdversary nx ns) :
    simulateQ toW (pGameComp A) =
      LeanXmss.Concrete.sequenceFin (fun _ : Fin nx ↦ LeanXmss.MultiUser.keygen) >>= fun mk ↦
        LeanXmss.Concrete.sequenceFin (fun _ : Fin ns ↦ sKeygen) >>= fun ss ↦
          pRest A ⟨mk, ss⟩ := by
  unfold pGameComp pRest
  rw [simulateQ_bind]
  change tw _ (SignState.init nx ns) >>= _ = _
  unfold keygen
  simp only [tw_bind, tw_xKeygen, tw_sKeygen, bind_map_left, bind_assoc, tw_pure, pure_bind,
    simulateQ_pure, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta]

/-! ## Hash queries -/

/-- **The rest makes at most the adversary's hash queries and its requests'.** -/
theorem isQueryBoundP_pRest {A : DAdversary nx ns} {qH sX sS : ℕ} (hA : DAdvBounds A qH sX sS)
    (keys : Keys nx ns) :
    IsQueryBoundP (pRest A keys) IsHashW (qH + sX * xmssSignBound + sS * sphincsSignBound) := by
  obtain ⟨hH, hX, hS⟩ := hA.recorded (fun j ↦ (keys.xmss j).1) (fun j ↦ (keys.sphincs j).1)
  unfold pRest
  refine (isQueryBoundP_bind (m := 0) (isQueryBoundP_simulateQ_toW _ _
    (costs_simulateQ_advImpl sign_isTotalQueryBound sphincsSign_isTotalQueryBound keys _ hH hX hS
      _)) fun _ _ ↦ by simp).mono (by omega)

/-- **The deployed game before verification makes at most `preQueries` hash queries.** -/
theorem isQueryBoundP_pGameComp {A : DAdversary nx ns} {qH sX sS : ℕ}
    (hA : DAdvBounds A qH sX sS) :
    IsQueryBoundP (pGameComp A) IsHash (preQueries nx ns qH sX sS) := by
  unfold pGameComp
  refine (isQueryBoundP_bind (n := nx * xmssKeygenBound + ns * sphincsKeygenBound +
    ((qH + sX * xmssSignBound + sS * sphincsSignBound) + 0)) (m := 0) ?_
    fun z _ ↦ by rcases z with ⟨out, st⟩; exact trivial).mono (by unfold preQueries; omega)
  refine costs_bind (costs_keygen keygenFromSeed_isTotalQueryBound
    sphincsKeygenFromSeed_isTotalQueryBound) (fun keys ↦ ?_) _
  obtain ⟨hH, hX, hS⟩ := hA.recorded (fun j ↦ (keys.xmss j).1) (fun j ↦ (keys.sphincs j).1)
  refine costs_bind (costs_simulateQ_advImpl sign_isTotalQueryBound sphincsSign_isTotalQueryBound
    keys _ hH hX hS) fun p ↦ ?_
  rcases p with ⟨⟨s, π⟩, tr⟩
  exact costs_pure _

end
end LeanVM.E2E.KS
-- STABLE
