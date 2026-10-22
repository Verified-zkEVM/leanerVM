/-
  LeanVM.E2E.Vis.PerKey.XmssLog

  W-vis, P7b: the single-key game's signing log of the per-key leanXMSS reduction is key `j`'s
  record in the reduction's state, with distinct leaves.
-/

module

public import LeanVM.E2E.Vis.PerKey.XmssFacts

/-!
# The challenger's log (W-vis, P7b)

The single-key game answers the reduction's world by passing the schemes' world through and
signing with key `j`'s secret key, logging every request (`τJ sk`). Every computation the
reduction routes logs nothing (`run_τJ_rImpl`); key `j`'s forwarded request logs exactly the
request and answer it records (`logsJ_xmssFwdJ`); the other answers leave key `j`'s record alone.
So on every run, the log is key `j`'s record, and its leaves are distinct (`logsJ_restJ`).
-/

namespace LeanVM.E2E

open LeanVM.Parameters LeanVM.Semantics LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Rom
open OracleSpec OracleComp
open scoped ENNReal

@[expose] public section

namespace PerKeyX

variable {nx ns : ℕ}

/-- **The single-key game's oracles**: the schemes' world passed through, signing requests answered
by key `j`'s signer and logged. -/
noncomputable abbrev τJ (sk : LeanXmss.Seeded.SecretKey) :
    QueryImpl RS (WriterT (QueryLog LeanXmss.SigningSpec) (OracleComp OW)) :=
  QueryImpl.ofLift OW (WriterT (QueryLog LeanXmss.SigningSpec) (OracleComp OW)) +
    LeanXmss.Security.signingOracle sk

/-- The schemes' world lifted into the reduction's and answered by the game's oracles logs
nothing. -/
theorem run_τJ_liftSig (sk : LeanXmss.Seeded.SecretKey) {α : Type} (oa : OracleComp OW α) :
    (simulateQ (τJ sk) (liftSig LeanXmss.SigningSpec oa)).run = (·, []) <$> oa := by
  unfold liftSig
  rw [← QueryImpl.simulateQ_compose]
  have h : (τJ sk ∘ₛ liftSigImpl LeanXmss.SigningSpec) =
      QueryImpl.ofLift OW (WriterT (QueryLog LeanXmss.SigningSpec) (OracleComp OW)) := by
    funext t
    rw [QueryImpl.apply_compose, liftSigImpl, simulateQ_spec_query]
    rfl
  rw [h, XmssRed.run_simulateQ_ofLift_writer]

/-- **A routed computation logs nothing.** -/
theorem run_τJ_rImpl (sk : LeanXmss.Seeded.SecretKey) (Pr : List UInt8 → Prop) [DecidablePred Pr]
    {α : Type} (oa : OracleComp OW α) (cp : QueryCache LeanXmss.HashSpec) :
    (simulateQ (τJ sk) ((simulateQ (rImpl LeanXmss.SigningSpec Pr) oa).run cp)).run =
      (·, []) <$> (simulateQ (routeImpl Pr) oa).run cp := by
  rw [run_simulateQ_rImpl, run_τJ_liftSig]

/-- Key `j`'s leaves are distinct. -/
def XInvJ (j : Fin nx) (st : SignState nx ns) : Prop := ((st.xlog j).map (·.1.1)).Nodup

/-- **Logging key `j`'s record**: from every state with distinct leaves, the game's log on every
run is what the run appends to key `j`'s record, and the leaves stay distinct. -/
def LogsJ (sk : LeanXmss.Seeded.SecretKey) (j : Fin nx) {α : Type}
    (x : StateT (SignState nx ns) RM α) : Prop :=
  ∀ (st : SignState nx ns) (cp : QueryCache LeanXmss.HashSpec), XInvJ j st →
    ∀ w ∈ support ((simulateQ (τJ sk) ((x.run st).run cp)).run),
      XInvJ j w.1.1.2 ∧ XmssRed.conv (w.1.1.2.xlog j) = XmssRed.conv (st.xlog j) ++ w.2

theorem logsJ_pure (sk : LeanXmss.Seeded.SecretKey) (j : Fin nx) {α : Type} (a : α) :
    LogsJ (ns := ns) sk j (pure a) := by
  intro st cp hst w hw
  simp only [StateT.run_pure, simulateQ_pure, WriterT.run_pure', support_pure,
    Set.mem_singleton_iff] at hw
  subst hw
  exact ⟨hst, by simp⟩

theorem logsJ_bind (sk : LeanXmss.Seeded.SecretKey) (j : Fin nx) {α β : Type}
    {x : StateT (SignState nx ns) RM α} {f : α → StateT (SignState nx ns) RM β}
    (hx : LogsJ sk j x) (hf : ∀ a, LogsJ sk j (f a)) : LogsJ sk j (x >>= f) := by
  intro st cp hst w hw
  rw [StateT.run_bind, StateT.run_bind, simulateQ_bind, WriterT.run_bind',
    mem_support_bind_iff] at hw
  obtain ⟨v, hv, hw⟩ := hw
  rw [support_map] at hw
  obtain ⟨w', hw', rfl⟩ := hw
  obtain ⟨hv1, hv2⟩ := hx st cp hst v hv
  obtain ⟨hw1, hw2⟩ := hf v.1.1.1 v.1.1.2 v.1.2 hv1 w' hw'
  exact ⟨hw1, by simp only [Prod.map, id] at hw2 ⊢; rw [hw2, hv2, List.append_assoc]⟩

/-- **A simulation by handlers that log key `j`'s records logs them.** -/
theorem logsJ_simulateQ (sk : LeanXmss.Seeded.SecretKey) (j : Fin nx) {ι : Type}
    {spec : OracleSpec.{0, 0} ι} (impl : QueryImpl spec (StateT (SignState nx ns) RM))
    (himpl : ∀ t, LogsJ sk j (impl t)) {α : Type} (oa : OracleComp spec α) :
    LogsJ sk j (simulateQ impl oa) := by
  induction oa using OracleComp.inductionOn with
  | pure a => rw [simulateQ_pure]; exact logsJ_pure sk j a
  | query_bind t k ih =>
    rw [simulateQ_query_bind]
    simp only [OracleQuery.input_query, monadLift_self]
    exact logsJ_bind sk j (himpl t) ih

/-- A routed run's outputs are the computation's. -/
theorem fst_mem_support_route (Pr : List UInt8 → Prop) [DecidablePred Pr] {α : Type} :
    ∀ (oa : OracleComp OW α) (c : QueryCache LeanXmss.HashSpec),
      ∀ z ∈ support ((simulateQ (routeImpl Pr) oa).run c), z.1 ∈ support oa := by
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro c z hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    simp
  | query_bind t k ih =>
    intro c z hz
    rw [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨r, -, hz⟩ := hz
    rw [mem_support_bind_iff]
    exact ⟨r.1, by simp, ih r.1 r.2 z hz⟩

/-- **A routed answer that keeps key `j`'s record logs nothing new.** -/
theorem logsJ_routed (sk : LeanXmss.Seeded.SecretKey) (j : Fin nx) (Pr : List UInt8 → Prop)
    [DecidablePred Pr] {α : Type} (y : SignState nx ns → OracleComp OW (α × SignState nx ns))
    (hy : ∀ st, ∀ z ∈ support (y st), z.2.xlog j = st.xlog j) :
    LogsJ sk j (StateT.mk fun st ↦ simulateQ (rImpl LeanXmss.SigningSpec Pr) (y st)) := by
  intro st cp hst w hw
  rw [StateT.run_mk, run_τJ_rImpl, support_map] at hw
  obtain ⟨z, hz, rfl⟩ := hw
  have h := hy st _ (fst_mem_support_route Pr (y st) cp z hz)
  simp only [XInvJ, h, List.append_nil] at hst ⊢
  exact ⟨hst, trivial⟩

variable [Sphincs.Params]

omit [Sphincs.Params] in
/-- **Key `j`'s forwarded request logs exactly what it records.** -/
theorem logsJ_xmssFwdJ (sk : LeanXmss.Seeded.SecretKey) (j : Fin nx) (req : XmssRequest) :
    LogsJ (ns := ns) sk j (xmssFwdJ j req) := by
  intro st cp hst w hw
  rw [run_xmssFwdJ] at hw
  by_cases h : ((st.xlog j).any fun e ↦ decide (e.1.1 = req.1)) = true
  · simp only [h, ↓reduceIte, StateT.run_pure, simulateQ_pure, WriterT.run_pure', support_pure,
      Set.mem_singleton_iff] at hw
    subst hw
    exact ⟨hst, by simp⟩
  · simp only [h, Bool.false_eq_true, ↓reduceIte, StateT.run_map, OracleComp.liftM_run_StateT,
      simulateQ_map, simulateQ_bind, simulateQ_pure, WriterT.run_map', WriterT.run_bind',
      support_map, support_bind, Set.mem_image, Set.mem_iUnion] at hw
    obtain ⟨v, ⟨u, hu, hv⟩, rfl⟩ := hw
    rw [simulateQ_spec_query] at hu
    change u ∈ support (LeanXmss.Security.signingOracle sk ⟨req.1, req.2⟩).run at hu
    rw [LeanXmss.Security.signingOracle, QueryImpl.run_withLogging_apply, mem_support_bind_iff] at hu
    obtain ⟨σ, -, hu⟩ := hu
    simp only [support_pure, Set.mem_singleton_iff] at hu
    subst hu
    simp only [WriterT.run_pure', support_pure, Set.mem_singleton_iff, exists_eq_left] at hv
    subst hv
    refine ⟨?_, ?_⟩
    · simp only [XInvJ, Prod.map, id, Function.update_self, List.map_append, List.map_cons, List.map_nil]
      refine List.nodup_append.mpr ⟨hst, List.nodup_singleton _, ?_⟩
      intro a ha b hb hab
      simp only [List.mem_singleton] at hb
      subst hb hab
      simp only [List.any_eq_true, decide_eq_true_eq, not_exists, not_and] at h
      obtain ⟨e, he, he'⟩ := List.mem_map.mp ha
      exact h e he he'
    · simp [XmssRed.conv]

/-- The adversary's coins and hash queries, translated, keep the signers' state. -/
theorem tw_advImpl_inl_inl_state (keys : Keys nx ns) (t : (unifSpec + HashSpec).Domain)
    (st : SignState nx ns) : ∀ z ∈ support (tw (advImpl keys (.inl (.inl t))) st), z.2 = st := by
  intro z hz
  rcases t with n | x
  · change z ∈ support (tw (coins ($ᵗ Fin (n + 1))) st) at hz
    rw [tw_coins, support_map] at hz
    obtain ⟨u, -, rfl⟩ := hz
    rfl
  · change z ∈ support (tw (hashQuery x) st) at hz
    rw [tw_hashQuery, support_map] at hz
    obtain ⟨u, -, rfl⟩ := hz
    rfl

/-- **The reduction's answers log key `j`'s records.** -/
theorem logsJ_advImplJ (sk : LeanXmss.Seeded.SecretKey) (pj : Bytes) (j : Fin nx)
    (keys : Keys nx ns) (t : (AdvSpec nx ns).Domain) : LogsJ sk j (advImplJ pj j keys t) := by
  rcases t with (t | ⟨i, req⟩) | ⟨i, msg⟩
  · rw [advImplJ_inl_inl]
    exact logsJ_routed sk j _ _ fun st z hz ↦ by rw [tw_advImpl_inl_inl_state keys t st z hz]
  · by_cases hij : i = j
    · subst hij
      rw [advImplJ_xmss_self]
      exact logsJ_xmssFwdJ sk i req
    · rw [advImplJ_xmss_ne _ _ _ hij]
      refine logsJ_routed sk j _ _ fun st z hz ↦ ?_
      rw [tw_xmssSign_eq] at hz
      split at hz
      · simp only [support_pure, Set.mem_singleton_iff] at hz; rw [hz]
      · rw [support_map] at hz
        obtain ⟨σ, -, rfl⟩ := hz
        simp [Function.update_of_ne (Ne.symm hij)]
  · rw [advImplJ_sphincs]
    refine logsJ_routed sk j _ _ fun st z hz ↦ ?_
    rw [tw_sphincsSign_eq] at hz
    split at hz
    · simp only [support_pure, Set.mem_singleton_iff] at hz; rw [hz]
    · rw [support_map] at hz
      obtain ⟨σ, -, rfl⟩ := hz
      rfl

/-- **No log**: a reduction computation whose game run logs nothing. -/
def NoLogJ (sk : LeanXmss.Seeded.SecretKey) {α : Type} (x : RM α) : Prop :=
  ∀ cp, ∀ w ∈ support ((simulateQ (τJ sk) (x.run cp)).run), w.2 = []

omit [Sphincs.Params] in
theorem noLogJ_pure (sk : LeanXmss.Seeded.SecretKey) {α : Type} (a : α) : NoLogJ sk (pure a : RM α) := by
  intro cp w hw
  simp only [StateT.run_pure, simulateQ_pure, WriterT.run_pure', support_pure,
    Set.mem_singleton_iff] at hw
  subst hw; rfl

omit [Sphincs.Params] in
theorem noLogJ_bind (sk : LeanXmss.Seeded.SecretKey) {α β : Type} {x : RM α} {f : α → RM β}
    (hx : NoLogJ sk x) (hf : ∀ a, NoLogJ sk (f a)) : NoLogJ sk (x >>= f) := by
  intro cp w hw
  rw [StateT.run_bind, simulateQ_bind, WriterT.run_bind', mem_support_bind_iff] at hw
  obtain ⟨v, hv, hw⟩ := hw
  rw [support_map] at hw
  obtain ⟨w', hw', rfl⟩ := hw
  simp only [Prod.map, id, hx cp v hv, hf v.1.1 v.1.2 w' hw', List.append_nil]

omit [Sphincs.Params] in
theorem noLogJ_rImpl (sk : LeanXmss.Seeded.SecretKey) (Pr : List UInt8 → Prop) [DecidablePred Pr]
    {α : Type} (oa : OracleComp OW α) :
    NoLogJ sk (simulateQ (rImpl LeanXmss.SigningSpec Pr) oa) := by
  intro cp w hw
  rw [run_τJ_rImpl, support_map] at hw
  obtain ⟨z, -, rfl⟩ := hw
  rfl

omit [Sphincs.Params] in
theorem noLogJ_sequenceFin (sk : LeanXmss.Seeded.SecretKey) {α : Type} :
    ∀ {n : ℕ} (f : Fin n → RM α), (∀ i, NoLogJ sk (f i)) →
      NoLogJ sk (LeanXmss.Concrete.sequenceFin f)
  | 0, _, _ => noLogJ_pure sk _
  | n + 1, f, h => by
    simp only [LeanXmss.Concrete.sequenceFin]
    exact noLogJ_bind sk (h 0) fun a ↦ noLogJ_bind sk
      (noLogJ_sequenceFin sk (fun i ↦ f i.succ) fun i ↦ h i.succ) fun _ ↦ noLogJ_pure sk _

omit [Sphincs.Params] in
/-- The other keys' generations log nothing. -/
theorem noLogJ_xKeygenR (sk : LeanXmss.Seeded.SecretKey) (pj : Bytes) : NoLogJ sk (xKeygenR pj) := by
  unfold xKeygenR
  exact noLogJ_bind sk (noLogJ_rImpl _ _ _) fun _ ↦ noLogJ_bind sk (noLogJ_rImpl _ _ _) fun _ ↦
    noLogJ_bind sk (noLogJ_rImpl _ _ _) fun _ ↦ noLogJ_bind sk (noLogJ_rImpl _ _ _) fun _ ↦
      noLogJ_pure sk _

theorem noLogJ_sKeygenR (sk : LeanXmss.Seeded.SecretKey) (pj : Bytes) : NoLogJ sk (sKeygenR pj) := by
  unfold sKeygenR
  exact noLogJ_bind sk (noLogJ_rImpl _ _ _) fun _ ↦ noLogJ_bind sk (noLogJ_rImpl _ _ _) fun _ ↦
    noLogJ_bind sk (noLogJ_rImpl _ _ _) fun _ ↦ noLogJ_bind sk (noLogJ_rImpl _ _ _) fun _ ↦
      noLogJ_pure sk _

/-- **The challenger's log is key `j`'s record**, with distinct leaves, on every run of the
reduction. -/
theorem xBodyJ_log (guest : Program) (fuel budget : ℕ) (A : GameAdversary nx ns)
    (sk : LeanXmss.Seeded.SecretKey) (j : Fin nx) (pkj : LeanXmss.PublicKey)
    (cp : QueryCache LeanXmss.HashSpec) :
    ∀ w ∈ support ((simulateQ (τJ sk) ((xBodyJ guest fuel budget A j pkj).run cp)).run),
      XInvJ j w.1.1.2.2.2.2 ∧ XmssRed.conv (w.1.1.2.2.2.2.xlog j) = w.2 := by
  intro w hw
  unfold xBodyJ at hw
  rw [StateT.run_bind, simulateQ_bind, WriterT.run_bind', mem_support_bind_iff] at hw
  obtain ⟨v1, hv1, hw⟩ := hw
  rw [support_map] at hw
  obtain ⟨w1, hw1, rfl⟩ := hw
  rw [StateT.run_bind, simulateQ_bind, WriterT.run_bind', mem_support_bind_iff] at hw1
  obtain ⟨v2, hv2, hw1⟩ := hw1
  rw [support_map] at hw1
  obtain ⟨w2, hw2, rfl⟩ := hw1
  have hl1 := noLogJ_sequenceFin sk _ (fun i ↦ by
    split
    · exact noLogJ_pure sk _
    · exact noLogJ_xKeygenR sk _) cp v1 hv1
  have hl2 := noLogJ_sequenceFin sk _ (fun _ ↦ noLogJ_sKeygenR sk _) _ v2 hv2
  -- the rest
  unfold restJ at hw2
  rw [StateT.run_bind, simulateQ_bind, WriterT.run_bind', mem_support_bind_iff] at hw2
  obtain ⟨v3, hv3, hw2⟩ := hw2
  rw [support_map] at hw2
  obtain ⟨w3, hw3, rfl⟩ := hw2
  have hinit : XInvJ j (SignState.init nx ns) := by simp [XInvJ, SignState.init]
  obtain ⟨hi3, hc3⟩ := logsJ_simulateQ sk j _ (logsJ_advImplJ sk _ j _) _ _ _ hinit v3 hv3
  rw [StateT.run_bind, simulateQ_bind, WriterT.run_bind', mem_support_bind_iff] at hw3
  obtain ⟨v4, hv4, hw3⟩ := hw3
  rw [support_map] at hw3
  obtain ⟨w4, hw4, rfl⟩ := hw3
  simp only [StateT.run_pure, simulateQ_pure, WriterT.run_pure', support_pure,
    Set.mem_singleton_iff] at hw4
  subst hw4
  rw [rc, run_τJ_rImpl, support_map] at hv4
  obtain ⟨z, hz, rfl⟩ := hv4
  have hfix := keepsLogs_viRec budget guest _ fuel _ _ _ (fst_mem_support_route _ _ _ z hz)
  simp only [SignState.init, XmssRed.conv, List.map_nil, List.nil_append] at hc3
  unfold XInvJ at hi3 ⊢
  simp only [Prod.map, id, hfix.1, hl1, hl2, List.nil_append]
  refine ⟨hi3, ?_⟩
  rw [show (∅ : QueryLog LeanXmss.SigningSpec) = [] from rfl, List.append_nil]
  simpa [XmssRed.conv] using hc3

end PerKeyX

end
end LeanVM.E2E
