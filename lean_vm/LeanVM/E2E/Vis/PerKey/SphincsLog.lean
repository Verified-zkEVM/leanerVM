/-
  LeanVM.E2E.Vis.PerKey.SphincsLog

  W-vis, P7b: the single-key game's signing log of the per-key leanSPHINCS reduction is key `j`'s
  record in the reduction's state, within the signature limit.
-/

module

public import LeanVM.E2E.Vis.PerKey.SphincsFacts
public import LeanVM.E2E.Vis.PerKey.XmssLog

/-!
# The challenger's log (W-vis, P7b, leanSPHINCS)

The leanSPHINCS counterpart of `Vis/PerKey/XmssLog.lean`. The single-key game answers the
reduction's world by passing the schemes' world through and signing with key `j`'s secret key,
logging every request (`τJS sk`, with `Sphincs.Security.Det.signingOracleDet`). Every computation
the reduction routes logs nothing (`run_τJS_rImpl`); key `j`'s forwarded request logs exactly the
request and answer it records (`logsJS_sphincsFwdJ`); the other answers leave key `j`'s record
alone. So on every run, the log is key `j`'s record (`convS`), and the record is within
`signatureLimit` (`sBodyJ_log`).
-/

namespace LeanVM.E2E

open LeanVM.Parameters LeanVM.Semantics LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Rom
open OracleSpec OracleComp
open scoped ENNReal

@[expose] public section

namespace PerKeyS

open PerKeyX (fst_mem_support_route tw_advImpl_inl_inl_state)

variable {nx ns : ℕ} [Sphincs.Params]

/-- The single-key game's signing oracle, its world the schemes'. -/
noncomputable def sigOWJ (sk : Sphincs.Seeded.SecretKey) :
    QueryImpl Sphincs.SigningSpec (WriterT (QueryLog Sphincs.SigningSpec) (OracleComp OW)) :=
  Sphincs.Security.Det.signingOracleDet sk

/-- **The single-key game's oracles**: the schemes' world passed through, signing requests answered
by key `j`'s signer and logged. -/
noncomputable abbrev τJS (sk : Sphincs.Seeded.SecretKey) :
    QueryImpl RSs (WriterT (QueryLog Sphincs.SigningSpec) (OracleComp OW)) :=
  QueryImpl.ofLift OW (WriterT (QueryLog Sphincs.SigningSpec) (OracleComp OW)) + sigOWJ sk

/-- A record of requests and answers, as the single-key game's log. -/
def convS (l : List (Sphincs.Message × Option Sphincs.Signature)) : QueryLog Sphincs.SigningSpec :=
  l.map fun e ↦ ⟨e.1, e.2⟩

/-- The schemes' world lifted into the reduction's and answered by the game's oracles logs
nothing. -/
theorem run_τJS_liftSig (sk : Sphincs.Seeded.SecretKey) {α : Type} (oa : OracleComp OW α) :
    (simulateQ (τJS sk) (liftSig Sphincs.SigningSpec oa)).run = (·, []) <$> oa := by
  unfold liftSig
  rw [← QueryImpl.simulateQ_compose]
  have h : (τJS sk ∘ₛ liftSigImpl Sphincs.SigningSpec) =
      QueryImpl.ofLift OW (WriterT (QueryLog Sphincs.SigningSpec) (OracleComp OW)) := by
    funext t
    rw [QueryImpl.apply_compose, liftSigImpl, simulateQ_spec_query]
    rfl
  rw [h, XmssRed.run_simulateQ_ofLift_writer]

/-- **A routed computation logs nothing.** -/
theorem run_τJS_rImpl (sk : Sphincs.Seeded.SecretKey) (Pr : List UInt8 → Prop) [DecidablePred Pr]
    {α : Type} (oa : OracleComp OW α) (cp : QueryCache LeanXmss.HashSpec) :
    (simulateQ (τJS sk) ((simulateQ (rImpl Sphincs.SigningSpec Pr) oa).run cp)).run =
      (·, []) <$> (simulateQ (routeImpl Pr) oa).run cp := by
  rw [run_simulateQ_rImpl, run_τJS_liftSig]

/-- Key `j`'s record is within the signature limit. -/
def SInvJ (j : Fin ns) (st : SignState nx ns) : Prop :=
  (st.slog j).length ≤ Sphincs.signatureLimit

/-- **Logging key `j`'s record**: from every state within the limit, the game's log on every run is
what the run appends to key `j`'s record, and the record stays within the limit. -/
def LogsJS (sk : Sphincs.Seeded.SecretKey) (j : Fin ns) {α : Type}
    (x : StateT (SignState nx ns) RMs α) : Prop :=
  ∀ (st : SignState nx ns) (cp : QueryCache LeanXmss.HashSpec), SInvJ j st →
    ∀ w ∈ support ((simulateQ (τJS sk) ((x.run st).run cp)).run),
      SInvJ j w.1.1.2 ∧ convS (w.1.1.2.slog j) = convS (st.slog j) ++ w.2

theorem logsJS_pure (sk : Sphincs.Seeded.SecretKey) (j : Fin ns) {α : Type} (a : α) :
    LogsJS (nx := nx) sk j (pure a) := by
  intro st cp hst w hw
  simp only [StateT.run_pure, simulateQ_pure, WriterT.run_pure', support_pure,
    Set.mem_singleton_iff] at hw
  subst hw
  exact ⟨hst, by simp⟩

theorem logsJS_bind (sk : Sphincs.Seeded.SecretKey) (j : Fin ns) {α β : Type}
    {x : StateT (SignState nx ns) RMs α} {f : α → StateT (SignState nx ns) RMs β}
    (hx : LogsJS sk j x) (hf : ∀ a, LogsJS sk j (f a)) : LogsJS sk j (x >>= f) := by
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
theorem logsJS_simulateQ (sk : Sphincs.Seeded.SecretKey) (j : Fin ns) {ι : Type}
    {spec : OracleSpec.{0, 0} ι} (impl : QueryImpl spec (StateT (SignState nx ns) RMs))
    (himpl : ∀ t, LogsJS sk j (impl t)) {α : Type} (oa : OracleComp spec α) :
    LogsJS sk j (simulateQ impl oa) := by
  induction oa using OracleComp.inductionOn with
  | pure a => rw [simulateQ_pure]; exact logsJS_pure sk j a
  | query_bind t k ih =>
    rw [simulateQ_query_bind]
    simp only [OracleQuery.input_query, monadLift_self]
    exact logsJS_bind sk j (himpl t) ih

/-- **A routed answer that keeps key `j`'s record logs nothing new.** -/
theorem logsJS_routed (sk : Sphincs.Seeded.SecretKey) (j : Fin ns) (Pr : List UInt8 → Prop)
    [DecidablePred Pr] {α : Type} (y : SignState nx ns → OracleComp OW (α × SignState nx ns))
    (hy : ∀ st, ∀ z ∈ support (y st), z.2.slog j = st.slog j) :
    LogsJS sk j (StateT.mk fun st ↦ simulateQ (rImpl Sphincs.SigningSpec Pr) (y st)) := by
  intro st cp hst w hw
  rw [StateT.run_mk, run_τJS_rImpl, support_map] at hw
  obtain ⟨z, hz, rfl⟩ := hw
  have h := hy st _ (fst_mem_support_route Pr (y st) cp z hz)
  simp only [SInvJ, h, List.append_nil] at hst ⊢
  exact ⟨hst, trivial⟩

/-- The game's signing oracle logs its request and answer. -/
theorem mem_support_signingOracleDet {sk : Sphincs.Seeded.SecretKey} {msg : Sphincs.Message}
    {u : Option Sphincs.Signature × QueryLog Sphincs.SigningSpec}
    (h : u ∈ support (Sphincs.Security.Det.signingOracleDet sk msg).run) : u.2 = [⟨msg, u.1⟩] := by
  rw [Sphincs.Security.Det.signingOracleDet, QueryImpl.run_withLogging_apply,
    mem_support_bind_iff] at h
  obtain ⟨σ, -, h⟩ := h
  simp only [support_pure, Set.mem_singleton_iff] at h
  subst h
  rfl

/-- **Key `j`'s forwarded request logs exactly what it records.** -/
theorem logsJS_sphincsFwdJ (sk : Sphincs.Seeded.SecretKey) (j : Fin ns) (msg : Sphincs.Message) :
    LogsJS (nx := nx) sk j (sphincsFwdJ j msg) := by
  intro st cp hst w hw
  rw [run_sphincsFwdJ] at hw
  by_cases h : Sphincs.signatureLimit ≤ (st.slog j).length
  · simp only [h, ↓reduceIte, StateT.run_pure, simulateQ_pure, WriterT.run_pure', support_pure,
      Set.mem_singleton_iff] at hw
    subst hw
    exact ⟨hst, by simp⟩
  · simp only [h, ↓reduceIte, StateT.run_map, OracleComp.liftM_run_StateT,
      simulateQ_map, simulateQ_bind, simulateQ_pure, WriterT.run_map', WriterT.run_bind',
      support_map, support_bind, Set.mem_image, Set.mem_iUnion] at hw
    obtain ⟨v, ⟨u, hu, hv⟩, rfl⟩ := hw
    rw [simulateQ_spec_query] at hu
    change u ∈ support (sigOWJ sk msg).run at hu
    have hu2 := mem_support_signingOracleDet (sk := sk) hu
    simp only [WriterT.run_pure', support_pure, Set.mem_singleton_iff] at hv
    obtain ⟨x, rfl, rfl⟩ := hv
    refine ⟨?_, ?_⟩
    · simp only [SInvJ, Prod.map, id, Function.update_self, List.length_append,
        List.length_singleton]
      omega
    · simp [convS, hu2]

/-- **The reduction's answers log key `j`'s records.** -/
theorem logsJS_advImplJS (sk : Sphincs.Seeded.SecretKey) (pj : Bytes) (j : Fin ns)
    (keys : Keys nx ns) (t : (AdvSpec nx ns).Domain) : LogsJS sk j (advImplJS pj j keys t) := by
  rcases t with (t | ⟨i, req⟩) | ⟨i, msg⟩
  · rw [advImplJS_inl_inl]
    exact logsJS_routed sk j _ _ fun st z hz ↦ by rw [tw_advImpl_inl_inl_state keys t st z hz]
  · rw [advImplJS_xmss]
    exact logsJS_routed sk j _ _ fun st z hz ↦ by rw [slog_tw_xmssSign keys i req st z hz]
  · by_cases hij : i = j
    · subst hij
      rw [advImplJS_sphincs_self]
      exact logsJS_sphincsFwdJ sk i msg
    · rw [advImplJS_sphincs_ne _ _ _ hij]
      refine logsJS_routed sk j _ _ fun st z hz ↦ ?_
      rw [tw_sphincsSign_eq] at hz
      split at hz
      · simp only [support_pure, Set.mem_singleton_iff] at hz; rw [hz]
      · rw [support_map] at hz
        obtain ⟨σ, -, rfl⟩ := hz
        simp [Function.update_of_ne (Ne.symm hij)]

/-- **No log**: a reduction computation whose game run logs nothing. -/
def NoLogJS (sk : Sphincs.Seeded.SecretKey) {α : Type} (x : RMs α) : Prop :=
  ∀ cp, ∀ w ∈ support ((simulateQ (τJS sk) (x.run cp)).run), w.2 = []

theorem noLogJS_pure (sk : Sphincs.Seeded.SecretKey) {α : Type} (a : α) :
    NoLogJS sk (pure a : RMs α) := by
  intro cp w hw
  simp only [StateT.run_pure, simulateQ_pure, WriterT.run_pure', support_pure,
    Set.mem_singleton_iff] at hw
  subst hw; rfl

theorem noLogJS_bind (sk : Sphincs.Seeded.SecretKey) {α β : Type} {x : RMs α} {f : α → RMs β}
    (hx : NoLogJS sk x) (hf : ∀ a, NoLogJS sk (f a)) : NoLogJS sk (x >>= f) := by
  intro cp w hw
  rw [StateT.run_bind, simulateQ_bind, WriterT.run_bind', mem_support_bind_iff] at hw
  obtain ⟨v, hv, hw⟩ := hw
  rw [support_map] at hw
  obtain ⟨w', hw', rfl⟩ := hw
  simp only [Prod.map, id, hx cp v hv, hf v.1.1 v.1.2 w' hw', List.append_nil]

theorem noLogJS_rImpl (sk : Sphincs.Seeded.SecretKey) (Pr : List UInt8 → Prop) [DecidablePred Pr]
    {α : Type} (oa : OracleComp OW α) :
    NoLogJS sk (simulateQ (rImpl Sphincs.SigningSpec Pr) oa) := by
  intro cp w hw
  rw [run_τJS_rImpl, support_map] at hw
  obtain ⟨z, -, rfl⟩ := hw
  rfl

theorem noLogJS_sequenceFin (sk : Sphincs.Seeded.SecretKey) {α : Type} :
    ∀ {n : ℕ} (f : Fin n → RMs α), (∀ i, NoLogJS sk (f i)) →
      NoLogJS sk (LeanXmss.Concrete.sequenceFin f)
  | 0, _, _ => noLogJS_pure sk _
  | n + 1, f, h => by
    simp only [LeanXmss.Concrete.sequenceFin]
    exact noLogJS_bind sk (h 0) fun a ↦ noLogJS_bind sk
      (noLogJS_sequenceFin sk (fun i ↦ f i.succ) fun i ↦ h i.succ) fun _ ↦ noLogJS_pure sk _

/-- The other keys' generations log nothing. -/
theorem noLogJS_xKeygenRS (sk : Sphincs.Seeded.SecretKey) (pj : Bytes) :
    NoLogJS sk (xKeygenRS pj) := by
  unfold xKeygenRS
  exact noLogJS_bind sk (noLogJS_rImpl _ _ _) fun _ ↦ noLogJS_bind sk (noLogJS_rImpl _ _ _) fun _ ↦
    noLogJS_bind sk (noLogJS_rImpl _ _ _) fun _ ↦ noLogJS_bind sk (noLogJS_rImpl _ _ _) fun _ ↦
      noLogJS_pure sk _

theorem noLogJS_sKeygenRS (sk : Sphincs.Seeded.SecretKey) (pj : Bytes) :
    NoLogJS sk (sKeygenRS pj) := by
  unfold sKeygenRS
  exact noLogJS_bind sk (noLogJS_rImpl _ _ _) fun _ ↦ noLogJS_bind sk (noLogJS_rImpl _ _ _) fun _ ↦
    noLogJS_bind sk (noLogJS_rImpl _ _ _) fun _ ↦ noLogJS_bind sk (noLogJS_rImpl _ _ _) fun _ ↦
      noLogJS_pure sk _

/-- **The challenger's log is key `j`'s record**, within the signature limit, on every run of the
reduction. -/
theorem sBodyJ_log (guest : Program) (fuel budget : ℕ) (A : GameAdversary nx ns)
    (sk : Sphincs.Seeded.SecretKey) (j : Fin ns) (pkj : Sphincs.PublicKey)
    (cp : QueryCache LeanXmss.HashSpec) :
    ∀ w ∈ support ((simulateQ (τJS sk) ((sBodyJ guest fuel budget A j pkj).run cp)).run),
      SInvJ j w.1.1.2.2.2.2 ∧ convS (w.1.1.2.2.2.2.slog j) = w.2 := by
  intro w hw
  unfold sBodyJ at hw
  rw [StateT.run_bind, simulateQ_bind, WriterT.run_bind', mem_support_bind_iff] at hw
  obtain ⟨v1, hv1, hw⟩ := hw
  rw [support_map] at hw
  obtain ⟨w1, hw1, rfl⟩ := hw
  rw [StateT.run_bind, simulateQ_bind, WriterT.run_bind', mem_support_bind_iff] at hw1
  obtain ⟨v2, hv2, hw1⟩ := hw1
  rw [support_map] at hw1
  obtain ⟨w2, hw2, rfl⟩ := hw1
  have hl1 := noLogJS_sequenceFin sk _ (fun _ ↦ noLogJS_xKeygenRS sk _) cp v1 hv1
  have hl2 := noLogJS_sequenceFin sk _ (fun i ↦ by
    split
    · exact noLogJS_pure sk _
    · exact noLogJS_sKeygenRS sk _) _ v2 hv2
  -- the rest
  unfold restJS at hw2
  rw [StateT.run_bind, simulateQ_bind, WriterT.run_bind', mem_support_bind_iff] at hw2
  obtain ⟨v3, hv3, hw2⟩ := hw2
  rw [support_map] at hw2
  obtain ⟨w3, hw3, rfl⟩ := hw2
  have hinit : SInvJ j (SignState.init nx ns) := by simp [SInvJ, SignState.init]
  obtain ⟨hi3, hc3⟩ := logsJS_simulateQ sk j _ (logsJS_advImplJS sk _ j _) _ _ _ hinit v3 hv3
  rw [StateT.run_bind, simulateQ_bind, WriterT.run_bind', mem_support_bind_iff] at hw3
  obtain ⟨v4, hv4, hw3⟩ := hw3
  rw [support_map] at hw3
  obtain ⟨w4, hw4, rfl⟩ := hw3
  simp only [StateT.run_pure, simulateQ_pure, WriterT.run_pure', support_pure,
    Set.mem_singleton_iff] at hw4
  subst hw4
  rw [rcS, run_τJS_rImpl, support_map] at hv4
  obtain ⟨z, hz, rfl⟩ := hv4
  have hfix := keepsLogs_viRec budget guest _ fuel _ _ _ (fst_mem_support_route _ _ _ z hz)
  simp only [SignState.init, convS, List.map_nil, List.nil_append] at hc3
  unfold SInvJ at hi3 ⊢
  simp only [Prod.map, id, hfix.2, hl1, hl2, List.nil_append]
  refine ⟨hi3, ?_⟩
  rw [show (∅ : QueryLog Sphincs.SigningSpec) = [] from rfl, List.append_nil]
  simpa [convS] using hc3

end PerKeyS

end
end LeanVM.E2E
