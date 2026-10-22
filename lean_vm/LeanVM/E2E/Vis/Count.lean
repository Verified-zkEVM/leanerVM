/-
  LeanVM.E2E.Vis.Count

  W-vis, P2d: the counts of the visible accounting. Key generation logs only hidden inputs; the
  rest of the game (the adversary with its oracles, then V_I recorded) makes at most `qH + budget`
  non-hidden hash queries, and at most the game's count of hash queries in all.
-/

module

public import LeanVM.E2E.Vis.Shape
public import LeanVM.E2E.Vis.Engine

/-!
# Counts (W-vis, P2d)

The plan is `docs/roadmap/w-vis.md`. The game (`gameRec`) is key generation (`keygenPhase`, the
run of `keygen` from the empty log), then the rest (`restRec`), both defined in
`Vis/Engine.lean` (P1). This module proves the counts on their bodies, so the forms on
`keygenPhase` and `restRec` are one-liners.

* `VisQ keys`: a non-hidden hash query. `CostsP P c x`: `x` makes at most `c` queries of `P`,
  from every state (`Costs` of `LeanVM.E2E.Engine` is `CostsP IsHash`).
* **The rest's non-hidden queries** (`costsP_restBody_vis`): at most `qH + budget`. The
  adversary's own hash queries count one each, at most `qH`; its signing requests count nothing,
  because every query of an honest signer of key `j` is prefixed by `j`'s parameter and an
  address (the scheme walks, P2b/P2c), so is in `SchemeIn keys`; V_I's are at most `budget`.
* **The rest's hash queries** (`costs_restBody`): the adversary's, its requests' and V_I's,
  `(qH + sX · cxs + sS · css) + budget`.
* **Key generation logs only hidden inputs** (`keygen_logs_hid`): every entry key generation adds
  to the oracle's log is a derivation or prefixed by the parameter of the key it generates
  (the scheme walks), so in `Hid keys` of the final keys. The walks are stated on the logging
  run of the scheme's key generation; `logsSat_hashRun` carries them to the game's log: every
  entry the game's run of a scheme computation adds is the input of a query of the logging run
  with the same output.

The walks (P2b, P2c) are hypotheses here, in the form of `w-vis.md` §3, until they land.
-/

namespace LeanVM.E2E

open LeanVM.Parameters LeanVM.Semantics LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Rom
open OracleSpec OracleComp

@[expose] public section

variable {nx ns : ℕ}

/-! ## Counting the queries of a predicate -/

section CostsP

/-- **`x` makes at most `c` queries of `P`**, from every state. -/
def CostsP (P : GameSpec.Domain → Prop) [DecidablePred P] (c : ℕ) {α : Type}
    (x : GameM nx ns α) : Prop :=
  ∀ st, IsQueryBoundP (x.run st) P c

variable {P : GameSpec.Domain → Prop} [DecidablePred P]

/-- A count can be loosened. -/
theorem CostsP.mono {c c' : ℕ} {α : Type} {x : GameM nx ns α} (h : CostsP P c x)
    (hc : c ≤ c') : CostsP P c' x := fun st ↦ (h st).mono hc

/-- A count of hash queries counts the queries of every predicate of hash queries. -/
theorem Costs.costsP {c : ℕ} {α : Type} {x : GameM nx ns α} (h : Costs c x)
    (hP : ∀ t, P t → IsHash t) : CostsP P c x := fun st ↦ (h st).of_imp hP

/-- `pure` makes no query. -/
theorem costsP_pure {α : Type} (a : α) : CostsP P 0 (pure a : GameM nx ns α) := fun st ↦ by
  simp

/-- The counts of a sequence add. -/
theorem costsP_bind {c c' : ℕ} {α β : Type} {x : GameM nx ns α} {f : α → GameM nx ns β}
    (hx : CostsP P c x) (hf : ∀ a, CostsP P c' (f a)) : CostsP P (c + c') (x >>= f) :=
  fun st ↦ by
    rw [StateT.run_bind]
    exact isQueryBoundP_bind (hx st) fun p _ ↦ hf p.1 p.2

/-- Reading the signers' state makes no query. -/
theorem costsP_get : CostsP P 0 (get : GameM nx ns (SignState nx ns)) := fun st ↦ by
  simp

/-- Changing the signers' state makes no query. -/
theorem costsP_modify (f : SignState nx ns → SignState nx ns) :
    CostsP P 0 (modify f : GameM nx ns Unit) := fun st ↦ by
  simp

/-- A map makes the computation's queries. -/
theorem costsP_map {c : ℕ} {α β : Type} (f : α → β) {x : GameM nx ns α} (hx : CostsP P c x) :
    CostsP P c (f <$> x) := fun st ↦ by
  rw [StateT.run_map, isQueryBoundP_map_iff]
  exact hx st

/-- A hash query counts one if it is a query of `P`. -/
theorem costsP_hashQuery (x : Bytes) :
    CostsP P (if P (.inr x) then 1 else 0) (hashQuery x : GameM nx ns Digest) := fun st ↦ by
  change IsQueryBoundP ((liftM (liftM (GameSpec.query (.inr x)) : OracleComp GameSpec Digest) :
    GameM nx ns Digest).run st) P _
  rw [OracleComp.liftM_run_StateT, isQueryBoundP_query_bind_iff]
  refine ⟨?_, fun _ ↦ trivial⟩
  by_cases h : P (.inr x) <;> simp [h]

/-- **A scheme computation whose every query satisfies `q`** makes no query of `P` if `P`'s hash
queries satisfy `q`'s negation. -/
theorem costsP_simulateQ_hash_zero {R : Type} (g : Digest → R) {α : Type}
    {oa : OracleComp (Bytes →ₒ R) α} {q : Bytes → Prop} [DecidablePred q]
    (hoa : IsQueryBoundP oa (fun x ↦ ¬ q x) 0) (hq : ∀ x, P (.inr x) → ¬ q x) :
    CostsP P 0 (simulateQ (fun x ↦ g <$> hashQuery x : QueryImpl (Bytes →ₒ R) (GameM nx ns))
      oa) := fun st ↦
  IsQueryBoundP.simulateQ_run_StateT_of_step hoa (fun x s ↦ by
    refine ((costsP_map g (costsP_hashQuery (P := P) (nx := nx) (ns := ns) x)) s).mono ?_
    by_cases h : P (.inr x)
    · simp [h, hq x h]
    · simp [h]) st

end CostsP

/-! ## The visible queries -/

variable [Sphincs.Params]

/-- **A visible query**: a hash query of a non-hidden input. -/
def VisQ (keys : Keys nx ns) : GameSpec.Domain → Prop
  | .inl _ => False
  | .inr x => ¬ Hid keys x

open Classical in
/-- Visible queries are decidable, classically. -/
noncomputable instance (keys : Keys nx ns) : DecidablePred (VisQ keys) := fun _ ↦ inferInstance

/-- A visible query is a hash query. -/
theorem visQ_isHash (keys : Keys nx ns) : ∀ t : GameSpec.Domain, VisQ keys t → IsHash t
  | .inl _, h => h.elim
  | .inr _, _ => trivial

/-- The leanXMSS parameter of an honest key is an honest key's parameter. -/
theorem xmss_mem_keyParams (keys : Keys nx ns) (j : Fin nx) :
    LeanXmss.bytesLE 16 (keys.xmss j).2.parameter ∈ keyParams keys :=
  List.mem_append_left _ (List.mem_ofFn.mpr ⟨j, rfl⟩)

/-- The leanSPHINCS parameter of an honest key is an honest key's parameter. -/
theorem sphincs_mem_keyParams (keys : Keys nx ns) (j : Fin ns) :
    Sphincs.bytesLE 16 (keys.sphincs j).2.parameter ∈ keyParams keys :=
  List.mem_append_right _ (List.mem_ofFn.mpr ⟨j, rfl⟩)

section Rest

variable {keys : Keys nx ns}

open Classical in
/-- **An honest leanXMSS signature makes no visible query**, if every query of the signer is
prefixed by its key's parameter and an address (the walk `xmss_sign_queries`, P2b). -/
theorem costsP_xmssSign_vis
    (hxw : ∀ sk i msg, IsQueryBoundP (LeanXmss.Seeded.sign sk i msg :
      OracleComp LeanXmss.HashSpec _)
      (fun x ↦ ¬ ∃ a, AddrOK a ∧ LeanXmss.bytesLE 16 sk.parameter ++ a <+: x) 0)
    (j : Fin nx) (req : XmssRequest) : CostsP (VisQ keys) 0 (xmssSign keys j req) := by
  unfold xmssSign
  rw [show 0 = 0 + 0 from rfl]
  refine costsP_bind costsP_get fun st ↦ ?_
  split
  · exact costsP_pure _
  · rw [show 0 = 0 + (0 + 0) from rfl]
    refine costsP_bind ?_ fun _ ↦ costsP_bind (costsP_modify _) fun _ ↦ costsP_pure _
    exact costsP_simulateQ_hash_zero digestBits (hxw _ _ _) fun x hv hq ↦
      hv (Or.inl ⟨_, xmss_mem_keyParams keys j, hq⟩)

open Classical in
/-- **An honest leanSPHINCS signature makes no visible query** (the walk
`sphincs_sign_queries`, P2c). -/
theorem costsP_sphincsSign_vis
    (hsw : ∀ sk msg, IsQueryBoundP (Sphincs.Seeded.sign sk msg : OracleComp Sphincs.HashSpec _)
      (fun x ↦ ¬ ∃ a, AddrOK a ∧ Sphincs.bytesLE 16 sk.parameter ++ a <+: x) 0)
    (j : Fin ns) (msg : Sphincs.Message) : CostsP (VisQ keys) 0 (sphincsSign keys j msg) := by
  unfold sphincsSign
  rw [show 0 = 0 + 0 from rfl]
  refine costsP_bind costsP_get fun st ↦ ?_
  split
  · exact costsP_pure _
  · rw [show 0 = 0 + (0 + 0) from rfl]
    refine costsP_bind ?_ fun _ ↦ costsP_bind (costsP_modify _) fun _ ↦ costsP_pure _
    exact costsP_simulateQ_hash_zero digestBits (hsw _ _) fun x hv hq ↦
      hv (Or.inl ⟨_, sphincs_mem_keyParams keys j, hq⟩)

open Classical in
/-- **The adversary's visible queries in the game**: at most its own hash queries. -/
theorem costsP_simulateQ_advImpl_vis
    (hxw : ∀ sk i msg, IsQueryBoundP (LeanXmss.Seeded.sign sk i msg :
      OracleComp LeanXmss.HashSpec _)
      (fun x ↦ ¬ ∃ a, AddrOK a ∧ LeanXmss.bytesLE 16 sk.parameter ++ a <+: x) 0)
    (hsw : ∀ sk msg, IsQueryBoundP (Sphincs.Seeded.sign sk msg : OracleComp Sphincs.HashSpec _)
      (fun x ↦ ¬ ∃ a, AddrOK a ∧ Sphincs.bytesLE 16 sk.parameter ++ a <+: x) 0)
    {α : Type} (oa : OracleComp (AdvSpec nx ns) α) {qH : ℕ} (hH : IsQueryBoundP oa AdvHash qH) :
    CostsP (VisQ keys) qH (simulateQ (advImpl keys) oa) := fun st ↦
  IsQueryBoundP.simulateQ_run_StateT_of_step hH (fun t s ↦ by
    rcases t with ((n | x) | ⟨j, req⟩) | ⟨j, msg⟩
    · exact (((costs_coins _).costsP (P := VisQ keys) (visQ_isHash keys)) s).mono (Nat.zero_le _)
    · refine ((costsP_hashQuery (P := VisQ keys) x) s).mono ?_
      simp only [AdvHash, ↓reduceIte]
      split <;> omega
    · exact ((costsP_xmssSign_vis hxw j req) s).mono (Nat.zero_le _)
    · exact ((costsP_sphincsSign_vis hsw j msg) s).mono (Nat.zero_le _)) st

end Rest

omit [Sphincs.Params] in
/-- **V_I's recorded run makes at most the budget of hash queries.** -/
theorem costs_viRec (budget : ℕ) (guest : Program) (ip : IdealProof) (fuel : ℕ)
    (s : NodeStatement) : Costs budget (viRec (nx := nx) (ns := ns) budget guest ip fuel s) :=
  fun st ↦ by
    have h := isQueryBoundP_idealVerify budget guest ip fuel s st
    rw [← viRec_map, StateT.run_map, isQueryBoundP_map_iff] at h
    exact h.mono (Nat.sub_le _ _)

/-- **The rest of the game**, in the game's monad: the adversary with its oracles, then V_I
recorded (the body of `restRec`, `Vis/Engine.lean`). -/
noncomputable abbrev restBody (guest : Program) (fuel budget : ℕ) (A : GameAdversary nx ns)
    (keys : Keys nx ns) :
    GameM nx ns (Keys nx ns × NodeStatement × IdealProof × Option (Bool × Log)) := do
  let (s, ip) ← simulateQ (advImpl keys)
    (A (fun j ↦ (keys.xmss j).1) (fun j ↦ (keys.sphincs j).1))
  let o ← viRec budget guest ip fuel s
  pure (keys, s, ip, o)

open Classical in
/-- **The rest's visible queries: at most `qH + budget`.** The adversary's own hash queries, at
most `qH`; none of its signing requests' (the walks); V_I's, at most `budget`. -/
theorem costsP_restBody_vis
    (hxw : ∀ sk i msg, IsQueryBoundP (LeanXmss.Seeded.sign sk i msg :
      OracleComp LeanXmss.HashSpec _)
      (fun x ↦ ¬ ∃ a, AddrOK a ∧ LeanXmss.bytesLE 16 sk.parameter ++ a <+: x) 0)
    (hsw : ∀ sk msg, IsQueryBoundP (Sphincs.Seeded.sign sk msg : OracleComp Sphincs.HashSpec _)
      (fun x ↦ ¬ ∃ a, AddrOK a ∧ Sphincs.bytesLE 16 sk.parameter ++ a <+: x) 0)
    (guest : Program) (fuel budget : ℕ) (A : GameAdversary nx ns) {qH : ℕ}
    (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH) (keys : Keys nx ns) :
    CostsP (VisQ keys) (qH + budget) (restBody guest fuel budget A keys) := by
  rw [show qH + budget = qH + (budget + 0) by omega]
  refine costsP_bind (costsP_simulateQ_advImpl_vis hxw hsw _ (hH _ _)) fun p ↦ ?_
  rcases p with ⟨s, ip⟩
  exact costsP_bind ((costs_viRec budget guest ip fuel s).costsP (visQ_isHash keys))
    fun _ ↦ costsP_pure _

/-- **The rest's hash queries**: the adversary's, its requests' and V_I's. -/
theorem costs_restBody {cxs css : ℕ}
    (hxs : ∀ sk i msg, IsTotalQueryBound
      (LeanXmss.Seeded.sign sk i msg : OracleComp LeanXmss.HashSpec _) cxs)
    (hss : ∀ sk msg, IsTotalQueryBound
      (Sphincs.Seeded.sign sk msg : OracleComp Sphincs.HashSpec _) css)
    (guest : Program) (fuel budget : ℕ) (A : GameAdversary nx ns) {qH sX sS : ℕ}
    (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH)
    (hX : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvXmss sX)
    (hS : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvSphincs sS) (keys : Keys nx ns) :
    Costs ((qH + sX * cxs + sS * css) + budget) (restBody guest fuel budget A keys) := by
  rw [show (qH + sX * cxs + sS * css) + budget = (qH + sX * cxs + sS * css) + (budget + 0) by
    omega]
  refine costs_bind (costs_simulateQ_advImpl hxs hss keys _ (hH _ _) (hX _ _) (hS _ _))
    fun p ↦ ?_
  rcases p with ⟨s, ip⟩
  exact costs_bind (costs_viRec budget guest ip fuel s) fun _ ↦ costs_pure _

/-! ## The entries key generation logs -/

section Logs

omit [Sphincs.Params]

/-- **Every entry `x` adds to the oracle's log satisfies `Q` at `x`'s output**, from every
signers' state and log. -/
def LogsSat {α : Type} (Q : α → Bytes → Prop) (x : GameM nx ns α) : Prop :=
  ∀ (st : SignState nx ns) (ℓ : Log) (p : (α × SignState nx ns) × Log),
    p ∈ support ((simulateQ gameImpl (x.run st)).run ℓ) →
      ∃ new : Log, p.2 = ℓ ++ new ∧ ∀ e ∈ new, Q p.1.1 e.1

/-- **Every output of `x` satisfies `R`**, from every signers' state and log. -/
def OutSat {α : Type} (R : α → Prop) (x : GameM nx ns α) : Prop :=
  ∀ (st : SignState nx ns) (ℓ : Log) (p : (α × SignState nx ns) × Log),
    p ∈ support ((simulateQ gameImpl (x.run st)).run ℓ) → R p.1.1

/-- A point of the run of a bind comes from a point of the first part's run. -/
theorem exists_mem_support_run_bind {α β : Type} {x : GameM nx ns α} {f : α → GameM nx ns β}
    {st : SignState nx ns} {ℓ : Log} {p : (β × SignState nx ns) × Log}
    (hp : p ∈ support ((simulateQ gameImpl ((x >>= f).run st)).run ℓ)) :
    ∃ q ∈ support ((simulateQ gameImpl (x.run st)).run ℓ),
      p ∈ support ((simulateQ gameImpl ((f q.1.1).run q.1.2)).run q.2) := by
  simpa only [StateT.run_bind, simulateQ_bind, mem_support_bind_iff] using hp

/-- `pure` logs nothing. -/
theorem logsSat_pure {α : Type} (Q : α → Bytes → Prop) (a : α) :
    LogsSat Q (pure a : GameM nx ns α) := by
  intro st ℓ p hp
  simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hp
  subst hp
  exact ⟨[], by simp, fun _ h ↦ absurd h List.not_mem_nil⟩

/-- `pure`'s output. -/
theorem outSat_pure {α : Type} {R : α → Prop} {a : α} (h : R a) :
    OutSat R (pure a : GameM nx ns α) := by
  intro st ℓ p hp
  simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hp
  subst hp
  exact h

/-- A bind's outputs are its continuation's. -/
theorem outSat_bind {α β : Type} {R : β → Prop} {x : GameM nx ns α} {f : α → GameM nx ns β}
    (hf : ∀ a, OutSat R (f a)) : OutSat R (x >>= f) := by
  intro st ℓ p hp
  obtain ⟨q, -, hp⟩ := exists_mem_support_run_bind hp
  exact hf _ _ _ _ hp

/-- **A bind's entries**: the first part's satisfy `Q1` at its output, which every output of the
continuation carries over to `Q`. -/
theorem logsSat_bind {α β : Type} {Q1 : α → Bytes → Prop} {Q : β → Bytes → Prop}
    {x : GameM nx ns α} {f : α → GameM nx ns β} (hx : LogsSat Q1 x)
    (hf : ∀ a, LogsSat Q (f a)) (hlink : ∀ a, OutSat (fun b ↦ ∀ y, Q1 a y → Q b y) (f a)) :
    LogsSat Q (x >>= f) := by
  intro st ℓ p hp
  obtain ⟨q, hq, hp⟩ := exists_mem_support_run_bind hp
  obtain ⟨n1, h1, hQ1⟩ := hx _ _ _ hq
  obtain ⟨n2, h2, hQ⟩ := hf _ _ _ _ hp
  have hl := hlink _ _ _ _ hp
  refine ⟨n1 ++ n2, by rw [h2, h1, List.append_assoc], fun e he ↦ ?_⟩
  rcases List.mem_append.mp he with he | he
  · exact hl _ (hQ1 e he)
  · exact hQ e he

/-- A map's entries. -/
theorem logsSat_of_map {α β : Type} {Q : β → Bytes → Prop} (g : α → β) {x : GameM nx ns α}
    (h : LogsSat Q (g <$> x)) : LogsSat (fun a ↦ Q (g a)) x := by
  intro st ℓ p hp
  refine h st ℓ ((g p.1.1, p.1.2), p.2) ?_
  rw [StateT.run_map, simulateQ_map, StateT.run_map, support_map]
  exact ⟨p, hp, rfl⟩

/-- **A `mapM`'s entries** satisfy `Q` at one of its outputs. -/
theorem logsSat_list_mapM {α β : Type} {Q : β → Bytes → Prop} {f : α → GameM nx ns β}
    (hf : ∀ a, LogsSat Q (f a)) :
    ∀ l : List α, LogsSat (fun bs y ↦ ∃ b ∈ bs, Q b y) (l.mapM f)
  | [] => by
    rw [List.mapM_nil]
    exact logsSat_pure _ _
  | a :: l => by
    rw [List.mapM_cons]
    refine logsSat_bind (hf a) (fun b ↦ ?_) (fun b ↦ ?_)
    · exact logsSat_bind (logsSat_list_mapM hf l) (fun bs ↦ logsSat_pure _ _)
        fun bs ↦ outSat_pure fun y ⟨b', hb', hq⟩ ↦ ⟨b', List.mem_cons_of_mem _ hb', hq⟩
    · exact outSat_bind fun bs ↦ outSat_pure fun y hq ↦ ⟨b, List.mem_cons_self, hq⟩

/-- **A vector `mapM`'s entries** satisfy `Q` at one of its outputs. -/
theorem logsSat_vector_mapM {α β : Type} {n : ℕ} {Q : β → Bytes → Prop}
    {f : α → GameM nx ns β} (hf : ∀ a, LogsSat Q (f a)) (v : Vector α n) :
    LogsSat (fun (w : Vector β n) y ↦ ∃ b ∈ w.toList, Q b y) (v.mapM f) := by
  refine logsSat_of_map (Q := fun bs y ↦ ∃ b ∈ bs, Q b y) Vector.toList ?_
  rw [Vector.toList_mapM]
  exact logsSat_list_mapM hf _

/-- Coins log nothing. -/
theorem logsSat_coins {α : Type} (Q : α → Bytes → Prop) (c : ProbComp α) :
    LogsSat Q (coins c : GameM nx ns α) := by
  intro st ℓ p hp
  refine ⟨[], ?_, fun _ h ↦ absurd h List.not_mem_nil⟩
  rw [List.append_nil]
  change p ∈ support ((simulateQ gameImpl ((liftM (liftM c : OracleComp GameSpec α) :
    GameM nx ns α).run st)).run ℓ) at hp
  rw [OracleComp.liftM_run_StateT, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hp
  obtain ⟨q, hq, hp⟩ := hp
  simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
  subst hp
  clear Q
  induction c using OracleComp.inductionOn generalizing ℓ with
  | pure a =>
    simp only [liftM_pure, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hq
    subst hq
    rfl
  | query_bind t mx ih =>
    rw [liftM_bind] at hq
    change q ∈ support ((simulateQ gameImpl (liftM (GameSpec.query (.inl t)) >>=
      fun a ↦ liftM (mx a))).run ℓ) at hq
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hq
    obtain ⟨r, hr', hq⟩ := hq
    rw [gameImpl_isLazySampler (.inl t) ℓ] at hr'
    simp only [gameLookup, gameRecord, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at hr'
    obtain ⟨u, -, rfl⟩ := hr'
    exact ih u ℓ hq

/-- **A hash query's run**: the signers' state kept, the log kept or extended by the query and
its answer. -/
theorem mem_support_run_hashQuery {x : Bytes} {st : SignState nx ns} {ℓ : Log}
    {q : (Digest × SignState nx ns) × Log}
    (hq : q ∈ support ((simulateQ gameImpl ((hashQuery x : GameM nx ns Digest).run st)).run ℓ)) :
    q.1.2 = st ∧ (q.2 = ℓ ∨ q.2 = ℓ ++ [(x, q.1.1)]) := by
  change q ∈ support ((simulateQ gameImpl ((liftM (liftM (GameSpec.query (.inr x)) :
    OracleComp GameSpec Digest) : GameM nx ns Digest).run st)).run ℓ) at hq
  rw [OracleComp.liftM_run_StateT, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
    mem_support_bind_iff] at hq
  obtain ⟨r, hr', hq⟩ := hq
  simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hq
  subst hq
  rw [gameImpl_isLazySampler (.inr x) ℓ] at hr'
  simp only [gameLookup, gameRecord] at hr'
  refine ⟨rfl, ?_⟩
  rcases h : look ℓ x with _ | u
  · rw [h] at hr'
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr'
    obtain ⟨u, -, rfl⟩ := hr'
    exact Or.inr rfl
  · rw [h] at hr'
    simp only [support_pure, Set.mem_singleton_iff] at hr'
    subst hr'
    exact Or.inl rfl

/-- **The game's run of a scheme computation, against the logging run**: every entry it adds
to the oracle's log is the input of a query of a logging run of the computation with the same
output. -/
theorem logsSat_hashRun {R : Type} (g : Digest → R) {β : Type} (oa : OracleComp (Bytes →ₒ R) β) :
    ∀ (st : SignState nx ns) (ℓ : Log) (p : (β × SignState nx ns) × Log),
      p ∈ support ((simulateQ gameImpl ((simulateQ (fun x ↦ g <$> hashQuery x :
        QueryImpl (Bytes →ₒ R) (GameM nx ns)) oa).run st)).run ℓ) →
      ∃ z ∈ support ((simulateQ (QueryImpl.ofLift (Bytes →ₒ R)
          (OracleComp (Bytes →ₒ R))).withLogging oa).run),
        z.1 = p.1.1 ∧ ∃ new : Log, p.2 = ℓ ++ new ∧ ∀ e ∈ new, e.1 ∈ z.2.map (·.1) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro st ℓ p hp
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
    subst hp
    refine ⟨(a, []), by simp, rfl, [], by simp, fun _ h ↦ absurd h List.not_mem_nil⟩
  | query_bind x mx ih =>
    intro st ℓ p hp
    rw [simulateQ_query_bind] at hp
    simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq] at hp
    change p ∈ support ((simulateQ gameImpl (((g <$> hashQuery x : GameM nx ns R) >>= fun u ↦
      simulateQ _ (mx u)).run st)).run ℓ) at hp
    rw [map_eq_pure_bind, bind_assoc] at hp
    obtain ⟨q, hq, hp⟩ := exists_mem_support_run_bind hp
    simp only [pure_bind] at hp
    obtain ⟨hst, hl⟩ := mem_support_run_hashQuery hq
    rw [hst] at hp
    obtain ⟨z, hz, hz1, new, hnew, hQ⟩ := ih (g q.1.1) st q.2 p hp
    refine ⟨(z.1, ⟨x, g q.1.1⟩ :: z.2), ?_, hz1, ?_⟩
    · rw [simulateQ_bind, simulateQ_spec_query, WriterT.run_bind,
        QueryImpl.run_withLogging_apply, QueryImpl.ofLift_apply, bind_assoc]
      simp only [pure_bind, mem_support_bind_iff, support_map, Set.mem_image]
      exact ⟨g q.1.1, by simp, z, hz, rfl⟩
    · rcases hl with hl | hl
      · exact ⟨new, by rw [hnew, hl], fun e he ↦ List.mem_cons_of_mem _ (hQ e he)⟩
      · refine ⟨(x, q.1.1) :: new, by rw [hnew, hl]; simp, fun e he ↦ ?_⟩
        rcases List.mem_cons.mp he with rfl | he
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hQ e he)

end Logs

/-! ## Key generation logs only hidden inputs -/

section Keygen

omit [Sphincs.Params] in
open Classical in
/-- **A leanXMSS key generation's entries** are derivations or prefixed by the generated key's
parameter and an address, if its logging run's queries are (the walk `xmss_keygen_queries`,
P2b). -/
theorem logsSat_xmssKeygen
    (hxk : ∀ seed, ∀ z ∈ support ((simulateQ (QueryImpl.ofLift LeanXmss.HashSpec
        (OracleComp LeanXmss.HashSpec)).withLogging (LeanXmss.Seeded.keygenFromSeed seed)).run),
      ∀ x ∈ z.2.map (·.1),
        DerivShape x ∨ ∃ a, AddrOK a ∧ LeanXmss.bytesLE 16 z.1.2.parameter ++ a <+: x)
    (seed : LeanXmss.MasterSeed) :
    LogsSat (fun b y ↦ DerivShape y ∨ ∃ a, AddrOK a ∧ LeanXmss.bytesLE 16 b.2.parameter ++ a <+: y)
      (xmssRun (LeanXmss.Seeded.keygenFromSeed seed) : GameM nx ns _) := by
  intro st ℓ p hp
  obtain ⟨z, hz, hz1, new, hnew, hQ⟩ := logsSat_hashRun digestBits _ st ℓ p hp
  refine ⟨new, hnew, fun e he ↦ ?_⟩
  rw [← hz1]
  exact hxk seed z hz e.1 (hQ e he)

open Classical in
/-- **A leanSPHINCS key generation's entries** (the walk `sphincs_keygen_queries`, P2c). -/
theorem logsSat_sphincsKeygen
    (hsk : ∀ seed, ∀ z ∈ support ((simulateQ (QueryImpl.ofLift Sphincs.HashSpec
        (OracleComp Sphincs.HashSpec)).withLogging (Sphincs.Seeded.keygenFromSeed seed)).run),
      ∀ x ∈ z.2.map (·.1),
        DerivShape x ∨ ∃ a, AddrOK a ∧ Sphincs.bytesLE 16 z.1.2.parameter ++ a <+: x)
    (seed : Sphincs.MasterSeed) :
    LogsSat (fun b y ↦ DerivShape y ∨ ∃ a, AddrOK a ∧ Sphincs.bytesLE 16 b.2.parameter ++ a <+: y)
      (sphincsRun (Sphincs.Seeded.keygenFromSeed seed) : GameM nx ns _) := by
  intro st ℓ p hp
  obtain ⟨z, hz, hz1, new, hnew, hQ⟩ := logsSat_hashRun digestBits _ st ℓ p hp
  refine ⟨new, hnew, fun e he ↦ ?_⟩
  rw [← hz1]
  exact hsk seed z hz e.1 (hQ e he)

omit [Sphincs.Params] in
/-- An entry of a vector's list is an entry of the vector. -/
theorem exists_getElem_of_mem_toList {β : Type} {n : ℕ} {w : Vector β n} {b : β}
    (hb : b ∈ w.toList) : ∃ j : Fin n, w[j] = b := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
  rw [Vector.length_toList] at hi
  exact ⟨⟨i, hi⟩, by simp⟩

open Classical in
/-- **Key generation logs only hidden inputs**: every entry it adds is in `Hid` of the keys it
generates. -/
theorem logsSat_keygen
    (hxk : ∀ seed, ∀ z ∈ support ((simulateQ (QueryImpl.ofLift LeanXmss.HashSpec
        (OracleComp LeanXmss.HashSpec)).withLogging (LeanXmss.Seeded.keygenFromSeed seed)).run),
      ∀ x ∈ z.2.map (·.1),
        DerivShape x ∨ ∃ a, AddrOK a ∧ LeanXmss.bytesLE 16 z.1.2.parameter ++ a <+: x)
    (hsk : ∀ seed, ∀ z ∈ support ((simulateQ (QueryImpl.ofLift Sphincs.HashSpec
        (OracleComp Sphincs.HashSpec)).withLogging (Sphincs.Seeded.keygenFromSeed seed)).run),
      ∀ x ∈ z.2.map (·.1),
        DerivShape x ∨ ∃ a, AddrOK a ∧ Sphincs.bytesLE 16 z.1.2.parameter ++ a <+: x) :
    LogsSat (fun keys y ↦ Hid keys y) (keygen : GameM nx ns (Keys nx ns)) := by
  unfold keygen
  refine logsSat_bind (logsSat_vector_mapM (fun _ ↦ logsSat_bind
      (logsSat_coins (fun _ _ ↦ False) _) (fun seed ↦ logsSat_xmssKeygen hxk seed)
      fun _ _ _ _ _ _ h ↦ h.elim) _) (fun xs ↦ ?_) (fun xs ↦ ?_)
  · refine logsSat_bind (logsSat_vector_mapM (fun _ ↦ logsSat_bind
        (logsSat_coins (fun _ _ ↦ False) _) (fun seed ↦ logsSat_sphincsKeygen hsk seed)
        fun _ _ _ _ _ _ h ↦ h.elim) _) (fun ss ↦ logsSat_pure _ _) (fun ss ↦ outSat_pure ?_)
    rintro y ⟨b, hb, hq | hq⟩
    · exact Or.inr hq
    · obtain ⟨j, rfl⟩ := exists_getElem_of_mem_toList hb
      exact Or.inl ⟨_, sphincs_mem_keyParams ⟨fun j ↦ xs[j], fun j ↦ ss[j]⟩ j, hq⟩
  · refine outSat_bind fun ss ↦ outSat_pure ?_
    rintro y ⟨b, hb, hq | hq⟩
    · exact Or.inr hq
    · obtain ⟨j, rfl⟩ := exists_getElem_of_mem_toList hb
      exact Or.inl ⟨_, xmss_mem_keyParams ⟨fun j ↦ xs[j], fun j ↦ ss[j]⟩ j, hq⟩

open Classical in
/-- **The key-generation phase's log is hidden** (`keygenPhase_hid` on the body of
`keygenPhase`, `Vis/Engine.lean`): every entry of the log key generation reaches from the empty
log is in `Hid` of the generated keys. -/
theorem keygenRun_hid
    (hxk : ∀ seed, ∀ z ∈ support ((simulateQ (QueryImpl.ofLift LeanXmss.HashSpec
        (OracleComp LeanXmss.HashSpec)).withLogging (LeanXmss.Seeded.keygenFromSeed seed)).run),
      ∀ x ∈ z.2.map (·.1),
        DerivShape x ∨ ∃ a, AddrOK a ∧ LeanXmss.bytesLE 16 z.1.2.parameter ++ a <+: x)
    (hsk : ∀ seed, ∀ z ∈ support ((simulateQ (QueryImpl.ofLift Sphincs.HashSpec
        (OracleComp Sphincs.HashSpec)).withLogging (Sphincs.Seeded.keygenFromSeed seed)).run),
      ∀ x ∈ z.2.map (·.1),
        DerivShape x ∨ ∃ a, AddrOK a ∧ Sphincs.bytesLE 16 z.1.2.parameter ++ a <+: x) :
    ∀ k ∈ support ((simulateQ gameImpl ((keygen : GameM nx ns (Keys nx ns)).run
      (SignState.init nx ns))).run []), ∀ e ∈ k.2, Hid k.1.1 e.1 := by
  intro k hk e he
  obtain ⟨new, hnew, hQ⟩ := logsSat_keygen hxk hsk _ _ _ hk
  rw [hnew, List.nil_append] at he
  exact hQ e he

end Keygen

/-! ## The forms on the game's phases (`Vis/Engine.lean`) -/

section Phases

open Classical in
/-- **The key-generation phase logs only hidden inputs.** -/
theorem keygenPhase_hid
    (hxk : ∀ seed, ∀ z ∈ support ((simulateQ (QueryImpl.ofLift LeanXmss.HashSpec
        (OracleComp LeanXmss.HashSpec)).withLogging (LeanXmss.Seeded.keygenFromSeed seed)).run),
      ∀ x ∈ z.2.map (·.1),
        DerivShape x ∨ ∃ a, AddrOK a ∧ LeanXmss.bytesLE 16 z.1.2.parameter ++ a <+: x)
    (hsk : ∀ seed, ∀ z ∈ support ((simulateQ (QueryImpl.ofLift Sphincs.HashSpec
        (OracleComp Sphincs.HashSpec)).withLogging (Sphincs.Seeded.keygenFromSeed seed)).run),
      ∀ x ∈ z.2.map (·.1),
        DerivShape x ∨ ∃ a, AddrOK a ∧ Sphincs.bytesLE 16 z.1.2.parameter ++ a <+: x) :
    ∀ k ∈ support (keygenPhase (nx := nx) (ns := ns)), ∀ e ∈ k.2, Hid k.1.1 e.1 :=
  keygenRun_hid hxk hsk

open Classical in
/-- **The rest's visible queries: at most `qH + budget`.** -/
theorem isQueryBoundP_restRec_vis
    (hxw : ∀ sk i msg, IsQueryBoundP (LeanXmss.Seeded.sign sk i msg :
      OracleComp LeanXmss.HashSpec _)
      (fun x ↦ ¬ ∃ a, AddrOK a ∧ LeanXmss.bytesLE 16 sk.parameter ++ a <+: x) 0)
    (hsw : ∀ sk msg, IsQueryBoundP (Sphincs.Seeded.sign sk msg : OracleComp Sphincs.HashSpec _)
      (fun x ↦ ¬ ∃ a, AddrOK a ∧ Sphincs.bytesLE 16 sk.parameter ++ a <+: x) 0)
    {guest : Program} {fuel budget : ℕ} {A : GameAdversary nx ns} {qH : ℕ}
    (keys : Keys nx ns) (st : SignState nx ns)
    (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH) :
    IsQueryBoundP (restRec guest fuel budget A keys st) (VisQ keys) (qH + budget) := by
  unfold restRec
  rw [show qH + budget = (qH + budget) + 0 from rfl]
  exact isQueryBoundP_bind (costsP_restBody_vis hxw hsw guest fuel budget A hH keys st)
    fun _ _ ↦ trivial

/-- **The rest's hash queries**: the adversary's, its requests' and V_I's. -/
theorem isQueryBoundP_restRec {cxs css : ℕ}
    (hxs : ∀ sk i msg, IsTotalQueryBound
      (LeanXmss.Seeded.sign sk i msg : OracleComp LeanXmss.HashSpec _) cxs)
    (hss : ∀ sk msg, IsTotalQueryBound
      (Sphincs.Seeded.sign sk msg : OracleComp Sphincs.HashSpec _) css)
    (guest : Program) (fuel budget : ℕ) (A : GameAdversary nx ns) {qH sX sS : ℕ}
    (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH)
    (hX : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvXmss sX)
    (hS : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvSphincs sS)
    (keys : Keys nx ns) (st : SignState nx ns) :
    IsQueryBoundP (restRec guest fuel budget A keys st) IsHash
      ((qH + sX * cxs + sS * css) + budget) := by
  unfold restRec
  rw [show (qH + sX * cxs + sS * css) + budget = ((qH + sX * cxs + sS * css) + budget) + 0
    from rfl]
  exact isQueryBoundP_bind (costs_restBody hxs hss guest fuel budget A hH hX hS keys st)
    fun _ _ ↦ trivial

end Phases

end
end LeanVM.E2E
