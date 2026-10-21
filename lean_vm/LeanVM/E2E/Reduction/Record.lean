/-
  LeanVM.E2E.Reduction.Record

  V_I run with a record of its queries: the game with V_I's trace, its marginal the game, and
  what the trace knows: every entry is answered by the game's final log, and V_I accepts with
  the trace's answers.
-/

module

public import LeanVM.E2E.Reduction.World

/-!
# V_I's trace

The per-key reductions of T5 run the whole game themselves, except the honest keys of the scheme
they attack, whose key generations and signatures the schemes' games make with queries the
reduction does not see. A forged claim's signature must come from the reduction's view: T4 at a
sub-log (`aggregate_knowledge_sub`) gives it valid under the answers of V_I's own queries. So
V_I runs with a record of its queries (`recQuery`: the budgeted hash, then the query and its
answer appended to a trace), in the game (`gameCompRec`, `gameRec`) and in the reductions.

* **The marginal** (`viRec_map`, `gameCompRec_map`, `gameRec_map`): forgetting the trace gives
  V_I's run, the game's computation and the game.
* **What the trace knows** (`gameRec_trace`): on every reachable outcome, every entry of the
  trace is answered alike by the game's final log (`TrSub`), and if V_I accepted, its `Option`
  run by the trace's lookup accepts too. Both are a relation closed under `pure` and `bind`
  (`RecRel`), V_I's two runs related by `rel_idealVerify`.
-/

namespace LeanVM.E2E

open LeanVM.Parameters LeanVM.Semantics LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Rom
open OracleSpec OracleComp
open scoped ENNReal

@[expose] public section

variable {nx ns : ℕ}

/-! ## The recorded query and V_I's recorded run -/

/-- **V_I's recorded hash**: the budgeted query, its input and answer appended to the trace. -/
def recQuery (budget : ℕ) (x : Bytes) : StateT Log (OptionT (GameM nx ns)) Digest := do
  let d ← (liftM (budgetedQuery budget x : OptionT (GameM nx ns) Digest) :
    StateT Log (OptionT (GameM nx ns)) Digest)
  modify (· ++ [(x, d)])
  pure d

/-- **V_I's recorded run**: V_I with the recorded hash from the empty trace; its verdict and
trace, `none` past the budget. -/
noncomputable def viRec (budget : ℕ) (guest : Program) (ip : IdealProof) (fuel : ℕ)
    (s : NodeStatement) : GameM nx ns (Option (Bool × Log)) :=
  ((idealVerify (recQuery budget) guest ip fuel s).run []).run

/-- The recorded query's run: the budgeted query's, its answer recorded. -/
theorem run_recQuery (budget : ℕ) (x : Bytes) (tr : Log) :
    (((recQuery budget x : StateT Log (OptionT (GameM nx ns)) Digest).run tr).run) =
      (Option.map fun d ↦ (d, tr ++ [(x, d)])) <$> (budgetedQuery budget x).run := by
  unfold recQuery
  simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, OptionT.run_bind, Option.elimM,
    liftM, monadLift, MonadLift.monadLift, StateT.run_lift, OptionT.run_bind, map_eq_bind_pure_comp]
  rw [bind_assoc]
  refine bind_congr fun o ↦ ?_
  rcases o with _ | d <;> simp [OptionT.run_pure]

/-- The projection relation: forgetting the trace of the first run gives the second. -/
def ProjRel {α : Type} (x : StateT Log (OptionT (GameM nx ns)) α) (x' : OptionT (GameM nx ns) α) :
    Prop :=
  ∀ tr, (Option.map Prod.fst) <$> (x.run tr).run = x'.run

/-- `ProjRel` holds of `pure`. -/
theorem projRel_pure {α : Type} (a : α) :
    ProjRel (pure a : StateT Log (OptionT (GameM nx ns)) α) (pure a) := by
  intro tr; simp

/-- `ProjRel` is closed under `bind`. -/
theorem projRel_bind {α β : Type} (x : StateT Log (OptionT (GameM nx ns)) α)
    (x' : OptionT (GameM nx ns) α) (f : α → StateT Log (OptionT (GameM nx ns)) β)
    (f' : α → OptionT (GameM nx ns) β) (hx : ProjRel x x') (hf : ∀ a, ProjRel (f a) (f' a)) :
    ProjRel (x >>= f) (x' >>= f') := by
  intro tr
  rw [StateT.run_bind, OptionT.run_bind, OptionT.run_bind, Option.elimM, Option.elimM, ← hx tr,
    map_bind, bind_map_left]
  refine bind_congr fun o ↦ ?_
  rcases o with _ | ⟨a, tr'⟩
  · simp
  · simpa using hf a tr'

/-- `ProjRel` holds of the recorded query and the budgeted query. -/
theorem projRel_recQuery (budget : ℕ) (x : Bytes) :
    ProjRel (recQuery (nx := nx) (ns := ns) budget x) (budgetedQuery budget x) := by
  intro tr
  rw [run_recQuery, Functor.map_map]
  conv_rhs => rw [← id_map (budgetedQuery budget x).run]
  congr 1
  funext o
  rcases o <;> rfl

/-- **Forgetting V_I's trace gives V_I's run.** -/
theorem viRec_map (budget : ℕ) (guest : Program) (ip : IdealProof) (fuel : ℕ) (s : NodeStatement) :
    (Option.map Prod.fst) <$> (viRec (nx := nx) (ns := ns) budget guest ip fuel s) =
      (idealVerify (budgetedQuery budget) guest ip fuel s).run :=
  rel_idealVerify (fun x x' ↦ ProjRel x x') projRel_pure projRel_bind _ _
    (projRel_recQuery budget) guest ip fuel s []

/-! ## What the trace knows -/

/-- **Every entry of the trace `tr` is answered alike by `H`.** -/
def TrSub (tr : Log) (H : Bytes → Option Digest) : Prop := ∀ e ∈ tr, H e.1 = some e.2

/-- A trace answered by a log is answered by every extension of it. -/
theorem TrSub.of_prefix {tr ℓ ℓ' : Log} (h : TrSub tr (look ℓ)) (hp : ℓ <+: ℓ') :
    TrSub tr (look ℓ') := fun e he ↦ look_of_prefix hp (h e he)

/-- A sub-trace of an answered trace is answered. -/
theorem TrSub.of_sublist {tr tr' : Log} {H : Bytes → Option Digest} (h : TrSub tr' H)
    (hs : tr <+: tr') : TrSub tr H := fun e he ↦ h e (hs.subset he)

/-- A trace answered by `H` has its lookup extended by `H`. -/
theorem TrSub.lookSub {tr : Log} {H : Bytes → Option Digest} (h : TrSub tr H) :
    LookSub (look tr) H := by
  intro x d hx
  obtain ⟨i, hi, hei, -⟩ := (look_eq_some_iff tr x d).mp hx
  have := h tr[i] (List.getElem_mem hi)
  rwa [hei] at this

/-- A trace answered by some lookup answers itself. -/
theorem TrSub.self {tr : Log} {H : Bytes → Option Digest} (h : TrSub tr H) : TrSub tr (look tr) := by
  intro e he
  obtain ⟨d, hd⟩ := Option.ne_none_iff_exists'.mp (look_ne_none_of_mem he)
  have h1 := h.lookSub e.1 d hd
  rw [h e he, Option.some.injEq] at h1
  rw [hd, h1]

/-- A budgeted query's run against the game's oracle extends the log, which answers it. -/
theorem mem_support_runG_budgetedQuery {budget : ℕ} {x : Bytes} {st : SignState nx ns} {ℓ : Log}
    {p : (Option Digest × SignState nx ns) × Log}
    (hp : p ∈ support (runG (budgetedQuery budget x) st ℓ)) :
    ℓ <+: p.2 ∧ ∀ d, p.1.1 = some d → look p.2 x = some d := by
  unfold runG at hp
  by_cases hb : budget ≤ st.spent
  · rw [run_budgetedQuery_of_le hb] at hp
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
    subst hp
    exact ⟨List.prefix_refl _, fun _ h ↦ absurd h (by simp)⟩
  · rw [run_budgetedQuery_of_lt hb, simulateQ_map, StateT.run_map, simulateQ_spec_query,
      support_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    obtain ⟨hpre, hlook⟩ := mem_support_gameImpl_hash hq
    exact ⟨hpre, fun d hd ↦ by simp only [Option.some.injEq] at hd; exact hd ▸ hlook⟩

/-- **The recorded relation** at the lookup `L`: from a trace answered by the log, every run of
`x` against the game's oracle extends the log, and a result `some (a, tr')` extends the trace,
answered by the final log; if `L` answers the final trace alike, the `Option` run `x'` returns
`some a`. -/
def RecRel (L : Bytes → Option Digest) {α : Type} (x : StateT Log (OptionT (GameM nx ns)) α)
    (x' : Option α) : Prop :=
  ∀ (tr : Log) (st : SignState nx ns) (ℓ : Log), TrSub tr (look ℓ) →
    ∀ p ∈ support (runG (x.run tr) st ℓ), ℓ <+: p.2 ∧ ∀ a tr', p.1.1 = some (a, tr') →
      tr <+: tr' ∧ TrSub tr' (look p.2) ∧ (TrSub tr' L → x' = some a)

/-- `RecRel` holds of `pure`. -/
theorem recRel_pure (L : Bytes → Option Digest) {α : Type} (a : α) :
    RecRel (nx := nx) (ns := ns) L (pure a) (pure a) := by
  intro tr st ℓ htr p hp
  rw [StateT.run_pure, runG_pure, support_pure, Set.mem_singleton_iff] at hp
  subst hp
  refine ⟨List.prefix_refl _, fun a' tr' h ↦ ?_⟩
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨List.prefix_refl _, htr, fun _ ↦ rfl⟩

/-- `RecRel` is closed under `bind`. -/
theorem recRel_bind (L : Bytes → Option Digest) {α β : Type} (x : StateT Log (OptionT (GameM nx ns)) α)
    (x' : Option α) (f : α → StateT Log (OptionT (GameM nx ns)) β) (f' : α → Option β)
    (hx : RecRel L x x') (hf : ∀ a, RecRel L (f a) (f' a)) : RecRel L (x >>= f) (x' >>= f') := by
  intro tr st ℓ htr p hp
  rw [StateT.run_bind] at hp
  obtain ⟨q, hq, hpq⟩ := mem_support_runG_bind hp
  obtain ⟨hℓq, hxq⟩ := hx tr st ℓ htr q hq
  rcases hpq with ⟨-, rfl⟩ | ⟨⟨a, trq⟩, ha, hp'⟩
  · exact ⟨hℓq, fun _ _ h ↦ absurd h (by simp)⟩
  · obtain ⟨htrq, hsubq, hxq'⟩ := hxq a trq ha
    obtain ⟨hqp, hfp⟩ := hf a trq q.1.2 q.2 hsubq p hp'
    refine ⟨hℓq.trans hqp, fun b tr' hb ↦ ?_⟩
    obtain ⟨htr', hsub', hf'⟩ := hfp b tr' hb
    refine ⟨htrq.trans htr', hsub', fun hL ↦ ?_⟩
    rw [hxq' (hL.of_sublist htr')]
    exact hf' hL

/-- `RecRel` holds of the recorded query against the lookup's answer. -/
theorem recRel_recQuery (L : Bytes → Option Digest) (budget : ℕ) (x : Bytes) :
    RecRel (nx := nx) (ns := ns) L (recQuery budget x) (L x) := by
  intro tr st ℓ htr p hp
  unfold runG at hp
  rw [run_recQuery, StateT.run_map, simulateQ_map, StateT.run_map, support_map] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  obtain ⟨hpre, hlook⟩ := mem_support_runG_budgetedQuery hq
  refine ⟨hpre, fun a tr' h ↦ ?_⟩
  rcases hd : q.1.1 with _ | d
  · simp [hd] at h
  · simp only [hd, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hx := hlook d hd
    refine ⟨List.prefix_append _ _, fun e he ↦ ?_, fun hL ↦ hL (x, d) (by simp)⟩
    rcases List.mem_append.mp he with he | he
    · exact (htr.of_prefix hpre) e he
    · rw [List.mem_singleton.mp he]; exact hx

/-- **`RecRel` holds of V_I's recorded run and its `Option` run by `L`.** -/
theorem recRel_idealVerify (L : Bytes → Option Digest) (budget : ℕ) (prog : Program)
    (ip : IdealProof) (fuel : ℕ) (s : NodeStatement) :
    RecRel (nx := nx) (ns := ns) L (idealVerify (recQuery budget) prog ip fuel s)
      (idealVerify L prog ip fuel s) :=
  rel_idealVerify (fun x x' ↦ RecRel L x x') (recRel_pure L) (recRel_bind L) _ _
    (recRel_recQuery L budget) prog ip fuel s

/-- **What V_I's trace knows.** On every reachable run of V_I's recorded run against the game's
oracle, if it returns a verdict and a trace, every entry of the trace is answered alike by the
final log, and the `Option` run of V_I by the trace's lookup returns the verdict. -/
theorem viRec_trace {budget : ℕ} {prog : Program} {ip : IdealProof} {fuel : ℕ} {s : NodeStatement}
    {st : SignState nx ns} {ℓ : Log}
    {p : (Option (Bool × Log) × SignState nx ns) × Log}
    (hp : p ∈ support ((simulateQ gameImpl ((viRec budget prog ip fuel s).run st)).run ℓ)) :
    ℓ <+: p.2 ∧ ∀ b tr, p.1.1 = some (b, tr) →
      TrSub tr (look p.2) ∧ idealVerify (look tr) prog ip fuel s = some b := by
  have h := recRel_idealVerify (nx := nx) (ns := ns) (look (p.1.1.map Prod.snd |>.getD []))
    budget prog ip fuel s [] st ℓ (fun _ h ↦ absurd h List.not_mem_nil) p hp
  refine ⟨h.1, fun b tr hbt ↦ ?_⟩
  obtain ⟨-, hsub, hv⟩ := h.2 b tr hbt
  simp only [hbt, Option.map_some, Option.getD_some] at hv
  exact ⟨hsub, hv hsub.self⟩

/-! ## The game with V_I's trace -/

variable [Sphincs.Params]

/-- **The game's computation with V_I's trace**: `gameComp`, V_I run recorded; the outcome and
the trace (empty past the budget). -/
noncomputable def gameCompRec (guest : Program) (fuel budget : ℕ) (A : GameAdversary nx ns) :
    OracleComp GameSpec (GameOutcome nx ns × Log) := do
  let (out, st) ← (do
      let keys ← keygen
      let (s, ip) ← simulateQ (advImpl keys)
        (A (fun j ↦ (keys.xmss j).1) (fun j ↦ (keys.sphincs j).1))
      let o ← viRec budget guest ip fuel s
      pure (keys, s, ip, o) : GameM nx ns _).run (SignState.init nx ns)
  pure (⟨out.1, out.2.1, out.2.2.1, (out.2.2.2.map Prod.fst).getD false, st⟩,
    (out.2.2.2.map Prod.snd).getD [])

/-- **Forgetting the trace gives the game's computation.** -/
theorem gameCompRec_map (guest : Program) (fuel budget : ℕ) (A : GameAdversary nx ns) :
    Prod.fst <$> gameCompRec guest fuel budget A = gameComp guest fuel budget A := by
  unfold gameCompRec gameComp
  simp only [map_bind, map_pure]
  simp only [← viRec_map, bind_map_left]
  have h : ∀ (keys : Keys nx ns) (p : NodeStatement × IdealProof),
      (viRec budget guest p.2 fuel p.1 >>= fun o ↦
        (pure (keys, p.1, p.2, (Option.map Prod.fst o).getD false) : GameM nx ns _)) =
      (fun q ↦ (q.1, q.2.1, q.2.2.1, (Option.map Prod.fst q.2.2.2).getD false)) <$>
        (viRec budget guest p.2 fuel p.1 >>= fun o ↦ (pure (keys, p.1, p.2, o) : GameM nx ns _)) := by
    intro keys p
    simp
  simp only [h, ← map_bind, StateT.run_map, bind_map_left]

/-- **The game with V_I's trace**: `gameCompRec` against the logged oracle from the empty log. -/
noncomputable def gameRec (guest : Program) (fuel budget : ℕ) (A : GameAdversary nx ns) :
    ProbComp ((GameOutcome nx ns × Log) × Log) :=
  (simulateQ gameImpl (gameCompRec guest fuel budget A)).run []

/-- **The game is the game with V_I's trace, the trace forgotten.** -/
theorem gameRec_map (guest : Program) (fuel budget : ℕ) (A : GameAdversary nx ns) :
    (fun p ↦ (p.1.1, p.2)) <$> gameRec guest fuel budget A = game guest fuel budget A := by
  rw [game_eq, ← gameCompRec_map, gameRec, simulateQ_map, StateT.run_map]

/-- **What the game's trace knows.** On every reachable outcome `((z, tr), ℓ)` of the game with
V_I's trace, every entry of the trace is answered alike by the final log, and if V_I accepted,
its `Option` run by the trace's lookup accepts. -/
theorem gameRec_trace {guest : Program} {fuel budget : ℕ} {A : GameAdversary nx ns}
    {p : (GameOutcome nx ns × Log) × Log} (hp : p ∈ support (gameRec guest fuel budget A)) :
    TrSub p.1.2 (look p.2) ∧ (p.1.1.accepted = true →
      idealVerify (look p.1.2) guest p.1.1.proof fuel p.1.1.statement = some true) := by
  unfold gameRec gameCompRec at hp
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hp
  obtain ⟨⟨⟨out, st⟩, ℓ⟩, hq, hp⟩ := hp
  simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
  subst hp
  obtain ⟨⟨⟨keys, st₁⟩, ℓ₁⟩, -, hq⟩ := mem_support_run_bind hq
  obtain ⟨⟨⟨⟨s, ip⟩, st₂⟩, ℓ₂⟩, -, hq⟩ := mem_support_run_bind hq
  obtain ⟨⟨⟨o, st₃⟩, ℓ₃⟩, hv, hq⟩ := mem_support_run_bind hq
  simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff,
    Prod.mk.injEq] at hq
  obtain ⟨⟨h₁, -⟩, h₃⟩ := hq
  subst h₁ h₃
  have h := (viRec_trace hv).2
  rcases o with _ | ⟨b, tr⟩
  · exact ⟨fun _ h ↦ absurd h List.not_mem_nil, fun h ↦ absurd h (by simp)⟩
  · obtain ⟨hsub, hvb⟩ := h b tr rfl
    refine ⟨hsub, fun ha ↦ ?_⟩
    simp only [Option.map_some, Option.getD_some] at ha
    subst ha
    exact hvb

end

end LeanVM.E2E
