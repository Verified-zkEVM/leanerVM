/-
  LeanVM.E2E.Vis.PerKey.XmssCount

  W-vis, P7f: the per-key leanXMSS reduction's hash queries. In leanXMSS's single-key game it
  makes at most the adversary's hash queries, V_I's budget, two per other key, key `j`'s
  generation, `cxs` per signing request to key `j` and one final verification.
-/

module

public import LeanVM.E2E.Vis.PerKey.XmssChain

/-!
# The per-key leanXMSS reduction's query count (W-vis, P7f)

The single-key game against reduction `j` is key `j`'s generation, then the reduction's run under
the challenger's oracles, then the final verification (`gameCore_xRedJ`). The reduction's run,
its log forgotten, is its image under `ΦJ sk` (`simulateQ_σJ_eq`), a computation with the private
cache over the schemes' world. There a computation costs `c` (`CostR c`) when it makes at most `c`
hash queries from every private cache:

* the routed oracle forwards only the queries outside its class (`isQueryBoundP_route`), so a
  class-routed computation costs at most its hash queries (`costR_route`), and a private one
  nothing (`costR_route_all`);
* another key's generation costs its two derivations (`costR_ΦJ_xKeygenR`, `costR_ΦJ_sKeygenR`);
* the adversary costs one per hash query and `cxs` per signing request to key `j`
  (`costR_simulateQ_run`, `costR_ΦJ_advImplJ`): its coins and every other key's request cost
  nothing;
* V_I costs at most its budget.

* `PerKeyX.hasHashQueryBound_xRedJ`: the reduction's budget in leanXMSS's single-key game.
-/

namespace LeanVM.E2E

open LeanVM.Parameters LeanVM.Semantics LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Rom
open OracleSpec OracleComp

@[expose] public section

/-! ## Costs with a private cache -/

/-- **`x` costs at most `c`**: from every private cache, at most `c` hash queries. -/
def CostR (c : ℕ) {α : Type}
    (x : StateT (QueryCache LeanXmss.HashSpec) (OracleComp OW) α) : Prop :=
  ∀ cp, IsQueryBoundP (x.run cp) IsHashW c

section CostR

variable {α β : Type}

theorem CostR.mono {c c' : ℕ} {x : StateT (QueryCache LeanXmss.HashSpec) (OracleComp OW) α}
    (h : CostR c x) (hc : c ≤ c') : CostR c' x := fun cp ↦ (h cp).mono hc

theorem costR_pure (a : α) :
    CostR 0 (pure a : StateT (QueryCache LeanXmss.HashSpec) (OracleComp OW) α) := fun cp ↦ by
  simp

theorem CostR.bind {c c' : ℕ} {x : StateT (QueryCache LeanXmss.HashSpec) (OracleComp OW) α}
    {f : α → StateT (QueryCache LeanXmss.HashSpec) (OracleComp OW) β} (hx : CostR c x)
    (hf : ∀ a, CostR c' (f a)) : CostR (c + c') (x >>= f) := fun cp ↦ by
  rw [StateT.run_bind]
  exact isQueryBoundP_bind (hx cp) fun z _ ↦ hf z.1 z.2

theorem CostR.map {c : ℕ} (f : α → β) {x : StateT (QueryCache LeanXmss.HashSpec) (OracleComp OW) α}
    (hx : CostR c x) : CostR c (f <$> x) := fun cp ↦ by
  rw [StateT.run_map, isQueryBoundP_map_iff]
  exact hx cp

/-- A computation of the schemes' world, lifted, costs its hash queries. -/
theorem costR_liftM {c : ℕ} {oa : OracleComp OW α} (h : IsQueryBoundP oa IsHashW c) :
    CostR c (liftM oa : StateT (QueryCache LeanXmss.HashSpec) (OracleComp OW) α) := fun cp ↦ by
  rw [OracleComp.liftM_run_StateT]
  exact (isQueryBoundP_bind (n := c) (m := 0) h fun _ _ ↦ by simp).mono (by omega)

/-- **A class-routed computation costs at most its hash queries.** -/
theorem costR_route (Pr : List UInt8 → Prop) [DecidablePred Pr] {c : ℕ} {oa : OracleComp OW α}
    (h : IsQueryBoundP oa IsHashW c) : CostR c (simulateQ (routeImpl Pr) oa) :=
  isQueryBoundP_route Pr (h.of_imp fun _ ht ↦ ht.1)

/-- **A computation routed entirely to the private oracle costs nothing.** -/
theorem costR_route_all (Pr : List UInt8 → Prop) [DecidablePred Pr] (hPr : ∀ x, Pr x)
    (oa : OracleComp OW α) : CostR 0 (simulateQ (routeImpl Pr) oa) :=
  isQueryBoundP_route Pr (walk_isQueryBoundP_of_all
    (walk_allQueriesSatisfy_true oa |>.mono fun t _ ht ↦ by
      rcases t with n | x
      · exact ht.1
      · exact ht.2 (hPr x)) 0)

/-- **The costs of a sequence add.** -/
theorem costR_sequenceFin {c : ℕ} :
    ∀ {n : ℕ} (f : Fin n → StateT (QueryCache LeanXmss.HashSpec) (OracleComp OW) α),
      (∀ i, CostR c (f i)) → CostR (n * c) (LeanXmss.Concrete.sequenceFin f)
  | 0, _, _ => by
    simp only [LeanXmss.Concrete.sequenceFin]
    exact (costR_pure _).mono (Nat.zero_le _)
  | n + 1, f, h => by
    simp only [LeanXmss.Concrete.sequenceFin]
    refine ((h 0).bind fun _ ↦ (costR_sequenceFin (fun i : Fin n ↦ f i.succ)
      fun i ↦ h i.succ).bind fun _ ↦ costR_pure _).mono ?_
    rw [Nat.succ_mul]
    omega

/-- **A simulation costs its steps**: one per `p`-query and `c` per other `q`-query, when the
computation makes at most `a` `p`-queries and `b` `q`-queries. -/
theorem costR_simulateQ_run {ι : Type} {spec : OracleSpec.{0, 0} ι} {σ : Type}
    (p q : ι → Prop) [DecidablePred p] [DecidablePred q] (c : ℕ)
    (impl : QueryImpl spec (StateT σ (StateT (QueryCache LeanXmss.HashSpec) (OracleComp OW))))
    (hp : ∀ t, p t → ∀ s, CostR 1 ((impl t).run s))
    (hq : ∀ t, ¬ p t → q t → ∀ s, CostR c ((impl t).run s))
    (hn : ∀ t, ¬ p t → ¬ q t → ∀ s, CostR 0 ((impl t).run s)) (oa : OracleComp spec α) :
    ∀ {a b : ℕ}, IsQueryBoundP oa p a → IsQueryBoundP oa q b → ∀ s,
      CostR (a + b * c) ((simulateQ impl oa).run s) := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
    intro a b _ _ s
    simp only [simulateQ_pure, StateT.run_pure]
    exact (costR_pure _).mono (Nat.zero_le _)
  | query_bind t k ih =>
    intro a b ha hb s
    rw [isQueryBoundP_query_bind_iff] at ha hb
    rw [simulateQ_query_bind]
    simp only [OracleQuery.input_query, monadLift_self]
    rw [StateT.run_bind]
    have hb' : (if q t then b - 1 else b) ≤ b := by split <;> omega
    have hmul := Nat.mul_le_mul_right c hb'
    by_cases hpt : p t
    · have ha0 : 0 < a := ha.1.resolve_left (not_not.mpr hpt)
      refine ((hp t hpt s).bind fun z ↦ ih z.1 (ha.2 z.1) (hb.2 z.1) z.2).mono ?_
      simp only [hpt, ↓reduceIte] at hmul ⊢
      omega
    · by_cases hqt : q t
      · have hb0 : 0 < b := hb.1.resolve_left (not_not.mpr hqt)
        refine ((hq t hpt hqt s).bind fun z ↦ ih z.1 (ha.2 z.1) (hb.2 z.1) z.2).mono ?_
        simp only [hpt, hqt, ↓reduceIte]
        obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
        rw [Nat.add_sub_cancel, Nat.succ_mul]
        omega
      · refine ((hn t hpt hqt s).bind fun z ↦ ih z.1 (ha.2 z.1) (hb.2 z.1) z.2).mono ?_
        simp only [hpt, hqt, ↓reduceIte]
        omega

end CostR

/-- A coin computation, lifted into the schemes' world, makes no hash query. -/
theorem isQueryBoundP_liftM_probCompW {α : Type} (p : ProbComp α) :
    IsQueryBoundP (liftM p : OracleComp OW α) IsHashW 0 :=
  walk_isQueryBoundP_of_all ((allQueriesSatisfy_liftM_probComp p (fun _ ↦ False)).mono
    fun t ht ↦ by
      rcases t with n | x
      · exact id
      · exact fun _ ↦ ht x rfl) 0

/-- One leanXMSS hash query. -/
theorem isTotalQueryBound_liftM_queryX (x : List UInt8) :
    IsTotalQueryBound (liftM (LeanXmss.HashSpec.query x) : OracleComp LeanXmss.HashSpec _) 1 := by
  rw [← bind_pure (liftM (LeanXmss.HashSpec.query x) : OracleComp LeanXmss.HashSpec _),
    isTotalQueryBound_query_bind_iff]
  exact ⟨Nat.one_pos, fun _ ↦ trivial⟩

/-- One leanSPHINCS hash query. -/
theorem isTotalQueryBound_liftM_queryS (x : List UInt8) :
    IsTotalQueryBound (liftM (Sphincs.HashSpec.query x) : OracleComp Sphincs.HashSpec _) 1 := by
  rw [← bind_pure (liftM (Sphincs.HashSpec.query x) : OracleComp Sphincs.HashSpec _),
    isTotalQueryBound_query_bind_iff]
  exact ⟨Nat.one_pos, fun _ ↦ trivial⟩

/-- V_I's recorded run, in the schemes' world, makes at most the budget of hash queries. -/
theorem isQueryBoundP_tw_viRec {nx ns : ℕ} [Sphincs.Params] (budget : ℕ) (guest : Program) (ip : IdealProof)
    (fuel : ℕ) (s : NodeStatement) (st : SignState nx ns) :
    IsQueryBoundP (tw (viRec budget guest ip fuel s) st) IsHashW budget := by
  have h := isQueryBoundP_idealVerify budget guest ip fuel s st
  rw [← viRec_map, StateT.run_map, isQueryBoundP_map_iff] at h
  exact isQueryBoundP_simulateQ_toW _ _ (h.mono (Nat.sub_le _ _))

/-- The adversary's coins and hash queries, in the schemes' world: one per hash query. -/
theorem isQueryBoundP_tw_advImpl_inl_inl {nx ns : ℕ} [Sphincs.Params] (keys : Keys nx ns)
    (t : (unifSpec + HashSpec).Domain) (st : SignState nx ns) :
    IsQueryBoundP (tw (advImpl keys (.inl (.inl t))) st) IsHashW
      (if AdvHash (nx := nx) (ns := ns) (.inl (.inl t)) then 1 else 0) := by
  refine isQueryBoundP_simulateQ_toW _ _ ?_
  rcases t with n | x
  · exact costs_coins _ st
  · exact costs_hashQuery x st

/-- The schemes' leanXMSS key generation makes at most `cxk` hash queries. -/
theorem isQueryBoundP_keygen_x {cxk : ℕ}
    (hxk : ∀ seed, IsTotalQueryBound (LeanXmss.Seeded.keygenFromSeed seed) cxk) :
    IsQueryBoundP (LeanXmss.MultiUser.keygen : OracleComp OW _) IsHashW cxk := by
  unfold LeanXmss.MultiUser.keygen
  exact (isQueryBoundP_bind (n := 0) (m := cxk) (isQueryBoundP_liftM_probCompW _)
    fun seed _ ↦ isQueryBoundP_liftM_hash _ _ (hxk seed)).mono (by omega)

namespace PerKeyX

variable {nx ns : ℕ}

/-- `ΦJ` of a simulation is the simulation by the images. -/
theorem ΦJ_simulateQ_run (sk : LeanXmss.Seeded.SecretKey) {ι : Type} {spec : OracleSpec.{0, 0} ι}
    {σ : Type} (impl : QueryImpl spec (StateT σ RM)) {α : Type} (oa : OracleComp spec α) (s : σ) :
    ΦJ sk ((simulateQ impl oa).run s) =
      (simulateQ (fun t ↦ stMap (fun {β : Type} (y : RM β) ↦ ΦJ sk y) (impl t)) oa).run s := by
  have h1 := simulateQ_morph (isMorphism_stMap (σ := σ) (isMorphism_ΦJ sk)) impl oa
  have h2 := congrArg (fun x ↦ StateT.run x s) h1
  simp only [run_stMap] at h2
  exact h2.symm

/-- A class-routed computation, under the game's oracles, costs at most its hash queries. -/
theorem costR_ΦJ_rc (sk : LeanXmss.Seeded.SecretKey) (pj : Bytes) {α : Type}
    {oa : OracleComp OW α} {c : ℕ} (h : IsQueryBoundP oa IsHashW c) : CostR c (ΦJ sk (rc pj oa)) := by
  rw [ΦJ_rc]
  exact costR_route _ h

/-- A private computation, under the game's oracles, costs nothing. -/
theorem costR_ΦJ_rp (sk : LeanXmss.Seeded.SecretKey) {α : Type} (oa : OracleComp OW α) :
    CostR 0 (ΦJ sk (rp oa)) := by
  rw [ΦJ_rp]
  exact costR_route_all _ (fun _ ↦ trivial) oa

/-- **The class-routed prefix of a leanXMSS key generation costs its two derivations.** -/
theorem costR_xPrefix' (pj : Bytes) : CostR 2 (xPrefix' pj) := by
  unfold xPrefix'
  refine ((costR_route _ (isQueryBoundP_liftM_probCompW _)).bind fun _ ↦
    (costR_route _ (isQueryBoundP_liftM_hash _ _ (isTotalQueryBound_liftM_queryX _))).bind fun _ ↦
    (costR_route _ (isQueryBoundP_liftM_hash _ _ (isTotalQueryBound_liftM_queryX _))).bind fun _ ↦
      costR_pure _).mono (by omega)

variable [Sphincs.Params]

omit [Sphincs.Params] in
/-- **The class-routed prefix of a leanSPHINCS key generation costs its two derivations.** -/
theorem costR_sPrefix' (pj : Bytes) : CostR 2 (sPrefix' pj) := by
  unfold sPrefix'
  refine ((costR_route _ (isQueryBoundP_liftM_probCompW _)).bind fun _ ↦
    (costR_route _ (isQueryBoundP_sLift _ _ (isTotalQueryBound_liftM_queryS _))).bind fun _ ↦
    (costR_route _ (isQueryBoundP_sLift _ _ (isTotalQueryBound_liftM_queryS _))).bind fun _ ↦
      costR_pure _).mono (by omega)

omit [Sphincs.Params] in
/-- **Another leanXMSS key's generation costs its two derivations**: its tree is private. -/
theorem costR_ΦJ_xKeygenR (sk : LeanXmss.Seeded.SecretKey) (pj : Bytes) :
    CostR 2 (ΦJ sk (xKeygenR pj)) := by
  rw [ΦJ_xKeygenR]
  refine ((costR_xPrefix' pj).bind (c' := 0) fun m ↦ ?_).mono (by omega)
  unfold xTree keyOfTree
  exact ((costR_route_all _ (fun _ ↦ trivial) _).bind fun _ ↦ costR_pure _).mono (by omega)

/-- **A leanSPHINCS key's generation costs its two derivations**: its tree is private. -/
theorem costR_ΦJ_sKeygenR (sk : LeanXmss.Seeded.SecretKey) (pj : Bytes) :
    CostR 2 (ΦJ sk (sKeygenR pj)) := by
  rw [ΦJ_sKeygenR]
  refine ((costR_sPrefix' pj).bind (c' := 0) fun m ↦ ?_).mono (by omega)
  unfold sTree keyOfTreeS
  exact ((costR_route_all _ (fun _ ↦ trivial) _).bind fun _ ↦ costR_pure _).mono (by omega)

/-- **The reduction's answers cost**: one per hash query, `cxs` per signing request to key `j`,
nothing for coins and the other keys' requests. -/
theorem costR_ΦJ_advImplJ {cxs : ℕ}
    (hxs : ∀ sk i msg, IsTotalQueryBound
      (LeanXmss.Seeded.sign sk i msg : OracleComp LeanXmss.HashSpec _) cxs)
    (sk : LeanXmss.Seeded.SecretKey) (pj : Bytes) (j : Fin nx) (keys : Keys nx ns)
    (t : (AdvSpec nx ns).Domain) (st : SignState nx ns) :
    CostR (if AdvHash t then 1 else if AdvXmssAt j t then cxs else 0)
      ((stMap (fun {β : Type} (y : RM β) ↦ ΦJ sk y) (advImplJ pj j keys t)).run st) := by
  rw [run_stMap]
  rcases t with (t | ⟨i, req⟩) | ⟨i, msg⟩
  · rw [advImplJ_inl_inl, StateT.run_mk]
    refine (costR_ΦJ_rc sk pj (isQueryBoundP_tw_advImpl_inl_inl keys t st)).mono ?_
    split <;> omega
  · by_cases hij : i = j
    · subst hij
      have hc : (if AdvHash (nx := nx) (ns := ns) (.inl (.inr (i, req))) then 1
          else if AdvXmssAt (ns := ns) i (.inl (.inr (i, req))) then cxs else 0) = cxs := by
        simp [AdvHash, AdvXmssAt]
      rw [hc, advImplJ_xmss_self, run_xmssFwdJ]
      split
      · rw [ΦJ_pure]
        exact (costR_pure _).mono (Nat.zero_le _)
      · rw [ΦJ_map, ΦJ_signQuery]
        exact (costR_liftM (isQueryBoundP_liftM_hash _ _ (hxs _ _ _))).map _
    · have hc : (if AdvHash (nx := nx) (ns := ns) (.inl (.inr (i, req))) then 1
          else if AdvXmssAt (ns := ns) j (.inl (.inr (i, req))) then cxs else 0) = 0 := by
        simp [AdvHash, AdvXmssAt, hij]
      rw [hc, advImplJ_xmss_ne _ _ _ hij, StateT.run_mk]
      exact costR_ΦJ_rp sk _
  · have hc : (if AdvHash (nx := nx) (ns := ns) (.inr (i, msg)) then 1
        else if AdvXmssAt (ns := ns) j (.inr (i, msg)) then cxs else 0) = 0 := by
      simp [AdvHash, AdvXmssAt]
    rw [hc, advImplJ_sphincs, StateT.run_mk]
    exact costR_ΦJ_rp sk _

/-- **The adversary's phase costs** at most its hash queries and `cxs` per signing request to
key `j`. -/
theorem costR_ΦJ_adv {cxs : ℕ}
    (hxs : ∀ sk i msg, IsTotalQueryBound
      (LeanXmss.Seeded.sign sk i msg : OracleComp LeanXmss.HashSpec _) cxs)
    (sk : LeanXmss.Seeded.SecretKey) (pj : Bytes) (j : Fin nx) (keys : Keys nx ns) {α : Type}
    (oa : OracleComp (AdvSpec nx ns) α) {qH sXk : ℕ} (hH : IsQueryBoundP oa AdvHash qH)
    (hXk : IsQueryBoundP oa (AdvXmssAt j) sXk) (st : SignState nx ns) :
    CostR (qH + sXk * cxs) (ΦJ sk ((simulateQ (advImplJ pj j keys) oa).run st)) := by
  rw [ΦJ_simulateQ_run]
  refine costR_simulateQ_run AdvHash (AdvXmssAt j) cxs _ (fun t ht s ↦ ?_) (fun t ht hq s ↦ ?_)
    (fun t ht hq s ↦ ?_) oa hH hXk st
  · have h := costR_ΦJ_advImplJ hxs sk pj j keys t s
    simpa [ht] using h
  · have h := costR_ΦJ_advImplJ hxs sk pj j keys t s
    simpa [ht, hq] using h
  · have h := costR_ΦJ_advImplJ hxs sk pj j keys t s
    simpa [ht, hq] using h

/-- **The reduction's run after the keys costs** the adversary's queries and V_I's budget. -/
theorem costR_ΦJ_restJ {cxs : ℕ}
    (hxs : ∀ sk i msg, IsTotalQueryBound
      (LeanXmss.Seeded.sign sk i msg : OracleComp LeanXmss.HashSpec _) cxs)
    (guest : Program) (fuel budget : ℕ) (A : GameAdversary nx ns) (sk : LeanXmss.Seeded.SecretKey)
    (pj : Bytes) (j : Fin nx) (keys : Keys nx ns) {qH sXk : ℕ}
    (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH)
    (hXk : ∀ pkx pks, IsQueryBoundP (A pkx pks) (AdvXmssAt j) sXk) :
    CostR (qH + sXk * cxs + (budget + 0)) (ΦJ sk (restJ guest fuel budget A pj j keys)) := by
  unfold restJ
  rw [ΦJ_bind]
  refine (costR_ΦJ_adv hxs sk pj j keys _ (hH _ _) (hXk _ _) _).bind fun p ↦ ?_
  rcases p with ⟨sip, st⟩
  dsimp only
  rw [ΦJ_bind]
  refine (costR_ΦJ_rc sk pj (isQueryBoundP_tw_viRec _ _ _ _ _ _)).bind fun q ↦ ?_
  rcases q with ⟨o, st'⟩
  dsimp only
  rw [ΦJ_pure]
  exact costR_pure _

/-- **The reduction's run costs** two per other key, the adversary's queries and V_I's budget. -/
theorem costR_ΦJ_xBodyJ {cxs : ℕ}
    (hxs : ∀ sk i msg, IsTotalQueryBound
      (LeanXmss.Seeded.sign sk i msg : OracleComp LeanXmss.HashSpec _) cxs)
    (guest : Program) (fuel budget : ℕ) (A : GameAdversary nx ns) (sk : LeanXmss.Seeded.SecretKey)
    (j : Fin nx) (pkj : LeanXmss.PublicKey) {qH sXk : ℕ}
    (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH)
    (hXk : ∀ pkx pks, IsQueryBoundP (A pkx pks) (AdvXmssAt j) sXk) :
    CostR (qH + budget + 2 * (nx + ns) + sXk * cxs) (ΦJ sk (xBodyJ guest fuel budget A j pkj)) := by
  unfold xBodyJ
  rw [ΦJ_bind, morph_sequenceFin (isMorphism_ΦJ sk)]
  refine ((costR_sequenceFin (c := 2) _ fun i ↦ ?_).bind
    (c' := ns * 2 + (qH + sXk * cxs + (budget + 0))) fun xs ↦ ?_).mono ?_
  · split
    · rw [ΦJ_pure]
      exact (costR_pure _).mono (Nat.zero_le _)
    · exact costR_ΦJ_xKeygenR sk _
  · rw [ΦJ_bind, morph_sequenceFin (isMorphism_ΦJ sk)]
    exact (costR_sequenceFin (c := 2) _ fun _ ↦ costR_ΦJ_sKeygenR sk _).bind fun ss ↦
      costR_ΦJ_restJ hxs guest fuel budget A sk _ j _ hH hXk
  · rw [Nat.mul_add]
    omega

/-- **The single-key game against reduction `j` makes at most** key `j`'s generation, the
reduction's run and one final verification's hash queries. -/
theorem isQueryBoundP_gameCore_xRedJ {cxk cxs cx : ℕ}
    (hxk : ∀ seed, IsTotalQueryBound (LeanXmss.Seeded.keygenFromSeed seed) cxk)
    (hxs : ∀ sk i msg, IsTotalQueryBound
      (LeanXmss.Seeded.sign sk i msg : OracleComp LeanXmss.HashSpec _) cxs)
    (hvx : ∀ pk msg σ, IsTotalQueryBound
      (LeanXmss.Concrete.verify pk msg σ : OracleComp LeanXmss.HashSpec Bool) cx)
    (guest : Program) (fuel budget : ℕ) (A : GameAdversary nx ns) (j : Fin nx) {qH sXk : ℕ}
    (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH)
    (hXk : ∀ pkx pks, IsQueryBoundP (A pkx pks) (AdvXmssAt j) sXk) :
    IsQueryBoundP (LeanXmss.Security.gameCore (xRedJ guest fuel budget A j)) IsHashW
      (qH + budget + 2 * (nx + ns) + cxk + sXk * cxs + cx) := by
  rw [gameCore_xRedJ]
  refine (isQueryBoundP_bind (isQueryBoundP_keygen_x hxk) fun kp _ ↦ ?_).mono
    (n := cxk + ((qH + budget + 2 * (nx + ns) + sXk * cxs) + (cx + 0))) (by omega)
  unfold contJ
  refine isQueryBoundP_bind ?_ fun w _ ↦ ?_
  · have h := costR_ΦJ_xBodyJ hxs guest fuel budget A kp.2 j kp.1 hH hXk ∅
    rw [ΦJ, run_stMap, simulateQ_σJ_eq, isQueryBoundP_map_iff] at h
    exact h
  · unfold finishJ
    exact isQueryBoundP_bind (isQueryBoundP_liftM_hash _ _ (hvx _ _ _)) fun _ _ ↦ trivial

/-- **The per-key leanXMSS reduction's hash-call budget (P7f)** in leanXMSS's single-key game:
the adversary's hash queries `qH`, V_I's budget, two derivations per other key, key `j`'s
generation `cxk`, `cxs` per signing request to key `j`, and one final verification `cx`. -/
theorem hasHashQueryBound_xRedJ {cxk cxs cx : ℕ}
    (hxk : ∀ seed, IsTotalQueryBound (LeanXmss.Seeded.keygenFromSeed seed) cxk)
    (hxs : ∀ sk i msg, IsTotalQueryBound
      (LeanXmss.Seeded.sign sk i msg : OracleComp LeanXmss.HashSpec _) cxs)
    (hvx : ∀ pk msg σ, IsTotalQueryBound
      (LeanXmss.Concrete.verify pk msg σ : OracleComp LeanXmss.HashSpec Bool) cx)
    (guest : Program) (fuel budget : ℕ) (A : GameAdversary nx ns) (j : Fin nx) {qH sXk : ℕ}
    (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH)
    (hXk : ∀ pkx pks, IsQueryBoundP (A pkx pks) (AdvXmssAt j) sXk) :
    LeanXmss.Security.HasHashQueryBound (xRedJ guest fuel budget A j)
      (qH + budget + 2 * (nx + ns) + cxk + sXk * cxs + cx) := by
  intro result hr
  unfold LeanXmss.Security.experiment at hr
  rw [StateT.run'_eq] at hr
  erw [support_map] at hr
  obtain ⟨r, hr, rfl⟩ := hr
  exact count_le_of_isQueryBoundP owImpl _ _
    (isQueryBoundP_gameCore_xRedJ hxk hxs hvx guest fuel budget A j hH hXk) ∅ r hr

end PerKeyX

end
end LeanVM.E2E
