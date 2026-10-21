/-
  LeanVM.E2E.Reduction.Xmss

  The leanXMSS reduction of T5: an adversary against leanXMSS's multi-user game that runs the
  whole end-to-end game with the multi-user game's keys, signing oracles and hash, and outputs
  the forged claim's signature V_I's trace knows.
-/

module

public import LeanVM.E2E.Reduction.Count
public import LeanVM.E2E.Reduction.GameW
public import LeanVM.E2E.KnowledgeSub

/-!
# The leanXMSS reduction

**The adversary** (`xAdv`). Against `n_x` leanXMSS keys (`LeanXmss.MultiUser`), it receives their
public keys and runs the game (`gameCompRec`, the game with V_I's trace) in the schemes' world
(`toW`): it generates the leanSPHINCS keys itself, answers the adversary's coins, hash queries and
leanSPHINCS requests as the game does, and its leanXMSS requests as the game does but with the
multi-user game's signing oracle in place of the signer (`xmssFwd`: a used leaf refused, else the
request forwarded and recorded); then V_I with its trace. It outputs, for a forged leanXMSS
claim `(pk_j, m)` of the root (no request to key `j` for `m` answered) with a signature valid
under the trace's answers (`XWin`), that signature under key `j` (`forgeryOf`, a classical
choice).

**Its run is the game's** (`map_xPrefix`). With the multi-user game's keys generated first, the
reduction's run, its signing log forgotten, is the translation of `gameCompRec`: the multi-user
key generation is the game's leanXMSS key generation, the forwarded requests are signed by the
keys' signers, and the rest is the game's own computation.
-/

namespace LeanVM.E2E

open LeanVM.Parameters LeanVM.Semantics LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Rom
open OracleSpec OracleComp
open scoped ENNReal

@[expose] public section

namespace XmssRed

variable {nx ns : ℕ}

/-- The reduction's world: the schemes' world and the multi-user leanXMSS signing oracle. -/
abbrev RSpec (nx : ℕ) := OW + LeanXmss.MultiUser.SigningSpec nx

/-- A computation of the schemes' world in the reduction's. -/
noncomputable def liftR {α : Type} (oa : OracleComp OW α) : OracleComp (RSpec nx) α :=
  simulateQ (fun t ↦ (liftM ((RSpec nx).query (.inl t)) : OracleComp (RSpec nx) _)) oa

/-- **The forwarded leanXMSS request** of key `j`: a used leaf refused; otherwise the request
sent to the multi-user signing oracle, and the request and its answer recorded (`xmssSign` with
the signer replaced by the oracle). -/
noncomputable def xmssFwd (j : Fin nx) (req : XmssRequest) :
    StateT (SignState nx ns) (OracleComp (RSpec nx)) (Option LeanXmss.Signature) := do
  if ((← get).xlog j).any (·.1.1 = req.1) then return none
  let σ ← (liftM (liftM ((RSpec nx).query (.inr ⟨j, ⟨req.1, req.2⟩⟩)) :
    OracleComp (RSpec nx) (Option LeanXmss.Signature)) :
      StateT (SignState nx ns) (OracleComp (RSpec nx)) (Option LeanXmss.Signature))
  modify fun st ↦ { st with xlog := Function.update st.xlog j (st.xlog j ++ [(req, σ)]) }
  pure σ


/-! ## The multi-user game's oracles -/

/-- The multi-user game's oracles for the reduction, with the keys `mk`: the schemes' world
passed through, the signing requests answered by the keys' signers and logged. -/
noncomputable abbrev τX (mk : Fin nx → LeanXmss.PublicKey × LeanXmss.Seeded.SecretKey) :
    QueryImpl (RSpec nx) (WriterT (QueryLog (LeanXmss.MultiUser.SigningSpec nx)) (OracleComp OW)) :=
  QueryImpl.ofLift OW (WriterT (QueryLog (LeanXmss.MultiUser.SigningSpec nx)) (OracleComp OW)) +
    LeanXmss.MultiUser.signingOracle (fun j ↦ (mk j).2)

/-- The multi-user game's oracles, the log forgotten. -/
noncomputable def σX (mk : Fin nx → LeanXmss.PublicKey × LeanXmss.Seeded.SecretKey) :
    QueryImpl (RSpec nx) (OracleComp OW) :=
  fun t ↦ Prod.fst <$> (τX mk t).run

/-- The forgetful oracles on the schemes' world are its queries. -/
theorem σX_inl (mk : Fin nx → LeanXmss.PublicKey × LeanXmss.Seeded.SecretKey) (t : OW.Domain) :
    σX mk (.inl t) = (liftM (OW.query t) : OracleComp OW _) := by
  simp only [σX, τX, QueryImpl.add_apply_inl, QueryImpl.ofLift_apply]
  change Prod.fst <$> (monadLift (liftM (OW.query t) : OracleComp OW _) :
    WriterT (QueryLog (LeanXmss.MultiUser.SigningSpec nx)) (OracleComp OW) _).run = _
  rw [WriterT.run_monadLift', Functor.map_map]
  exact id_map _

/-- The forgetful oracles on a signing request are the key's signer. -/
theorem σX_inr (mk : Fin nx → LeanXmss.PublicKey × LeanXmss.Seeded.SecretKey)
    (q : LeanXmss.MultiUser.SignRequest nx) :
    σX mk (.inr q) = (liftM (LeanXmss.Seeded.sign (mk q.key).2 q.request.leafIndex
      q.request.message : OracleComp LeanXmss.HashSpec _) : OracleComp OW _) := by
  simp [σX, τX, QueryImpl.add_apply_inr, LeanXmss.MultiUser.signingOracle,
]

/-- A computation of the schemes' world, lifted into the reduction's and answered by the
forgetful oracles, is itself. -/
theorem simulateQ_σX_liftR (mk : Fin nx → LeanXmss.PublicKey × LeanXmss.Seeded.SecretKey)
    {α : Type} (oa : OracleComp OW α) : simulateQ (σX mk) (liftR oa) = oa := by
  unfold liftR
  rw [← QueryImpl.simulateQ_compose]
  conv_rhs => rw [← simulateQ_ofLift_eq_self oa]
  congr 1

/-- A forwarded request on a used leaf is refused. -/
theorem run_xmssFwd_of_used {j : Fin nx} {req : XmssRequest} {st : SignState nx ns}
    (h : ((st.xlog j).any fun e ↦ decide (e.1.1 = req.1)) = true) :
    (xmssFwd j req).run st = pure (none, st) := by
  simp [xmssFwd, h]

/-- A forwarded request on a fresh leaf: the oracle's answer, recorded. -/
theorem run_xmssFwd_of_fresh {j : Fin nx} {req : XmssRequest} {st : SignState nx ns}
    (h : ¬ ((st.xlog j).any fun e ↦ decide (e.1.1 = req.1)) = true) :
    (xmssFwd j req).run st =
      (fun σ ↦ (σ, { st with xlog := Function.update st.xlog j (st.xlog j ++ [(req, σ)]) })) <$>
        (liftM ((RSpec nx).query (.inr ⟨j, ⟨req.1, req.2⟩⟩)) :
          OracleComp (RSpec nx) (Option LeanXmss.Signature)) := by
  simp only [xmssFwd, h, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get,
    pure_bind, OracleComp.liftM_run_StateT, bind_assoc, StateT.run_modify, StateT.run_pure,
    map_eq_bind_pure_comp]
  rfl

variable [Sphincs.Params]

/-- **The reduction's answers to the adversary**: the game's (`advImpl`, translated), the leanXMSS
requests forwarded. -/
noncomputable def advImplX (keys : Keys nx ns) :
    QueryImpl (AdvSpec nx ns) (StateT (SignState nx ns) (OracleComp (RSpec nx)))
  | .inl (.inl t) => StateT.mk fun st ↦ liftR (tw (advImpl keys (.inl (.inl t))) st)
  | .inl (.inr q) => xmssFwd q.1 q.2
  | .inr q => StateT.mk fun st ↦ liftR (tw (advImpl keys (.inr q)) st)

/-- The secret key the reduction places for the keys under attack; never used. -/
def dummyKey : LeanXmss.Seeded.SecretKey := ⟨0, 0, 0⟩

/-- What the reduction's run reaches: the keys it holds (the leanXMSS secret keys dummies), the
root statement and idealized proof, V_I's recorded verdict and the signers' final state. -/
abbrev BOut (nx ns : ℕ) : Type :=
  Keys nx ns × NodeStatement × IdealProof × Option (Bool × Log) × SignState nx ns

/-- **The reduction's run** with the leanXMSS public keys `xpks`. -/
noncomputable def xCore (guest : Program) (fuel budget : ℕ) (A : GameAdversary nx ns)
    (xpks : Fin nx → LeanXmss.PublicKey) : OracleComp (RSpec nx) (BOut nx ns) := do
  let ss ← liftR (LeanXmss.Concrete.sequenceFin fun _ : Fin ns ↦ sKeygen)
  let keys : Keys nx ns := ⟨fun j ↦ (xpks j, dummyKey), ss⟩
  let (sip, st) ← (simulateQ (advImplX keys)
    (A (fun j ↦ (keys.xmss j).1) (fun j ↦ (keys.sphincs j).1))).run (SignState.init nx ns)
  let (o, st') ← liftR (tw (viRec budget guest sip.2 fuel sip.1) st)
  pure (keys, sip.1, sip.2, o, st')

/-- The game's outcome and V_I's trace of a run of the reduction, with the leanXMSS keys `mk`. -/
def fullOut (mk : Fin nx → LeanXmss.PublicKey × LeanXmss.Seeded.SecretKey) (r : BOut nx ns) :
    GameOutcome nx ns × Log :=
  (⟨⟨mk, r.1.sphincs⟩, r.2.1, r.2.2.1, (r.2.2.2.1.map Prod.fst).getD false, r.2.2.2.2⟩,
    (r.2.2.2.1.map Prod.snd).getD [])

/-- **The reduction's win in the game**: V_I accepts, and a leanXMSS claim of the root for an
honest key `j` on a message no request to key `j` was answered for has a signature valid under
the trace's answers. -/
def XWin (z : GameOutcome nx ns) (tr : Log) : Prop :=
  z.accepted = true ∧ ∃ j : Fin nx, ∃ msg σ, ((z.keys.xmss j).1, msg) ∈ z.statement.claims.xmss ∧
    (∀ e ∈ z.state.xlog j, e.1.2 = msg → e.2 = none) ∧
    xmssVerifyWith (look tr) (z.keys.xmss j).1 msg σ = some true

/-- A leanXMSS signature, never used: the reduction's output when it has no forgery. -/
def dummySig : LeanXmss.Signature := ⟨⟨0, by decide⟩, fun _ ↦ ⟨0, fun _ ↦ 0, fun _ ↦ 0⟩⟩

open Classical in
/-- **The reduction's forgery**: the forged claim's key, message and signature when the run wins
(`XWin`), a dummy otherwise. -/
noncomputable def forgeryOf [NeZero nx] (r : BOut nx ns) : LeanXmss.MultiUser.Forgery nx :=
  if h : XWin (fullOut r.1.xmss r).1 (fullOut r.1.xmss r).2 then
    ⟨h.2.choose, ⟨h.2.choose_spec.choose, h.2.choose_spec.choose_spec.choose⟩⟩
  else ⟨0, ⟨0, dummySig⟩⟩

/-- **The leanXMSS reduction**: the game run with the multi-user game's keys, signing oracles and
hash; the forged claim's signature its trace knows. -/
noncomputable def xAdv [NeZero nx] (guest : Program) (fuel budget : ℕ) (A : GameAdversary nx ns) :
    LeanXmss.MultiUser.Adversary nx where
  main xpks := forgeryOf <$> xCore guest fuel budget A xpks

/-! ## The reduction's run is the game's -/

/-- The forwarded request, answered by the keys' signers, is the game's signing oracle. -/
theorem simulateQ_xmssFwd (mk : Fin nx → LeanXmss.PublicKey × LeanXmss.Seeded.SecretKey)
    (ss : Fin ns → Sphincs.PublicKey × Sphincs.Seeded.SecretKey) (j : Fin nx) (req : XmssRequest)
    (st : SignState nx ns) :
    simulateQ (σX mk) ((xmssFwd j req).run st) = tw (xmssSign ⟨mk, ss⟩ j req) st := by
  unfold xmssFwd xmssSign
  by_cases h : ((st.xlog j).any fun e ↦ decide (e.1.1 = req.1)) = true
  · simp [h, tw]
  · simp only [h, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind,
      tw, simulateQ_bind] at *
    have h₁ := tw_xmssRun (nx := nx) (ns := ns) (LeanXmss.Seeded.sign (mk j).2 req.1 req.2) st
    unfold tw at h₁
    rw [h₁, OracleComp.liftM_run_StateT, simulateQ_bind, simulateQ_spec_query, σX_inr]
    simp only [bind_map_left, simulateQ_pure, pure_bind, StateT.run_modify, bind_assoc,
      StateT.run_pure]

/-- **The reduction answers the adversary as the game does**: its handler, its signing requests
answered by the keys' signers, is the game's, translated. -/
theorem mapStateTBase_advImplX (mk : Fin nx → LeanXmss.PublicKey × LeanXmss.Seeded.SecretKey)
    (ss : Fin ns → Sphincs.PublicKey × Sphincs.Seeded.SecretKey) :
    (σX mk).mapStateTBase (advImplX ⟨fun j ↦ ((mk j).1, dummyKey), ss⟩) =
      toW.mapStateTBase (advImpl ⟨mk, ss⟩) := by
  funext t
  rcases t with (t | q) | q
  · simp only [QueryImpl.mapStateTBase, advImplX, StateT.run_mk, simulateQ_σX_liftR]
    have : advImpl (⟨fun j ↦ ((mk j).1, dummyKey), ss⟩ : Keys nx ns) (.inl (.inl t)) =
        advImpl ⟨mk, ss⟩ (.inl (.inl t)) := by
      simp only [advImpl, QueryImpl.add_apply_inl]
    rw [this]
    rfl
  · simp only [QueryImpl.mapStateTBase, advImplX]
    exact congrArg StateT.mk (funext fun st ↦ simulateQ_xmssFwd mk ss q.1 q.2 st)
  · simp only [QueryImpl.mapStateTBase, advImplX, StateT.run_mk, simulateQ_σX_liftR]
    have : advImpl (⟨fun j ↦ ((mk j).1, dummyKey), ss⟩ : Keys nx ns) (.inr q) =
        advImpl ⟨mk, ss⟩ (.inr q) := by
      simp only [advImpl, QueryImpl.add_apply_inr]
      rfl
    rw [this]
    rfl

omit [Sphincs.Params] in
/-- A bind into `pure` is a map. -/
theorem map_eq_bind_pure_comp' {m : Type → Type} [Monad m] [LawfulMonad m] {α β : Type}
    (x : m α) (f : α → β) : (x >>= fun a ↦ pure (f a)) = f <$> x :=
  (map_eq_bind_pure_comp m f x).symm

/-- The multi-user game's run of the reduction, the keys generated first: the keys, the
reduction's run and the signing log. -/
noncomputable def xPrefix (guest : Program) (fuel budget : ℕ) (A : GameAdversary nx ns) :
    OracleComp OW ((Fin nx → LeanXmss.PublicKey × LeanXmss.Seeded.SecretKey) × BOut nx ns ×
      QueryLog (LeanXmss.MultiUser.SigningSpec nx)) := do
  let mk ← LeanXmss.Concrete.sequenceFin fun _ : Fin nx ↦ LeanXmss.MultiUser.keygen
  let p ← (simulateQ (τX mk) (xCore guest fuel budget A (fun j ↦ (mk j).1))).run
  pure (mk, p.1, p.2)

/-- **The reduction's run is the game's.** With the multi-user game's keys generated first, the
reduction's run, its signing log forgotten, is the translation of the game with V_I's trace. -/
theorem map_xPrefix (guest : Program) (fuel budget : ℕ) (A : GameAdversary nx ns) :
    (fun p ↦ fullOut p.1 p.2.1) <$> xPrefix guest fuel budget A =
      simulateQ toW (gameCompRec guest fuel budget A) := by
  -- The reduction's side, its log forgotten.
  have hL : ∀ mk : Fin nx → LeanXmss.PublicKey × LeanXmss.Seeded.SecretKey,
      (fun p ↦ fullOut mk p.1) <$>
          (simulateQ (τX mk) (xCore guest fuel budget A (fun j ↦ (mk j).1))).run =
        LeanXmss.Concrete.sequenceFin (fun _ : Fin ns ↦ sKeygen) >>= fun ss ↦
          tw (simulateQ (advImpl ⟨mk, ss⟩) (A (fun j ↦ (mk j).1) (fun j ↦ (ss j).1)))
            (SignState.init nx ns) >>= fun q ↦
          tw (viRec budget guest q.1.2 fuel q.1.1) q.2 >>= fun q' ↦
          pure (fullOut mk (⟨fun j ↦ ((mk j).1, dummyKey), ss⟩, q.1.1, q.1.2, q'.1, q'.2)) := by
    intro mk
    have h := fst_map_run_simulateQ_writer' (τX mk) (xCore guest fuel budget A (fun j ↦ (mk j).1))
    have hm : (fun p ↦ fullOut mk p.1) <$>
        (simulateQ (τX mk) (xCore guest fuel budget A (fun j ↦ (mk j).1))).run =
        fullOut mk <$> (Prod.fst <$>
          (simulateQ (τX mk) (xCore guest fuel budget A (fun j ↦ (mk j).1))).run) := by
      rw [Functor.map_map]
    rw [hm, h]
    change fullOut mk <$> simulateQ (σX mk) (xCore guest fuel budget A (fun j ↦ (mk j).1)) = _
    unfold xCore
    simp only [simulateQ_bind, simulateQ_σX_liftR, simulateQ_pure, map_bind, map_pure]
    refine bind_congr fun ss ↦ ?_
    rw [QueryImpl.simulateQ_mapStateTBase_run, mapStateTBase_advImplX, ←
      QueryImpl.simulateQ_mapStateTBase_run]
    rfl
  rw [toW_gameCompRec]
  unfold xPrefix
  simp only [map_bind, map_pure]
  refine bind_congr fun mk ↦ ?_
  refine (map_eq_bind_pure_comp' _
    (fun a : BOut nx ns × QueryLog (LeanXmss.MultiUser.SigningSpec nx) ↦ fullOut mk a.1)).trans ?_
  rw [hL]
  rfl

/-! ## The reduction's signing log -/

/-- A request log of the game as the scheme's signing transcript. -/
def conv (l : List (XmssRequest × Option LeanXmss.Signature)) : QueryLog LeanXmss.SigningSpec :=
  l.map fun e ↦ ⟨⟨e.1.1, e.1.2⟩, e.2⟩

omit [Sphincs.Params] in
/-- The schemes' world passed through a writer logs nothing. -/
theorem run_simulateQ_ofLift_writer {L : Type} {α : Type} (oa : OracleComp OW α) :
    (simulateQ (QueryImpl.ofLift OW (WriterT (List L) (OracleComp OW))) oa).run =
      (fun a ↦ (a, ([] : List L))) <$> oa := by
  induction oa using OracleComp.inductionOn with
  | pure value =>
      simp only [simulateQ_pure, WriterT.run_pure', map_pure]
      rfl
  | query_bind input next ih =>
      simp only [simulateQ_query_bind, WriterT.run_bind', QueryImpl.ofLift_apply, ih, map_bind]
      change ((fun a ↦ (a, ([] : List L))) <$> (liftM (OW.query input) : OracleComp OW _)) >>= _ = _
      simp only [Functor.map_map]
      rfl

omit [Sphincs.Params] in
/-- A computation of the schemes' world, lifted into the reduction's and answered by the
multi-user game's oracles, logs nothing. -/
theorem run_simulateQ_τX_liftR (mk : Fin nx → LeanXmss.PublicKey × LeanXmss.Seeded.SecretKey)
    {α : Type} (oa : OracleComp OW α) :
    (simulateQ (τX mk) (liftR oa)).run = (·, []) <$> oa := by
  unfold liftR
  rw [← QueryImpl.simulateQ_compose]
  have h : (τX mk ∘ₛ fun t ↦ (liftM ((RSpec nx).query (.inl t)) : OracleComp (RSpec nx) _)) =
      QueryImpl.ofLift OW (WriterT (QueryLog (LeanXmss.MultiUser.SigningSpec nx)) (OracleComp OW)) := by
    funext t
    rw [QueryImpl.apply_compose, simulateQ_spec_query]
    rfl
  rw [h, run_simulateQ_ofLift_writer]

/-- The leaves of every leanXMSS log are distinct. -/
def XInv (st : SignState nx ns) : Prop := ∀ j, ((st.xlog j).map (·.1.1)).Nodup

omit [Sphincs.Params] in
/-- The log of key `j` of a log appended is the logs' appended. -/
theorem keyLog_append (l l' : QueryLog (LeanXmss.MultiUser.SigningSpec nx)) (j : Fin nx) :
    LeanXmss.MultiUser.keyLog (l ++ l') j =
      LeanXmss.MultiUser.keyLog l j ++ LeanXmss.MultiUser.keyLog l' j := by
  simp [LeanXmss.MultiUser.keyLog, List.filterMap_append]

/-- **One answer of the reduction, in the multi-user game**: the leaves stay distinct, and each
key's leanXMSS log grows by that key's part of the signing log. -/
theorem step_xLog (mk : Fin nx → LeanXmss.PublicKey × LeanXmss.Seeded.SecretKey)
    (keys : Keys nx ns) (t : (AdvSpec nx ns).Domain) (st : SignState nx ns) (hst : XInv st) :
    ∀ p ∈ support ((((τX mk).mapStateTBase (advImplX keys) t).run st).run),
      XInv p.1.2 ∧ ∀ j, conv (p.1.2.xlog j) = conv (st.xlog j) ++
        LeanXmss.MultiUser.keyLog p.2 j := by
  intro p hp
  rcases t with (t | ⟨j, req⟩) | q
  · simp only [QueryImpl.mapStateTBase, advImplX, StateT.run_mk, run_simulateQ_τX_liftR,
      support_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    rcases t with n | x
    · change q ∈ support (tw (coins ($ᵗ Fin (n + 1))) st) at hq
      rw [tw_coins, support_map] at hq
      obtain ⟨u, -, rfl⟩ := hq
      exact ⟨hst, fun j ↦ by simp [LeanXmss.MultiUser.keyLog]⟩
    · change q ∈ support (tw (hashQuery x) st) at hq
      rw [tw_hashQuery, support_map] at hq
      obtain ⟨u, -, rfl⟩ := hq
      exact ⟨hst, fun j ↦ by simp [LeanXmss.MultiUser.keyLog]⟩
  · simp only [QueryImpl.mapStateTBase, advImplX, StateT.run_mk] at hp
    by_cases h : ((st.xlog j).any fun e ↦ decide (e.1.1 = req.1)) = true
    · rw [run_xmssFwd_of_used h, simulateQ_pure, WriterT.run_pure', support_pure,
        Set.mem_singleton_iff] at hp
      subst hp
      exact ⟨hst, fun j ↦ by simp [LeanXmss.MultiUser.keyLog]⟩
    · rw [run_xmssFwd_of_fresh h, simulateQ_map, WriterT.run_map', simulateQ_spec_query,
        support_map] at hp
      obtain ⟨⟨σ, w⟩, hσ, rfl⟩ := hp
      change (σ, w) ∈ support (LeanXmss.MultiUser.signingOracle (fun j ↦ (mk j).2)
        ⟨j, ⟨req.1, req.2⟩⟩).run at hσ
      rw [LeanXmss.MultiUser.signingOracle, QueryImpl.run_withLogging_apply,
        mem_support_bind_iff] at hσ
      obtain ⟨σ', -, hσ⟩ := hσ
      simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hσ
      obtain ⟨rfl, rfl⟩ := hσ
      refine ⟨fun j' ↦ ?_, fun j' ↦ ?_⟩
      · by_cases hj : j' = j
        · subst hj
          simp only [Prod.map, id, Function.update_self, List.map_append, List.map_cons,
            List.map_nil]
          refine List.nodup_append.mpr ⟨hst j', List.nodup_singleton _, ?_⟩
          intro a ha b hb
          simp only [List.mem_singleton] at hb
          subst hb
          intro hab
          subst hab
          simp only [List.any_eq_true, decide_eq_true_eq, not_exists, not_and] at h
          obtain ⟨e, he, he'⟩ := List.mem_map.mp ha
          exact h e he he'
        · simp only [Prod.map, id, Function.update_of_ne hj]
          exact hst j'
      · by_cases hj : j' = j
        · subst hj
          simp [Prod.map, conv, LeanXmss.MultiUser.keyLog]
        · simp [Prod.map, conv, LeanXmss.MultiUser.keyLog, Function.update_of_ne hj, Ne.symm hj]
  · simp only [QueryImpl.mapStateTBase, advImplX, StateT.run_mk, run_simulateQ_τX_liftR,
      support_map] at hp
    obtain ⟨q', hq, rfl⟩ := hp
    have hx := xlog_tw_sphincsSign keys q.1 q.2 st q' hq
    refine ⟨fun j ↦ ?_, fun j ↦ ?_⟩
    · simp only at hx ⊢; rw [hx]; exact hst j
    · simp only at hx ⊢; rw [hx]; simp [LeanXmss.MultiUser.keyLog]

/-- **The reduction's answers to a whole adversary, in the multi-user game**: the leaves stay
distinct, and each key's leanXMSS log grows by that key's part of the signing log. -/
theorem adv_xLog (mk : Fin nx → LeanXmss.PublicKey × LeanXmss.Seeded.SecretKey)
    (keys : Keys nx ns) {α : Type} (oa : OracleComp (AdvSpec nx ns) α) :
    ∀ (st : SignState nx ns), XInv st →
      ∀ p ∈ support (((simulateQ ((τX mk).mapStateTBase (advImplX keys)) oa).run st).run),
        XInv p.1.2 ∧ ∀ j, conv (p.1.2.xlog j) = conv (st.xlog j) ++
          LeanXmss.MultiUser.keyLog p.2 j := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro st hst p hp
    simp only [simulateQ_pure, StateT.run_pure, WriterT.run_pure', support_pure,
      Set.mem_singleton_iff] at hp
    subst hp
    exact ⟨hst, fun j ↦ by simp [LeanXmss.MultiUser.keyLog]⟩
  | query_bind t k ih =>
    intro st hst p hp
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, WriterT.run_bind',
      mem_support_bind_iff] at hp
    obtain ⟨q, hq, hp⟩ := hp
    obtain ⟨hq1, hq2⟩ := step_xLog mk keys t st hst q hq
    rw [support_map] at hp
    obtain ⟨p', hp', rfl⟩ := hp
    obtain ⟨hp1, hp2⟩ := ih q.1.1 q.1.2 hq1 p' hp'
    refine ⟨hp1, fun j ↦ ?_⟩
    simp only [Prod.map, id, keyLog_append, hp2 j, hq2 j, List.append_assoc]

/-- **The reduction's signing log in the multi-user game**: on every reachable run, the final
leanXMSS logs have distinct leaves, and each is the multi-user log's part for its key. -/
theorem xCore_log (guest : Program) (fuel budget : ℕ) (A : GameAdversary nx ns)
    (mk : Fin nx → LeanXmss.PublicKey × LeanXmss.Seeded.SecretKey) :
    ∀ p ∈ support ((simulateQ (τX mk) (xCore guest fuel budget A (fun j ↦ (mk j).1))).run),
      (∀ j, (p.1.1.xmss j).1 = (mk j).1) ∧ XInv p.1.2.2.2.2 ∧
        ∀ j, conv (p.1.2.2.2.2.xlog j) = LeanXmss.MultiUser.keyLog p.2 j := by
  intro p hp
  unfold xCore at hp
  simp only [simulateQ_bind, WriterT.run_bind', run_simulateQ_τX_liftR, bind_map_left,
    mem_support_bind_iff, support_map, Set.mem_image] at hp
  obtain ⟨ss, -, q, ⟨a, ha, b, ⟨o, ho, c, hc, rfl⟩, rfl⟩, rfl⟩ := hp
  rw [QueryImpl.simulateQ_mapStateTBase_run] at ha
  have hinit : XInv (SignState.init nx ns) := fun j ↦ by simp [SignState.init]
  obtain ⟨hq1, hq2⟩ := adv_xLog mk _ _ _ hinit a ha
  simp only [simulateQ_pure, WriterT.run_pure', support_pure, Set.mem_singleton_iff] at hc
  subst hc
  obtain ⟨hx, -⟩ := keepsLogs_viRec budget guest a.1.1.2 fuel a.1.1.1 a.1.2 o ho
  refine ⟨fun j ↦ rfl, fun j ↦ ?_, fun j ↦ ?_⟩
  · simp only [Prod.map, id]
    rw [hx]
    exact hq1 j
  · have h2 := hq2 j
    simp only [SignState.init, conv, List.map_nil, List.nil_append] at h2
    simp only [Prod.map, id, hx, List.nil_append, keyLog_append]
    rw [conv, h2]
    simp [LeanXmss.MultiUser.keyLog]

/-! ## The reduction's win -/

/-- **The forgery's check in the multi-user game**: verify the forgery under the named key, and
judge it against that key's requests. -/
noncomputable def finishX [NeZero nx]
    (p : (Fin nx → LeanXmss.PublicKey × LeanXmss.Seeded.SecretKey) × BOut nx ns ×
      QueryLog (LeanXmss.MultiUser.SigningSpec nx)) : OracleComp OW Bool := do
  let f := forgeryOf p.2.1
  let verified ← liftM (LeanXmss.Concrete.verify (p.1 f.key).1 f.forgery.message
    f.forgery.signature : OracleComp LeanXmss.HashSpec Bool)
  return decide (LeanXmss.SigningTranscript.Valid (LeanXmss.MultiUser.keyLog p.2.2 f.key) ∧
    ¬LeanXmss.SigningTranscript.Contains (LeanXmss.MultiUser.keyLog p.2.2 f.key) f.forgery) &&
      verified

/-- **The multi-user game of the reduction** is its run, then the forgery's check. -/
theorem gameCore_xAdv [NeZero nx] (guest : Program) (fuel budget : ℕ) (A : GameAdversary nx ns) :
    LeanXmss.MultiUser.gameCore (xAdv guest fuel budget A) =
      xPrefix guest fuel budget A >>= finishX := by
  unfold LeanXmss.MultiUser.gameCore xPrefix xAdv finishX
  simp only [bind_assoc, pure_bind, simulateQ_map, WriterT.run_map', bind_map_left]
  rfl

/-- The cache `c` holds every entry of the trace `tr`, as outputs. -/
def CacheTr (c : QueryCache LeanXmss.HashSpec) (tr : Log) : Prop :=
  ∀ e ∈ tr, c e.1 = some (hBits e.2)

/-- `XWin` reads only the leanXMSS public keys. -/
theorem xWin_congr {a b : Fin nx → LeanXmss.PublicKey × LeanXmss.Seeded.SecretKey}
    (h : ∀ j, (a j).1 = (b j).1) (r : BOut nx ns) :
    XWin (fullOut a r).1 (fullOut a r).2 ↔ XWin (fullOut b r).1 (fullOut b r).2 := by
  simp only [XWin, fullOut, h]

omit [Sphincs.Params] in
/-- **The check of a forgery passes** when its signature is valid under a trace the cache
holds, the key's log has distinct leaves and no answered request for the message. -/
theorem run_finish_of {mk : Fin nx → LeanXmss.PublicKey × LeanXmss.Seeded.SecretKey}
    {log : QueryLog (LeanXmss.MultiUser.SigningSpec nx)} {j : Fin nx} {msg : LeanXmss.Message}
    {σ : LeanXmss.Signature} {tr : Log} {l : List (XmssRequest × Option LeanXmss.Signature)}
    {c : QueryCache LeanXmss.HashSpec} {pk : LeanXmss.PublicKey}
    (hσ : xmssVerifyWith (look tr) pk msg σ = some true) (hpk : pk = (mk j).1)
    (hforged : ∀ e ∈ l, e.1.2 = msg → e.2 = none) (hlog : conv l = LeanXmss.MultiUser.keyLog log j)
    (hnodup : (l.map (·.1.1)).Nodup) (hc : CacheTr c tr) :
    (simulateQ owImpl (do
      let verified ← liftM (LeanXmss.Concrete.verify (mk j).1 msg σ :
        OracleComp LeanXmss.HashSpec Bool)
      return decide (LeanXmss.SigningTranscript.Valid (LeanXmss.MultiUser.keyLog log j) ∧
        ¬LeanXmss.SigningTranscript.Contains (LeanXmss.MultiUser.keyLog log j) ⟨msg, σ⟩) &&
          verified : OracleComp OW Bool)).run' c = pure true := by
  have hcache : CacheHas c (look tr) := by
    intro x d hx
    obtain ⟨i, hi, hei, -⟩ := (look_eq_some_iff _ x d).mp hx
    have := hc _ (List.getElem_mem hi)
    rw [hei] at this
    exact this
  subst hpk
  have hver : (simulateQ (randomOracle : QueryImpl LeanXmss.HashSpec
      (StateT (QueryCache LeanXmss.HashSpec) ProbComp))
      (LeanXmss.Concrete.verify (mk j).1 msg σ : OracleComp LeanXmss.HashSpec Bool)).run c =
      pure (true, c) := run_verify_of_xmssVerifyWith hcache hσ
  simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind]
  rw [QueryImpl.simulateQ_add_liftM_right, hver]
  simp only [pure_bind, simulateQ_pure, StateT.run_pure, map_pure, Bool.and_true]
  rw [← hlog]
  congr 1
  simp only [decide_eq_true_eq]
  refine ⟨?_, ?_⟩
  · simpa [LeanXmss.SigningTranscript.Valid, conv, List.map_map, Function.comp_def] using hnodup
  · rintro ⟨e, he, hm, hs⟩
    obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
    simp at hm hs
    rw [hforged e' he' hm] at hs
    exact absurd hs (by simp)

/-- **The forgery's check passes** on a reachable run of the reduction that wins in the game,
from a cache holding V_I's trace. -/
theorem run_finishX [NeZero nx] {guest : Program} {fuel budget : ℕ} {A : GameAdversary nx ns}
    {y : ((Fin nx → LeanXmss.PublicKey × LeanXmss.Seeded.SecretKey) × BOut nx ns ×
      QueryLog (LeanXmss.MultiUser.SigningSpec nx)) × QueryCache LeanXmss.HashSpec}
    (hy : y.1 ∈ support (xPrefix guest fuel budget A))
    (hw : XWin (fullOut y.1.1 y.1.2.1).1 (fullOut y.1.1 y.1.2.1).2)
    (hc : CacheTr y.2 (fullOut y.1.1 y.1.2.1).2) :
    (simulateQ owImpl (finishX y.1)).run' y.2 = pure true := by
  obtain ⟨⟨mk, r, log⟩, c⟩ := y
  simp only at hy hw hc ⊢
  unfold xPrefix at hy
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hy
  obtain ⟨mk', -, p, hp, rfl, rfl, rfl⟩ := hy
  obtain ⟨hkeys, hinv, hlog⟩ := xCore_log guest fuel budget A mk p hp
  have hw' := (xWin_congr (fun j ↦ (hkeys j)) p.1).mpr hw
  unfold finishX forgeryOf
  simp only [hw', ↓reduceDIte]
  obtain ⟨-, hforged, hσ⟩ := hw'.2.choose_spec.choose_spec.choose_spec
  simp only [fullOut] at hσ hforged hc
  exact run_finish_of hσ (hkeys _) hforged (hlog _) (hinv _) hc

/-! ## The bound -/

/-- **A leanXMSS forgery** (`Forged`'s first part): a leanXMSS claim of the root statement for an
honest key on a message no request to that key was answered for. -/
def ForgedX (z : GameOutcome nx ns) : Prop :=
  ∃ j : Fin nx, ∃ msg, ((z.keys.xmss j).1, msg) ∈ z.statement.claims.xmss ∧
    ∀ e ∈ z.state.xlog j, e.1.2 = msg → e.2 = none

omit [Sphincs.Params] in
/-- A draw followed by a continuation that returns `true` wherever an event holds wins at least
as often as the event. -/
theorem le_prEvent_bind_of_pure {α : Type} (mx : ProbComp α) (f : α → ProbComp Bool)
    (p : α → Prop) (h : ∀ a ∈ support mx, p a → f a = pure true) :
    Pr{let a ← mx}[p a] ≤ Pr{let b ← mx >>= f}[b = true] := by
  classical
  calc Pr{let a ← mx}[p a] = Pr{let a ← mx >>= pure}[p a] := by rw [bind_pure]
    _ ≤ Pr{let b ← mx >>= f}[b = true] := by
      refine prEvent_bind_mono_of_forall_le_of_support _ _ _ _ _ fun a ha ↦ ?_
      rw [prEvent_pure]
      split_ifs with hp
      · rw [h a ha hp, prEvent_pure]; simp
      · exact zero_le

omit [Sphincs.Params] in
/-- The multi-user game's advantage, its count forgotten. -/
theorem forgeAdvantage_eq (adv : LeanXmss.MultiUser.Adversary nx) :
    LeanXmss.MultiUser.forgeAdvantage adv =
      Pr{let b ← (simulateQ owImpl (LeanXmss.MultiUser.gameCore adv)).run' ∅}[b = true] := by
  have h := QueryImpl.fst_map_run_withCost (m := StateT (QueryCache LeanXmss.HashSpec) ProbComp)
    owImpl (fun t ↦ Multiplicative.ofAdd (match t with | .inl _ => (0 : ℕ) | .inr _ => 1))
    (LeanXmss.MultiUser.gameCore adv)
  have key : Prod.fst <$> ((simulateQ (owImpl.withCost
      (fun t ↦ Multiplicative.ofAdd (match t with | .inl _ => (0 : ℕ) | .inr _ => 1)))
        (LeanXmss.MultiUser.gameCore adv)).run).run' ∅ =
      (simulateQ owImpl (LeanXmss.MultiUser.gameCore adv)).run' ∅ := by
    rw [StateT.run'_eq, StateT.run'_eq, Functor.map_map, ← h, StateT.run_map, Functor.map_map]
  rw [← key, prEvent_map]
  rfl

/-- **On the game with V_I's trace, a leanXMSS forgery on a good log is a win of the trace**: V_I
accepts, the forged claim has a signature valid under the trace's answers (T4 at the trace,
`aggregate_knowledge_sub`), and the final log's cache holds the trace. -/
theorem xWin_of_gameRec
    (hG : ∀ (ℓ : Log) (rows : List BlakeRow) (h : TableOK (look ℓ) rows),
      Guest.Located.GuestHypsM (Guest.Value.HashModel.oracle rows ℓ h))
    {fuel budget : ℕ} {A : GameAdversary nx ns} {p : (GameOutcome nx ns × Log) × Log}
    (hp : p ∈ support (gameRec Guest.guest fuel budget A)) (ha : p.1.1.accepted = true)
    (hf : ForgedX p.1.1) (hbad : ¬ AggBad p.2) :
    XWin p.1.1 p.1.2 ∧ CacheTr (logCache p.2) p.1.2 := by
  obtain ⟨hsub, hv⟩ := gameRec_trace hp
  have hk := aggregate_knowledge_sub (hG p.2) (hG p.1.2) hbad hsub.lookSub (hv ha)
  obtain ⟨j, msg, hmem, hforged⟩ := hf
  obtain ⟨σ, hσ⟩ := hk.1 _ hmem
  refine ⟨⟨ha, j, msg, σ, hmem, hforged, hσ⟩, fun e he ↦ ?_⟩
  rw [logCache_apply, hsub e he]
  rfl

/-- **The leanXMSS reduction (T5, leanXMSS part).** In the game of the deployed guest, V_I
accepting a root statement with a leanXMSS forgery on a log without the chain's bad events is at
most as likely as the reduction's win in leanXMSS's multi-user game, if the guest's open callees
are sound over every oracle model. -/
theorem prEvent_forgedX_le [NeZero nx]
    (hG : ∀ (ℓ : Log) (rows : List BlakeRow) (h : TableOK (look ℓ) rows),
      Guest.Located.GuestHypsM (Guest.Value.HashModel.oracle rows ℓ h))
    (fuel budget : ℕ) (A : GameAdversary nx ns) :
    Pr{let z ← game Guest.guest fuel budget A}[z.1.accepted = true ∧ ForgedX z.1 ∧ ¬ AggBad z.2] ≤
      LeanXmss.MultiUser.forgeAdvantage (xAdv Guest.guest fuel budget A) := by
  let F : (GameOutcome nx ns × Log) × QueryCache LeanXmss.HashSpec → Prop :=
    fun o ↦ XWin o.1.1 o.1.2 ∧ CacheTr o.2 o.1.2
  calc Pr{let z ← game Guest.guest fuel budget A}[z.1.accepted = true ∧ ForgedX z.1 ∧ ¬ AggBad z.2]
      = Pr{let p ← gameRec Guest.guest fuel budget A}[p.1.1.accepted = true ∧ ForgedX p.1.1 ∧
          ¬ AggBad p.2] := by
        rw [← gameRec_map, prEvent_map]
    _ ≤ Pr{let p ← gameRec Guest.guest fuel budget A}[F (p.1, logCache p.2)] :=
        prEvent_mono_of_support _ _ _ fun p hp h ↦ xWin_of_gameRec hG hp h.1 h.2.1 h.2.2
    _ = Pr{let o ← Prod.map id logCache <$> gameRec Guest.guest fuel budget A}[F o] := by
        rw [prEvent_map]; rfl
    _ = Pr{let o ← (simulateQ owImpl (simulateQ toW
          (gameCompRec Guest.guest fuel budget A))).run ∅}[F o] :=
        (evalDistEq_run_toW_nil _).prEvent_eq F
    _ = Pr{let y ← (simulateQ owImpl (xPrefix Guest.guest fuel budget A)).run ∅}[
          F (fullOut y.1.1 y.1.2.1, y.2)] := by
        rw [← map_xPrefix, simulateQ_map, StateT.run_map, prEvent_map]
    _ ≤ Pr{let b ← (simulateQ owImpl (xPrefix Guest.guest fuel budget A)).run ∅ >>= fun y ↦
          (simulateQ owImpl (finishX y.1)).run' y.2}[b = true] := by
        refine le_prEvent_bind_of_pure _ _ (fun y : ((Fin nx → LeanXmss.PublicKey ×
            LeanXmss.Seeded.SecretKey) × BOut nx ns × QueryLog (LeanXmss.MultiUser.SigningSpec nx)) ×
            QueryCache LeanXmss.HashSpec ↦ F (fullOut y.1.1 y.1.2.1, y.2))
          fun y hy hF ↦ run_finishX (guest := Guest.guest) (fuel := fuel) (budget := budget)
            (A := A) ?_ hF.1 hF.2
        have h1 : y.1 ∈ support ((simulateQ owImpl (xPrefix Guest.guest fuel budget A)).run' ∅) := by
          rw [StateT.run'_eq, support_map]; exact ⟨y, hy, rfl⟩
        exact support_simulateQ_run'_subset _ _ _ h1
    _ = LeanXmss.MultiUser.forgeAdvantage (xAdv Guest.guest fuel budget A) := by
        rw [forgeAdvantage_eq, gameCore_xAdv, simulateQ_bind, StateT.run'_eq, StateT.run_bind,
          map_bind]
        simp only [StateT.run'_eq, map_bind]

/-! ## The reduction's hash calls -/

/-- **The reduction's multi-user game makes at most the game's hash queries and one final
verification's.** -/
theorem isQueryBoundP_gameCore_xAdv [NeZero nx] {guest : Program} {fuel budget : ℕ}
    {A : GameAdversary nx ns} {Q cx : ℕ} (hQ : IsQueryBoundP (gameComp guest fuel budget A) IsHash Q)
    (hv : ∀ pk msg σ, IsTotalQueryBound
      (LeanXmss.Concrete.verify pk msg σ : OracleComp LeanXmss.HashSpec Bool) cx) :
    IsQueryBoundP (LeanXmss.MultiUser.gameCore (xAdv guest fuel budget A)) IsHashW (Q + cx) := by
  rw [gameCore_xAdv]
  refine isQueryBoundP_bind (n := Q) (m := cx) ?_ fun y _ ↦ ?_
  · have h1 : IsQueryBoundP (gameCompRec guest fuel budget A) IsHash Q := by
      rw [← isQueryBoundP_map_iff (f := Prod.fst), gameCompRec_map]; exact hQ
    have h2 := isQueryBoundP_simulateQ_toW _ _ h1
    rw [← map_xPrefix, isQueryBoundP_map_iff] at h2
    exact h2
  · unfold finishX
    exact (isQueryBoundP_bind (n := cx) (m := 0) (isQueryBoundP_liftM_hash _ _ (hv _ _ _))
      fun _ _ ↦ by simp).mono (by omega)

/-- **The reduction's hash-call budget** in leanXMSS's multi-user game: the game's `Q` and one
final verification's `cx`. -/
theorem hasHashQueryBound_xAdv [NeZero nx] {guest : Program} {fuel budget : ℕ}
    {A : GameAdversary nx ns} {Q cx : ℕ} (hQ : IsQueryBoundP (gameComp guest fuel budget A) IsHash Q)
    (hv : ∀ pk msg σ, IsTotalQueryBound
      (LeanXmss.Concrete.verify pk msg σ : OracleComp LeanXmss.HashSpec Bool) cx) :
    LeanXmss.MultiUser.HasHashQueryBound (xAdv guest fuel budget A) (Q + cx) := by
  intro result hr
  unfold LeanXmss.MultiUser.experiment at hr
  rw [StateT.run'_eq] at hr
  erw [support_map] at hr
  obtain ⟨r, hr, rfl⟩ := hr
  exact count_le_of_isQueryBoundP owImpl _ _ (isQueryBoundP_gameCore_xAdv hQ hv) ∅ r hr

end XmssRed

end
end LeanVM.E2E
