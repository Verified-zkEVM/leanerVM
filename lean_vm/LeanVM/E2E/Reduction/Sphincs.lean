/-
  LeanVM.E2E.Reduction.Sphincs

  The leanSPHINCS reduction of T5: an adversary against leanSPHINCS's multi-user game that runs
  the whole end-to-end game with the multi-user game's keys, signing oracles and hash, and outputs
  the forged claim's signature V_I's trace knows.
-/

module

public import LeanVM.E2E.Reduction.Xmss

/-!
# The leanSPHINCS reduction

**The adversary** (`sAdv`). Against `n_s` leanSPHINCS keys (`Sphincs.Security.Multi`), it receives
their public keys and runs the game with V_I's trace in the schemes' world: it generates the
leanXMSS keys itself, answers the adversary's coins, hash queries and leanXMSS requests as the
game does, and its leanSPHINCS requests as the game does but with the multi-user game's signing
oracle in place of the signer (`sphincsFwd`: past `signatureLimit` requests refused, else the
request forwarded and recorded); then V_I with its trace. It outputs, for a forged leanSPHINCS
claim of the root with a signature valid under the trace's answers (`SWin`), that signature
(`forgeryOfS`).

**Its run is the game's, in distribution.** The multi-user game generates the leanSPHINCS keys
first, from seeds drawn at once; the game generates the leanXMSS keys first, each leanSPHINCS key
from its own seed. With the keys fixed, the reduction's run, its signing log forgotten, is the
rest of the translated game (`map_sCore`); in the schemes' lazy random oracle the key
generations commute and the seeds may be drawn in either way (`romRun_bind_comm`,
`romRun_sKeygenAll`), so the reduction's run and the translated game have the same distribution
of outcome, trace and cache (`evalDistEq_sPrefix`).
-/

namespace LeanVM.E2E

open LeanVM.Parameters LeanVM.Semantics LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Rom
open OracleSpec OracleComp
open scoped ENNReal

@[expose] public section

namespace SphincsRed

open XmssRed (map_eq_bind_pure_comp' le_prEvent_bind_of_pure CacheTr)

variable {nx ns : ℕ} [Sphincs.Params]

/-- The reduction's world: the schemes' world and the multi-user leanSPHINCS signing oracle. -/
abbrev RSpec (ns : ℕ) := OW + Sphincs.Security.Multi.SigningSpec ns

/-- A computation of the schemes' world in the reduction's. -/
noncomputable def liftR {α : Type} (oa : OracleComp OW α) : OracleComp (RSpec ns) α :=
  simulateQ (fun t ↦ (liftM ((RSpec ns).query (.inl t)) : OracleComp (RSpec ns) _)) oa

/-- **The forwarded leanSPHINCS request** of key `j`: past `signatureLimit` forwarded requests
refused; otherwise the request sent to the multi-user signing oracle, and the request and its
answer recorded (`sphincsSign` with the signer replaced by the oracle). -/
noncomputable def sphincsFwd (j : Fin ns) (msg : Sphincs.Message) :
    StateT (SignState nx ns) (OracleComp (RSpec ns)) (Option Sphincs.Signature) := do
  if Sphincs.signatureLimit ≤ ((← get).slog j).length then return none
  let σ ← (liftM (liftM ((RSpec ns).query (.inr (j, msg))) :
    OracleComp (RSpec ns) (Option Sphincs.Signature)) :
      StateT (SignState nx ns) (OracleComp (RSpec ns)) (Option Sphincs.Signature))
  modify fun st ↦ { st with slog := Function.update st.slog j (st.slog j ++ [(msg, σ)]) }
  pure σ

/-! ## The multi-user game's oracles -/

/-- The multi-user game's signing oracle, its world the schemes'. -/
noncomputable def sigOW (sk : Fin ns → Sphincs.PublicKey × Sphincs.Seeded.SecretKey) :
    QueryImpl (Sphincs.Security.Multi.SigningSpec ns)
      (WriterT (QueryLog (Sphincs.Security.Multi.SigningSpec ns)) (OracleComp OW)) :=
  Sphincs.Security.Multi.signingOracle sk

/-- The multi-user game's oracles for the reduction, with the keys `sk`: the schemes' world
passed through, the signing requests answered by the keys' signers and logged. -/
noncomputable abbrev τS (sk : Fin ns → Sphincs.PublicKey × Sphincs.Seeded.SecretKey) :
    QueryImpl (RSpec ns)
      (WriterT (QueryLog (Sphincs.Security.Multi.SigningSpec ns)) (OracleComp OW)) :=
  QueryImpl.ofLift OW (WriterT (QueryLog (Sphincs.Security.Multi.SigningSpec ns)) (OracleComp OW)) +
    sigOW sk

/-- The multi-user game's oracles, the log forgotten. -/
noncomputable def σS (sk : Fin ns → Sphincs.PublicKey × Sphincs.Seeded.SecretKey) :
    QueryImpl (RSpec ns) (OracleComp OW) :=
  fun t ↦ Prod.fst <$> (τS sk t).run

/-- The forgetful oracles on the schemes' world are its queries. -/
theorem σS_inl (sk : Fin ns → Sphincs.PublicKey × Sphincs.Seeded.SecretKey) (t : OW.Domain) :
    σS sk (.inl t) = (liftM (OW.query t) : OracleComp OW _) := by
  simp only [σS, τS, QueryImpl.add_apply_inl, QueryImpl.ofLift_apply]
  change Prod.fst <$> (monadLift (liftM (OW.query t) : OracleComp OW _) :
    WriterT (QueryLog (Sphincs.Security.Multi.SigningSpec ns)) (OracleComp OW) _).run = _
  rw [WriterT.run_monadLift', Functor.map_map]
  exact id_map _

/-- The forgetful oracles on a signing request are the key's signer. -/
theorem σS_inr (sk : Fin ns → Sphincs.PublicKey × Sphincs.Seeded.SecretKey)
    (q : Fin ns × Sphincs.Message) :
    σS sk (.inr q) = sLift (Sphincs.Seeded.sign (sk q.1).2 q.2 : OracleComp Sphincs.HashSpec _) := by
  have h : Prod.fst <$> (Sphincs.Security.Multi.signingOracle sk q).run =
      (liftM (Sphincs.Seeded.sign (sk q.1).2 q.2 : OracleComp Sphincs.HashSpec _) :
        OracleComp Sphincs.OracleWorld _) := by
    rw [Sphincs.Security.Multi.signingOracle, QueryImpl.run_withLogging_apply]
    simp
  exact h

/-- A computation of the schemes' world, lifted into the reduction's and answered by the
forgetful oracles, is itself. -/
theorem simulateQ_σS_liftR (sk : Fin ns → Sphincs.PublicKey × Sphincs.Seeded.SecretKey)
    {α : Type} (oa : OracleComp OW α) : simulateQ (σS sk) (liftR oa) = oa := by
  unfold liftR
  rw [← QueryImpl.simulateQ_compose]
  conv_rhs => rw [← simulateQ_ofLift_eq_self oa]
  congr 1

/-- A forwarded request past the limit is refused. -/
theorem run_sphincsFwd_of_full {j : Fin ns} {msg : Sphincs.Message} {st : SignState nx ns}
    (h : Sphincs.signatureLimit ≤ (st.slog j).length) :
    (sphincsFwd j msg).run st = pure (none, st) := by
  simp [sphincsFwd, h]

/-- A forwarded request within the limit: the oracle's answer, recorded. -/
theorem run_sphincsFwd_of_room {j : Fin ns} {msg : Sphincs.Message} {st : SignState nx ns}
    (h : ¬ Sphincs.signatureLimit ≤ (st.slog j).length) :
    (sphincsFwd j msg).run st =
      (fun σ ↦ (σ, { st with slog := Function.update st.slog j (st.slog j ++ [(msg, σ)]) })) <$>
        (liftM ((RSpec ns).query (.inr (j, msg))) :
          OracleComp (RSpec ns) (Option Sphincs.Signature)) := by
  simp only [sphincsFwd, h, ↓reduceIte, StateT.run_bind, StateT.run_get,
    pure_bind, OracleComp.liftM_run_StateT, bind_assoc, StateT.run_modify, StateT.run_pure,
    map_eq_bind_pure_comp]
  rfl

/-- **The reduction's answers to the adversary**: the game's (`advImpl`, translated), the
leanSPHINCS requests forwarded. -/
noncomputable def advImplS (keys : Keys nx ns) :
    QueryImpl (AdvSpec nx ns) (StateT (SignState nx ns) (OracleComp (RSpec ns)))
  | .inl t => StateT.mk fun st ↦ liftR (tw (advImpl keys (.inl t)) st)
  | .inr q => sphincsFwd q.1 q.2

/-- The secret key the reduction places for the keys under attack; never used. -/
def dummyKey : Sphincs.Seeded.SecretKey := ⟨0, 0, 0⟩

/-- **The reduction's run** with the leanSPHINCS public keys `spks`. -/
noncomputable def sCore (guest : Program) (fuel budget : ℕ) (A : GameAdversary nx ns)
    (spks : Fin ns → Sphincs.PublicKey) : OracleComp (RSpec ns) (XmssRed.BOut nx ns) := do
  let xs ← liftR (LeanXmss.Concrete.sequenceFin fun _ : Fin nx ↦ LeanXmss.MultiUser.keygen)
  let keys : Keys nx ns := ⟨xs, fun j ↦ (spks j, dummyKey)⟩
  let (sip, st) ← (simulateQ (advImplS keys)
    (A (fun j ↦ (keys.xmss j).1) (fun j ↦ (keys.sphincs j).1))).run (SignState.init nx ns)
  let (o, st') ← liftR (tw (viRec budget guest sip.2 fuel sip.1) st)
  pure (keys, sip.1, sip.2, o, st')

/-- The game's outcome and V_I's trace of a run of the reduction, with the leanSPHINCS keys `sk`. -/
def fullOut (sk : Fin ns → Sphincs.PublicKey × Sphincs.Seeded.SecretKey) (r : XmssRed.BOut nx ns) :
    GameOutcome nx ns × Log :=
  (⟨⟨r.1.xmss, sk⟩, r.2.1, r.2.2.1, (r.2.2.2.1.map Prod.fst).getD false, r.2.2.2.2⟩,
    (r.2.2.2.1.map Prod.snd).getD [])

/-- **The reduction's win in the game**: V_I accepts, and a leanSPHINCS claim of the root for an
honest key `j` on a message no request to key `j` was answered for has a signature valid under
the trace's answers. -/
def SWin (z : GameOutcome nx ns) (tr : Log) : Prop :=
  z.accepted = true ∧ ∃ j : Fin ns, ∃ msg σ, ((z.keys.sphincs j).1, msg) ∈ z.statement.claims.sphincs ∧
    (∀ e ∈ z.state.slog j, e.1 = msg → e.2 = none) ∧
    sphincsVerifyWith (look tr) (z.keys.sphincs j).1 msg σ = some true

/-- A leanSPHINCS signature, never used: the reduction's output when it has no forgery. -/
def dummySig : Sphincs.Signature :=
  ⟨0, fun _ ↦ ⟨fun _ ↦ ⟨fun _ ↦ 0, fun _ ↦ 0⟩, fun _ ↦ 0⟩, fun _ ↦ ⟨0, fun _ ↦ 0, fun _ ↦ 0⟩⟩

open Classical in
/-- **The reduction's forgery**: the forged claim's key, message and signature when the run wins
(`SWin`), a dummy otherwise. -/
noncomputable def forgeryOfS [NeZero ns] (r : XmssRed.BOut nx ns) :
    Sphincs.Security.Multi.Forgery ns :=
  if h : SWin (fullOut r.1.sphincs r).1 (fullOut r.1.sphincs r).2 then
    ⟨h.2.choose, h.2.choose_spec.choose, h.2.choose_spec.choose_spec.choose⟩
  else ⟨0, 0, dummySig⟩

/-- **The leanSPHINCS reduction**: the game run with the multi-user game's keys, signing oracles
and hash; the forged claim's signature its trace knows. -/
noncomputable def sAdv [NeZero ns] (guest : Program) (fuel budget : ℕ) (A : GameAdversary nx ns) :
    Sphincs.Security.Multi.Adversary ns where
  main spks := forgeryOfS <$> sCore guest fuel budget A spks

/-! ## The reduction's run is the game's -/

/-- The forwarded request, answered by the keys' signers, is the game's signing oracle. -/
theorem simulateQ_sphincsFwd (xs : Fin nx → LeanXmss.PublicKey × LeanXmss.Seeded.SecretKey)
    (sk : Fin ns → Sphincs.PublicKey × Sphincs.Seeded.SecretKey) (j : Fin ns)
    (msg : Sphincs.Message) (st : SignState nx ns) :
    simulateQ (σS sk) ((sphincsFwd j msg).run st) = tw (sphincsSign ⟨xs, sk⟩ j msg) st := by
  by_cases h : Sphincs.signatureLimit ≤ (st.slog j).length
  · rw [run_sphincsFwd_of_full h]
    unfold sphincsSign
    simp [h, tw]
  · rw [run_sphincsFwd_of_room h, simulateQ_map, simulateQ_spec_query, σS_inr]
    unfold sphincsSign
    simp only [h, ↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind, tw, simulateQ_bind]
    have h₁ := tw_sphincsRun (nx := nx) (ns := ns)
      (Sphincs.Seeded.sign (sk j).2 msg : OracleComp Sphincs.HashSpec _) st
    unfold tw at h₁
    rw [h₁]
    simp only [simulateQ_pure, pure_bind, StateT.run_modify, bind_assoc,
      StateT.run_pure, map_eq_bind_pure_comp]
    rfl

/-- **The reduction answers the adversary as the game does**: its handler, its signing requests
answered by the keys' signers, is the game's, translated. -/
theorem mapStateTBase_advImplS (xs : Fin nx → LeanXmss.PublicKey × LeanXmss.Seeded.SecretKey)
    (sk : Fin ns → Sphincs.PublicKey × Sphincs.Seeded.SecretKey) :
    (σS sk).mapStateTBase (advImplS ⟨xs, fun j ↦ ((sk j).1, dummyKey)⟩) =
      toW.mapStateTBase (advImpl ⟨xs, sk⟩) := by
  funext t
  rcases t with t | q
  · simp only [QueryImpl.mapStateTBase, advImplS, StateT.run_mk, simulateQ_σS_liftR]
    have : advImpl (⟨xs, fun j ↦ ((sk j).1, dummyKey)⟩ : Keys nx ns) (.inl t) =
        advImpl ⟨xs, sk⟩ (.inl t) := by
      simp only [advImpl, QueryImpl.add_apply_inl]
      rfl
    rw [this]
    rfl
  · simp only [QueryImpl.mapStateTBase, advImplS]
    exact congrArg StateT.mk (funext fun st ↦ simulateQ_sphincsFwd xs sk q.1 q.2 st)

/-- **With the leanSPHINCS keys fixed, the reduction's run is the rest of the game**: its
signing log forgotten, the leanXMSS keys, then the rest of the translated game at all the keys. -/
theorem map_sCore (guest : Program) (fuel budget : ℕ) (A : GameAdversary nx ns)
    (sk : Fin ns → Sphincs.PublicKey × Sphincs.Seeded.SecretKey) :
    (fun p ↦ fullOut sk p.1) <$>
        (simulateQ (τS sk) (sCore guest fuel budget A (fun j ↦ (sk j).1))).run =
      LeanXmss.Concrete.sequenceFin (fun _ : Fin nx ↦ LeanXmss.MultiUser.keygen) >>= fun xs ↦
        gameRest guest fuel budget A ⟨xs, sk⟩ := by
  have h := fst_map_run_simulateQ_writer' (τS sk) (sCore guest fuel budget A (fun j ↦ (sk j).1))
  have hm : (fun p ↦ fullOut sk p.1) <$>
      (simulateQ (τS sk) (sCore guest fuel budget A (fun j ↦ (sk j).1))).run =
      fullOut sk <$> (Prod.fst <$>
        (simulateQ (τS sk) (sCore guest fuel budget A (fun j ↦ (sk j).1))).run) := by
    rw [Functor.map_map]
  rw [hm, h]
  change fullOut sk <$> simulateQ (σS sk) (sCore guest fuel budget A (fun j ↦ (sk j).1)) = _
  unfold sCore gameRest
  simp only [simulateQ_bind, simulateQ_σS_liftR, simulateQ_pure, map_bind, map_pure]
  refine bind_congr fun xs ↦ ?_
  rw [QueryImpl.simulateQ_mapStateTBase_run, mapStateTBase_advImplS, ←
    QueryImpl.simulateQ_mapStateTBase_run]
  rfl

/-- The multi-user game's run of the reduction, before the forgery's check: the seeds, the keys,
the reduction's run and the signing log. -/
noncomputable def sPrefix (guest : Program) (fuel budget : ℕ) (A : GameAdversary nx ns) :
    OracleComp OW ((Fin ns → Sphincs.PublicKey × Sphincs.Seeded.SecretKey) × XmssRed.BOut nx ns ×
      QueryLog (Sphincs.Security.Multi.SigningSpec ns)) := do
  let seeds ← (liftM (Sphincs.Security.Multi.sampleSeeds ns) : OracleComp OW _)
  let sk ← sLift (Sphincs.Security.Multi.keygenAll ns seeds)
  let p ← (simulateQ (τS sk) (sCore guest fuel budget A (fun j ↦ (sk j).1))).run
  pure (sk, p.1, p.2)

/-- **The reduction's run has the game's distribution**: in the schemes' random oracle, its
outcome, trace and final cache are distributed as the translated game's. -/
theorem evalDistEq_sPrefix (guest : Program) (fuel budget : ℕ) (A : GameAdversary nx ns) :
    Prod.map (fun p ↦ fullOut p.1 p.2.1) id <$> romRun (sPrefix guest fuel budget A) ∅ =ᵈ
      romRun (simulateQ toW (gameCompRec guest fuel budget A)) ∅ := by
  have h1 : Prod.map (fun p ↦ fullOut p.1 p.2.1) id <$> romRun (sPrefix guest fuel budget A) ∅ =
      romRun ((liftM (Sphincs.Security.Multi.sampleSeeds ns) : OracleComp OW _) >>= fun seeds ↦
        sLift (Sphincs.Security.Multi.keygenAll ns seeds) >>= fun sk ↦
          LeanXmss.Concrete.sequenceFin (fun _ : Fin nx ↦ LeanXmss.MultiUser.keygen) >>= fun xs ↦
            gameRest guest fuel budget A ⟨xs, sk⟩) ∅ := by
    have h0 : (fun p ↦ fullOut p.1 p.2.1) <$> sPrefix guest fuel budget A =
        (liftM (Sphincs.Security.Multi.sampleSeeds ns) : OracleComp OW _) >>= fun seeds ↦
          sLift (Sphincs.Security.Multi.keygenAll ns seeds) >>= fun sk ↦
            LeanXmss.Concrete.sequenceFin (fun _ : Fin nx ↦ LeanXmss.MultiUser.keygen) >>=
              fun xs ↦ gameRest guest fuel budget A ⟨xs, sk⟩ := by
      unfold sPrefix
      simp only [map_bind, map_pure]
      refine bind_congr fun seeds ↦ bind_congr fun sk ↦ ?_
      rw [← map_sCore, map_eq_bind_pure_comp]
      rfl
    rw [← h0]
    unfold romRun
    rw [simulateQ_map, StateT.run_map]
    rfl
  rw [h1, toW_gameCompRec]
  refine EvalDistEq.trans (m' := ProbComp) (romRun_sKeygenAll _ ∅) ?_
  exact romRun_bind_comm _ _ (fun sk xs ↦ gameRest guest fuel budget A ⟨xs, sk⟩) ∅

/-! ## The reduction's signing log -/

/-- The requests to key `j` of the multi-user signing log and their answers. -/
def sKeyLog (log : QueryLog (Sphincs.Security.Multi.SigningSpec ns)) (j : Fin ns) :
    List (Sphincs.Message × Option Sphincs.Signature) :=
  log.filterMap fun e ↦ if e.1.1 = j then some (e.1.2, e.2) else none

omit [Sphincs.Params] in
/-- The log of key `j` of a log appended is the logs' appended. -/
theorem sKeyLog_append (l l' : QueryLog (Sphincs.Security.Multi.SigningSpec ns)) (j : Fin ns) :
    sKeyLog (l ++ l') j = sKeyLog l j ++ sKeyLog l' j := by
  simp [sKeyLog, List.filterMap_append]

/-- A computation of the schemes' world, lifted into the reduction's and answered by the
multi-user game's oracles, logs nothing. -/
theorem run_simulateQ_τS_liftR (sk : Fin ns → Sphincs.PublicKey × Sphincs.Seeded.SecretKey)
    {α : Type} (oa : OracleComp OW α) :
    (simulateQ (τS sk) (liftR oa)).run = (·, []) <$> oa := by
  unfold liftR
  rw [← QueryImpl.simulateQ_compose]
  have h : (τS sk ∘ₛ fun t ↦ (liftM ((RSpec ns).query (.inl t)) : OracleComp (RSpec ns) _)) =
      QueryImpl.ofLift OW
        (WriterT (QueryLog (Sphincs.Security.Multi.SigningSpec ns)) (OracleComp OW)) := by
    funext t
    rw [QueryImpl.apply_compose, simulateQ_spec_query]
    rfl
  rw [h, XmssRed.run_simulateQ_ofLift_writer]

/-- The multi-user signing oracle logs its request and answer. -/
theorem mem_support_signingOracle {sk : Fin ns → Sphincs.PublicKey × Sphincs.Seeded.SecretKey}
    {q : Fin ns × Sphincs.Message} {σ : Option Sphincs.Signature}
    {w : QueryLog (Sphincs.Security.Multi.SigningSpec ns)}
    (h : (σ, w) ∈ support (Sphincs.Security.Multi.signingOracle sk q).run) : w = [⟨q, σ⟩] := by
  rw [Sphincs.Security.Multi.signingOracle, QueryImpl.run_withLogging_apply,
    mem_support_bind_iff] at h
  obtain ⟨σ', -, h⟩ := h
  simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  rfl

/-- No leanSPHINCS log is past the limit. -/
def SInv (st : SignState nx ns) : Prop := ∀ j, (st.slog j).length ≤ Sphincs.signatureLimit

/-- **One answer of the reduction, in the multi-user game**: no log passes the limit, and each
key's leanSPHINCS log grows by that key's part of the signing log. -/
theorem step_sLog (sk : Fin ns → Sphincs.PublicKey × Sphincs.Seeded.SecretKey)
    (keys : Keys nx ns) (t : (AdvSpec nx ns).Domain) (st : SignState nx ns) (hst : SInv st) :
    ∀ p ∈ support ((((τS sk).mapStateTBase (advImplS keys) t).run st).run),
      SInv p.1.2 ∧ ∀ j, p.1.2.slog j = st.slog j ++ sKeyLog p.2 j := by
  intro p hp
  rcases t with t | ⟨j, msg⟩
  · simp only [QueryImpl.mapStateTBase, advImplS, StateT.run_mk, run_simulateQ_τS_liftR,
      support_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    have hs : q.2.slog = st.slog := by
      rcases t with (n | x) | ⟨j, req⟩
      · change q ∈ support (tw (coins ($ᵗ Fin (n + 1))) st) at hq
        rw [tw_coins, support_map] at hq
        obtain ⟨u, -, rfl⟩ := hq
        rfl
      · change q ∈ support (tw (hashQuery x) st) at hq
        rw [tw_hashQuery, support_map] at hq
        obtain ⟨u, -, rfl⟩ := hq
        rfl
      · exact slog_tw_xmssSign keys j req st q hq
    refine ⟨fun j ↦ ?_, fun j ↦ ?_⟩
    · simp only; rw [hs]; exact hst j
    · simp only; rw [hs]; simp [sKeyLog]
  · simp only [QueryImpl.mapStateTBase, advImplS, StateT.run_mk] at hp
    by_cases h : Sphincs.signatureLimit ≤ (st.slog j).length
    · rw [run_sphincsFwd_of_full h, simulateQ_pure, WriterT.run_pure', support_pure,
        Set.mem_singleton_iff] at hp
      subst hp
      exact ⟨hst, fun j ↦ by simp [sKeyLog]⟩
    · rw [run_sphincsFwd_of_room h, simulateQ_map, WriterT.run_map', simulateQ_spec_query,
        support_map] at hp
      obtain ⟨⟨σ, w⟩, hσ, rfl⟩ := hp
      have hw : w = [⟨(j, msg), σ⟩] := mem_support_signingOracle (sk := sk) hσ
      subst hw
      refine ⟨fun j' ↦ ?_, fun j' ↦ ?_⟩
      · by_cases hj : j' = j
        · subst hj
          simp only [Prod.map, id, Function.update_self, List.length_append, List.length_singleton]
          omega
        · simp only [Prod.map, id, Function.update_of_ne hj]
          exact hst j'
      · by_cases hj : j' = j
        · subst hj
          simp [Prod.map, sKeyLog]
        · simp [Prod.map, sKeyLog, Function.update_of_ne hj, Ne.symm hj]

/-- **The reduction's answers to a whole adversary, in the multi-user game**: no log passes the
limit, and each key's leanSPHINCS log grows by that key's part of the signing log. -/
theorem adv_sLog (sk : Fin ns → Sphincs.PublicKey × Sphincs.Seeded.SecretKey)
    (keys : Keys nx ns) {α : Type} (oa : OracleComp (AdvSpec nx ns) α) :
    ∀ (st : SignState nx ns), SInv st →
      ∀ p ∈ support (((simulateQ ((τS sk).mapStateTBase (advImplS keys)) oa).run st).run),
        SInv p.1.2 ∧ ∀ j, p.1.2.slog j = st.slog j ++ sKeyLog p.2 j := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro st hst p hp
    simp only [simulateQ_pure, StateT.run_pure, WriterT.run_pure', support_pure,
      Set.mem_singleton_iff] at hp
    subst hp
    exact ⟨hst, fun j ↦ by simp [sKeyLog]⟩
  | query_bind t k ih =>
    intro st hst p hp
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, WriterT.run_bind',
      mem_support_bind_iff] at hp
    obtain ⟨q, hq, hp⟩ := hp
    obtain ⟨hq1, hq2⟩ := step_sLog sk keys t st hst q hq
    rw [support_map] at hp
    obtain ⟨p', hp', rfl⟩ := hp
    obtain ⟨hp1, hp2⟩ := ih q.1.1 q.1.2 hq1 p' hp'
    refine ⟨hp1, fun j ↦ ?_⟩
    simp only [Prod.map, id, sKeyLog_append, hp2 j, hq2 j, List.append_assoc]

/-- **The reduction's signing log in the multi-user game**: on every reachable run, the held
public keys are the multi-user game's, no leanSPHINCS log passes the limit, and each is the
multi-user log's part for its key. -/
theorem sCore_log (guest : Program) (fuel budget : ℕ) (A : GameAdversary nx ns)
    (sk : Fin ns → Sphincs.PublicKey × Sphincs.Seeded.SecretKey) :
    ∀ p ∈ support ((simulateQ (τS sk) (sCore guest fuel budget A (fun j ↦ (sk j).1))).run),
      (∀ j, (p.1.1.sphincs j).1 = (sk j).1) ∧ SInv p.1.2.2.2.2 ∧
        ∀ j, p.1.2.2.2.2.slog j = sKeyLog p.2 j := by
  intro p hp
  unfold sCore at hp
  simp only [simulateQ_bind, WriterT.run_bind', run_simulateQ_τS_liftR, bind_map_left,
    mem_support_bind_iff, support_map, Set.mem_image] at hp
  obtain ⟨xs, -, q, ⟨a, ha, b, ⟨o, ho, c, hc, rfl⟩, rfl⟩, rfl⟩ := hp
  rw [QueryImpl.simulateQ_mapStateTBase_run] at ha
  have hinit : SInv (SignState.init nx ns) := fun j ↦ by simp [SignState.init]
  obtain ⟨hq1, hq2⟩ := adv_sLog sk _ _ _ hinit a ha
  simp only [simulateQ_pure, WriterT.run_pure', support_pure, Set.mem_singleton_iff] at hc
  subst hc
  obtain ⟨-, hs⟩ := keepsLogs_viRec budget guest a.1.1.2 fuel a.1.1.1 a.1.2 o ho
  refine ⟨fun j ↦ rfl, fun j ↦ ?_, fun j ↦ ?_⟩
  · simp only [Prod.map, id]
    rw [hs]
    exact hq1 j
  · have h2 := hq2 j
    simp only [SignState.init, List.nil_append] at h2
    simp only [Prod.map, id, hs, List.nil_append, sKeyLog_append, h2]
    simp [sKeyLog]

/-! ## The reduction's win -/

/-- **The forgery's check in the multi-user game**: verify the forgery under the named key, and
judge it against the signing log. -/
noncomputable def finishS [NeZero ns]
    (p : (Fin ns → Sphincs.PublicKey × Sphincs.Seeded.SecretKey) × XmssRed.BOut nx ns ×
      QueryLog (Sphincs.Security.Multi.SigningSpec ns)) : OracleComp OW Bool := do
  let f := forgeryOfS p.2.1
  let verified ← sLift (Sphincs.Concrete.verify (p.1 f.key).1 f.message f.signature :
    OracleComp Sphincs.HashSpec Bool)
  return decide (Sphincs.Security.Multi.Valid p.2.2 f.key ∧
    ¬Sphincs.Security.Multi.Contains p.2.2 f) && verified

/-- **The multi-user game of the reduction** is its run, then the forgery's check. -/
theorem gameCore_sAdv [NeZero ns] (guest : Program) (fuel budget : ℕ) (A : GameAdversary nx ns) :
    (Sphincs.Security.Multi.gameCore (sAdv guest fuel budget A) : OracleComp OW Bool) =
      sPrefix guest fuel budget A >>= finishS := by
  have hmap : ∀ (keys : Fin ns → Sphincs.PublicKey × Sphincs.Seeded.SecretKey)
      (X : OracleComp (RSpec ns) (XmssRed.BOut nx ns)),
      (simulateQ (QueryImpl.ofLift Sphincs.OracleWorld (WriterT (QueryLog
          (Sphincs.Security.Multi.SigningSpec ns)) (OracleComp Sphincs.OracleWorld)) +
        Sphincs.Security.Multi.signingOracle keys) (forgeryOfS <$> X)).run =
      Prod.map forgeryOfS id <$> (simulateQ (QueryImpl.ofLift Sphincs.OracleWorld (WriterT (QueryLog
          (Sphincs.Security.Multi.SigningSpec ns)) (OracleComp Sphincs.OracleWorld)) +
        Sphincs.Security.Multi.signingOracle keys) X).run := by
    intro keys X
    have h := simulateQ_map (impl := QueryImpl.ofLift Sphincs.OracleWorld (WriterT (QueryLog
          (Sphincs.Security.Multi.SigningSpec ns)) (OracleComp Sphincs.OracleWorld)) +
        Sphincs.Security.Multi.signingOracle keys)
      (X : OracleComp (Sphincs.OracleWorld + Sphincs.Security.Multi.SigningSpec ns) _) forgeryOfS
    exact (congrArg WriterT.run h).trans (WriterT.run_map' _ _)
  unfold Sphincs.Security.Multi.gameCore sPrefix sAdv finishS
  dsimp only
  simp only [hmap, bind_assoc, pure_bind, bind_map_left]
  rfl

omit [Sphincs.Params] in
/-- The requests to key `j` are counted by its part of the log. -/
theorem requests_eq_length (log : QueryLog (Sphincs.Security.Multi.SigningSpec ns)) (j : Fin ns) :
    Sphincs.Security.Multi.requests log j = (sKeyLog log j).length := by
  unfold Sphincs.Security.Multi.requests sKeyLog
  induction log with
  | nil => rfl
  | cons e log ih =>
    by_cases h : e.1.1 = j
    · simp [h, ih]
    · simp [h, ih]

/-- **The check of a forgery passes** when its signature is valid under a trace the cache
holds, and the key answered at most `signatureLimit` requests, none for the message. -/
theorem run_finish_ofS {sk : Fin ns → Sphincs.PublicKey × Sphincs.Seeded.SecretKey}
    {log : QueryLog (Sphincs.Security.Multi.SigningSpec ns)} {j : Fin ns} {msg : Sphincs.Message}
    {σ : Sphincs.Signature} {tr : Log} {c : QueryCache LeanXmss.HashSpec} {pk : Sphincs.PublicKey}
    {l : List (Sphincs.Message × Option Sphincs.Signature)}
    (hσ : sphincsVerifyWith (look tr) pk msg σ = some true) (hpk : pk = (sk j).1)
    (hforged : ∀ e ∈ l, e.1 = msg → e.2 = none) (hl : l = sKeyLog log j)
    (hlen : l.length ≤ Sphincs.signatureLimit) (hc : CacheTr c tr) :
    (simulateQ owImpl (do
      let verified ← sLift (Sphincs.Concrete.verify (sk j).1 msg σ :
        OracleComp Sphincs.HashSpec Bool)
      return decide (Sphincs.Security.Multi.Valid log j ∧
        ¬Sphincs.Security.Multi.Contains log ⟨j, msg, σ⟩) && verified : OracleComp OW Bool)).run' c =
      pure true := by
  have hcache : CacheHas c (look tr) := by
    intro x d hx
    obtain ⟨i, hi, hei, -⟩ := (look_eq_some_iff _ x d).mp hx
    have := hc _ (List.getElem_mem hi)
    rw [hei] at this
    exact this
  subst hpk hl
  have hver : (simulateQ owImpl (sLift (Sphincs.Concrete.verify (sk j).1 msg σ :
      OracleComp Sphincs.HashSpec Bool))).run c = pure (true, c) := by
    unfold sLift
    have h1 := QueryImpl.simulateQ_add_liftM_right (impl₁' := unifFwdImpl Sphincs.HashSpec)
      (impl₂' := (randomOracle : QueryImpl Sphincs.HashSpec
        (StateT (QueryCache Sphincs.HashSpec) ProbComp)))
      (Sphincs.Concrete.verify (sk j).1 msg σ : OracleComp Sphincs.HashSpec Bool)
    have h2 : (simulateQ (randomOracle : QueryImpl Sphincs.HashSpec
        (StateT (QueryCache Sphincs.HashSpec) ProbComp))
        (Sphincs.Concrete.verify (sk j).1 msg σ : OracleComp Sphincs.HashSpec Bool)).run c =
        pure (true, c) := run_verify_of_sphincsVerifyWith hcache hσ
    exact (congrArg (fun x ↦ StateT.run x c) h1).trans h2
  simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind]
  rw [hver]
  simp only [pure_bind, simulateQ_pure, StateT.run_pure, map_pure, Bool.and_true]
  congr 1
  simp only [decide_eq_true_eq]
  refine ⟨?_, ?_⟩
  · rw [Sphincs.Security.Multi.Valid, requests_eq_length]
    exact hlen
  · rintro ⟨e, he, hm, hs⟩
    have hmem : (msg, some σ) ∈ sKeyLog log j := by
      refine List.mem_filterMap.mpr ⟨e, he, ?_⟩
      simp only [Prod.ext_iff] at hm
      simp [hm.1, hm.2, hs]
    have := hforged _ hmem rfl
    exact absurd this (by simp)

/-- `SWin` reads only the leanSPHINCS public keys. -/
theorem sWin_congr {a b : Fin ns → Sphincs.PublicKey × Sphincs.Seeded.SecretKey}
    (h : ∀ j, (a j).1 = (b j).1) (r : XmssRed.BOut nx ns) :
    SWin (fullOut a r).1 (fullOut a r).2 ↔ SWin (fullOut b r).1 (fullOut b r).2 := by
  simp only [SWin, fullOut, h]

/-- **The forgery's check passes** on a reachable run of the reduction that wins in the game,
from a cache holding V_I's trace. -/
theorem run_finishS [NeZero ns] {guest : Program} {fuel budget : ℕ} {A : GameAdversary nx ns}
    {y : ((Fin ns → Sphincs.PublicKey × Sphincs.Seeded.SecretKey) × XmssRed.BOut nx ns ×
      QueryLog (Sphincs.Security.Multi.SigningSpec ns)) × QueryCache LeanXmss.HashSpec}
    (hy : y.1 ∈ support (sPrefix guest fuel budget A))
    (hw : SWin (fullOut y.1.1 y.1.2.1).1 (fullOut y.1.1 y.1.2.1).2)
    (hc : CacheTr y.2 (fullOut y.1.1 y.1.2.1).2) :
    (simulateQ owImpl (finishS y.1)).run' y.2 = pure true := by
  obtain ⟨⟨sk, r, log⟩, c⟩ := y
  simp only at hy hw hc ⊢
  unfold sPrefix at hy
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hy
  obtain ⟨seeds, -, sk', -, p, hp, rfl, rfl, rfl⟩ := hy
  obtain ⟨hkeys, hinv, hlog⟩ := sCore_log guest fuel budget A sk p hp
  have hw' := (sWin_congr (fun j ↦ (hkeys j)) p.1).mpr hw
  unfold finishS forgeryOfS
  simp only [hw', ↓reduceDIte]
  obtain ⟨-, hforged, hσ⟩ := hw'.2.choose_spec.choose_spec.choose_spec
  simp only [fullOut] at hσ hforged hc
  exact run_finish_ofS hσ (hkeys _) hforged (hlog _) (hinv _) hc

/-- The multi-user game's advantage, its count forgotten. -/
theorem forgeAdvantage_eq (adv : Sphincs.Security.Multi.Adversary ns) :
    Sphincs.Security.Multi.forgeAdvantage adv =
      Pr{let b ← ((simulateQ owImpl (Sphincs.Security.Multi.gameCore adv :
        OracleComp OW Bool)).run' ∅)}[b = true] := by
  have h := QueryImpl.fst_map_run_withCost (m := StateT (QueryCache LeanXmss.HashSpec) ProbComp)
    owImpl (fun t ↦ Multiplicative.ofAdd (match t with | .inl _ => (0 : ℕ) | .inr _ => 1))
    (Sphincs.Security.Multi.gameCore adv : OracleComp OW Bool)
  have key : Prod.fst <$> ((simulateQ (owImpl.withCost
      (fun t ↦ Multiplicative.ofAdd (match t with | .inl _ => (0 : ℕ) | .inr _ => 1)))
        (Sphincs.Security.Multi.gameCore adv : OracleComp OW Bool)).run).run' ∅ =
      (simulateQ owImpl (Sphincs.Security.Multi.gameCore adv : OracleComp OW Bool)).run' ∅ := by
    rw [StateT.run'_eq, StateT.run'_eq, Functor.map_map, ← h, StateT.run_map, Functor.map_map]
  rw [← key, prEvent_map]
  rfl

/-! ## The bound -/

/-- **A leanSPHINCS forgery** (`Forged`'s second part): a leanSPHINCS claim of the root statement
for an honest key on a message no request to that key was answered for. -/
def ForgedS (z : GameOutcome nx ns) : Prop :=
  ∃ j : Fin ns, ∃ msg, ((z.keys.sphincs j).1, msg) ∈ z.statement.claims.sphincs ∧
    ∀ e ∈ z.state.slog j, e.1 = msg → e.2 = none

/-- **On the game with V_I's trace, a leanSPHINCS forgery on a good log is a win of the
trace.** -/
theorem sWin_of_gameRec
    (hG : ∀ (ℓ : Log) (rows : List BlakeRow) (h : TableOK (look ℓ) rows),
      Guest.Located.GuestHypsM (Guest.Value.HashModel.oracle rows ℓ h))
    {fuel budget : ℕ} {A : GameAdversary nx ns} {p : (GameOutcome nx ns × Log) × Log}
    (hp : p ∈ support (gameRec Guest.guest fuel budget A)) (ha : p.1.1.accepted = true)
    (hf : ForgedS p.1.1) (hbad : ¬ AggBad p.2) :
    SWin p.1.1 p.1.2 ∧ CacheTr (logCache p.2) p.1.2 := by
  obtain ⟨hsub, hv⟩ := gameRec_trace hp
  have hk := aggregate_knowledge_sub (hG p.2) (hG p.1.2) hbad hsub.lookSub (hv ha)
  obtain ⟨j, msg, hmem, hforged⟩ := hf
  obtain ⟨σ, hσ⟩ := hk.2.1 _ hmem
  refine ⟨⟨ha, j, msg, σ, hmem, hforged, hσ⟩, fun e he ↦ ?_⟩
  rw [logCache_apply, hsub e he]
  rfl

/-- **The leanSPHINCS reduction (T5, leanSPHINCS part).** In the game of the deployed guest, V_I
accepting a root statement with a leanSPHINCS forgery on a log without the chain's bad events is
at most as likely as the reduction's win in leanSPHINCS's multi-user game, if the guest's open
callees are sound over every oracle model. -/
theorem prEvent_forgedS_le [NeZero ns]
    (hG : ∀ (ℓ : Log) (rows : List BlakeRow) (h : TableOK (look ℓ) rows),
      Guest.Located.GuestHypsM (Guest.Value.HashModel.oracle rows ℓ h))
    (fuel budget : ℕ) (A : GameAdversary nx ns) :
    Pr{let z ← game Guest.guest fuel budget A}[z.1.accepted = true ∧ ForgedS z.1 ∧ ¬ AggBad z.2] ≤
      Sphincs.Security.Multi.forgeAdvantage (sAdv Guest.guest fuel budget A) := by
  let F : (GameOutcome nx ns × Log) × QueryCache LeanXmss.HashSpec → Prop :=
    fun o ↦ SWin o.1.1 o.1.2 ∧ CacheTr o.2 o.1.2
  calc Pr{let z ← game Guest.guest fuel budget A}[z.1.accepted = true ∧ ForgedS z.1 ∧ ¬ AggBad z.2]
      = Pr{let p ← gameRec Guest.guest fuel budget A}[p.1.1.accepted = true ∧ ForgedS p.1.1 ∧
          ¬ AggBad p.2] := by
        rw [← gameRec_map, prEvent_map]
    _ ≤ Pr{let p ← gameRec Guest.guest fuel budget A}[F (p.1, logCache p.2)] :=
        prEvent_mono_of_support _ _ _ fun p hp h ↦ sWin_of_gameRec hG hp h.1 h.2.1 h.2.2
    _ = Pr{let o ← Prod.map id logCache <$> gameRec Guest.guest fuel budget A}[F o] := by
        rw [prEvent_map]; rfl
    _ = Pr{let o ← romRun (simulateQ toW (gameCompRec Guest.guest fuel budget A)) ∅}[F o] :=
        (evalDistEq_run_toW_nil _).prEvent_eq F
    _ = Pr{let o ← Prod.map (fun p ↦ fullOut p.1 p.2.1) id <$>
          romRun (sPrefix Guest.guest fuel budget A) ∅}[F o] :=
        ((evalDistEq_sPrefix _ _ _ _).prEvent_eq F).symm
    _ = Pr{let y ← romRun (sPrefix Guest.guest fuel budget A) ∅}[
          F (fullOut y.1.1 y.1.2.1, y.2)] := by
        rw [prEvent_map]; rfl
    _ ≤ Pr{let b ← romRun (sPrefix Guest.guest fuel budget A) ∅ >>= fun y ↦
          (simulateQ owImpl (finishS y.1)).run' y.2}[b = true] := by
        refine le_prEvent_bind_of_pure _ _ (fun y : ((Fin ns → Sphincs.PublicKey ×
            Sphincs.Seeded.SecretKey) × XmssRed.BOut nx ns ×
              QueryLog (Sphincs.Security.Multi.SigningSpec ns)) ×
            QueryCache LeanXmss.HashSpec ↦ F (fullOut y.1.1 y.1.2.1, y.2))
          fun y hy hF ↦ run_finishS (guest := Guest.guest) (fuel := fuel) (budget := budget)
            (A := A) ?_ hF.1 hF.2
        have h1 : y.1 ∈ support ((simulateQ owImpl (sPrefix Guest.guest fuel budget A)).run' ∅) := by
          rw [StateT.run'_eq, support_map]; exact ⟨y, hy, rfl⟩
        exact support_simulateQ_run'_subset _ _ _ h1
    _ = Sphincs.Security.Multi.forgeAdvantage (sAdv Guest.guest fuel budget A) := by
        rw [forgeAdvantage_eq, gameCore_sAdv, simulateQ_bind, StateT.run'_eq, StateT.run_bind,
          map_bind]
        simp only [StateT.run'_eq, map_bind]

/-! ## The reduction's hash calls -/

omit [Sphincs.Params] in
/-- V_I's recorded run makes at most the budget of hash queries. -/
theorem isQueryBoundP_viRec (budget : ℕ) (guest : Program) (ip : IdealProof) (fuel : ℕ)
    (s : NodeStatement) (st : SignState nx ns) :
    IsQueryBoundP ((viRec budget guest ip fuel s).run st) IsHash budget := by
  have h := isQueryBoundP_idealVerify budget guest ip fuel s st
  rw [← viRec_map, StateT.run_map, isQueryBoundP_map_iff] at h
  exact h.mono (Nat.sub_le _ _)

/-- **The rest of the game makes at most the adversary's hash queries, its requests' and V_I's
budget.** -/
theorem isQueryBoundP_gameRest {cxs css : ℕ}
    (hxs : ∀ sk i msg, IsTotalQueryBound
      (LeanXmss.Seeded.sign sk i msg : OracleComp LeanXmss.HashSpec _) cxs)
    (hss : ∀ sk msg, IsTotalQueryBound
      (Sphincs.Seeded.sign sk msg : OracleComp Sphincs.HashSpec _) css)
    (guest : Program) (fuel budget : ℕ) (A : GameAdversary nx ns) {qH sX sS : ℕ}
    (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH)
    (hX : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvXmss sX)
    (hS : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvSphincs sS) (keys : Keys nx ns) :
    IsQueryBoundP (gameRest guest fuel budget A keys) IsHashW
      ((qH + sX * cxs + sS * css) + (budget + 0)) := by
  unfold gameRest
  refine isQueryBoundP_bind (isQueryBoundP_simulateQ_toW _ _
    (costs_simulateQ_advImpl hxs hss keys _ (hH _ _) (hX _ _) (hS _ _) _)) fun q _ ↦ ?_
  exact isQueryBoundP_bind (isQueryBoundP_simulateQ_toW _ _ (isQueryBoundP_viRec _ _ _ _ _ _))
    fun _ _ ↦ by simp

/-- **The reduction's multi-user game makes at most the game's hash queries and one final
verification's.** -/
theorem isQueryBoundP_gameCore_sAdv [NeZero ns] {cxk csk cxs css cs : ℕ}
    (hxk : ∀ seed, IsTotalQueryBound (LeanXmss.Seeded.keygenFromSeed seed) cxk)
    (hsk : ∀ seed, IsTotalQueryBound (Sphincs.Seeded.keygenFromSeed seed) csk)
    (hxs : ∀ sk i msg, IsTotalQueryBound
      (LeanXmss.Seeded.sign sk i msg : OracleComp LeanXmss.HashSpec _) cxs)
    (hss : ∀ sk msg, IsTotalQueryBound
      (Sphincs.Seeded.sign sk msg : OracleComp Sphincs.HashSpec _) css)
    (hvs : ∀ pk msg σ, IsTotalQueryBound
      (Sphincs.Concrete.verify pk msg σ : OracleComp Sphincs.HashSpec Bool) cs)
    (guest : Program) (fuel budget : ℕ) (A : GameAdversary nx ns) {qH sX sS : ℕ}
    (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH)
    (hX : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvXmss sX)
    (hS : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvSphincs sS) :
    IsQueryBoundP (Sphincs.Security.Multi.gameCore (sAdv guest fuel budget A) : OracleComp OW Bool)
      IsHashW (nx * cxk + ns * csk + (qH + sX * cxs + sS * css) + budget + cs) := by
  rw [gameCore_sAdv]
  refine (isQueryBoundP_bind (n := ns * csk + (nx * cxk + ((qH + sX * cxs + sS * css) +
    (budget + 0)) + 0)) (m := cs) ?_ fun y _ ↦ ?_).mono (by omega)
  · unfold sPrefix
    refine (isQueryBoundP_bind (n := 0) (m := ns * csk + (nx * cxk + ((qH + sX * cxs + sS * css) +
      (budget + 0)) + 0)) ?_ fun seeds _ ↦ ?_).mono (by omega)
    · rw [← simulateQ_toW_liftM]
      exact isQueryBoundP_simulateQ_toW _ 0 (isQueryBoundP_liftM_probComp _)
    · refine isQueryBoundP_bind (isQueryBoundP_sLift _ _ ?_) fun sk _ ↦ ?_
      · rw [keygenAll_eq_sequenceFin]
        exact isTotalQueryBound_sequenceFin _ _ fun i ↦ hsk _
      · refine isQueryBoundP_bind ?_ fun _ _ ↦ isQueryBoundP_pure _ _ _
        refine (isQueryBoundP_map_iff (p := IsHashW) _ (fun p ↦ fullOut sk p.1) _).mp ?_
        refine (congrArg (fun x ↦ IsQueryBoundP x IsHashW
          (nx * cxk + ((qH + sX * cxs + sS * css) + (budget + 0)))) (map_sCore guest fuel budget A sk)).mpr ?_
        refine isQueryBoundP_bind (isQueryBoundP_sequenceFin cxk _ fun _ ↦ ?_) fun xs _ ↦
          isQueryBoundP_gameRest hxs hss guest fuel budget A hH hX hS _
        unfold LeanXmss.MultiUser.keygen
        refine (isQueryBoundP_bind (n := 0) (m := cxk) ?_ fun _ _ ↦
          isQueryBoundP_liftM_hash _ _ (hxk _)).mono (by omega)
        rw [← simulateQ_toW_liftM]
        exact isQueryBoundP_simulateQ_toW _ 0 (isQueryBoundP_liftM_probComp _)
  · unfold finishS
    exact (isQueryBoundP_bind (n := cs) (m := 0) (isQueryBoundP_sLift _ _ (hvs _ _ _))
      fun _ _ ↦ by simp).mono (by omega)

/-- **The reduction's hash-call budget** in leanSPHINCS's multi-user game: the game's and one final
verification's `cs`. -/
theorem hasHashQueryBound_sAdv [NeZero ns] {cxk csk cxs css cs : ℕ}
    (hxk : ∀ seed, IsTotalQueryBound (LeanXmss.Seeded.keygenFromSeed seed) cxk)
    (hsk : ∀ seed, IsTotalQueryBound (Sphincs.Seeded.keygenFromSeed seed) csk)
    (hxs : ∀ sk i msg, IsTotalQueryBound
      (LeanXmss.Seeded.sign sk i msg : OracleComp LeanXmss.HashSpec _) cxs)
    (hss : ∀ sk msg, IsTotalQueryBound
      (Sphincs.Seeded.sign sk msg : OracleComp Sphincs.HashSpec _) css)
    (hvs : ∀ pk msg σ, IsTotalQueryBound
      (Sphincs.Concrete.verify pk msg σ : OracleComp Sphincs.HashSpec Bool) cs)
    (guest : Program) (fuel budget : ℕ) (A : GameAdversary nx ns) {qH sX sS : ℕ}
    (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH)
    (hX : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvXmss sX)
    (hS : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvSphincs sS) :
    Sphincs.Security.Multi.HasHashQueryBound (sAdv guest fuel budget A)
      (nx * cxk + ns * csk + (qH + sX * cxs + sS * css) + budget + cs) := by
  intro result hr
  unfold Sphincs.Security.Multi.experiment at hr
  rw [StateT.run'_eq] at hr
  erw [support_map] at hr
  obtain ⟨r, hr, rfl⟩ := hr
  exact count_le_of_isQueryBoundP owImpl _ _
    (isQueryBoundP_gameCore_sAdv hxk hsk hxs hss hvs guest fuel budget A hH hX hS) ∅ r hr

end SphincsRed

end
end LeanVM.E2E
