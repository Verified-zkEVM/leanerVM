/-
  LeanVM.E2E.Vis.PerKey.SphincsChain

  W-vis, P7b: the per-key leanSPHINCS bound. The game's win against leanSPHINCS key `j`, without a
  coincidence of key `j`'s parameter, is at most the per-key reduction's advantage in leanSPHINCS's
  single-key game.
-/

module

public import LeanVM.E2E.Vis.PerKey.SphincsFacts
public import LeanVM.E2E.Vis.PerKey.SphincsFinal
public import LeanVM.E2E.Vis.PerKey.Partition

/-!
# The per-key leanSPHINCS bound (W-vis, P7b)

The leanSPHINCS counterpart of `Vis/PerKey/XmssChain.lean`. The chain, for leanSPHINCS key `j`:

1. the game with V_I's trace, its final log's cache holding the trace (`gameRec_trace`), is the
   schemes' lazy oracle on the translated game (`evalDistEq_run_toW_nil`, `toW_gameCompRec`);
2. key `j`'s generation is run first (`romRun_sts_front`: `romRun_sequenceFin_front` on the
   leanSPHINCS keys, then `romRun_bind_comm` past the leanXMSS keys), and the rest `RJS` is run
   from its cache, which holds nothing private for key `j` (`keygen_cache_not_privJS`);
3. the rest is the class-routed rest with its caches merged (`evalDistEq_route`); key `j`'s secret
   key in its outcome may be replaced by the reduction's hole key (`route_RJS_self`);
4. the class-routed rest and the reduction's run give the event the same probability
   (`prEvent_viewS`), the event forcing good keys (`goodKeysS_of_not_keyCollAt`);
5. the reduction's run, logged by the challenger, passes the final check where the event holds
   (`run_finishJS`, `sBodyJ_log`);
6. the single-key game is key `j`'s generation, then the reduction's run and the check
   (`gameCore_sRedJ`).

* `prEvent_sWinAt_le`: the bound.
-/

namespace LeanVM.E2E

open LeanVM.Parameters LeanVM.Semantics LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Rom
open OracleSpec OracleComp
open scoped ENNReal

@[expose] public section

namespace PerKeyS

open PerKeyX (XKey SKey withKeys sequenceFin_slot_self map_route_gameRest_congr)

variable {nx ns : ℕ} [Sphincs.Params]

/-- The game's oracles are the challenger's, the log forgotten. -/
theorem σJS_eq_fst_τJS (sk : Sphincs.Seeded.SecretKey) (t : RSs.Domain) :
    σJS sk t = Prod.fst <$> (τJS sk t).run := by
  rcases t with u | msg
  · change (liftM (OW.query u) : OracleComp OW _) = Prod.fst <$>
      ((fun a ↦ (a, ([] : QueryLog Sphincs.SigningSpec))) <$> (liftM (OW.query u) : OracleComp OW _))
    rw [Functor.map_map]
    exact (id_map _).symm
  · exact (fst_signingOracleDet sk msg).symm

/-- **The game's run is the challenger's, the log forgotten.** -/
theorem simulateQ_σJS_eq (sk : Sphincs.Seeded.SecretKey) {α : Type} (y : OracleComp RSs α) :
    simulateQ (σJS sk) y = Prod.fst <$> (simulateQ (τJS sk) y).run := by
  rw [fst_map_run_simulateQ_writer']
  congr 1
  funext t
  exact σJS_eq_fst_τJS sk t

/-- The single-key game's advantage, its count forgotten. -/
theorem forgeAdvantage_eqS (adv : Sphincs.Security.Adversary) :
    Sphincs.Security.Det.forgeAdvantageDet adv =
      Pr{let b ← (simulateQ owImpl (Sphincs.Security.Det.gameCoreDet adv :
        OracleComp OW Bool)).run' ∅}[b = true] := by
  have h := QueryImpl.fst_map_run_withCost (m := StateT (QueryCache LeanXmss.HashSpec) ProbComp)
    owImpl (fun t ↦ Multiplicative.ofAdd (match t with | .inl _ => (0 : ℕ) | .inr _ => 1))
    (Sphincs.Security.Det.gameCoreDet adv : OracleComp OW Bool)
  have key : Prod.fst <$> ((simulateQ (owImpl.withCost
      (fun t ↦ Multiplicative.ofAdd (match t with | .inl _ => (0 : ℕ) | .inr _ => 1)))
        (Sphincs.Security.Det.gameCoreDet adv : OracleComp OW Bool)).run).run' ∅ =
      (simulateQ owImpl (Sphincs.Security.Det.gameCoreDet adv : OracleComp OW Bool)).run' ∅ := by
    rw [StateT.run'_eq, StateT.run'_eq, Functor.map_map, ← h, StateT.run_map, Functor.map_map]
  rw [← key, prEvent_map]
  rfl

/-- **Replacing leanSPHINCS key `j` by a key of the same parameter keeps the keys' parameters.** -/
theorem keyParams_setJS (keys : Keys nx ns) (j : Fin ns) (k : SKey)
    (hk : k.2.parameter = (keys.sphincs j).2.parameter) :
    keyParams (setJS j k keys) = keyParams keys := by
  unfold keyParams setJS
  congr 1
  congr 1
  funext i
  unfold updJS
  dsimp only
  split
  · subst i; rw [hk]
  · rfl

/-- **Replacing key `j` by a key of the same public key keeps the win against key `j`.** -/
theorem sWinAt_holeOutS (j : Fin ns) (k : SKey) (z : GameOutcome nx ns × Log)
    (hk : k.1 = (z.1.keys.sphincs j).1) :
    SWinAt j (holeOutS j k z).1 (holeOutS j k z).2 ↔ SWinAt j z.1 z.2 := by
  simp only [SWinAt, holeOutS, withKeys, setJS, updJS, ↓reduceIte, hk]

/-- **The class-routed rest's outcomes hold key `j`**: replacing it by itself changes nothing. -/
theorem route_RJS_self (guest : Program) (fuel budget : ℕ) (A : GameAdversary nx ns)
    (Pr : List UInt8 → Prop) [DecidablePred Pr] (j : Fin ns) (kj : SKey) :
    simulateQ (routeImpl Pr) (RJS guest fuel budget A j kj) =
      holeOutS j kj <$> simulateQ (routeImpl Pr) (RJS guest fuel budget A j kj) := by
  have h : RJS guest fuel budget A j kj =
      LeanXmss.Concrete.sequenceFin (fun _ : Fin nx ↦
        (LeanXmss.MultiUser.keygen : OracleComp OW _)) >>= fun xs ↦
      LeanXmss.Concrete.sequenceFin (fun i : Fin ns ↦
        if i = j then pure kj else (sKeygen : OracleComp OW _)) >>= fun ss ↦
        gameRest guest fuel budget A ⟨xs, updJS j kj ss⟩ := by
    unfold RJS
    conv_lhs => rw [sequenceFin_slot_self j kj]
    simp only [bind_assoc, pure_bind]
    rfl
  rw [h]
  simp only [simulateQ_bind, map_bind]
  refine bind_congr fun xs ↦ bind_congr fun ss ↦ ?_
  rw [map_route_gameRest_congr guest fuel budget A Pr _ (holeOutS j kj) id fun z hz ↦ ?_, id_map]
  simp only [holeOutS, setJS, hz, updJS_updJS, id]
  rw [← hz]
  rfl

/-- **The single-key game after key generation**: the reduction's run logged by the challenger,
then the final check. -/
noncomputable def contJS (guest : Program) (fuel budget : ℕ) (A : GameAdversary nx ns)
    (j : Fin ns) (kp : SKey) : OracleComp OW Bool :=
  (simulateQ (τJS kp.2) ((sBodyJ guest fuel budget A j kp.1).run ∅)).run >>= fun w ↦
    finishJS kp.1 (forgeryOfJS j w.1.1, w.2)

/-- **The single-key game against the per-key reduction**: key generation, then `contJS`. -/
theorem gameCore_sRedJ (guest : Program) (fuel budget : ℕ) (A : GameAdversary nx ns)
    (j : Fin ns) :
    (Sphincs.Security.Det.gameCoreDet (sRedJ guest fuel budget A j) : OracleComp OW Bool) =
      (sKeygen : OracleComp OW _) >>= contJS guest fuel budget A j := by
  unfold Sphincs.Security.Det.gameCoreDet sKeygen contJS sRedJ
  simp only [bind_assoc]
  refine bind_congr fun seed ↦ bind_congr fun kp ↦ ?_
  change (simulateQ (τJS kp.2) (forgeryOfJS j <$> (fun x ↦ x.1) <$>
    (sBodyJ guest fuel budget A j kp.1).run ∅)).run >>= finishJS kp.1 = _
  simp only [simulateQ_map, WriterT.run_map', Functor.map_map, bind_map_left]
  rfl

/-- The game's event for reduction `j`: a win against leanSPHINCS key `j`, no coincidence at key
`j`, and the cache holding the trace. -/
def FJS (j : Fin ns) (o : (GameOutcome nx ns × Log) × QueryCache LeanXmss.HashSpec) : Prop :=
  SWinAt j o.1.1 o.1.2 ∧ ¬ KeyCollAt o.1.1.keys (Fin.natAdd nx j) ∧ XmssRed.CacheTr o.2 o.1.2

/-- Replacing key `j` twice keeps the last. -/
theorem holeOutS_holeOutS (j : Fin ns) (k k' : SKey) (z : GameOutcome nx ns × Log) :
    holeOutS j k (holeOutS j k' z) = holeOutS j k z := by
  simp only [holeOutS, withKeys, setJS, updJS_updJS]

/-- **The bound after key `j`'s generation.** From each output of key `j`'s generation, the
game's event in the rest is at most as likely as the single-key game's win after it. -/
theorem prEvent_RJS_le (guest : Program) (fuel budget : ℕ) (A : GameAdversary nx ns) (j : Fin ns)
    (r : SKey × QueryCache LeanXmss.HashSpec)
    (hr : r ∈ support (romRun (sKeygen : OracleComp OW _) ∅)) :
    Pr{let o ← romRun (RJS guest fuel budget A j r.1) r.2}[FJS j o] ≤
      Pr{let b ← romRun (contJS guest fuel budget A j r.1) r.2}[b.1 = true] := by
  obtain ⟨hsk, hc0⟩ := keygen_cache_not_privJS r hr
  obtain ⟨⟨pkj, sk⟩, c0⟩ := r
  simp only at hsk hc0
  have hpj : Sphincs.bytesLE 16 sk.parameter = Sphincs.bytesLE 16 pkj.parameter := by rw [hsk]
  let pj := Sphincs.bytesLE 16 sk.parameter
  let kj : SKey := (pkj, sk)
  let kj' : SKey := (pkj, holeKeyS pkj)
  let ev : GameOutcome nx ns × Log → QueryCache LeanXmss.HashSpec →
      QueryCache LeanXmss.HashSpec → Prop :=
    fun o cp c ↦ FJS j (holeOutS j kj o, mergeCache (PrivJ pj) cp c) ∧ o.1.keys.sphincs j = kj'
  have hc : ∀ x, PrivJ pj x → c0 x = none := fun x hx ↦ by
    by_contra h
    exact hc0 x h hx
  -- the game's rest is the class-routed rest, its caches merged
  have h1 : Pr{let o ← romRun (RJS guest fuel budget A j kj) c0}[FJS j o] =
      Pr{let z ← romRun ((simulateQ (routeImpl (PrivJ pj))
          (RJS guest fuel budget A j kj)).run ∅) c0}[FJS j (z.1.1, mergeCache (PrivJ pj) z.1.2 z.2)] := by
    rw [← (evalDistEq_route (PrivJ pj) _ c0 hc).prEvent_eq, prEvent_map]
  -- key `j`'s secret key in the outcome replaced by the hole key
  have h2 : Pr{let z ← romRun ((simulateQ (routeImpl (PrivJ pj))
        (RJS guest fuel budget A j kj)).run ∅) c0}[FJS j (z.1.1, mergeCache (PrivJ pj) z.1.2 z.2)] =
      Pr{let z ← romRun ((holeOutS j kj' <$> simulateQ (routeImpl (PrivJ pj))
        (RJS guest fuel budget A j kj)).run ∅) c0}[ev z.1.1 z.1.2 z.2] := by
    conv_lhs => rw [route_RJS_self guest fuel budget A (PrivJ pj) j kj]
    rw [romRun_pm_map, romRun_pm_map, prEvent_map, prEvent_map]
    refine prEvent_congr _ _ _ fun z ↦ ?_
    simp only [ev, holeOutS_holeOutS]
    simp [holeOutS, withKeys, setJS, updJS, kj']
  -- the event forces good keys
  have hev : ∀ z cp c, ev z cp c → GoodKeysS (Sphincs.bytesLE 16 sk.parameter) j
      (pkj, holeKeyS pkj) (z.1.keys.xmss, z.1.keys.sphincs) := by
    intro z cp c ⟨hF, hj⟩
    have hcoll : ¬ KeyCollAt z.1.keys (Fin.natAdd nx j) := by
      have h : ¬ KeyCollAt (setJS j kj z.1.keys) (Fin.natAdd nx j) := hF.2.1
      unfold KeyCollAt at h ⊢
      rwa [keyParams_setJS _ _ _ (by rw [hj]; exact hsk)] at h
    have := goodKeysS_of_not_keyCollAt z.1.keys j kj' hj hcoll
    rw [hpj]
    exact this
  -- the reduction's view
  have h3 := prEvent_viewS guest fuel budget A sk pkj hsk j ev hev ∅ c0
  -- the reduction's run is the challenger's, its log forgotten
  have h4 : Pr{let z ← romRun ((outJS <$> ΦJS sk (sBodyJ guest fuel budget A j pkj)).run ∅) c0}[
        ev z.1.1 z.1.2 z.2] =
      Pr{let z ← romRun (simulateQ (τJS sk) ((sBodyJ guest fuel budget A j pkj).run ∅)).run c0}[
        ev (outJS z.1.1.1) z.1.1.2 z.2] := by
    rw [romRun_pm_map, prEvent_map, ΦJS, run_stMap, simulateQ_σJS_eq]
    simp only [romRun, simulateQ_map, StateT.run_map, prEvent_map]
  -- the check passes where the event holds
  have h5 : Pr{let z ← romRun (simulateQ (τJS sk)
        ((sBodyJ guest fuel budget A j pkj).run ∅)).run c0}[ev (outJS z.1.1.1) z.1.1.2 z.2] ≤
      Pr{let b ← romRun (contJS guest fuel budget A j (pkj, sk)) c0}[b.1 = true] := by
    unfold contJS
    rw [romRun_bind, ← prEvent_map (p := fun b ↦ b = true), map_bind]
    simp only [← StateT.run'_eq]
    refine XmssRed.le_prEvent_bind_of_pure _ _ _ fun z hz he ↦ ?_
    obtain ⟨hinv, hlog⟩ := sBodyJ_log guest fuel budget A sk j pkj ∅ z.1
      (fst_mem_support_of_mem_romRun hz)
    obtain ⟨hF, hj⟩ := he
    have hw := (sWinAt_holeOutS j kj (outJS z.1.1.1) (by rw [hj])).mp hF.1
    have hk : (z.1.1.1.1.sphincs j).1 = pkj := congrArg Prod.fst hj
    have hc := hF.2.2
    simp only [holeOutS, pj, hpj] at hc
    exact run_finishJS j pkj z.1.1.1 z.1.2 z.1.1.2 z.2 hw hk hc hlog hinv
  calc Pr{let o ← romRun (RJS guest fuel budget A j kj) c0}[FJS j o]
      = _ := h1
    _ = _ := h2
    _ = _ := h3
    _ = _ := h4
    _ ≤ _ := h5

/-- **Key `j`'s generation first.** In the schemes' lazy random oracle, the translated game's
key generations and rest are leanSPHINCS key `j`'s generation, then `RJS`. -/
theorem romRun_sts_front (guest : Program) (fuel budget : ℕ) (A : GameAdversary nx ns)
    (j : Fin ns) :
    romRun (LeanXmss.Concrete.sequenceFin (fun _ : Fin nx ↦ LeanXmss.MultiUser.keygen) >>= fun mk ↦
        LeanXmss.Concrete.sequenceFin (fun _ : Fin ns ↦ sKeygen) >>= fun ss ↦
          gameRest guest fuel budget A ⟨mk, ss⟩) ∅ =ᵈ
      romRun ((sKeygen : OracleComp OW _) >>= fun a ↦ RJS guest fuel budget A j a) ∅ := by
  have e1 : romRun ((sKeygen : OracleComp OW _) >>= fun a ↦ RJS guest fuel budget A j a) ∅ =ᵈ
      romRun (LeanXmss.Concrete.sequenceFin (fun _ : Fin nx ↦
          (LeanXmss.MultiUser.keygen : OracleComp OW _)) >>= fun xs ↦
        (sKeygen : OracleComp OW _) >>= fun a ↦
          LeanXmss.Concrete.sequenceFin (fun i : Fin ns ↦
            if i = j then pure a else (sKeygen : OracleComp OW _)) >>= fun ss ↦
            gameRest guest fuel budget A ⟨xs, ss⟩) ∅ := by
    unfold RJS
    exact romRun_bind_comm _ _ (fun a xs ↦ LeanXmss.Concrete.sequenceFin (fun i : Fin ns ↦
      if i = j then pure a else (sKeygen : OracleComp OW _)) >>= fun ss ↦
        gameRest guest fuel budget A ⟨xs, ss⟩) ∅
  have e2 : romRun (LeanXmss.Concrete.sequenceFin (fun _ : Fin nx ↦
          (LeanXmss.MultiUser.keygen : OracleComp OW _)) >>= fun xs ↦
        (sKeygen : OracleComp OW _) >>= fun a ↦
          LeanXmss.Concrete.sequenceFin (fun i : Fin ns ↦
            if i = j then pure a else (sKeygen : OracleComp OW _)) >>= fun ss ↦
            gameRest guest fuel budget A ⟨xs, ss⟩) ∅ =ᵈ
      romRun (LeanXmss.Concrete.sequenceFin (fun _ : Fin nx ↦ LeanXmss.MultiUser.keygen) >>=
        fun mk ↦ LeanXmss.Concrete.sequenceFin (fun _ : Fin ns ↦ sKeygen) >>= fun ss ↦
          gameRest guest fuel budget A ⟨mk, ss⟩) ∅ := by
    rw [romRun_bind, romRun_bind]
    exact EvalDistEq.bind_right _ fun r ↦
      romRun_sequenceFin_front ns (fun _ ↦ sKeygen) j
        (fun _ ss ↦ gameRest guest fuel budget A ⟨r.1, ss⟩) r.2
  exact (e1.trans e2).symm

/-- **The per-key leanSPHINCS bound (P7b).** In the game with V_I's trace, a win against
leanSPHINCS key `j` (`SWinAt j`) without a coincidence of key `j`'s parameter (`KeyCollAt`) is at
most as likely as the per-key reduction's win in leanSPHINCS's single-key game. -/
theorem prEvent_sWinAt_le (guest : Program) (fuel budget : ℕ) (A : GameAdversary nx ns)
    (j : Fin ns) :
    Pr{let p ← gameRec guest fuel budget A}[SWinAt j p.1.1 p.1.2 ∧
        ¬ KeyCollAt p.1.1.keys (Fin.natAdd nx j)] ≤
      Sphincs.Security.Det.forgeAdvantageDet (sRedJ guest fuel budget A j) := by
  calc Pr{let p ← gameRec guest fuel budget A}[SWinAt j p.1.1 p.1.2 ∧
        ¬ KeyCollAt p.1.1.keys (Fin.natAdd nx j)]
      ≤ Pr{let p ← gameRec guest fuel budget A}[FJS j (p.1, logCache p.2)] := by
        refine prEvent_mono_of_support _ _ _ fun p hp h ↦ ⟨h.1, h.2, fun e he ↦ ?_⟩
        rw [logCache_apply, (gameRec_trace hp).1 e he]
        rfl
    _ = Pr{let o ← Prod.map id logCache <$> gameRec guest fuel budget A}[FJS j o] := by
        rw [prEvent_map]; rfl
    _ = Pr{let o ← romRun (simulateQ toW (gameCompRec guest fuel budget A)) ∅}[FJS j o] :=
        (evalDistEq_run_toW_nil _).prEvent_eq _
    _ = Pr{let o ← romRun ((sKeygen : OracleComp OW _) >>= fun a ↦
          RJS guest fuel budget A j a) ∅}[FJS j o] := by
        rw [toW_gameCompRec]
        exact (romRun_sts_front guest fuel budget A j).prEvent_eq _
    _ ≤ Pr{let b ← romRun ((sKeygen : OracleComp OW _) >>=
          contJS guest fuel budget A j) ∅}[b.1 = true] := by
        rw [romRun_bind, romRun_bind]
        exact prEvent_bind_mono_of_forall_le_of_support _ _ _ _ _ fun r hr ↦
          prEvent_RJS_le guest fuel budget A j r hr
    _ = Sphincs.Security.Det.forgeAdvantageDet (sRedJ guest fuel budget A j) := by
        rw [forgeAdvantage_eqS, gameCore_sRedJ, StateT.run'_eq, prEvent_map]

end PerKeyS

end
end LeanVM.E2E
