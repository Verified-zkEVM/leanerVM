/-
  LeanVM.E2E.Vis.PerKey.XmssChain

  W-vis, P7b: the per-key leanXMSS bound. The game's win against leanXMSS key `j`, without a
  coincidence of key `j`'s parameter, is at most the per-key reduction's advantage in leanXMSS's
  single-key game.
-/

module

public import LeanVM.E2E.Vis.PerKey.XmssFacts
public import LeanVM.E2E.Vis.PerKey.XmssFinal
public import LeanVM.E2E.Vis.PerKey.Partition

/-!
# The per-key leanXMSS bound (W-vis, P7b)

The chain, for key `j`:

1. the game with V_I's trace, its final log's cache holding the trace (`gameRec_trace`), is the
   schemes' lazy oracle on the translated game (`evalDistEq_run_toW_nil`, `toW_gameCompRec`);
2. key `j`'s generation is run first (`romRun_sequenceFin_front`), and the rest `RJ` is run from
   its cache, which holds nothing private for key `j` (`keygen_cache_not_privJ`);
3. the rest is the class-routed rest with its caches merged (`evalDistEq_route`); key `j`'s secret
   key in its outcome may be replaced by the reduction's hole key (`route_RJ_self`);
4. the class-routed rest and the reduction's run give the event the same probability
   (`prEvent_view`), the event forcing good keys (`goodKeys_of_not_keyCollAt`);
5. the reduction's run, logged by the challenger, passes the final check where the event holds
   (`run_finishJ`, `xBodyJ_log`);
6. the single-key game is key `j`'s generation, then the reduction's run and the check
   (`gameCore_xRedJ`).

* `prEvent_xWinAt_le`: the bound.
-/

namespace LeanVM.E2E

open LeanVM.Parameters LeanVM.Semantics LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Rom
open OracleSpec OracleComp
open scoped ENNReal

@[expose] public section

namespace PerKeyX

variable {nx ns : ℕ}

/-- The game's oracles are the challenger's, the log forgotten. -/
theorem σJ_eq_fst_τJ (sk : LeanXmss.Seeded.SecretKey) (t : RS.Domain) :
    σJ sk t = Prod.fst <$> (τJ sk t).run := by
  rcases t with u | req
  · change (liftM (OW.query u) : OracleComp OW _) = Prod.fst <$>
      ((fun a ↦ (a, ([] : QueryLog LeanXmss.SigningSpec))) <$> (liftM (OW.query u) : OracleComp OW _))
    rw [Functor.map_map]
    exact (id_map _).symm
  · change (liftM (LeanXmss.Seeded.sign sk req.leafIndex req.message : OracleComp LeanXmss.HashSpec _) :
      OracleComp OW _) = Prod.fst <$> (LeanXmss.Security.signingOracle sk req).run
    rw [LeanXmss.Security.signingOracle, QueryImpl.run_withLogging_apply]
    simp

/-- **The game's run is the challenger's, the log forgotten.** -/
theorem simulateQ_σJ_eq (sk : LeanXmss.Seeded.SecretKey) {α : Type} (y : OracleComp RS α) :
    simulateQ (σJ sk) y = Prod.fst <$> (simulateQ (τJ sk) y).run := by
  rw [fst_map_run_simulateQ_writer']
  congr 1
  funext t
  exact σJ_eq_fst_τJ sk t

/-- The single-key game's advantage, its count forgotten. -/
theorem forgeAdvantage_eq' (adv : LeanXmss.Security.Adversary) :
    LeanXmss.Security.forgeAdvantage adv =
      Pr{let b ← (simulateQ owImpl (LeanXmss.Security.gameCore adv)).run' ∅}[b = true] := by
  have h := QueryImpl.fst_map_run_withCost (m := StateT (QueryCache LeanXmss.HashSpec) ProbComp)
    owImpl (fun t ↦ Multiplicative.ofAdd (match t with | .inl _ => (0 : ℕ) | .inr _ => 1))
    (LeanXmss.Security.gameCore adv)
  have key : Prod.fst <$> ((simulateQ (owImpl.withCost
      (fun t ↦ Multiplicative.ofAdd (match t with | .inl _ => (0 : ℕ) | .inr _ => 1)))
        (LeanXmss.Security.gameCore adv)).run).run' ∅ =
      (simulateQ owImpl (LeanXmss.Security.gameCore adv)).run' ∅ := by
    rw [StateT.run'_eq, StateT.run'_eq, Functor.map_map, ← h, StateT.run_map, Functor.map_map]
  rw [← key, prEvent_map]
  rfl

variable [Sphincs.Params]

/-- **Replacing key `j` by a key of the same parameter keeps the keys' parameters.** -/
theorem keyParams_setJ (keys : Keys nx ns) (j : Fin nx) (k : XKey)
    (hk : k.2.parameter = (keys.xmss j).2.parameter) : keyParams (setJ j k keys) = keyParams keys := by
  unfold keyParams setJ
  congr 1
  congr 1
  funext i
  unfold updJ
  dsimp only
  split
  · subst i; rw [hk]
  · rfl

/-- **Replacing key `j` by a key of the same public key keeps the win against key `j`.** -/
theorem xWinAt_holeOut (j : Fin nx) (k : XKey) (z : GameOutcome nx ns × Log)
    (hk : k.1 = (z.1.keys.xmss j).1) :
    XWinAt j (holeOut j k z).1 (holeOut j k z).2 ↔ XWinAt j z.1 z.2 := by
  simp only [XWinAt, holeOut, withKeys, setJ, updJ, ↓reduceIte, hk]

/-- **The class-routed rest's outcomes hold key `j`**: replacing it by itself changes nothing. -/
theorem route_RJ_self (guest : Program) (fuel budget : ℕ) (A : GameAdversary nx ns)
    (Pr : List UInt8 → Prop) [DecidablePred Pr] (j : Fin nx) (kj : XKey) :
    simulateQ (routeImpl Pr) (RJ guest fuel budget A j kj) =
      holeOut j kj <$> simulateQ (routeImpl Pr) (RJ guest fuel budget A j kj) := by
  have h : RJ guest fuel budget A j kj =
      LeanXmss.Concrete.sequenceFin (fun i : Fin nx ↦
        if i = j then pure kj else (LeanXmss.MultiUser.keygen : OracleComp OW _)) >>= fun xs ↦
      LeanXmss.Concrete.sequenceFin (fun _ : Fin ns ↦ (sKeygen : OracleComp OW _)) >>= fun ss ↦
        gameRest guest fuel budget A ⟨updJ j kj xs, ss⟩ := by
    unfold RJ
    conv_lhs => rw [sequenceFin_slot_self j kj]
    simp only [bind_assoc, pure_bind]
    rfl
  rw [h]
  simp only [simulateQ_bind, map_bind]
  refine bind_congr fun xs ↦ bind_congr fun ss ↦ ?_
  rw [map_route_gameRest_congr guest fuel budget A Pr _ (holeOut j kj) id fun z hz ↦ ?_, id_map]
  simp only [holeOut, setJ, hz, updJ_updJ, id]
  rw [← hz]
  rfl

/-- **The single-key game after key generation**: the reduction's run logged by the challenger,
then the final check. -/
noncomputable def contJ (guest : Program) (fuel budget : ℕ) (A : GameAdversary nx ns) (j : Fin nx)
    (kp : XKey) : OracleComp OW Bool :=
  (simulateQ (τJ kp.2) ((xBodyJ guest fuel budget A j kp.1).run ∅)).run >>= fun w ↦
    finishJ kp.1 (forgeryOfJ j w.1.1, w.2)

/-- **The single-key game against the per-key reduction**: key generation, then `contJ`. -/
theorem gameCore_xRedJ (guest : Program) (fuel budget : ℕ) (A : GameAdversary nx ns) (j : Fin nx) :
    LeanXmss.Security.gameCore (xRedJ guest fuel budget A j) =
      (LeanXmss.MultiUser.keygen : OracleComp OW _) >>= contJ guest fuel budget A j := by
  unfold LeanXmss.Security.gameCore LeanXmss.MultiUser.keygen contJ xRedJ
  simp only [bind_assoc]
  refine bind_congr fun seed ↦ bind_congr fun kp ↦ ?_
  simp only [StateT.run'_eq, simulateQ_map, WriterT.run_map', Functor.map_map, bind_map_left]
  rfl

/-- The game's event for reduction `j`: a win against key `j`, no coincidence at key `j`, and the
cache holding the trace. -/
def FJ (j : Fin nx) (o : (GameOutcome nx ns × Log) × QueryCache LeanXmss.HashSpec) : Prop :=
  XWinAt j o.1.1 o.1.2 ∧ ¬ KeyCollAt o.1.1.keys (Fin.castAdd ns j) ∧ XmssRed.CacheTr o.2 o.1.2

/-- Replacing key `j` twice keeps the last. -/
theorem holeOut_holeOut (j : Fin nx) (k k' : XKey) (z : GameOutcome nx ns × Log) :
    holeOut j k (holeOut j k' z) = holeOut j k z := by
  simp only [holeOut, withKeys, setJ, updJ_updJ]

/-- **The bound after key `j`'s generation.** From each output of key `j`'s generation, the
game's event in the rest is at most as likely as the single-key game's win after it. -/
theorem prEvent_RJ_le (guest : Program) (fuel budget : ℕ) (A : GameAdversary nx ns) (j : Fin nx)
    (r : XKey × QueryCache LeanXmss.HashSpec)
    (hr : r ∈ support (romRun (LeanXmss.MultiUser.keygen : OracleComp OW _) ∅)) :
    Pr{let o ← romRun (RJ guest fuel budget A j r.1) r.2}[FJ j o] ≤
      Pr{let b ← romRun (contJ guest fuel budget A j r.1) r.2}[b.1 = true] := by
  obtain ⟨hsk, hc0⟩ := keygen_cache_not_privJ r hr
  obtain ⟨⟨pkj, sk⟩, c0⟩ := r
  simp only at hsk hc0
  have hpj : LeanXmss.bytesLE 16 sk.parameter = LeanXmss.bytesLE 16 pkj.parameter := by rw [hsk]
  let pj := LeanXmss.bytesLE 16 sk.parameter
  let kj : XKey := (pkj, sk)
  let kj' : XKey := (pkj, holeKey pkj)
  let ev : GameOutcome nx ns × Log → QueryCache LeanXmss.HashSpec →
      QueryCache LeanXmss.HashSpec → Prop :=
    fun o cp c ↦ FJ j (holeOut j kj o, mergeCache (PrivJ pj) cp c) ∧ o.1.keys.xmss j = kj'
  have hc : ∀ x, PrivJ pj x → c0 x = none := fun x hx ↦ by
    by_contra h
    exact hc0 x h hx
  -- the game's rest is the class-routed rest, its caches merged
  have h1 : Pr{let o ← romRun (RJ guest fuel budget A j kj) c0}[FJ j o] =
      Pr{let z ← romRun ((simulateQ (routeImpl (PrivJ pj)) (RJ guest fuel budget A j kj)).run ∅) c0}[
        FJ j (z.1.1, mergeCache (PrivJ pj) z.1.2 z.2)] := by
    rw [← (evalDistEq_route (PrivJ pj) _ c0 hc).prEvent_eq, prEvent_map]
  -- key `j`'s secret key in the outcome replaced by the hole key
  have h2 : Pr{let z ← romRun ((simulateQ (routeImpl (PrivJ pj)) (RJ guest fuel budget A j kj)).run ∅) c0}[
        FJ j (z.1.1, mergeCache (PrivJ pj) z.1.2 z.2)] =
      Pr{let z ← romRun ((holeOut j kj' <$> simulateQ (routeImpl (PrivJ pj))
        (RJ guest fuel budget A j kj)).run ∅) c0}[ev z.1.1 z.1.2 z.2] := by
    conv_lhs => rw [route_RJ_self guest fuel budget A (PrivJ pj) j kj]
    rw [romRun_pm_map, romRun_pm_map, prEvent_map, prEvent_map]
    refine prEvent_congr _ _ _ fun z ↦ ?_
    simp only [ev, holeOut_holeOut]
    simp [holeOut, withKeys, setJ, updJ, kj']
  -- the event forces good keys
  have hev : ∀ z cp c, ev z cp c → GoodKeys (LeanXmss.bytesLE 16 sk.parameter) j (pkj, holeKey pkj)
      (z.1.keys.xmss, z.1.keys.sphincs) := by
    intro z cp c ⟨hF, hj⟩
    have hcoll : ¬ KeyCollAt z.1.keys (Fin.castAdd ns j) := by
      have h : ¬ KeyCollAt (setJ j kj z.1.keys) (Fin.castAdd ns j) := hF.2.1
      unfold KeyCollAt at h ⊢
      rwa [keyParams_setJ _ _ _ (by rw [hj]; exact hsk)] at h
    have := goodKeys_of_not_keyCollAt z.1.keys j kj' hj hcoll
    rw [hpj]
    exact this
  -- the reduction's view
  have h3 := prEvent_view guest fuel budget A sk pkj hsk j ev hev ∅ c0
  -- the reduction's run is the challenger's, its log forgotten
  have h4 : Pr{let z ← romRun ((outJ <$> ΦJ sk (xBodyJ guest fuel budget A j pkj)).run ∅) c0}[
        ev z.1.1 z.1.2 z.2] =
      Pr{let z ← romRun (simulateQ (τJ sk) ((xBodyJ guest fuel budget A j pkj).run ∅)).run c0}[
        ev (outJ z.1.1.1) z.1.1.2 z.2] := by
    rw [romRun_pm_map, prEvent_map, ΦJ, run_stMap, simulateQ_σJ_eq]
    simp only [romRun, simulateQ_map, StateT.run_map, prEvent_map]
  -- the check passes where the event holds
  have h5 : Pr{let z ← romRun (simulateQ (τJ sk) ((xBodyJ guest fuel budget A j pkj).run ∅)).run c0}[
        ev (outJ z.1.1.1) z.1.1.2 z.2] ≤
      Pr{let b ← romRun (contJ guest fuel budget A j (pkj, sk)) c0}[b.1 = true] := by
    unfold contJ
    rw [romRun_bind, ← prEvent_map (p := fun b ↦ b = true), map_bind]
    simp only [← StateT.run'_eq]
    refine XmssRed.le_prEvent_bind_of_pure _ _ _ fun z hz he ↦ ?_
    obtain ⟨hinv, hlog⟩ := xBodyJ_log guest fuel budget A sk j pkj ∅ z.1
      (fst_mem_support_of_mem_romRun hz)
    obtain ⟨hF, hj⟩ := he
    have hw := (xWinAt_holeOut j kj (outJ z.1.1.1) (by rw [hj])).mp hF.1
    have hk : (z.1.1.1.1.xmss j).1 = pkj := congrArg Prod.fst hj
    have hc := hF.2.2
    simp only [holeOut, pj, hpj] at hc
    exact run_finishJ j pkj z.1.1.1 z.1.2 z.1.1.2 z.2 hw hk hc hlog hinv
  calc Pr{let o ← romRun (RJ guest fuel budget A j kj) c0}[FJ j o]
      = _ := h1
    _ = _ := h2
    _ = _ := h3
    _ = _ := h4
    _ ≤ _ := h5

/-- **The per-key leanXMSS bound (P7b).** In the game with V_I's trace, a win against leanXMSS key
`j` (`XWinAt j`) without a coincidence of key `j`'s parameter (`KeyCollAt`) is at most as likely as
the per-key reduction's win in leanXMSS's single-key game. -/
theorem prEvent_xWinAt_le (guest : Program) (fuel budget : ℕ) (A : GameAdversary nx ns)
    (j : Fin nx) :
    Pr{let p ← gameRec guest fuel budget A}[XWinAt j p.1.1 p.1.2 ∧
        ¬ KeyCollAt p.1.1.keys (Fin.castAdd ns j)] ≤
      LeanXmss.Security.forgeAdvantage (xRedJ guest fuel budget A j) := by
  calc Pr{let p ← gameRec guest fuel budget A}[XWinAt j p.1.1 p.1.2 ∧
        ¬ KeyCollAt p.1.1.keys (Fin.castAdd ns j)]
      ≤ Pr{let p ← gameRec guest fuel budget A}[FJ j (p.1, logCache p.2)] := by
        refine prEvent_mono_of_support _ _ _ fun p hp h ↦ ⟨h.1, h.2, fun e he ↦ ?_⟩
        rw [logCache_apply, (gameRec_trace hp).1 e he]
        rfl
    _ = Pr{let o ← Prod.map id logCache <$> gameRec guest fuel budget A}[FJ j o] := by
        rw [prEvent_map]; rfl
    _ = Pr{let o ← romRun (simulateQ toW (gameCompRec guest fuel budget A)) ∅}[FJ j o] :=
        (evalDistEq_run_toW_nil _).prEvent_eq _
    _ = Pr{let o ← romRun ((LeanXmss.MultiUser.keygen : OracleComp OW _) >>= fun a ↦
          RJ guest fuel budget A j a) ∅}[FJ j o] := by
        rw [toW_gameCompRec]
        exact ((romRun_sequenceFin_front nx (fun _ ↦ LeanXmss.MultiUser.keygen) j
          (fun _ xs ↦ LeanXmss.Concrete.sequenceFin (fun _ : Fin ns ↦ (sKeygen : OracleComp OW _)) >>=
            fun ss ↦ gameRest guest fuel budget A ⟨xs, ss⟩) ∅).prEvent_eq _).symm
    _ ≤ Pr{let b ← romRun ((LeanXmss.MultiUser.keygen : OracleComp OW _) >>=
          contJ guest fuel budget A j) ∅}[b.1 = true] := by
        rw [romRun_bind, romRun_bind]
        exact prEvent_bind_mono_of_forall_le_of_support _ _ _ _ _ fun r hr ↦
          prEvent_RJ_le guest fuel budget A j r hr
    _ = LeanXmss.Security.forgeAdvantage (xRedJ guest fuel budget A j) := by
        rw [forgeAdvantage_eq', gameCore_xRedJ, StateT.run'_eq, prEvent_map]

end PerKeyX

end
end LeanVM.E2E
