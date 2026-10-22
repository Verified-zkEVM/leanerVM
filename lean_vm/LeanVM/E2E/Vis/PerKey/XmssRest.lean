/-
  LeanVM.E2E.Vis.PerKey.XmssRest

  W-vis, P7b: after the keys, the per-key leanXMSS reduction's run under the single-key game's
  oracles is the class-routed game, when no other key's parameter is key `j`'s.
-/

module

public import LeanVM.E2E.Vis.PerKey.XmssRun
public import LeanVM.E2E.Vis.PerKey.RouteFacts
public import LeanVM.E2E.Vis.WalkSphincs

/-!
# The reduction's rest is the class-routed game (W-vis, P7b)

For keys whose other parameters are not key `j`'s (`GoodJ`):

* every input of another key's signer is in the private class (`privJ_of_schemeInputN`), so the
  reduction's private signing is the class-routed signing;
* every input of key `j`'s signer is outside it (`not_privJ_of_schemeInput`), so the class-routed
  signing of key `j` is its signer, which is what the single-key game's signing oracle runs.

Hence the reduction's answers to the adversary, under the game's oracles, are the class-routed
game's (`stMap_ΦJ_advImplJ`), and so is the reduction's whole run after the keys
(`map_ΦJ_restJ`), the keys in its outcome holding key `j`'s place by `holeKey`.
-/

namespace LeanVM.E2E

open LeanVM.Parameters LeanVM.Semantics LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Rom
open OracleSpec OracleComp
open scoped ENNReal

@[expose] public section

/-! ## The private class and the schemes' inputs -/

/-- A parameter-prefixed input is address-shaped. -/
theorem ParamPrefixed.addrShaped {p x : Bytes} (hp : p.length = 16) (h : ParamPrefixed p x) :
    AddrShaped x := by
  obtain ⟨a, ha, r, rfl⟩ := h
  have ha16 := ha.1
  refine ⟨by simp [hp, ha16]; omega, ?_⟩
  have e : ((p ++ a ++ r).drop 16).take 16 = a := by
    rw [List.append_assoc, List.drop_append_of_le_length (by omega), List.drop_eq_nil_of_le
      (by omega), List.nil_append, List.take_append_of_le_length (by omega),
      List.take_of_length_le (by omega)]
  rw [e]; exact ha

/-- **Another key's input is private**: a scheme input of a parameter other than `pj`, not
shaped as a derivation, is in `PrivJ pj`. -/
theorem privJ_of_schemeInputN {p pj x : Bytes} (hp : p.length = 16) (hpj : pj.length = 16)
    (hne : p ≠ pj) (h : SchemeInputN p x) : PrivJ pj x := by
  refine ⟨h.1.1.addrShaped hp, h.2, fun hx ↦ hne ?_⟩
  obtain ⟨a, -, r, hr⟩ := h.1.1
  obtain ⟨r', hr'⟩ := hx
  have h1 := congrArg (List.take 16) hr
  have h2 := congrArg (List.take 16) hr'
  rw [List.append_assoc, List.take_append_of_le_length (by omega),
    List.take_of_length_le (by omega)] at h1
  rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)] at h2
  exact h1.trans h2.symm

/-- **Key `j`'s input is not private**: a scheme input of `pj` is outside `PrivJ pj`. -/
theorem not_privJ_of_schemeInput {pj x : Bytes} (h : SchemeInput pj x) : ¬ PrivJ pj x := by
  rintro ⟨-, -, hx⟩
  obtain ⟨a, -, r, rfl⟩ := h.1
  exact hx ⟨a ++ r, by rw [List.append_assoc]⟩

/-! ## Routing through the game's translation -/

section Tw

variable {nx ns : ℕ}

/-- **Routing a translated simulation** is simulating with the routed translated handler. -/
theorem route_tw_simulateQ {m : Type → Type} [Monad m] [LawfulMonad m] (R : QueryImpl OW m)
    {ι : Type} {spec : OracleSpec.{0, 0} ι} (impl : QueryImpl spec (GameM nx ns)) {α : Type}
    (oa : OracleComp spec α) (st : SignState nx ns) :
    simulateQ R (tw (simulateQ impl oa) st) =
      (simulateQ (fun t ↦ (StateT.mk fun st ↦ simulateQ R (tw (impl t) st) :
        StateT (SignState nx ns) m _)) oa).run st := by
  induction oa using OracleComp.inductionOn generalizing st with
  | pure x => simp [tw_pure]
  | query_bind t k ih =>
    rw [simulateQ_query_bind, simulateQ_query_bind]
    simp only [OracleQuery.input_query, monadLift_self]
    rw [tw_bind, simulateQ_bind, StateT.run_bind]
    simp only [StateT.run_mk]
    exact bind_congr fun p ↦ ih p.1 p.2

variable [Sphincs.Params]

/-- The game's leanXMSS signing oracle, translated. -/
theorem tw_xmssSign_eq (keys : Keys nx ns) (i : Fin nx) (req : XmssRequest) (st : SignState nx ns) :
    tw (xmssSign keys i req) st =
      if ((st.xlog i).any fun e ↦ decide (e.1.1 = req.1)) = true then pure (none, st)
      else (fun σ ↦ (σ, { st with xlog := Function.update st.xlog i (st.xlog i ++ [(req, σ)]) })) <$>
        (liftM (LeanXmss.Seeded.sign (keys.xmss i).2 req.1 req.2 :
          OracleComp LeanXmss.HashSpec _) : OracleComp OW _) := by
  unfold xmssSign
  by_cases h : ((st.xlog i).any fun e ↦ decide (e.1.1 = req.1)) = true
  · simp [h, tw]
  · simp only [h, Bool.false_eq_true, ↓reduceIte]
    rw [tw_bind]
    simp only [tw, StateT.run_get, simulateQ_pure, pure_bind, h, Bool.false_eq_true, ↓reduceIte]
    have h₁ := tw_xmssRun (nx := nx) (ns := ns) (LeanXmss.Seeded.sign (keys.xmss i).2 req.1 req.2) st
    unfold tw at h₁
    rw [StateT.run_bind, simulateQ_bind, h₁]
    simp [map_eq_bind_pure_comp, bind_assoc, StateT.run_modify]

/-- The game's leanSPHINCS signing oracle, translated. -/
theorem tw_sphincsSign_eq (keys : Keys nx ns) (i : Fin ns) (msg : Sphincs.Message)
    (st : SignState nx ns) :
    tw (sphincsSign keys i msg) st =
      if Sphincs.signatureLimit ≤ (st.slog i).length then pure (none, st)
      else (fun σ ↦ (σ, { st with slog := Function.update st.slog i (st.slog i ++ [(msg, σ)]) })) <$>
        sLift (Sphincs.Seeded.sign (keys.sphincs i).2 msg : OracleComp Sphincs.HashSpec _) := by
  unfold sphincsSign
  by_cases h : Sphincs.signatureLimit ≤ (st.slog i).length
  · simp [h, tw]
  · simp only [h, ↓reduceIte]
    rw [tw_bind]
    simp only [tw, StateT.run_get, simulateQ_pure, pure_bind, h, ↓reduceIte]
    have h₁ := tw_sphincsRun (nx := nx) (ns := ns) (Sphincs.Seeded.sign (keys.sphincs i).2 msg) st
    unfold tw at h₁
    rw [StateT.run_bind, simulateQ_bind, h₁]
    simp [map_eq_bind_pure_comp, bind_assoc, StateT.run_modify]

end Tw

/-! ## The reduction's answers are the class-routed game's -/

namespace PerKeyX

variable {nx ns : ℕ} [Sphincs.Params]

/-- **Good keys for reduction `j`**: no other key's parameter is `pj`. -/
def GoodJ (pj : Bytes) (j : Fin nx) (keys : Keys nx ns) : Prop :=
  (∀ i, i ≠ j → LeanXmss.bytesLE 16 (keys.xmss i).2.parameter ≠ pj) ∧
    ∀ i, Sphincs.bytesLE 16 (keys.sphincs i).2.parameter ≠ pj

/-- **The class-routed game's answers to the adversary.** -/
noncomputable def gAdv (pj : Bytes) (keys : Keys nx ns) :
    QueryImpl (AdvSpec nx ns) (StateT (SignState nx ns) PM) :=
  fun t ↦ StateT.mk fun st ↦ simulateQ (routeImpl (PrivJ pj)) (tw (advImpl keys t) st)

omit [Sphincs.Params] in
theorem length_bytesLE16_x (p : LeanXmss.PublicParameter) : (LeanXmss.bytesLE 16 p).length = 16 := by
  simp [LeanXmss.bytesLE]

omit [Sphincs.Params] in
theorem length_bytesLE16_s (p : Sphincs.PublicParameter) : (Sphincs.bytesLE 16 p).length = 16 := by
  simp [Sphincs.bytesLE]

omit [Sphincs.Params] in
/-- Key `j`'s forwarded request, run. -/
theorem run_xmssFwdJ (j : Fin nx) (req : XmssRequest) (st : SignState nx ns) :
    (xmssFwdJ j req).run st =
      if ((st.xlog j).any fun e ↦ decide (e.1.1 = req.1)) = true then pure (none, st)
      else (fun σ ↦ (σ, { st with xlog := Function.update st.xlog j (st.xlog j ++ [(req, σ)]) })) <$>
        (liftM (liftM (RS.query (.inr ⟨req.1, req.2⟩)) : OracleComp RS (Option LeanXmss.Signature)) :
          RM (Option LeanXmss.Signature)) := by
  by_cases h : ((st.xlog j).any fun e ↦ decide (e.1.1 = req.1)) = true
  · simp [xmssFwdJ, h]
  · simp only [xmssFwdJ, h, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get,
      pure_bind, OracleComp.liftM_run_StateT, bind_assoc, StateT.run_modify, StateT.run_pure,
      map_eq_bind_pure_comp]
    rfl

/-- The class-routed and the private run of a translated leanXMSS signing oracle agree, when the
signing key's parameter is not `pj`. -/
theorem route_tw_xmssSign_priv (pj : Bytes) (hpj : pj.length = 16) (keys : Keys nx ns) (i : Fin nx)
    (hi : LeanXmss.bytesLE 16 (keys.xmss i).2.parameter ≠ pj) (req : XmssRequest)
    (st : SignState nx ns) :
    simulateQ (routeImpl (fun _ ↦ True)) (tw (xmssSign keys i req) st) =
      simulateQ (routeImpl (PrivJ pj)) (tw (xmssSign keys i req) st) := by
  refine simulateQ_routeImpl_congr _ _ ?_
  rw [tw_xmssSign_eq]
  split
  · exact allQueriesSatisfy_pure _ _
  · rw [map_eq_bind_pure_comp]
    refine allQueriesSatisfy_bind ?_ fun _ ↦ allQueriesSatisfy_pure _ _
    refine (allQueriesSatisfy_liftM_hash ((queriesSat_iff _ _).mp
      (xmss_sign_queriesN (keys.xmss i).2 req.1 req.2))).mono fun t ht x hx ↦ ?_
    exact ⟨fun _ ↦ privJ_of_schemeInputN (length_bytesLE16_x _) hpj hi (ht x hx), fun _ ↦ trivial⟩

/-- The class-routed and the private run of a translated leanSPHINCS signing oracle agree, when the
signing key's parameter is not `pj`. -/
theorem route_tw_sphincsSign_priv (pj : Bytes) (hpj : pj.length = 16) (keys : Keys nx ns)
    (i : Fin ns) (hi : Sphincs.bytesLE 16 (keys.sphincs i).2.parameter ≠ pj) (msg : Sphincs.Message)
    (st : SignState nx ns) :
    simulateQ (routeImpl (fun _ ↦ True)) (tw (sphincsSign keys i msg) st) =
      simulateQ (routeImpl (PrivJ pj)) (tw (sphincsSign keys i msg) st) := by
  refine simulateQ_routeImpl_congr _ _ ?_
  rw [tw_sphincsSign_eq]
  split
  · exact allQueriesSatisfy_pure _ _
  · rw [map_eq_bind_pure_comp]
    refine allQueriesSatisfy_bind ?_ fun _ ↦ allQueriesSatisfy_pure _ _
    refine (allQueriesSatisfy_sLift ((queriesSat_iff _ _).mp
      (sphincs_sign_queriesN (keys.sphincs i).2 msg))).mono fun t ht x hx ↦ ?_
    exact ⟨fun _ ↦ privJ_of_schemeInputN (length_bytesLE16_s _) hpj hi (ht x hx), fun _ ↦ trivial⟩

omit [Sphincs.Params] in
/-- **Key `j`'s signer is forwarded** by the class-routed game: its inputs are `pj`'s. -/
theorem route_liftM_sign_j (sk : LeanXmss.Seeded.SecretKey) (i : LeanXmss.LeafIndex)
    (m : LeanXmss.Message) :
    simulateQ (routeImpl (PrivJ (LeanXmss.bytesLE 16 sk.parameter)))
        (liftM (LeanXmss.Seeded.sign sk i m : OracleComp LeanXmss.HashSpec _) : OracleComp OW _) =
      liftM (liftM (LeanXmss.Seeded.sign sk i m : OracleComp LeanXmss.HashSpec _) :
        OracleComp OW _) := by
  refine simulateQ_routeImpl_of_off _ ?_
  refine (allQueriesSatisfy_liftM_hash ((queriesSat_iff _ _).mp
    (xmss_sign_queries sk i m))).mono fun t ht x hx ↦ not_privJ_of_schemeInput (ht x hx)

omit [Sphincs.Params] in
/-- `ΦJ` of a pure computation. -/
theorem ΦJ_pure (sk : LeanXmss.Seeded.SecretKey) {α : Type} (a : α) :
    ΦJ sk (pure a : RM α) = pure a := (isMorphism_ΦJ sk).pure a

omit [Sphincs.Params] in
/-- `ΦJ` of a map. -/
theorem ΦJ_map (sk : LeanXmss.Seeded.SecretKey) {α β : Type} (f : α → β) (x : RM α) :
    ΦJ sk (f <$> x) = f <$> ΦJ sk x := by
  rw [map_eq_bind_pure_comp, (isMorphism_ΦJ sk).bind, map_eq_bind_pure_comp]
  exact bind_congr fun a ↦ ΦJ_pure sk _

/-- The adversary's coins and hash queries do not read the keys. -/
theorem advImpl_inl_inl (keys keys' : Keys nx ns) (t : (unifSpec + HashSpec).Domain) :
    advImpl keys (.inl (.inl t)) = advImpl keys' (.inl (.inl t)) := by
  simp only [advImpl, QueryImpl.add_apply_inl]

theorem advImpl_xmss (keys : Keys nx ns) (i : Fin nx) (req : XmssRequest) :
    advImpl keys (.inl (.inr (i, req))) = xmssSign keys i req := rfl

theorem advImpl_sphincs (keys : Keys nx ns) (i : Fin ns) (msg : Sphincs.Message) :
    advImpl keys (.inr (i, msg)) = sphincsSign keys i msg := rfl

theorem advImplJ_inl_inl (pj : Bytes) (j : Fin nx) (keys : Keys nx ns)
    (t : (unifSpec + HashSpec).Domain) :
    advImplJ pj j keys (.inl (.inl t)) =
      StateT.mk fun st ↦ rc pj (tw (advImpl keys (.inl (.inl t))) st) := rfl

theorem advImplJ_xmss_self (pj : Bytes) (j : Fin nx) (keys : Keys nx ns) (req : XmssRequest) :
    advImplJ pj j keys (.inl (.inr (j, req))) = xmssFwdJ j req := by
  simp [advImplJ]

theorem advImplJ_xmss_ne (pj : Bytes) (j : Fin nx) (keys : Keys nx ns) {i : Fin nx} (hij : i ≠ j)
    (req : XmssRequest) :
    advImplJ pj j keys (.inl (.inr (i, req))) =
      StateT.mk fun st ↦ rp (tw (xmssSign keys i req) st) := by
  simp [advImplJ, hij, advImpl_xmss]

theorem advImplJ_sphincs (pj : Bytes) (j : Fin nx) (keys : Keys nx ns) (i : Fin ns)
    (msg : Sphincs.Message) :
    advImplJ pj j keys (.inr (i, msg)) = StateT.mk fun st ↦ rp (tw (sphincsSign keys i msg) st) :=
  rfl

theorem run_gAdv (pj : Bytes) (keys : Keys nx ns) (t : (AdvSpec nx ns).Domain)
    (st : SignState nx ns) :
    (gAdv pj keys t).run st = simulateQ (routeImpl (PrivJ pj)) (tw (advImpl keys t) st) := rfl

/-- **The reduction's answers, under the game's oracles, are the class-routed game's**, for good
keys: the reduction's keys `keysR` are the game's `keysG` but for key `j`'s secret key, which the
game's signing oracle holds. -/
theorem stMap_ΦJ_advImplJ (sk : LeanXmss.Seeded.SecretKey) (j : Fin nx) (keysR keysG : Keys nx ns)
    (hx : ∀ i, i ≠ j → keysR.xmss i = keysG.xmss i) (hs : keysR.sphincs = keysG.sphincs)
    (hj : (keysG.xmss j).2 = sk) (hgood : GoodJ (LeanXmss.bytesLE 16 sk.parameter) j keysG)
    (t : (AdvSpec nx ns).Domain) :
    stMap (fun {β : Type} (y : RM β) ↦ ΦJ sk y)
        (advImplJ (LeanXmss.bytesLE 16 sk.parameter) j keysR t) =
      gAdv (LeanXmss.bytesLE 16 sk.parameter) keysG t := by
  have hpj : (LeanXmss.bytesLE 16 sk.parameter).length = 16 := length_bytesLE16_x _
  refine StateT.ext fun st ↦ ?_
  rw [run_stMap, run_gAdv]
  rcases t with (t | ⟨i, req⟩) | ⟨i, msg⟩
  · rw [advImplJ_inl_inl, StateT.run_mk, ΦJ_rc, advImpl_inl_inl keysR keysG]
  · rw [advImpl_xmss]
    by_cases hij : i = j
    · subst hij
      rw [advImplJ_xmss_self, run_xmssFwdJ, tw_xmssSign_eq, hj]
      split
      · rw [ΦJ_pure, simulateQ_pure]
      · rw [ΦJ_map, simulateQ_map, ΦJ_signQuery, route_liftM_sign_j]
    · rw [advImplJ_xmss_ne _ _ _ hij, StateT.run_mk, ΦJ_rp]
      have hkey : xmssSign keysR i req = xmssSign keysG i req := by
        unfold xmssSign; rw [hx i hij]
      rw [hkey]
      exact route_tw_xmssSign_priv _ hpj keysG i (hgood.1 i hij) req st
  · rw [advImpl_sphincs, advImplJ_sphincs, StateT.run_mk, ΦJ_rp]
    have hkey : sphincsSign keysR i msg = sphincsSign keysG i msg := by
      unfold sphincsSign; rw [hs]
    rw [hkey]
    exact route_tw_sphincsSign_priv _ hpj keysG i (hgood.2 i) msg st

omit [Sphincs.Params] in
/-- `ΦJ` of a bind. -/
theorem ΦJ_bind (sk : LeanXmss.Seeded.SecretKey) {α β : Type} (x : RM α) (f : α → RM β) :
    ΦJ sk (x >>= f) = ΦJ sk x >>= fun a ↦ ΦJ sk (f a) := (isMorphism_ΦJ sk).bind x f

/-- An outcome with other keys. -/
def withKeys (keys : Keys nx ns) (z : GameOutcome nx ns) : GameOutcome nx ns := { z with keys := keys }

/-- **The reduction's adversary phase, under the game's oracles, is the class-routed game's.** -/
theorem ΦJ_adv (sk : LeanXmss.Seeded.SecretKey) (j : Fin nx) (keysR keysG : Keys nx ns)
    (hx : ∀ i, i ≠ j → keysR.xmss i = keysG.xmss i) (hs : keysR.sphincs = keysG.sphincs)
    (hj : (keysG.xmss j).2 = sk) (hgood : GoodJ (LeanXmss.bytesLE 16 sk.parameter) j keysG)
    {α : Type} (oa : OracleComp (AdvSpec nx ns) α) (st : SignState nx ns) :
    ΦJ sk ((simulateQ (advImplJ (LeanXmss.bytesLE 16 sk.parameter) j keysR) oa).run st) =
      simulateQ (routeImpl (PrivJ (LeanXmss.bytesLE 16 sk.parameter)))
        (tw (simulateQ (advImpl keysG) oa) st) := by
  have h1 := simulateQ_morph (isMorphism_stMap (σ := SignState nx ns) (isMorphism_ΦJ sk))
    (advImplJ (LeanXmss.bytesLE 16 sk.parameter) j keysR) oa
  have h2 := congrArg (fun x ↦ StateT.run x st) h1
  simp only [run_stMap] at h2
  rw [← h2, route_tw_simulateQ]
  have hh : (fun t ↦ stMap (fun {β : Type} (y : RM β) ↦ ΦJ sk y)
      (advImplJ (LeanXmss.bytesLE 16 sk.parameter) j keysR t)) =
      gAdv (LeanXmss.bytesLE 16 sk.parameter) keysG :=
    funext fun t ↦ stMap_ΦJ_advImplJ sk j keysR keysG hx hs hj hgood t
  rw [hh]
  rfl

/-- **The reduction's run after the keys, under the game's oracles, is the class-routed game's
rest**, its outcome's keys the reduction's. -/
theorem map_ΦJ_restJ (guest : Program) (fuel budget : ℕ) (A : GameAdversary nx ns)
    (sk : LeanXmss.Seeded.SecretKey) (j : Fin nx) (keysR keysG : Keys nx ns)
    (hx : ∀ i, i ≠ j → keysR.xmss i = keysG.xmss i) (hs : keysR.sphincs = keysG.sphincs)
    (hj : (keysG.xmss j).2 = sk) (hpk : (keysR.xmss j).1 = (keysG.xmss j).1)
    (hgood : GoodJ (LeanXmss.bytesLE 16 sk.parameter) j keysG) :
    outJ <$> ΦJ sk (restJ guest fuel budget A (LeanXmss.bytesLE 16 sk.parameter) j keysR) =
      (fun z ↦ (withKeys keysR z.1, z.2)) <$>
        simulateQ (routeImpl (PrivJ (LeanXmss.bytesLE 16 sk.parameter)))
          (gameRest guest fuel budget A keysG) := by
  have hpub : (fun i ↦ (keysR.xmss i).1) = fun i ↦ (keysG.xmss i).1 := by
    funext i
    by_cases hij : i = j
    · subst hij; exact hpk
    · rw [hx i hij]
  unfold restJ gameRest
  rw [ΦJ_bind, ΦJ_adv sk j keysR keysG hx hs hj hgood, hpub, hs]
  simp only [simulateQ_bind, map_bind]
  refine bind_congr fun q ↦ ?_
  rw [ΦJ_bind, rc, ΦJ_rImpl, map_bind]
  refine bind_congr fun q' ↦ ?_
  rw [ΦJ_pure, simulateQ_pure, map_pure, map_pure]
  rfl

end PerKeyX

end
end LeanVM.E2E
