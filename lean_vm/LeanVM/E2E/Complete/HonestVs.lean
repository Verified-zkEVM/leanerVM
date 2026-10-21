/-
  LeanVM.E2E.Complete.HonestVs

  `verify_sub`'s body at its honest frames under the honest run's table: its exponent tables,
  computed by `main` and handed down `__loop5`'s iterations, are its precondition.
-/

module

public import LeanVM.E2E.Complete.HonestBodies
public import LeanVM.Guest.B2C.Sites

/-!
# `verify_sub` at its honest frames

`verify_sub`'s precondition (`Pre glob L 16`) holds its arguments `4`, `5` (cells `6`, `7`) to be
exponent tables (`B1.ExpTables`, `End.vs_sem`). The honest values come down from `main`:

* `main` computes the tables (`exponent_tables`, values `65`, `66`), and its located body under
  the honest run's table gives them the meaning (`End.knownB_main`), read at its frame
  (`FrameHolds.val`);
* `main` calls `__loop5` with them as arguments `16`, `6` (`main_sites_loop5`, decided on its
  body), and each `__loop5` iteration hands its arguments `16`, `6` on unchanged to the next
  (`loop5_sites_loop5`) and to `verify_sub` as its arguments `4`, `5` (`loop5_sites_vs`);
* so at every `__loop5` iteration down from `main` (`honest_exp_root`, `honest_exp_loop`) its
  arguments `16`, `6` are exponent tables, and so are its `verify_sub` callee's frame cells `6`,
  `7` (`FrameHolds.kid`): `verify_sub`'s body holds at its honest frame (`honest_vs_bodyAt`,
  `honest_bodyAt` at `j = 16`).

`honest_frame_val`: the honest memory reads every value a node instance's path names at its cell
(`FrameHolds.val`), for the decoder's statements.
-/

namespace LeanVM.E2E.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Check LeanVM.Guest.Value
open LeanVM.Guest.End (mainEntry JumpTables)

@[expose] public section

/-! ## The call sites, decided -/

theorem idxOf_loop5 : B2C.idxOf "__loop5" = some 36 := by decide +kernel

theorem idxOf_vs : B2C.idxOf "verify_sub" = some 16 := by decide +kernel

theorem idxOf_main' : B2C.idxOf "main" = some 1 := by decide +kernel

theorem loop5_params : (coreOf 36).params = (List.range 18).map V.n := by decide +kernel

theorem loop5_name : (coreOf 36).name = "__loop5" := by decide +kernel

theorem vs_plain : (certOf 16).pre = [] ∧ (certOf 16).mem = [] := by decide +kernel

/-- `main` calls `__loop5` with its exponent tables `66`, `65` as arguments `6`, `16`. -/
theorem main_sites_loop5 : ∀ p ∈ B2C.blockSites (coreOf 1).body, p.1 = "__loop5" →
    p.2[6]? = some (V.n 66) ∧ p.2[16]? = some (V.n 65) := by decide +kernel

/-- `__loop5` calls itself with its arguments `1, …, 17` unchanged. -/
theorem loop5_sites_loop5 : ∀ p ∈ B2C.blockSites (coreOf 36).body, p.1 = "__loop5" →
    p.2 = .n 87 :: (List.range 17).map (fun i ↦ V.n (i + 1)) := by decide +kernel

/-- `__loop5` calls `verify_sub` with its arguments `16`, `6` as `verify_sub`'s `4`, `5`. -/
theorem loop5_sites_vs : ∀ p ∈ B2C.blockSites (coreOf 36).body, p.1 = "verify_sub" →
    p.2 = [.n 65, .n 66, .n 13, .n 14, .n 16, .n 6, .n 79] := by decide +kernel

/-- `main`'s exponent tables' cells. -/
theorem main_exp_cells : 2 ≤ B2C.cellJ 1 (V.n 65) ∧ B2C.cellJ 1 (V.n 65) < B2C.fsN 1 ∧
    2 ≤ B2C.cellJ 1 (V.n 66) ∧ B2C.cellJ 1 (V.n 66) < B2C.fsN 1 := by decide +kernel

/-! ## Callees on a path -/

/-- **The `i`-th callee of a valid node, a node, is the `i`-th call's**, entered, valid on its
words. -/
theorem kid_call {S : BlakeSem} {rd : Reader} {σ : Val} {es : List Ev} {kids : List Tree}
    (hkv : Tree.KidsValidB S coreProgram rd σ (calls es) kids) {i : ℕ} {k : Tree}
    (hk : kids[i]? = some k) {f : String} {σ' : Val} {b : List ℕ} {ks : List Tree}
    (hn : k = .node f σ' b ks) :
    ∃ c, (calls es)[i]? = some c ∧ c.f = f ∧
      k.ValidB S coreProgram rd (c.args.map σ) (c.rets.map σ) := by
  have hkvg := B2C.kidsValidB_get hkv
  have hlen : i < (calls es).length := by
    rw [← hkvg.1]
    exact (List.getElem?_eq_some_iff.mp hk).1
  obtain ⟨c, hc⟩ : ∃ c, (calls es)[i]? = some c := ⟨_, List.getElem?_eq_getElem hlen⟩
  obtain ⟨k', hk', hkn, hkval⟩ := hkvg.2 i c hc
  obtain rfl : k' = k := Option.some.inj (hk'.symm.trans hk)
  have htk := B2C.kidsValidB_taken hkv hc (hk.trans (by rw [hn]))
  refine ⟨c, hc, ?_, hkval htk⟩
  rw [← hkn, hn]
  rfl

/-- The arguments of a call on a path are values the path names. -/
theorem args_named {j : ℕ} {es : List Ev} {vs : List V} {c : Call} (hc : c ∈ calls es) {v : V}
    (hv : v ∈ c.args) : v ∈ B2C.namedOf (coreOf j).params es vs := by
  obtain ⟨e, he, hec⟩ := List.mem_filterMap.mp hc
  refine B2C.uses_named he ?_
  rcases e with _ | _ | ⟨f, args, rets⟩ | ⟨f, args⟩ <;> simp only [Ev.call?, reduceCtorEq,
    Option.some.injEq] at hec
  · subst hec; exact List.mem_append_left _ hv
  · subst hec; exact hv

section Honest

variable {S : BlakeSem} (hfun : B2C.SemFunctional S)
  (hcan : ∀ {m : Fin 4 → E} {cv0 cv1 o0 o1 md : E}, S.check m cv0 cv1 o0 o1 md →
    CanonicalCells m cv0 cv1 o0 o1 md)
  {hdr : E × E} {rd : Reader} {T : Tree} (hname : T.name = "main")
  (hH : HonestAtB S coreProgram B2C.fs B2C.H B2C.C hdr T B2C.cert rd [] [])
  {n : ℕ} (hrun : runB S guest (honest coreProgram B2C.fs B2C.H B2C.C hdr T) n Regs.initial =
    some (Regs.final guest))

include hfun hname hH in
/-- **The honest memory reads every value a node instance's path names at its cell**
(`FrameHolds.val`). -/
theorem honest_frame_val {I : Inst} (hI : I ∈ honestInsts coreProgram B2C.fs B2C.H hdr T)
    {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node f σ bufs kids)
    {j : ℕ} (hj : B2C.idxOf f = some j) {es : List Ev} {vs : List V}
    (hw : walk σ (coreOf j).body = .ret es vs) :
    ∀ v ∈ B2C.namedOf (coreOf j).params es vs, 2 ≤ B2C.cellJ j v → B2C.cellJ j v < B2C.fsN j →
      (honest coreProgram B2C.fs B2C.H B2C.C hdr T).read (gpow (I.fp + B2C.cellJ j v)) = some (σ v) :=
  ((B2C.b2HypsB hfun).frame hdr rd T hname hH I hI f σ bufs kids ht j hj es vs hw).val

include hfun hname hH in
/-- **The decoder's valuation at an honest frame is the instance's** on every value its path
names (`Located.valAt`, `honest_frame_val`). -/
theorem honest_valAt {I : Inst} (hI : I ∈ honestInsts coreProgram B2C.fs B2C.H hdr T)
    {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node f σ bufs kids)
    {j : ℕ} (hj : B2C.idxOf f = some j) {es : List Ev} {vs : List V}
    (hw : walk σ (coreOf j).body = .ret es vs) {v : V} (hv : v ∈ B2C.namedOf (coreOf j).params es vs)
    (h2 : 2 ≤ B2C.cellJ j v) (hn : B2C.cellJ j v < B2C.fsN j) :
    Located.valAt (honest coreProgram B2C.fs B2C.H B2C.C hdr T) f I.fp v = σ v := by
  obtain ⟨i, rfl, hi, hn', hfind, hcore, -, -, h1, hlt⟩ := B2C.fn_of_idx hj
  have hcn : (coreOf (i + 1)).name = f := by rw [hcore]; exact hn'
  have hr := honest_frame_val hfun hname hH hI ht hj hw v hv h2 hn
  unfold Located.valAt frameVal valG wd
  rw [← hcn, certByName_coreOf h1 hlt, show gpow I.fp * gpow ((certOf (i + 1)).locs.getD v.idx 0) =
    gpow (I.fp + B2C.cellJ (i + 1) v) by rw [gpow, gpow, gpow, pow_add]; rfl, hr]
  rfl

include hfun hcan hname hH hrun in
/-- **`main`'s exponent tables reach its `__loop5` callee** as its arguments `16`, `6`. -/
theorem honest_exp_root {R P : Inst} (hR : R ∈ honestInsts coreProgram B2C.fs B2C.H hdr T)
    (hRt : R.t = T) (hRfp : R.fp = 0) {i : ℕ} (hk : R.t.kids[i]? = some P.t) {σP : Val} {bufs : List ℕ} {kids : List Tree}
    (hPt : P.t = .node "__loop5" σP bufs kids) :
    B1.ExpTables (honest coreProgram B2C.fs B2C.H B2C.C hdr T).read (σP (V.n 16)) (σP (V.n 6)) := by
  set L := honest coreProgram B2C.fs B2C.H B2C.C hdr T with hL
  have hvR : R.t.ValidB S coreProgram L.read [] [] := by rw [hRt]; exact hH.toHonestB.valid_image
  rcases hRt' : R.t with ⟨fR, σR, bufsR, kidsR⟩ | ⟨fR, σR⟩
  · rw [hRt'] at hvR hk
    have hfR : fR = "main" := by rw [← hname, ← hRt, hRt']; rfl
    subst hfR
    obtain ⟨fn, hf, -, es, vs, hw, -, -, hkv⟩ := hvR
    obtain ⟨-, -, -, -, -, -, hname'⟩ := End.main_facts
    obtain rfl : fn = coreOf 1 := Option.some.inj
      (hf.symm.trans (by rw [← hname']; exact End.coreOf_find le_rfl (by decide)))
    obtain ⟨c, hc, hcf, hvP⟩ := kid_call hkv hk hPt
    have hcm : c ∈ calls es := List.mem_of_getElem? hc
    obtain ⟨h6, h16⟩ := main_sites_loop5 _ (B2C.walk_sites (σ := σR) _ (by rw [hw]; exact hcm)) hcf
    -- `__loop5`'s values are `main`'s
    rw [hPt] at hvP
    obtain ⟨fnP, hfP, hparP, -⟩ := hvP
    obtain rfl : fnP = coreOf 36 := Option.some.inj
      (hfP.symm.trans (by rw [← loop5_name]; exact End.coreOf_find (by decide) (by decide)))
    rw [loop5_params] at hparP
    have e16 : σP (V.n 16) = σR (V.n 65) := by
      have := congrArg (fun l ↦ l[16]?) hparP
      simpa [h16] using this
    have e6 : σP (V.n 6) = σR (V.n 66) := by
      have := congrArg (fun l ↦ l[6]?) hparP
      simpa [h6] using this
    rw [e16, e6]
    -- `main`'s tables, from its located body under the honest run's table
    obtain ⟨h16', h32⟩ := honest_logMem hH
    have hs : SafeB (honestSem hdr T n) guest L n ⟨gpow 0, 1⟩ := by
      have := honest_safe_initial hcan hrun
      rwa [show (Regs.initial : Regs K) = ⟨gpow 0, 1⟩ by rw [gpow, pow_zero]; rfl] at this
    have hb := End.mainBodyLB_of_safe (honest_vsKnown hfun hcan hrun) (B1.expKnownB _) h16' h32 hs
    obtain ⟨hlen, -, hsm⟩ := End.main_cut
    rw [← List.take_append_drop ((certOf 1).cutAt 1).start (coreOf 1).body, holdsListB_append] at hb
    obtain ⟨-, hsem⟩ := End.knownB_main (B1.expKnownB _) (i := 1) (by rw [hlen]) (by decide)
      (holdsListB_mono (relLB_le_rel _) _ (fun _ ↦ trivial) (fun _ _ ↦ trivial) hb)
    rw [hsm] at hsem
    have hx := hsem _ List.mem_cons_self
    -- read at `main`'s frame
    have hF := (B2C.b2HypsB hfun).frame hdr rd T hname hH R hR "main" σR bufsR kidsR hRt' 1
      idxOf_main' es vs hw
    obtain ⟨a1, a2, b1, b2⟩ := main_exp_cells
    have r65 := hF.val (V.n 65) (args_named hcm (List.mem_of_getElem? h16)) a1 a2
    have r66 := hF.val (V.n 66) (args_named hcm (List.mem_of_getElem? h6)) b1 b2
    rw [hRfp, Nat.zero_add] at r65 r66
    have w65 : wd L 1 ((certOf 1).locs.getD 65 0) = σR (V.n 65) := by
      simp only [wd, one_mul]
      rw [show (certOf 1).locs.getD 65 0 = B2C.cellJ 1 (V.n 65) from rfl, r65]
      rfl
    have w66 : wd L 1 ((certOf 1).locs.getD 66 0) = σR (V.n 66) := by
      simp only [wd, one_mul]
      rw [show (certOf 1).locs.getD 66 0 = B2C.cellJ 1 (V.n 66) from rfl, r66]
      rfl
    have := hx
    simp only [w65, w66] at this
    exact this
  · rw [hRt'] at hvR
    exact hvR.elim

/-- **A `__loop5` iteration hands its exponent tables to the next.** -/
theorem honest_exp_loop {S : BlakeSem} {κ : ℕ} {L : MemImage κ} {P P' : Inst} {σP : Val} {bufs : List ℕ}
    {kids : List Tree} (hPt : P.t = .node "__loop5" σP bufs kids) {args rets : List E}
    (hvP : P.t.ValidB S coreProgram L.read args rets)
    (hexp : B1.ExpTables L.read (σP (V.n 16)) (σP (V.n 6))) {i : ℕ} (hk : P.t.kids[i]? = some P'.t)
    {σP' : Val} {bufs' : List ℕ} {kids' : List Tree} (hP't : P'.t = .node "__loop5" σP' bufs' kids') :
    B1.ExpTables L.read (σP' (V.n 16)) (σP' (V.n 6)) := by
  rw [hPt] at hvP hk
  obtain ⟨fn, hf, -, es, vs, hw, -, -, hkv⟩ := hvP
  obtain rfl : fn = coreOf 36 := Option.some.inj
    (hf.symm.trans (by rw [← loop5_name]; exact End.coreOf_find (by decide) (by decide)))
  obtain ⟨c, hc, hcf, hvP'⟩ := kid_call hkv hk hP't
  have hcm : c ∈ calls es := List.mem_of_getElem? hc
  have hargs : c.args = .n 87 :: (List.range 17).map (fun i ↦ V.n (i + 1)) :=
    loop5_sites_loop5 _ (B2C.walk_sites (σ := σP) _ (by rw [hw]; exact hcm)) hcf
  rw [hP't] at hvP'
  obtain ⟨fnP, hfP, hparP, -⟩ := hvP'
  obtain rfl : fnP = coreOf 36 := Option.some.inj
    (hfP.symm.trans (by rw [← loop5_name]; exact End.coreOf_find (by decide) (by decide)))
  rw [loop5_params, hargs] at hparP
  have e16 : σP' (V.n 16) = σP (V.n 16) := by
    have := congrArg (fun l ↦ l[16]?) hparP
    simpa using this
  have e6 : σP' (V.n 6) = σP (V.n 6) := by
    have := congrArg (fun l ↦ l[6]?) hparP
    simpa using this
  rw [e16, e6]
  exact hexp

include hfun hcan hname hH hrun in
/-- **`verify_sub`'s body at its honest frame** under the honest run's table: at the
`verify_sub` callee `W` of a `__loop5` iteration `P` whose arguments `16`, `6` are exponent
tables. -/
theorem honest_vs_bodyAt {P W : Inst} (hP : P ∈ honestInsts coreProgram B2C.fs B2C.H hdr T)
    {σP : Val} {bufs : List ℕ} {kids : List Tree} (hPt : P.t = .node "__loop5" σP bufs kids)
    {argsP retsP : List E}
    (hvP : P.t.ValidB S coreProgram (honest coreProgram B2C.fs B2C.H B2C.C hdr T).read argsP retsP)
    (hexp : B1.ExpTables (honest coreProgram B2C.fs B2C.H B2C.C hdr T).read (σP (V.n 16))
      (σP (V.n 6)))
    (hW : W ∈ honestInsts coreProgram B2C.fs B2C.H hdr T) {i : ℕ} (hk : P.t.kids[i]? = some W.t)
    (hVfp : P.kidFps[i]? = some W.fp) {σV : Val} {bufsV : List ℕ} {kidsV : List Tree}
    (hWt : W.t = .node "verify_sub" σV bufsV kidsV) {args rets : List E}
    (hvW : W.t.ValidB S coreProgram (honest coreProgram B2C.fs B2C.H B2C.C hdr T).read args rets) :
    Located.BodyAtB (honestSem hdr T n) (honest coreProgram B2C.fs B2C.H B2C.C hdr T) "verify_sub"
      args rets W.fp := by
  set L := honest coreProgram B2C.fs B2C.H B2C.C hdr T with hL
  have hvP' := hvP
  rw [hPt] at hvP' hk
  obtain ⟨fn, hf, -, es, vs, hw, -, -, hkv⟩ := hvP'
  obtain rfl : fn = coreOf 36 := Option.some.inj
    (hf.symm.trans (by rw [← loop5_name]; exact End.coreOf_find (by decide) (by decide)))
  obtain ⟨c, hc, hcf, -⟩ := kid_call hkv hk hWt
  have hcm : c ∈ calls es := List.mem_of_getElem? hc
  have hargs : c.args = [.n 65, .n 66, .n 13, .n 14, .n 16, .n 6, .n 79] :=
    loop5_sites_vs _ (B2C.walk_sites (σ := σP) _ (by rw [hw]; exact hcm)) hcf
  have hF := (B2C.b2HypsB hfun).frame hdr rd T hname hH P hP "__loop5" σP bufs kids hPt 36
    idxOf_loop5 es vs hw
  obtain ⟨-, -, hka, -⟩ := hF.kid i c W.fp hc hVfp
  have r4 := hka 4 (by rw [hargs]; decide)
  have r5 := hka 5 (by rw [hargs]; decide)
  simp only [hargs] at r4 r5
  obtain ⟨hp, hm⟩ := vs_plain
  refine honest_bodyAt hfun hcan hname hH hrun hW hWt idxOf_vs (by decide)
    ⟨by rw [hp]; intro _ h; simp at h, by rw [hm]; intro _ h; simp at h, ?_⟩ hvW
  rw [End.vs_sem]
  intro p hp'
  simp only [List.mem_singleton] at hp'
  subst hp'
  show B1.ExpTables L.read (wd L (gpow W.fp) 6) (wd L (gpow W.fp) 7)
  have hgp : ∀ a o : ℕ, gpow a * gpow o = gpow (a + o) := fun a o ↦ by rw [gpow, gpow, gpow, pow_add]
  simp only [wd, hgp]
  rw [show W.fp + 6 = W.fp + (2 + 4) by omega, show W.fp + 7 = W.fp + (2 + 5) by omega, r4, r5]
  exact hexp

end Honest

end
end LeanVM.E2E.Complete
