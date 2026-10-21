/-
  LeanVM.Guest.B2C.RunsOn

  Every honest instance runs on the honest run: its entry is reached from `main`'s, and the run
  from it reaches its return registers and then the end, under any functional semantics of
  `BLAKE2S`.
-/

module

public import LeanVM.Guest.B2C.B2FinalB

/-!
# The honest instances on the run

B2's completeness (`B2B.lean`) gives each honest instance a run from its entry at its frame to its
return registers (`instB_runs`); the completeness walk also keeps the callees' entries on the
caller's run (`CplRunKB`, `KidsOn`). So, by descent from `main`, every honest node instance's
entry is reached from `main`'s, and its run reaches its return registers and then the end
(`honest_onRun`): the instance's run is a segment of the run of `main` to the end, which the
end-to-end theorem's halting run is.

* `cplRunKB_all`: the completeness checks give `CplRunKB` for every compiled function;
* `instKB_kids`: an honest instance's run, its node callees entered on it;
* `insts_induct`: a property of an allocation's root that its instances hand to their callees
  holds of every instance;
* `honest_onRun`: every honest node instance is valid, on the run from `main`'s entry, and
  returns into it.
-/

namespace LeanVM.Guest.B2C

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.End (mainEntry JumpTables)

@[expose] public section

variable {S : BlakeSem}

/-- **Every compiled function runs, its callees' entries on its run**, by the kernel's
completeness checks. -/
theorem cplRunKB_all : ∀ j, 1 ≤ j → j < nFns → CplRunKB S j :=
  fun _ h1 hj ↦ cplRunKB_of h1 hj (Cplw.cplOk_all _ h1 hj)

/-- A callee whose tree is a node was entered. -/
theorem kidsValidB_taken {P : Core.Program} {rd : Reader} {σ : Val} :
    ∀ {cs : List Memory.Call} {ks : List Memory.Tree}, Tree.KidsValidB S P rd σ cs ks →
      ∀ {i : ℕ} {c : Memory.Call} {f : String} {σ' : Val} {bufs : List ℕ} {kids : List Memory.Tree},
        cs[i]? = some c → ks[i]? = some (.node f σ' bufs kids) → c.taken = true
  | [], [], _, _, _, _, _, _, _, h, _ => by simp at h
  | [], _ :: _, h, _, _, _, _, _, _, _, _ => h.elim
  | _ :: _, [], h, _, _, _, _, _, _, _, _ => h.elim
  | c :: cs, k :: ks, ⟨_, hk, h⟩, i, c', f, σ', bufs, kids, hc, hk' => by
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hc hk'
      subst hc hk'
      cases ht : c.taken
      · rw [ht] at hk
        simp only [Bool.false_eq_true, ↓reduceIte] at hk
        obtain ⟨⟨f', σ'', he⟩, -⟩ := hk
        cases he
      · rfl
    | succ i =>
      simp only [List.getElem?_cons_succ] at hc hk'
      exact kidsValidB_taken h hc hk'

/-! ## An instance's run, its callees entered on it -/

section Insts

variable (h : B2HypsB S) {hdr : E × E} {rd : Reader} {T : Memory.Tree} (hname : T.name = "main")
  (hH : HonestAtB S coreProgram fs H C hdr T cert rd [] [])
include h hname hH

/-- **An honest instance's run, its callees entered on it**: a run from its entry at its frame to
its return registers (`main`: the final ones), each callee whose tree is a node entered on it, at
its entry and frame, returning to registers from which the run goes on to the instance's return
registers. -/
theorem instKB_kids {I : Inst} (hI : I ∈ honestInsts coreProgram fs H hdr T)
    (hm : I.t.name = "main" → I.fp = 0) {args rets : List E}
    (hv : I.t.ValidB S coreProgram (honest coreProgram fs H C hdr T).read args rets) :
    ∃ (r : Regs K) (c : Opcode → ℕ),
      (if I.t.name = "main" then r = Regs.final guest
        else retRegs (honest coreProgram fs H C hdr T) (gpow I.fp) = some r) ∧
      RunCB S guest (honest coreProgram fs H C hdr T) ⟨gpow (entryOf I.t.name), gpow I.fp⟩ r c ∧
      (∀ (i : ℕ) (k : Memory.Tree) (J : Inst), I.t.kids[i]? = some k →
        J ∈ honestInsts coreProgram fs H hdr T → J.t = k → I.kidFps[i]? = some J.fp →
        ∀ f σ bufs kids, k = .node f σ bufs kids →
          ReachB S guest (honest coreProgram fs H C hdr T) ⟨gpow (entryOf I.t.name), gpow I.fp⟩
            ⟨gpow (entryOf J.t.name), gpow J.fp⟩ ∧
          ∃ rJ, retRegs (honest coreProgram fs H C hdr T) (gpow J.fp) = some rJ ∧
            ReachB S guest (honest coreProgram fs H C hdr T) rJ r) ∧
      ∀ j, idxOf I.t.name = some j → rets.length = (certOf j).nret := by
  set L := honest coreProgram fs H C hdr T with hL
  rcases hti : I.t with ⟨f, σ, bufs, kids⟩ | ⟨f, σ⟩
  · rw [hti] at hv
    obtain ⟨fn, hf, hpar, es, vs, hw, hrets, hev, hk⟩ := hv
    obtain ⟨j, hj⟩ := idxOf_of_find hf
    obtain ⟨i, rfl, hi, hn', hfind, hcore, -, -, h1, hlt⟩ := fn_of_idx hj
    obtain rfl : fn = coreProgram[i] := Option.some.inj (hf.symm.trans hfind)
    have hw' : walk σ (coreOf (i + 1)).body = .ret es vs := by rw [hcore]; exact hw
    have hF := h.frame hdr rd T hname hH I hI f σ bufs kids hti (i + 1) hj es vs hw'
    have hkv := kidsValidB_get hk
    have hkids : I.t.kids = kids := by rw [hti]; rfl
    have hex : ∀ i' : ℕ, ∃ ci : Opcode → ℕ, ∀ (c : Memory.Call) (kfp : ℕ), (calls es)[i']? = some c →
        I.kidFps[i']? = some kfp → c.taken = true → (∃ r, retRegs L (gpow kfp) = some r ∧
          RunCB S guest L ⟨gpow (entryOf c.f), gpow kfp⟩ r ci) ∧
          ∀ k (hk : k < c.rets.length),
            L.read (gpow (kfp + (2 + c.args.length + k))) = some (σ c.rets[k]) := by
      intro i'
      cases hc : (calls es)[i']? with
      | none => exact ⟨0, fun c _ h' => absurd h' (by simp)⟩
      | some c =>
        obtain ⟨k, hk', hkn, hkval⟩ := hkv.2 i' c hc
        by_cases htk : c.taken = true
        · obtain ⟨J, hJ, hJt, hJfp, -⟩ := honest_kid hI (k := k) (by rw [hkids]; exact hk')
          have hne : c.f ≠ "main" := calls_ne_main hfind hw (List.mem_of_getElem? hc)
          have hJn : J.t.name = c.f := by rw [hJt, hkn]
          obtain ⟨r, ci, hr, hrun, -, hrets'⟩ := instB_runs h hname hH (J.t.total fs + 1) J hJ
            (Nat.lt_succ_self _) (fun hm' => absurd (hJn ▸ hm') hne) _ _ (hJt ▸ hkval htk)
          refine ⟨ci, fun c' kfp hc' hkfp _ => ?_⟩
          obtain rfl : c' = c := (Option.some.inj hc').symm
          obtain rfl : kfp = J.fp := Option.some.inj (hkfp.symm.trans hJfp)
          rw [hJn] at hr hrun
          simp only [hne, ↓reduceIte] at hr
          refine ⟨⟨r, hr, hrun⟩, fun k' hk'' => ?_⟩
          have := hrets' k' (by simpa using hk'')
          simpa using this
        · refine ⟨0, fun c' kfp hc' _ ht' => ?_⟩
          obtain rfl : c' = c := (Option.some.inj hc').symm
          exact absurd ht' htk
    choose cf hcf using hex
    set ck := (List.range (calls es).length).map cf with hck
    have hK : KidsRunB S L σ es I.kidFps ck := by
      refine ⟨by simp [hck], fun i' c kfp hc hkfp ht => ?_⟩
      have hi' : i' < (calls es).length := (List.getElem?_eq_some_iff.mp hc).1
      have hget : ck.getD i' 0 = cf i' := by simp [hck, hi']
      rw [hget]
      exact hcf i' c kfp hc hkfp ht
    have hjt : JumpTables L := jumpTablesB_honestC hH.toHonestB hname
    have hκ : logMem (T.total fs) ≤ 32 := hH.toHonestB.logMem_le
    have hmain : i + 1 = 1 → I.fp = 0 := fun h1' =>
      hm (by rw [hti]; exact (idx_one_iff hj).mp h1')
    obtain ⟨r, c, hr, hrun, -, -, hko, hnret⟩ := cplRunKB_all (S := S) (i + 1) (by omega) hlt L hκ
      (End.jtHolds_of hjt) hjt I.fp hmain σ es vs hw' hev I.kidFps I.hdr hF ck hK
    have hent : entryOf (Memory.Tree.node f σ bufs kids).name = (fnOf (i + 1)).entry := by
      simp only [Tree.name]
      rw [entryOf_of hj]
    refine ⟨r, c, ?_, by rw [hent]; exact hrun, fun i' k J hk' hJ hJt hJfp f' σ' bufs' kids' hkn ↦ ?_,
      fun j' hj' ↦ ?_⟩
    · have key := idx_one_iff hj
      split_ifs with hfm
      · split at hr
        · exact hr
        · exact absurd (key.mpr hfm) ‹_›
      · split at hr
        · exact absurd (key.mp ‹_›) hfm
        · exact hr
    · have hk' : kids[i']? = some k := hk'
      have hlen : i' < (calls es).length := by
        rw [← hkv.1]
        exact (List.getElem?_eq_some_iff.mp hk').1
      obtain ⟨c', hc'⟩ : ∃ c', (calls es)[i']? = some c' := ⟨_, List.getElem?_eq_getElem hlen⟩
      obtain ⟨k', hk'', hkn', -⟩ := hkv.2 i' c' hc'
      obtain rfl : k' = k := Option.some.inj (hk''.symm.trans hk')
      subst hkn
      have htk := kidsValidB_taken hk hc' hk'
      obtain ⟨h1', rJ, hrJ, h2'⟩ := hko i' hlen c' J.fp hc' hJfp htk
      have hJn : J.t.name = c'.f := by rw [hJt, ← hkn']
      rw [hent, hJn]
      exact ⟨h1', rJ, hrJ, h2'⟩
    · obtain rfl : j' = i + 1 := Option.some.inj (hj'.symm.trans hj)
      rw [← hrets, List.length_map, hnret]
  · rw [hti] at hv
    exact hv.elim

end Insts

/-! ## By descent -/

section Descent

variable {fs : String → ℕ} {lp : String → Bool} {H : Inst → ℕ → E × E} {U : List Inst}
  {Q : Inst → Prop}

mutual
/-- **Descent through an allocation**: a property of the root of `t`'s instances that every
instance of `U` hands to its callees' roots holds of all of `t`'s instances. -/
theorem insts_induct
    (hstep : ∀ I ∈ U, Q I → ∀ (i : ℕ) (k : Memory.Tree) (J : Inst), I.t.kids[i]? = some k →
      J ∈ U → J.t = k → I.kidFps[i]? = some J.fp → Q J) :
    ∀ (t : Memory.Tree) (fp : ℕ) (hdr : E × E), (∀ J ∈ t.insts fs lp H fp hdr, J ∈ U) →
      (∀ R rest, t.insts fs lp H fp hdr = R :: rest → Q R) → ∀ J ∈ t.insts fs lp H fp hdr, Q J
  | .node f σ bufs kids, fp, hdr, hU, hR, J, hJ => by
      have hR0 := hR _ _ insts_node
      rw [insts_node, List.mem_cons] at hJ
      rcases hJ with rfl | hJ
      · exact hR0
      · refine instsKids_induct hstep kids _ _ 0 (hU _ (by rw [insts_node]; exact List.mem_cons_self))
          hR0 (fun i ↦ by rw [Nat.zero_add]; try rfl) (fun i ↦ by rw [Nat.zero_add]; try rfl) (fun J' hJ' ↦ hU J' ?_) J hJ
        rw [insts_node]
        exact List.mem_cons_of_mem _ hJ'
  | .phantom f σ, fp, hdr, _, hR, J, hJ => by
      rw [insts_phantom, List.mem_singleton] at hJ
      subst hJ
      exact hR _ _ insts_phantom

/-- **Descent through the callees `ks` of `I` from its `j`-th**, at the frames `ps`. -/
theorem instsKids_induct
    (hstep : ∀ I ∈ U, Q I → ∀ (i : ℕ) (k : Memory.Tree) (J : Inst), I.t.kids[i]? = some k →
      J ∈ U → J.t = k → I.kidFps[i]? = some J.fp → Q J) :
    ∀ (ks : List Memory.Tree) (ps : List ℕ) (I : Inst) (j : ℕ), I ∈ U → Q I →
      (∀ i, I.t.kids[j + i]? = ks[i]?) → (∀ i, I.kidFps[j + i]? = ps[i]?) →
      (∀ J ∈ Tree.instsKids fs lp H I j ps ks, J ∈ U) →
      ∀ J ∈ Tree.instsKids fs lp H I j ps ks, Q J
  | [], _, _, _, _, _, _, _, _, J, hJ => by
      rw [instsKids_nil] at hJ
      exact absurd hJ List.not_mem_nil
  | _ :: _, [], _, _, _, _, _, _, _, J, hJ => by
      rw [instsKids_nil_left] at hJ
      exact absurd hJ List.not_mem_nil
  | k :: ks, p :: ps, I, j, hI, hQ, hk, hp, hU, J, hJ => by
      obtain ⟨R, rest, he, hRt, hRfp, -⟩ := head_insts (fs := fs) (lp := lp) (H := H) k p (H I j)
      have hsub : ∀ J' ∈ k.insts fs lp H p (H I j), J' ∈ U := fun J' hJ' ↦
        hU J' (by rw [instsKids_cons]; exact List.mem_append_left _ hJ')
      rw [instsKids_cons, List.mem_append] at hJ
      rcases hJ with hJ | hJ
      · refine insts_induct hstep k p (H I j) hsub (fun R' rest' he' ↦ ?_) J hJ
        rw [he] at he'
        obtain ⟨rfl, -⟩ := List.cons.inj he'
        refine hstep I hI hQ j k R (by simpa using hk 0) (hsub R (by rw [he]; exact List.mem_cons_self))
          hRt ?_
        rw [hRfp]
        simpa using hp 0
      · refine instsKids_induct hstep ks ps I (j + 1) hI hQ (fun i ↦ ?_) (fun i ↦ ?_)
          (fun J' hJ' ↦ hU J' (by rw [instsKids_cons]; exact List.mem_append_right _ hJ')) J hJ
        · rw [show j + 1 + i = j + (i + 1) by omega, hk (i + 1)]
          rfl
        · rw [show j + 1 + i = j + (i + 1) by omega, hp (i + 1)]
          rfl
end

end Descent

/-! ## Every honest instance on the run -/

variable (S) in
/-- **An instance on the run** of the memory `L` from `main`'s entry: its entry, at its frame, is
reached from `main`'s, and the run from it reaches its return registers (`main`: the final ones)
and then the final registers. -/
def OnRunB {κ : ℕ} (L : MemImage κ) (I : Inst) : Prop :=
  ReachB S guest L ⟨gpow mainEntry, 1⟩ ⟨gpow (entryOf I.t.name), gpow I.fp⟩ ∧
    ∃ r, (if I.t.name = "main" then r = Regs.final guest else retRegs L (gpow I.fp) = some r) ∧
      ReachB S guest L ⟨gpow (entryOf I.t.name), gpow I.fp⟩ r ∧ ReachB S guest L r (Regs.final guest)

/-- **Every honest node instance is on the run**: valid on its call's words, `main` only at the
root, its entry reached from `main`'s, and its run returning into the run to the end. -/
theorem honest_onRun (h : B2HypsB S) {hdr : E × E} {rd : Reader} {T : Memory.Tree}
    (hname : T.name = "main") (hH : HonestAtB S coreProgram fs H C hdr T cert rd [] []) :
    ∀ J ∈ honestInsts coreProgram fs H hdr T, ∀ f σ bufs kids, J.t = .node f σ bufs kids →
      (∃ args rets, J.t.ValidB S coreProgram (honest coreProgram fs H C hdr T).read args rets) ∧
      (J.t.name = "main" → J.fp = 0) ∧ OnRunB S (honest coreProgram fs H C hdr T) J := by
  set L := honest coreProgram fs H C hdr T with hL
  let Q : Inst → Prop := fun J ↦ ∀ f σ bufs kids, J.t = .node f σ bufs kids →
    (∃ args rets, J.t.ValidB S coreProgram L.read args rets) ∧ (J.t.name = "main" → J.fp = 0) ∧
      OnRunB S L J
  have hstep : ∀ I ∈ honestInsts coreProgram fs H hdr T, Q I → ∀ (i : ℕ) (k : Memory.Tree) (J : Inst),
      I.t.kids[i]? = some k → J ∈ honestInsts coreProgram fs H hdr T → J.t = k →
      I.kidFps[i]? = some J.fp → Q J := by
    intro I hI hQ i k J hk hJ hJt hJfp f σ bufs kids hJn
    rcases hIt : I.t with ⟨fI, σI, bufsI, kidsI⟩ | ⟨fI, σI⟩
    · obtain ⟨⟨args, rets, hv⟩, hm, hon0, r0, hr0, hon1, hon2⟩ := hQ fI σI bufsI kidsI hIt
      obtain ⟨r, c, hr, hrun, hkids, -⟩ := instKB_kids h hname hH hI hm hv
      have hr' : r = r0 := by
        by_cases hm' : I.t.name = "main"
        · simp only [hm', ↓reduceIte] at hr hr0
          rw [hr, hr0]
        · simp only [hm', ↓reduceIte] at hr hr0
          exact Option.some.inj (hr.symm.trans hr0)
      subst hr'
      obtain ⟨hreach, rJ, hrJ, hback⟩ := hkids i k J hk hJ hJt hJfp f σ bufs kids (hJt.symm.trans hJn)
      -- the callee's validity and name
      have hv' := hv
      rw [hIt] at hv'
      obtain ⟨fn, hf, -, es, vs, hw, -, -, hkv⟩ := hv'
      have hkvg := kidsValidB_get hkv
      have hk' : kidsI[i]? = some k := by rw [hIt] at hk; exact hk
      have hlen : i < (calls es).length := by
        rw [← hkvg.1]
        exact (List.getElem?_eq_some_iff.mp hk').1
      obtain ⟨c', hc'⟩ : ∃ c', (calls es)[i]? = some c' := ⟨_, List.getElem?_eq_getElem hlen⟩
      obtain ⟨k', hk'', hkn', hkval⟩ := hkvg.2 i c' hc'
      obtain rfl : k' = k := Option.some.inj (hk''.symm.trans hk')
      have htk := kidsValidB_taken hkv hc' (hk'.trans (by rw [← hJt, hJn]))
      have hne : c'.f ≠ "main" := calls_ne_main hf hw (List.mem_of_getElem? hc')
      have hJname : J.t.name = c'.f := by rw [hJt, hkn']
      refine ⟨⟨_, _, hJt ▸ hkval htk⟩, fun hm' ↦ absurd (hJname ▸ hm') hne,
        hon0.trans hreach, rJ, ?_, ?_, hback.trans hon2⟩
      · simp only [hJname, hne, ↓reduceIte]
        exact hrJ
      · -- the callee's own run
        obtain ⟨rJ', cJ, hrJ', hrunJ, -⟩ := instKB_kids h hname hH hJ
          (fun hm' ↦ absurd (hJname ▸ hm') hne) (hJt ▸ hkval htk)
        simp only [hJname, hne, ↓reduceIte] at hrJ'
        obtain rfl := Option.some.inj (hrJ'.symm.trans hrJ)
        exact hrunJ.reach
    · rw [hIt] at hk
      simp [Tree.kids] at hk
  have hall := insts_induct (U := honestInsts coreProgram fs H hdr T) (Q := Q) hstep T 0 hdr
    (fun J hJ ↦ hJ) (fun R rest he ↦ ?_)
  · exact fun J hJ ↦ hall J hJ
  -- the root
  intro f σ bufs kids hRt
  obtain ⟨R', rest', he', hRt', hRfp, -⟩ := head_insts (fs := fs) (lp := coreProgram.loop) (H := H) T 0 hdr
  rw [he'] at he
  obtain ⟨rfl, -⟩ := List.cons.inj he
  have hR : R' ∈ honestInsts coreProgram fs H hdr T := by
    unfold honestInsts
    rw [he']
    exact List.mem_cons_self
  have hv : R'.t.ValidB S coreProgram L.read [] [] := by rw [hRt']; exact hH.toHonestB.valid_image
  obtain ⟨r, c, hr, hrun, -⟩ := instKB_kids h hname hH hR (fun _ ↦ hRfp) hv
  have hRn : R'.t.name = "main" := by rw [hRt', hname]
  have hent : ⟨gpow (entryOf R'.t.name), gpow R'.fp⟩ = (⟨gpow mainEntry, 1⟩ : Regs K) := by
    rw [hRn, entryOf_main, hRfp, show (gpow 0 : K) = 1 by rw [gpow, pow_zero]]
  refine ⟨⟨_, _, hv⟩, fun _ ↦ hRfp, by rw [hent]; exact ReachB.refl _, r, hr, hrun.reach, ?_⟩
  simp only [hRn, ↓reduceIte] at hr
  rw [hr]
  exact ReachB.refl _

end
end LeanVM.Guest.B2C
