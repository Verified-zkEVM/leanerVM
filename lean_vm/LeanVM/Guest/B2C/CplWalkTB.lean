/-
  LeanVM.Guest.B2C.CplWalkTB

  The completeness walk's table jumps (`CplWalkT.lean`) under any semantics of `BLAKE2S`.
-/

module

public import LeanVM.Guest.B2C.CplWalkT
public import LeanVM.Guest.B2C.CplWalkB

/-!
# Table jumps along a path under any `BLAKE2S` semantics

`CplWalkT.lean`'s `tbl_segJ`, `walk_matchNilZ`, `walk_matchZ`, `walk_dispatchZ` over `WHB`
(`tblB_segJ`, `walkB_matchNilZ`, `walkB_matchZ`, `walkB_dispatchZ`), proved as there.
-/

namespace LeanVM.Guest.B2C

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Exec
open LeanVM.Guest.Check LeanVM.Guest.Memory

@[expose] public section

variable {S : BlakeSem}

/-! ## Paths through a table jump -/

section Walk

variable {κ : ℕ} {L : MemImage κ} {j fp : ℕ} {σ : Val} {es : List Ev} {vs : List V}
  {kfps : List ℕ} {hdr : E × E} {ck : List (Opcode → ℕ)} {segs : List Exec.Seg} {X : CX}
  {wJ : ℕ} {wenv : Trie Sym}

/-- Entering the join `J` with counts `c`: the run is at its segment. -/
theorem tblB_segJ (H : WHB S L j fp X segs wJ wenv σ es vs kfps hdr ck) {J : ℕ} {se sj : CW}
    (h : segAtC X J se = some sj) (hok : CWOkB S L fp X se) (he : EnvAt L fp X wJ wenv J) {W0 : Regs K}
    {n : ℕ} {xc : Opcode → ℕ} {c : Cnt} (u : ℕ) {cr : Opcode → ℕ}
    (hr : RunCB S guest L W0 ⟨gpow (X.entry + J), gpow fp⟩ cr)
    (hc : ∀ op, cr op ≤ c.get op + xc op + ksum ck n op)
    (hnm : ∀ n, se.nm.testBit n = true → V.n n ∈ namedOf (coreOf j).params es vs) :
    PosZB S H { sj with cnt := c, uq := u } W0 n xc := by
  obtain ⟨s, hs, hst, rfl⟩ := segAtC_eq h
  have h' : segAtC X J { se with cnt := c, uq := u } =
      some ⟨s, s.items, se.book, se.fr, se.tg, se.nx, c, u, some J, se.nm⟩ := by
    unfold segAtC
    rw [hs]
    simp [hst]
  exact (segAtCB_pos H h' hok.book hok.fr hok.tg hok.nx he hr hc hnm).1

theorem walkB_matchNilZ (H : WHB S L j fp X segs wJ wenv σ es vs kfps hdr ck) (v : V) (ss : List Stmt)
    (st : CW) : WGoodB S H (.match_ v [] :: ss) st := by
  intro ebef eaft o W0 pre xc hw hes hs hshape hp hok
  simp [cw, RC.ok] at hok

/-- **A `match`**: the run jumps through the table to the arm the path takes, walks it to the
join, and goes on. -/
theorem walkB_matchZ (H : WHB S L j fp X segs wJ wenv σ es vs kfps hdr ck) (v : V) (a0 : List Stmt)
    (as : List (List Stmt)) (ss : List Stmt) (st : CW)
    (iha : ∀ k (hk : k < (a0 :: as).length) st, WGoodB S H (a0 :: as)[k] st)
    (ih : ∀ st, WGoodB S H ss st) : WGoodB S H (.match_ v (a0 :: as) :: ss) st := by
  intro ebef eaft o W0 pre xc hw hes hs hshape hp hok
  obtain ⟨t, ft, t0, ts, base, se, s0, J, c0, u0, c, u, sj, hk, hsu, htb, hself, hl, hvn, hsel, hin,
    harm, hao, hse, hs0, h0, hck0, ha, hsj, hcw⟩ := cw_match hok
  have hkr : armKeyD X.acs v.idx = (armRaw X.acs v.idx).map (fun cs ↦ cs.map Cnt.ofList) := rfl
  generalize armKeyD X.acs v.idx = key at hs0 hck0 ha hcw hkr
  have hnr : Stmt.noRet (.match_ v (a0 :: as)) = true := by
    rcases hshape with h | ⟨h, -, -⟩
    · simp only [Stmt.noRetList, Bool.and_eq_true] at h
      exact h.1
    · exact (lastOkC_cons h fun vs hv ↦ by cases hv).1
  -- the arm the path takes
  have hw0 : o = (walkArms σ v 0 (a0 :: as)).seq (walk σ ss) := by rw [← hw]; rfl
  obtain ⟨e1, hwa⟩ : ∃ e1, walkArms σ v 0 (a0 :: as) = .fall e1 := by
    rcases walkArms_noRetC (σ := σ) v (a0 :: as) 0 hnr with h | h
    · exact h
    · exact absurd (show o = .stuck by rw [hw0, h]; rfl) hs
  obtain ⟨k, hka, hvk, hwk, hcost⟩ :=
    tbl_walkArmsC (acs := X.acs) (key := armRaw X.acs v.idx) (a0 :: as) 0 hwa
  rw [Nat.zero_add] at hvk hcost
  have hw' : o = (walk σ ss).pre e1 := by rw [hw0, hwa]; rfl
  have hst' : walk σ ss ≠ .stuck := fun h ↦ hs (by rw [hw', h]; rfl)
  have hes2 : es = ebef ++ e1 ++ ((walk σ ss).evs ++ eaft) := by
    rw [hes, hw', walk_pre_evs hst']
    simp
  -- the table read
  have hkt : k < (t0 :: ts).length := by simpa [hl] using hka
  have hslot := tbl_armsOk (t0 :: ts) 0 hao k hkt
  rw [Nat.zero_add, H.G] at hslot
  obtain ⟨hfind, hlt⟩ := tbl_slot H.jt H.tab hslot
  have hfr := inFrame_mem hin
  have hv2 := hfr _ List.mem_cons_self
  have ht2 := hfr t (by simp)
  have hcv : rdc L fp (X.loc.cell v) = some (σ v) :=
    val_cell H.frame H.loc (hp.sel hvn hsel) hv2.1 (H.fs ▸ hv2.2)
  obtain ⟨⟨a1, a2, a3⟩, ham, hae⟩ := List.any_eq_true.mp harm
  simp only [Bool.and_eq_true] at hae
  obtain ⟨⟨ha1, ha2⟩, ha3⟩ := hae
  have e1' : a1 = v.idx := Nat.eq_of_beq_eq_true ha1
  have e2' : a2 = t := Nat.eq_of_beq_eq_true ha2
  have e3' : a3 = base := Nat.eq_of_beq_eq_true ha3
  subst e1' e2' e3'
  rw [H.arms] at ham
  have harmw : L.read (gpow (fp + a2)) = some (armWord σ v.idx a3) :=
    H.frame.arm _ ham ht2.1 (H.fs ▸ ht2.2)
  have hσk : σ (V.n v.idx) = ofK (gpow k) := by rw [← hvn]; exact hvk
  rw [tbl_armWord hσk hfind hlt, gpow_addC] at harmw
  have htg1 : TgOk L fp ((a2, X.loc.cell v, a3) :: st.tg) := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · refine ⟨σ v, ofK (gpow (X.entry + (t0 :: ts)[k])), hcv, by rw [hvk]; exact isInK_ofK _, harmw,
        isInK_ofK _, ?_⟩
      show L.read ((σ v).limb 0 * gpow a3) = some (ofK (gpow (X.entry + (t0 :: ts)[k])))
      rw [hvk, limb_ofK0, ← gpow_addC, Nat.add_comm k a3]
      exact H.jt _ _ hslot
    · exact hp.ok.tg x hx
  have hp0 : PosZB S H { st with tg := (a2, X.loc.cell v, a3) :: st.tg } W0 (calls ebef).length xc :=
    ⟨hp.seg, ⟨hp.ok.env, hp.ok.book, hp.ok.fr, htg1, hp.ok.nx⟩, hp.run, hp.fresh, hp.nm, hp.ix⟩
  -- the jump to the arm
  obtain ⟨hseg, hbk, hfr', htg, hnx, -, hreach⟩ := endAtCB_reach H hp0 hse
  simp only at hseg hbk hfr' htg hnx hreach
  have hft : ft.Is L (gpow fp) (gpow fp) := by
    unfold Facts.self at hself
    split at hself
    · show gpow fp = gpow fp * gpow 0
      rw [gpow_zero', mul_one]
    · show gpow fp = gpow 0
      rw [gpow_zero']
      exact H.ctx.fpOne hself
    · cases hself
  obtain ⟨cr, hcr, hcle, henv⟩ := hreach ⟨gpow (X.entry + (t0 :: ts)[k]), gpow fp⟩ (by
    rw [hk]
    exact ⟨_, _, ⟨_, harmw, isInK_ofK _, by rw [limb_ofK0]⟩, hft, rfl⟩)
  have htk : (t0 :: ts)[k] ∈ st.seg.exit.succ := by rw [hsu]; exact List.getElem_mem hkt
  have henvk := envAtB_of_exit H hp.seg (H.exits _ hp.seg _ (Or.inl rfl)) htk henv
  have hok0 : CWOkB S L fp X se :=
    ⟨by rw [hseg]; exact hp.ok.env, by rw [hbk]; exact hp.ok.book, by rw [hfr']; exact hp.ok.fr,
      by rw [htg]; exact htg1, by rw [hnx]; exact hp.ok.nx⟩
  -- the arm, its counts restarted if counted separately
  have hse'b : (armSt key se).book = se.book := by cases key <;> rfl
  have hok0' : CWOkB S L fp X (armSt key se) := by
    cases key <;> exact ⟨hok0.env, hok0.book, hok0.fr, hok0.tg, hok0.nx⟩
  have hcnt' : ∀ op, (armSt key se).cnt.get op ≤ se.cnt.get op := by
    intro op
    cases key
    · exact le_rfl
    · cases op <;> exact Nat.zero_le _
  have hnm0 : ∀ n, se.nm.testBit n = true → V.n n ∈ namedOf (coreOf j).params es vs := by
    rw [endAtC_nm hse]
    exact hp.nm
  have hnm0' : ∀ n, (armSt key se).nm.testBit n = true → V.n n ∈ namedOf (coreOf j).params es vs := by
    cases key <;> exact hnm0
  obtain ⟨hkt', s, ckk, ukk, hsk, hcwk, hckc, hchk⟩ :=
    tbl_arm hs0 (by rw [hse'b]; exact h0) hck0 ha hl k hka
  let xa : Opcode → ℕ := fun op ↦ xc op + (se.cnt.get op - (armSt key se).cnt.get op)
  obtain ⟨hps, -⟩ := segAtCB_pos H (xc := xa) (n := (calls ebef).length) hsk hok0'.book hok0'.fr hok0'.tg hok0'.nx henvk hcr
    (fun op ↦ by have := hcle op; have := hcnt' op; simp only [xa]; omega) hnm0'
  have hatoms : ∀ a, Stmt.atom a ∈ (a0 :: as)[k] → Ev.atom a ∈ es := fun a ha' ↦ by
    rw [hes2]
    exact List.mem_append_left _ (List.mem_append_right _ (atom_on_pathC hwk ha'))
  have hB := fileBB_ok H.frame H.loc H.hev _ (armSt key se).book hok0'.book hatoms
  rw [← H.fs] at hB
  have hpk : PosZB S H { s with book := fileB X.loc X.fs (a0 :: as)[k] (armSt key se).book } W0
      (calls ebef).length xa :=
    ⟨hps.seg, ⟨hps.ok.env, hB, hps.ok.fr, hps.ok.tg, hps.ok.nx⟩, hps.run, hps.fresh, hps.nm, hps.ix⟩
  have hokk : (cw X (a0 :: as)[k]
      { s with book := fileB X.loc X.fs (a0 :: as)[k] (armSt key se).book }).ok = true := by
    rw [hcwk]
    rfl
  obtain ⟨hj1, -, -⟩ := iha k hka _ ebef ((walk σ ss).evs ++ eaft) (.fall e1) W0 [] xa hwk hes2
    (fun h ↦ by cases h) (Or.inl (tbl_noRetArms hnr k hka)) hpk hokk
  obtain ⟨es', hfe, hArr⟩ := hj1 J ckk ukk hcwk
  obtain rfl := Out.fall.inj hfe
  obtain ⟨⟨crj, hcrj, hcj⟩, henvJ⟩ := hArr
  -- the join
  have hc1 : cost1 X.acs σ (.match_ v (a0 :: as)) = costArms X.acs σ v (armRaw X.acs v.idx) 0 (a0 :: as) :=
    rfl
  have hp'' := tblB_segJ H hsj hok0 henvJ u hcrj (c := armCnt key se c) (n := (calls (ebef ++ e1)).length)
    (xc := xc + cost1 X.acs σ (.match_ v (a0 :: as))) (fun op ↦ by
      have h1 := hcj op
      have h2 := hckc op
      rw [hc1, hcost]
      simp only [Pi.add_apply, xa] at h1 ⊢
      cases key with
      | none =>
        have hr : armRaw X.acs v.idx = none := Option.map_eq_none_iff.mp hkr.symm
        rw [hr]
        simp only [armCnt, armSt, Nat.sub_self, Nat.add_zero] at h1 ⊢
        omega
      | some cs' =>
        obtain ⟨cs, hr, rfl⟩ := Option.map_eq_some_iff.mp hkr.symm
        rw [hr]
        have h3 := Cnt.le_spec hchk op
        rw [tbl_nth_ofList] at h3
        simp only [armCnt, armSt] at h1 ⊢
        have h4 : ({ se with cnt := Cnt.zero } : CW).cnt.get op = 0 := by cases op <;> rfl
        rw [h4, Nat.sub_zero] at h1
        omega) hnm0
  exact walkB_step H ih hnr (show walk1 σ (.match_ v (a0 :: as)) = .fall e1 from hwa) hw hes hs
    hshape hp'' hcw hok

/-- **A `dispatch`**: the run calls, through the table, the callee the path takes, and goes on
at the return point. -/
theorem walkB_dispatchZ (H : WHB S L j fp X segs wJ wenv σ es vs kfps hdr ck) (v : V) (fs : List String)
    (args rets : List V) (ss : List Stmt) (st : CW) (ih : ∀ st, WGoodB S H ss st) :
    WGoodB S H (.dispatch v fs args rets :: ss) st := by
  intro ebef eaft o W0 pre xc hw hes hs hshape hp hok
  obtain ⟨t, q, r, base, sr, hk, -, hvn, hsel, htc, hle, hsu, hsite, -, -, -, hin, hself, haf, hcw⟩ :=
    cw_dispatch hok
  obtain ⟨se, s', hse, hs', rfl⟩ := afterC_ok haf
  -- the callee the path takes
  have hw0 : o = (pick σ v args rets 0 fs).seq (walk σ ss) := by rw [← hw]; rfl
  obtain ⟨e1, hpk⟩ : ∃ e1, pick σ v args rets 0 fs = .fall e1 := by
    rcases pick_noRetC (σ := σ) (x := v) (a := args) (r := rets) fs 0 with h | h
    · exact h
    · exact absurd (show o = .stuck by rw [hw0, h]; rfl) hs
  obtain ⟨k, hkf, hvk, rfl⟩ := tbl_pick fs 0 hpk
  rw [Nat.zero_add] at hvk
  obtain ⟨pc, j', hslot, hj, hf, -, -⟩ := tbl_tcOk H.G fs 0 htc k hkf
  rw [Nat.zero_add, H.G] at hslot
  obtain ⟨hj1, hj2, he⟩ := calleeC_some H.G hj
  have hfn : fs[k] = (coreOf j').name := by rw [hf, H.G]; rfl
  have hw' : o = (walk σ ss).pre [.call fs[k] args rets] := by rw [hw0, hpk]; rfl
  have hst' : walk σ ss ≠ .stuck := fun h ↦ hs (by rw [hw', h]; rfl)
  have hes2 : es = ebef ++ Ev.call fs[k] args rets :: ((walk σ ss).evs ++ eaft) := by
    rw [hes, hw', walk_pre_evs hst']
    simp
  set n := (calls ebef).length with hn
  have hci : (calls es)[n]? = some ⟨fs[k], args, rets, true⟩ := by rw [hes2]; exact calls_at rfl
  obtain ⟨s0, hs0, hq0, hr0, ht0⟩ := siteOk_spec hsite
  have hnl := notLastB H hci fun h ↦ hself _ (List.getElem_mem hkf) (h.trans H.name.symm)
  have hfr := inFrame_mem hin
  have hin' : inFrame X.fs (s0.q :: args.map X.loc.cell) = true := by
    rw [hq0]
    simp only [inFrame, Bool.and_eq_true] at hin ⊢
    obtain ⟨-, hq, -, h2⟩ := hin
    refine ⟨hq, ?_⟩
    rw [List.map_append, inFrame_append, Bool.and_eq_true] at h2
    exact h2.1
  obtain ⟨kfp, hkfp, hq, hfcs, hret⟩ := callB_frame H hci hj1 hj2 hfn hs0 hnl hin' (selfs := [])
    (fun o ho ↦ by cases ho)
  rw [hq0] at hq
  rw [hr0] at hfcs hret
  obtain ⟨-, hkid⟩ := H.kids
  obtain ⟨⟨rr, hrr, hrun⟩, hrets⟩ := hkid n _ kfp hci hkfp rfl
  rw [hret] at hrr
  obtain rfl := Option.some.inj hrr
  -- the table read
  have ht2 := hfr t List.mem_cons_self
  have hent : entryOf fs[k] = pc := by rw [hfn, entryOf_callee hj1 hj2, he]
  have htgt : rdc L fp t = some (ofK (gpow pc)) := by
    have := (H.frame.site n _ kfp s0 hci hkfp (by rw [← siteC_eq H.sites]; exact hs0)).2
      (by rw [ht0]; have := ht2.1; omega) (by rw [ht0]; exact ht2.1) (by rw [ht0, ← H.fs]; exact ht2.2)
    rw [ht0, gpow_addC] at this
    rw [← hent]
    exact this
  have hv2 := hfr (X.loc.cell v) (by simp)
  have hcv : rdc L fp (X.loc.cell v) = some (σ v) :=
    val_cell H.frame H.loc (hp.sel hvn hsel) hv2.1 (H.fs ▸ hv2.2)
  have htg1 : TgOk L fp ((t, X.loc.cell v, base) :: st.tg) := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · refine ⟨σ v, ofK (gpow pc), hcv, by rw [hvk]; exact isInK_ofK _, htgt, isInK_ofK _, ?_⟩
      show L.read ((σ v).limb 0 * gpow base) = some (ofK (gpow pc))
      rw [hvk, limb_ofK0, ← gpow_addC, Nat.add_comm k base]
      exact H.jt _ _ hslot
    · exact hp.ok.tg x hx
  have hp0 : PosZB S H { st with tg := (t, X.loc.cell v, base) :: st.tg } W0 n xc :=
    ⟨hp.seg, ⟨hp.ok.env, hp.ok.book, hp.ok.fr, htg1, hp.ok.nx⟩, hp.run, hp.fresh, hp.nm, hp.ix⟩
  -- the call
  have hp1 := posZB_fr H hp0 hq hfcs
  obtain ⟨hseg, hbk, hfr', htg, hnx, -, hreach⟩ := endAtCB_reach H hp1 hse
  simp only at hseg hbk hfr' htg hnx hreach
  obtain ⟨cr, hcr, hcle, henv⟩ := hreach ⟨gpow pc, gpow kfp⟩ (by
    rw [hk]
    exact ⟨_, gpow pc, hq, isInK_ofK _, ⟨_, htgt, isInK_ofK _, by rw [limb_ofK0]⟩, by simp⟩)
  rw [hent] at hrun
  have hgr : gpow r = gpow (X.entry + (r - X.entry)) := by rw [Nat.add_sub_cancel' hle]
  have hrun2 : RunCB S guest L W0 ⟨gpow (X.entry + (r - X.entry)), gpow fp⟩ (cr + ck.getD n 0) := by
    rw [← hgr]
    exact hcr.trans hrun
  have henvR : EnvAt L fp X wJ wenv (r - X.entry) :=
    envAtB_of_exit H hp.seg (H.exits _ hp.seg _ (Or.inl rfl)) (by rw [hsu]; simp) henv
  obtain ⟨hps, -⟩ :=
    segAtCB_pos H (xc := xc) hs' (by rw [hbk]; exact hp.ok.book) (by rw [hfr']; exact hp1.ok.fr)
      (by rw [htg]; exact htg1) (by rw [hnx]; exact hp.ok.nx) henvR (n := n + 1) hrun2
      (fun op ↦ by rw [Pi.add_apply, ksum_succ]; have := hcle op; omega)
      (by rw [endAtC_nm hse]; exact hp.nm)
  have hc1 : (calls (ebef ++ [.call fs[k] args rets])).length = n + 1 := calls_append_one rfl
  refine walkB_step H ih rfl
    (show walk1 σ (.dispatch v fs args rets) = .fall [.call fs[k] args rets] from hpk) hw hes hs
    hshape ?_ hcw hok
  rw [hc1]
  refine ⟨hps.seg, ⟨hps.ok.env, hps.ok.book, fun x hx ↦ ?_, hps.ok.tg, hps.ok.nx⟩, hps.run,
    fun t' ht' ↦ ?_, hps.nm, hps.ix⟩
  · rcases List.mem_cons.mp hx with rfl | hx
    · refine ⟨kfp, hq, fun p hp' ↦ ?_⟩
      rcases List.mem_append.mp hp' with hp' | hp'
      · exact hfcs p hp'
      · obtain ⟨i, hi, rfl⟩ := argFC_mem hp'
        have hv : X.loc.cell rets[i] ∈ (args ++ rets).map X.loc.cell :=
          List.mem_map.mpr ⟨_, List.mem_append_right _ (List.getElem_mem hi), rfl⟩
        have hc := hfr _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hv)))
        have hm : Ev.call fs[k] args rets ∈ es := by rw [hes2]; simp
        refine ⟨σ rets[i], val_cell H.frame H.loc (uses_named hm (by simp [Ev.uses, List.getElem_mem]))
          hc.1 (H.fs ▸ hc.2), ?_⟩
        have := hrets i hi
        rw [gpow_addC] at this
        exact this
    · exact hp.ok.fr x hx
  · simp only at ht'
    cases hre : rets.isEmpty
    · rw [hre] at ht'; cases ht'
    · rw [hre] at ht'
      exact hps.fresh t' ht'

end Walk

end
end LeanVM.Guest.B2C
