/-
  LeanVM.Guest.B1.Tables.VtC.Lift

  `verify_tables`, placed: from its honest valuation on every memory holding its layout, the
  uniform placed form (`CompleteAtD`).
-/

module

public import LeanVM.Guest.B1.Tables.FlatAt
public import LeanVM.Guest.B1.Tables.VtC.RcReads
public import LeanVM.Guest.B1.Tables.VtC.InBuf
public import LeanVM.Guest.B1.Tables.VtC.Kids

/-!
# `verify_tables`, placed

`vt_completeAt`: `verify_tables` is `CompleteAtD` on the caller's words `Lin` when, at every frame
pointer, its own buffers' words `own fp` (the allocator's sizes `sizes` from
`fp + fs "verify_tables"`) and an oracle `w fp` (their bases, the hints', witnesses' and callees'
words) make the honest valuation `vtσ rd (w fp) args` satisfy every statement (`VSH`) on every
memory defined below `2^κ` holding `Lin` and the buffers, its loads inside listed buffers of that
layout (`LoadsInBuf`), its allocations the allocator's, its returns `rets`; and the callees, on
that layout, are placed from their relations (`hkids`, the pure functions' lift).

The callees' arguments and returns are the same on every such memory: the evaluations agree off
the range checks' reads (`ev_agree`, `vt_dead`), which no call uses; so the callees are fixed
from one such memory (`vtRdS`).
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Fwd
open LeanVM.Guest.B1.Main (Layout MemL RegionL)
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

/-! ## Kernel facts of the body -/

theorem vt_flat : vtPre.all Stmt.flat = true := by decide +kernel

theorem vt_addrs : vtPre.filterMap Main.Stmt.addrS = [] := by decide +kernel

theorem vt_not_loop : coreProgram.loop "verify_tables" = false := by decide +kernel

/-- A statement's callees are `verify_tables`' and its dispatches are short. -/
def vtCallOk : Stmt → Bool
  | .call f _ _ | .callIf _ f _ => vtKidS.contains f
  | .dispatch _ fs _ _ => fs.all vtKidS.contains && decide (fs.length < 2 ^ 64 - 1)
  | _ => true

theorem vt_callOk : vtPre.all vtCallOk = true := by decide +kernel

/-- No load in a branch. -/
def noLoadIte : Stmt → Bool
  | .ite _ z n => (z ++ n).all fun t ↦ match t with
    | .atom (.load ..) => false
    | _ => true
  | _ => true

theorem vt_noLoadIte : vtPre.all noLoadIte = true := by decide +kernel

/-- A load of the evaluation list is a statement of the body. -/
theorem vtEvL_load_mem {d p : V} {off : ℕ} (h : Stmt.atom (.load d p off) ∈ vtEvL) :
    Stmt.atom (.load d p off) ∈ vtPre := by
  obtain ⟨s, hs, hfs⟩ := List.mem_map.mp h
  have hs' : s = .atom (.load d p off) := by
    cases s with
    | atom a => cases a <;> simp_all [fixNe]
    | _ => simp_all [fixNe]
  subst hs'
  have key : ∀ ss : List Stmt, ss.all noLoadIte = true →
      Stmt.atom (.load d p off) ∈ flatIte ss → Stmt.atom (.load d p off) ∈ ss := by
    intro ss
    induction ss with
    | nil => simp [flatIte]
    | cons t ts ih =>
      intro hok hm
      simp only [List.all_cons, Bool.and_eq_true] at hok
      cases t with
      | ite c z n =>
        simp only [flatIte, List.mem_append] at hm
        rcases hm with (hm | hm) | hm
        · have := List.all_eq_true.mp hok.1 _ (List.mem_append_left _ hm)
          simp at this
        · have := List.all_eq_true.mp hok.1 _ (List.mem_append_right _ hm)
          simp at this
        · exact List.mem_cons_of_mem _ (ih hok.2 hm)
      | _ =>
        simp only [flatIte, List.mem_cons] at hm
        rcases hm with hm | hm
        · rw [hm]; exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (ih hok.2 hm)
  exact key vtPre vt_noLoadIte hs

/-! ## Addresses -/

theorem limb_mul_gen (b j off : ℕ) :
    (ofK (gpow b) * gen ^ j).limb 0 * gpow off = gpow (b + j + off) := by
  have e : ofK (gpow b) * gen ^ j = ofK (gpow (b + j)) := by
    rw [gen_pow_eq_ofK, ← ofK_mul, gpow, gpow, gpow, pow_add]
  rw [e, Main.addr_ofK]

/-- A load inside a listed buffer of a layout reads inside the layout. -/
theorem inBuf_region {σ : Val} {bufs : List (E × ℕ)} {L : Layout}
    (hbufs : ∀ q ∈ bufs, ∃ b, q.1 = ofK (gpow b) ∧ ∀ i < q.2, RegionL L (b + i))
    {p : V} {off : ℕ} (h : InBuf σ bufs p off) :
    ∃ i, (σ p).limb 0 * gpow off = gpow i ∧ RegionL L i := by
  obtain ⟨q, hq, j, hp, hj⟩ := h
  obtain ⟨b, hb, hr⟩ := hbufs q hq
  refine ⟨b + j + off, by rw [hp, hb, limb_mul_gen], ?_⟩
  have := hr (j + off) hj
  rwa [← Nat.add_assoc] at this

/-! ## The honest valuation on two memories -/

/-- **On two memories holding the layout, the honest valuations agree off the range checks'
reads**, when the first one's loads land inside the layout. -/
theorem vt_agree {rd1 rd2 : Reader} {w : ℕ → E} {args : List E} (hl : args.length = 22)
    {L : Layout} (h1 : MemL rd1 L) (h2 : MemL rd2 L) {bufs : List (E × ℕ)}
    (hbufs : ∀ q ∈ bufs, ∃ b, q.1 = ofK (gpow b) ∧ ∀ i < q.2, RegionL L (b + i))
    (hld : LoadsInBuf (vtσ rd1 w args) bufs vtPre) {v : V} (hv : vtAux v.idx = false) :
    vtσ rd1 w args v = vtσ rd2 w args v := by
  have hrd : ∀ d p off, Stmt.atom (.load d p off) ∈ vtEvL →
      rd1 ((B1.Val.ofArgs (ev rd1 w args vtEvL) p).limb 0 * gpow off) =
        rd2 ((B1.Val.ofArgs (ev rd1 w args vtEvL) p).limb 0 * gpow off) := by
    intro d p off hm
    obtain ⟨i, hi, hr⟩ := inBuf_region hbufs (hld d p off (vtEvL_load_mem hm))
    have hi' : (B1.Val.ofArgs (ev rd1 w args vtEvL) p).limb 0 * gpow off = gpow i := hi
    rw [hi']
    exact Main.memL_agree h1 h2 i hr
  have hag := ev_agree rd1 rd2 w vtAux vtEvL args args (by rw [hl]; exact vt_chk) rfl
    (fun _ _ ↦ rfl) vt_dead vt_aux hrd
  unfold vtσ B1.Val.ofArgs
  exact hag _ hv

/-! ## Calls -/

/-- A statement holds with calls by `C`, by the taken branch for an `ite`: mono in `C`. -/
theorem vsh_mono {C C' : CallRel} (hC : CallRel.Le C C') {rd : Reader} {σ : Val} :
    ∀ {s : Stmt}, VSH C rd σ s → VSH C' rd σ s
  | .atom _, h => h
  | .call .., h => hC _ _ _ h
  | .callIf .., h => ⟨h.1, fun hc ↦ hC _ _ _ (h.2 hc)⟩
  | .dispatch .., h => let ⟨j, hj, hx, hc⟩ := h; ⟨j, hj, hx, hC _ _ _ hc⟩
  | .ite .., h => ⟨h.1, fun hc t ht ↦ sholds_mono hC (h.2.1 hc t ht),
      fun hc t ht ↦ sholds_mono hC (h.2.2 hc t ht)⟩
  | .ret _, h => h
  | .match_ .., h => h
where
  sholds_mono {C C' : CallRel} (hC : CallRel.Le C C') {rd : Reader} {σ : Val} :
      ∀ {s : Stmt}, SHolds C rd σ s → SHolds C' rd σ s
    | .atom _, h => h
    | .call .., h => hC _ _ _ h
    | .callIf .., h => ⟨h.1, fun hc ↦ hC _ _ _ (h.2 hc)⟩
    | .dispatch .., h => let ⟨j, hj, hx, hc⟩ := h; ⟨j, hj, hx, hC _ _ _ hc⟩
    | .ite .., h => h
    | .ret _, h => h
    | .match_ .., h => h

/-- The callee an entered frame is, its arguments' and returns' words under `σ`, on the layout
`L`. -/
noncomputable def kidOf (σ : Val) (L : Layout) (c : Call) : Kid :=
  ⟨c.f, c.taken, c.args.map σ, L, Returns (c.rets.map σ)⟩

theorem callsMatch_kids {σ σS : Val} {L : Layout} :
    ∀ (cs : List Call) (outs : List (List E × Layout)),
      (∀ c ∈ cs, ∀ v ∈ c.args ++ c.rets, σ v = σS v) →
      OutsOk (cs.map (kidOf σS L)) outs → CallsMatch σ cs (cs.map (kidOf σS L)) outs
  | [], [], _, _ => trivial
  | [], _ :: _, _, h => h.elim
  | _ :: _, [], _, h => h.elim
  | c :: cs, o :: os, hag, ⟨ho, hos⟩ => by
    refine ⟨rfl, rfl, fun ht ↦ ⟨?_, ?_⟩, callsMatch_kids cs os
      (fun c' hc' ↦ hag c' (List.mem_cons_of_mem _ hc')) hos⟩
    · exact List.map_congr_left fun v hv ↦ hag c List.mem_cons_self v (List.mem_append_left _ hv)
    · rw [show o.1 = c.rets.map σS from (ho ht).1]
      exact List.map_congr_left fun v hv ↦ hag c List.mem_cons_self v (List.mem_append_right _ hv)

/-- A call, conditional call or dispatch. -/
def callB : Stmt → Bool
  | .call .. | .callIf .. | .dispatch .. => true
  | _ => false

/-- **A call statement's values are not range-check reads.** -/
theorem vt_call_vals {s : Stmt} (hs : s ∈ vtPre) (hc : callB s = true) :
    ∀ v ∈ s.vals, vtAux v.idx = false := by
  have hfix : fixNe s = s := by cases s <;> simp_all [callB, fixNe]
  have hm : s ∈ vtEvL := by
    have := vtEvL_mem hs (fun c z n h ↦ by subst h; simp [callB] at hc)
    rwa [hfix] at this
  have hd := List.all_eq_true.mp vt_dead s hm
  exact dead_vals hd (fun x y t1 t2 k h ↦ by subst h; simp [callB] at hc)

/-- The layout of the caller's words and the buffers at `fp`. -/
def vtL (Lin : Layout) (sizes : List ℕ) (own : ℕ → List (List E)) (fs : String → ℕ) (fp : ℕ) :
    Layout :=
  Lin ++ bufL (fp + fs "verify_tables") sizes (own fp)

theorem regionL_append {L L' : Layout} {i : ℕ} (h : RegionL (L ++ L') i) :
    RegionL L i ∨ RegionL L' i := by
  obtain ⟨q, hq, h1, h2⟩ := h
  rcases List.mem_append.mp hq with hq | hq
  · exact Or.inl ⟨q, hq, h1, h2⟩
  · exact Or.inr ⟨q, hq, h1, h2⟩

theorem regionL_append_left {L L' : Layout} {i : ℕ} (h : RegionL L i) : RegionL (L ++ L') i :=
  let ⟨q, hq, h1, h2⟩ := h; ⟨q, List.mem_append_left _ hq, h1, h2⟩

theorem regionL_append_right {L L' : Layout} {i : ℕ} (h : RegionL L' i) : RegionL (L ++ L') i :=
  let ⟨q, hq, h1, h2⟩ := h; ⟨q, List.mem_append_right _ hq, h1, h2⟩

variable {fs : String → ℕ} {cert : String → V → ℕ}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
/-- **`verify_tables` is complete, placed**, from its honest valuation on every memory holding its
layout, its calls by relations loading from that layout, and the callees placed from those. -/
theorem vt_completeAt {κ : ℕ} (Lin : Layout) (args rets : List E) (hl : args.length = 22)
    (sizes : List ℕ) (own : ℕ → List (List E))
    (hown : ∀ fp, List.Forall₂ (fun c s => c.length ≤ s) (own fp) sizes)
    (w : ℕ → ℕ → E) (bufs : ℕ → List (E × ℕ))
    (hbufs : ∀ fp, ∀ q ∈ bufs fp, ∃ b, q.1 = ofK (gpow b) ∧
      ∀ i < q.2, RegionL (vtL Lin sizes own fs fp) (b + i))
    (hrun : ∀ fp rd, LowDef κ rd → MemL rd (vtL Lin sizes own fs fp) →
      (∀ s ∈ vtPre, VSH (coreProgram.RelIn rd (RegionL (vtL Lin sizes own fs fp))) rd
        (vtσ rd (w fp) args) s) ∧
      LoadsInBuf (vtσ rd (w fp) args) (bufs fp) vtPre ∧
      (vtPre.filterMap Main.Stmt.allocSz).map
        (fun x => x.2.elim id fun s => logG (vtσ rd (w fp) args s)) = sizes ∧
      ((vtPre.filterMap Main.Stmt.allocSz).map Prod.fst).map (vtσ rd (w fp) args) =
        (bases (fp + fs "verify_tables") sizes).map (fun b => ofK (gpow b)) ∧
      vtRets.map (vtσ rd (w fp) args) = rets)
    (hpure : ∀ fp, ∀ g ∈ vtKidS, ∀ a r, (∀ rd, LowDef κ rd → MemL rd (vtL Lin sizes own fs fp) →
      coreProgram.RelIn rd (RegionL (vtL Lin sizes own fs fp)) g a r) →
      CompleteAtD fs cert κ g (vtL Lin sizes own fs fp) a (Returns r)) :
    CompleteAtD fs cert κ "verify_tables" Lin args (Returns rets) := by
  obtain ⟨fn, hf, hp, hb⟩ := vtFound
  have hb' : fn.body = vtPre ++ [.ret vtRets] := hb
  -- the canonical memory and its callees
  classical
  obtain ⟨rdS, hS⟩ : ∃ rdS : ℕ → Reader, ∀ fp, (∃ rd, LowDef κ rd ∧ MemL rd (vtL Lin sizes own fs fp)) →
      LowDef κ (rdS fp) ∧ MemL (rdS fp) (vtL Lin sizes own fs fp) :=
    ⟨fun fp ↦ if h : ∃ rd, LowDef κ rd ∧ MemL rd (vtL Lin sizes own fs fp) then h.choose else fun _ ↦ none,
      fun fp h ↦ by simp only [h, ↓reduceDIte]; exact h.choose_spec⟩
  generalize hσS : (fun fp ↦ vtσ (rdS fp) (w fp) args) = σS
  -- the valuations agree at a call's values
  have hag : ∀ fp rd, LowDef κ rd → MemL rd (vtL Lin sizes own fs fp) → ∀ s ∈ vtPre, callB s = true →
      ∀ v ∈ s.vals, vtσ rd (w fp) args v = σS fp v := by
    intro fp rd hlow hL s hs hc v hv
    obtain ⟨-, hld, -⟩ := hrun fp rd hlow hL
    rw [← hσS]
    exact vt_agree hl hL (hS fp ⟨rd, hlow, hL⟩).2 (hbufs fp) hld (vt_call_vals hs hc v hv)
  have hmap : ∀ fp rd, LowDef κ rd → MemL rd (vtL Lin sizes own fs fp) → ∀ s ∈ vtPre, callB s = true →
      ∀ l : List V, (∀ v ∈ l, v ∈ s.vals) → l.map (vtσ rd (w fp) args) = l.map (σS fp) :=
    fun fp rd hlow hL s hs hc l hl' ↦
      List.map_congr_left fun v hv ↦ hag fp rd hlow hL s hs hc v (hl' v hv)
  -- the calls are the same on every memory
  have hcs : ∀ fp rd, LowDef κ rd → MemL rd (vtL Lin sizes own fs fp) →
      (vtPre.filterMap (Stmt.callSF (vtσ rd (w fp) args))).map (Main.mkCall (vtσ rd (w fp) args)) =
        (vtPre.filterMap (Stmt.callSF (σS fp))).map (Main.mkCall (σS fp)) := by
    intro fp rd hlow hL
    rw [List.map_filterMap, List.map_filterMap]
    refine List.filterMap_congr fun s hs ↦ ?_
    cases s with
    | call f a r => simp only [Stmt.callSF, Main.Stmt.callS, Option.map_some, Main.mkCall]
    | callIf c f a =>
      simp only [Stmt.callSF, Main.Stmt.callS, Option.map_some, Main.mkCall]
      rw [hag fp rd hlow hL _ hs rfl c (by simp [Stmt.vals])]
    | dispatch x fs' a r =>
      simp only [Stmt.callSF, Option.map_some, Main.mkCall]
      rw [hag fp rd hlow hL _ hs rfl x (by simp [Stmt.vals])]
    | _ => simp only [Stmt.callSF, Main.Stmt.callS, Option.map_none]
  refine completeAt_flatD (fs := fs) (cert := cert) hf vt_not_loop κ Lin args rets hb' vt_flat
    vt_addrs sizes own hown
    (fun fp ↦ ((vtPre.filterMap (Stmt.callSF (σS fp))).map (Main.mkCall (σS fp))).map
      (kidOf (σS fp) (vtL Lin sizes own fs fp))) ?hkc ?hkr ?hkm ?hσ
  case hkr =>
    intro fp k hk _ i hi
    obtain ⟨c, -, rfl⟩ := List.mem_map.mp hk
    exact regionL_append hi
  case hkm =>
    intro fp rd hB hLin k hk
    obtain ⟨c, -, rfl⟩ := List.mem_map.mp hk
    exact Main.memL_append.mpr ⟨hLin, hB⟩
  case hkc =>
    intro fp k hk ht
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hk
    by_cases hex : ∃ rd, LowDef κ rd ∧ MemL rd (vtL Lin sizes own fs fp)
    swap
    · intro fp'
      refine ⟨0, [], c.rets.map (σS fp), [], ⟨rfl, rfl⟩, by simp [Within], disj_nil,
        fun rd hlow hL ↦ absurd ⟨rd, hlow, by simpa [kidOf] using hL⟩ hex⟩
    obtain ⟨hlS, hLS⟩ := hS fp hex
    have hvS : ∀ s ∈ vtPre, VSH (coreProgram.RelIn (rdS fp) (RegionL (vtL Lin sizes own fs fp))) (rdS fp) (σS fp) s := by
      rw [← hσS]; exact (hrun fp (rdS fp) hlS hLS).1
    obtain ⟨t, ht', rfl⟩ := List.mem_map.mp hc
    obtain ⟨s, hs, hst⟩ := List.mem_filterMap.mp ht'
    have hok := List.all_eq_true.mp vt_callOk s hs
    cases s with
    | call f a r =>
      simp only [Stmt.callSF, Main.Stmt.callS, Option.some.injEq] at hst
      subst hst
      simp only [Main.mkCall, kidOf]
      refine hpure fp f (by simpa [vtCallOk] using hok) _ _ fun rd hlow hL ↦ ?_
      have h : coreProgram.RelIn rd (RegionL (vtL Lin sizes own fs fp)) f (a.map (vtσ rd (w fp) args))
          (r.map (vtσ rd (w fp) args)) := (hrun fp rd hlow hL).1 _ hs
      rwa [hmap fp rd hlow hL _ hs rfl a (fun v hv ↦ by simp [Stmt.vals, hv]),
        hmap fp rd hlow hL _ hs rfl r (fun v hv ↦ by simp [Stmt.vals, hv])] at h
    | callIf cnd f a =>
      simp only [Stmt.callSF, Main.Stmt.callS, Option.some.injEq] at hst
      subst hst
      simp only [Main.mkCall, kidOf, decide_eq_true_eq, List.map_nil] at ht ⊢
      refine hpure fp f (by simpa [vtCallOk] using hok) _ _ fun rd hlow hL ↦ ?_
      have h : IsInK (vtσ rd (w fp) args cnd) ∧ (vtσ rd (w fp) args cnd ≠ 0 →
          coreProgram.RelIn rd (RegionL (vtL Lin sizes own fs fp)) f (a.map (vtσ rd (w fp) args)) []) :=
        (hrun fp rd hlow hL).1 _ hs
      have e := hag fp rd hlow hL _ hs rfl cnd (by simp [Stmt.vals])
      have h2 := h.2 (by rw [e]; exact ht)
      rwa [hmap fp rd hlow hL _ hs rfl a (fun v hv ↦ by simp [Stmt.vals, hv])] at h2
    | dispatch x fs' a r =>
      simp only [Stmt.callSF, Option.some.injEq] at hst
      subst hst
      simp only [vtCallOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hok
      obtain ⟨j, hj, hxj, -⟩ := hvS _ hs
      have hlog : logG (σS fp x) = j := by rw [hxj]; exact logG_spec (by omega)
      simp only [Main.mkCall, kidOf, hlog, List.getD_eq_getElem _ _ hj]
      refine hpure fp _ (by simpa using hok.1 _ (List.getElem_mem hj)) _ _ fun rd hlow hL ↦ ?_
      obtain ⟨j', hj', hxj', h⟩ := ((hrun fp rd hlow hL).1 _ hs :
        ∃ (j' : ℕ) (h : j' < fs'.length), vtσ rd (w fp) args x = ofK (gpow j') ∧
          coreProgram.RelIn rd (RegionL (vtL Lin sizes own fs fp)) fs'[j'] (a.map (vtσ rd (w fp) args))
            (r.map (vtσ rd (w fp) args)))
      have e := hag fp rd hlow hL _ hs rfl x (by simp [Stmt.vals])
      have hjj : j' = j := by
        have := congrArg logG (hxj'.symm.trans (e.trans hxj))
        rwa [logG_spec (by omega), logG_spec (by omega)] at this
      subst hjj
      rwa [hmap fp rd hlow hL _ hs rfl a (fun v hv ↦ by simp [Stmt.vals, hv]),
        hmap fp rd hlow hL _ hs rfl r (fun v hv ↦ by simp [Stmt.vals, hv])] at h
    | _ => simp [Stmt.callSF, Main.Stmt.callS] at hst
  case hσ =>
    intro fp outs ho rd hlow hB hLin
    have hL : MemL rd (vtL Lin sizes own fs fp) := Main.memL_append.mpr ⟨hLin, hB⟩
    obtain ⟨hv, hld, hsz, hbs, hrt⟩ := hrun fp rd hlow hL
    have hvR : ∀ s ∈ vtPre, VSH (coreProgram.Rel rd) rd (vtσ rd (w fp) args) s := fun s hs ↦
      vsh_mono (fun _ _ _ h ↦ Program.RelIn.rel h) (hv s hs)
    have hpar := vt_params (rd := rd) (w := w fp) hl
    have hag' := hag fp rd hlow hL
    have hcs' := hcs fp rd hlow hL
    beta_reduce at ho
    generalize vtσ rd (w fp) args = σ at hv hld hsz hbs hrt hvR hpar hag' hcs'
    refine ⟨σ, by rw [hp]; exact hpar, fun s hs ↦ ?_, ?_, hsz, hbs, ?_, ?_⟩
    · have hok := List.all_eq_true.mp vt_callOk s hs
      cases s with
      | dispatch x fs' a r =>
        simp only [vtCallOk, Bool.and_eq_true, decide_eq_true_eq] at hok
        obtain ⟨j, hj, hxj, -⟩ := hvR _ hs
        exact ⟨j, hj, by omega, hxj⟩
      | _ => exact True.intro
    · rw [hb', holdsList_append]
      exact holdsList_of_vsh vtPre vt_iteOk hvR hrt
    · rw [hcs']
      apply callsMatch_kids (σS := σS fp) (L := vtL Lin sizes own fs fp)
      rotate_left
      · exact ho
      intro c hc v hv
      obtain ⟨t, ht', rfl⟩ := List.mem_map.mp hc
      obtain ⟨s, hs, hst⟩ := List.mem_filterMap.mp ht'
      cases s with
      | call f a r =>
        simp only [Stmt.callSF, Main.Stmt.callS, Option.some.injEq] at hst
        subst hst
        exact hag' _ hs rfl v (by simpa [Main.mkCall, Stmt.vals] using hv)
      | callIf cnd f a =>
        simp only [Stmt.callSF, Main.Stmt.callS, Option.some.injEq] at hst
        subst hst
        exact hag' _ hs rfl v (by simp_all [Main.mkCall, Stmt.vals])
      | dispatch x fs' a r =>
        simp only [Stmt.callSF, Option.some.injEq] at hst
        subst hst
        exact hag' _ hs rfl v (by simp_all [Main.mkCall, Stmt.vals])
      | _ => simp [Stmt.callSF, Main.Stmt.callS] at hst
    · intro q hq
      obtain ⟨s, hs, hsq⟩ := List.mem_filterMap.mp hq
      cases s with
      | atom a =>
        cases a with
        | load d p off =>
          simp only [Stmt.loadS, Option.some.injEq] at hsq
          subst hsq
          obtain ⟨i, hi, hr⟩ := inBuf_region (hbufs fp) (hld d p off hs)
          exact ⟨i, hi, regionL_append hr⟩
        | _ => simp [Stmt.loadS] at hsq
      | _ => simp [Stmt.loadS] at hsq
end
end LeanVM.Guest.B1.Tables
