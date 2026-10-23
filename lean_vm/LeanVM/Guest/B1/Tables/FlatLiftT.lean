/-
  LeanVM.Guest.B1.Tables.FlatLiftT

  A flat function evaluated forward, placed by a tree of honest shape (`Budget.NodeHonest`).
-/

module

public import LeanVM.Guest.B1.Tables.FlatLift
public import LeanVM.Guest.B1.Tables.FlatAtT
public import LeanVM.Guest.Budget.Strengthen

/-!
# Flat functions, placed, by a tree of honest shape

`flat_completeAtT`: `flat_completeAt` by a tree `NodeHonest F.name Q (flatCalls F.pre)
(fun _ ↦ sizes) Ts` when the honest valuation satisfies `Q` on every memory holding the layout,
`Ts` covers the body's calls, and the predicate `Ts[i]` holds of every valid tree of call `i`'s
callee at its honest arguments, on every memory defined below `2^κ` holding the layout
(`CompleteAtD.toT_on` on the callee's `Lift.completeAtD_of_relIn`).
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Fwd
open LeanVM.Guest.B1.Main (Layout MemL RegionL)
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

theorem flatCalls_length (pre : List Stmt) (σ : Val) :
    (flatCalls pre σ).length = (pre.filter callB).length := by
  unfold flatCalls
  rw [List.length_map]
  induction pre with
  | nil => rfl
  | cons s ss ih =>
    cases s <;> simp [List.filterMap_cons, List.filter_cons, Stmt.callSF, Main.Stmt.callS, callB, ih]

variable {fs : String → ℕ} {cert : String → V → ℕ}

theorem kidsDT_of_getElem {κ : ℕ} {σS : Val} {L : Layout} :
    ∀ (cs : List Call) (Ts : List (Tree → Prop)),
      (∀ i (c : Call), cs[i]? = some c → c.taken = true →
        CompleteAtDT fs cert κ c.f L (c.args.map σS) (Returns (c.rets.map σS))
          (Ts.getD i fun _ ↦ True)) →
      KidsDT fs cert κ (cs.map (kidOf σS L)) Ts
  | [], _, _ => trivial
  | c :: cs, Ts, h => by
    refine ⟨fun ht ↦ ?_, kidsDT_of_getElem cs Ts.tail fun i c' hc ht ↦ ?_⟩
    · have := h 0 c rfl ht
      cases Ts <;> exact this
    · have := h (i + 1) c' (by simpa using hc) ht
      cases Ts <;> simpa using this

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
/-- **A flat function is complete, placed, by a tree of honest shape.** -/
theorem flat_completeAtT (F : FlatFn) {κ : ℕ} (Lin : Layout) (args rets : List E)
    (hl : args.length = F.k)
    (sizes : List ℕ) (own : ℕ → List (List E))
    (hown : ∀ fp, List.Forall₂ (fun c s => c.length ≤ s) (own fp) sizes)
    (w : ℕ → ℕ → E) (bufs : ℕ → List (E × ℕ))
    (hbufs : ∀ fp, ∀ q ∈ bufs fp, ∃ b, q.1 = ofK (gpow b) ∧
      ∀ i < q.2, RegionL (flatL F.name Lin sizes own fs fp) (b + i))
    (hrun : ∀ fp rd, LowDef κ rd → MemL rd (flatL F.name Lin sizes own fs fp) →
      (∀ s ∈ F.pre, VSH (coreProgram.RelIn rd (RegionL (flatL F.name Lin sizes own fs fp))) rd
        (F.σ rd (w fp) args) s) ∧
      LoadsInBuf (F.σ rd (w fp) args) (bufs fp) F.evL ∧
      (F.pre.filterMap Main.Stmt.allocSz).map
        (fun x => x.2.elim id fun s => logG (F.σ rd (w fp) args s)) = sizes ∧
      ((F.pre.filterMap Main.Stmt.allocSz).map Prod.fst).map (F.σ rd (w fp) args) =
        (bases (fp + fs F.name) sizes).map (fun b => ofK (gpow b)) ∧
      F.rets.map (F.σ rd (w fp) args) = rets)
    (Q : Val → Prop) (Ts : List (Tree → Prop))
    (hQ : ∀ fp rd, LowDef κ rd → MemL rd (flatL F.name Lin sizes own fs fp) →
      Q (F.σ rd (w fp) args))
    (hTl : (F.pre.filter callB).length ≤ Ts.length)
    (hT : ∀ fp rd, LowDef κ rd → MemL rd (flatL F.name Lin sizes own fs fp) → ∀ i (c : Call),
      (flatCalls F.pre (F.σ rd (w fp) args))[i]? = some c → c.taken = true →
      ∀ (t : Tree) (r : List E), t.name = c.f →
        t.Valid coreProgram rd (c.args.map (F.σ rd (w fp) args)) r → t.BufsOk coreProgram →
        (Ts.getD i fun _ ↦ True) t) :
    CompleteAtDT fs cert κ F.name Lin args (Returns rets)
      (Budget.NodeHonest coreProgram F.name Q (flatCalls F.pre) (fun _ ↦ sizes) Ts) := by
  have hf := F.hf
  have hp := F.hp
  have hb' := F.hb
  classical
  obtain ⟨rdS, hS⟩ : ∃ rdS : ℕ → Reader, ∀ fp, (∃ rd, LowDef κ rd ∧
      MemL rd (flatL F.name Lin sizes own fs fp)) →
      LowDef κ (rdS fp) ∧ MemL (rdS fp) (flatL F.name Lin sizes own fs fp) :=
    ⟨fun fp ↦ if h : ∃ rd, LowDef κ rd ∧ MemL rd (flatL F.name Lin sizes own fs fp) then
      h.choose else fun _ ↦ none, fun fp h ↦ by simp only [h, ↓reduceDIte]; exact h.choose_spec⟩
  generalize hσS : (fun fp ↦ F.σ (rdS fp) (w fp) args) = σS
  have hag : ∀ fp rd, LowDef κ rd → MemL rd (flatL F.name Lin sizes own fs fp) → ∀ s ∈ F.pre,
      callB s = true → ∀ v ∈ s.vals, F.σ rd (w fp) args v = σS fp v := by
    intro fp rd hlow hL s hs hc v hv
    obtain ⟨-, hld, -⟩ := hrun fp rd hlow hL
    rw [← hσS]
    exact F.agree hl hL (hS fp ⟨rd, hlow, hL⟩).2 (hbufs fp) hld (F.call_vals hs hc v hv)
  have hmap : ∀ fp rd, LowDef κ rd → MemL rd (flatL F.name Lin sizes own fs fp) → ∀ s ∈ F.pre,
      callB s = true → ∀ l : List V, (∀ v ∈ l, v ∈ s.vals) →
        l.map (F.σ rd (w fp) args) = l.map (σS fp) :=
    fun fp rd hlow hL s hs hc l hl' ↦
      List.map_congr_left fun v hv ↦ hag fp rd hlow hL s hs hc v (hl' v hv)
  have hcs : ∀ fp rd, LowDef κ rd → MemL rd (flatL F.name Lin sizes own fs fp) →
      flatCalls F.pre (F.σ rd (w fp) args) = flatCalls F.pre (σS fp) := by
    intro fp rd hlow hL
    unfold flatCalls
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
  -- a call's values agree
  have hagc : ∀ fp rd, LowDef κ rd → MemL rd (flatL F.name Lin sizes own fs fp) →
      ∀ c ∈ flatCalls F.pre (σS fp), ∀ v ∈ c.args ++ c.rets, F.σ rd (w fp) args v = σS fp v := by
    intro fp rd hlow hL c hc v hv
    obtain ⟨t, ht', rfl⟩ := List.mem_map.mp hc
    obtain ⟨s, hs, hst⟩ := List.mem_filterMap.mp ht'
    cases s with
    | call f a r =>
      simp only [Stmt.callSF, Main.Stmt.callS, Option.some.injEq] at hst
      subst hst
      exact hag fp rd hlow hL _ hs rfl v (by simpa [Main.mkCall, Stmt.vals] using hv)
    | callIf cnd f a =>
      simp only [Stmt.callSF, Main.Stmt.callS, Option.some.injEq] at hst
      subst hst
      exact hag fp rd hlow hL _ hs rfl v (by simp_all [Main.mkCall, Stmt.vals])
    | dispatch x fs' a r =>
      simp only [Stmt.callSF, Option.some.injEq] at hst
      subst hst
      exact hag fp rd hlow hL _ hs rfl v (by simp_all [Main.mkCall, Stmt.vals])
    | _ => simp [Stmt.callSF, Main.Stmt.callS] at hst
  -- each entered callee is complete
  have hkd : ∀ fp, ∀ c ∈ flatCalls F.pre (σS fp), c.taken = true →
      CompleteAtD fs cert κ c.f (flatL F.name Lin sizes own fs fp) (c.args.map (σS fp))
        (Returns (c.rets.map (σS fp))) := by
    intro fp c hc ht
    by_cases hex : ∃ rd, LowDef κ rd ∧ MemL rd (flatL F.name Lin sizes own fs fp)
    swap
    · intro fp'
      exact ⟨0, [], c.rets.map (σS fp), [], ⟨rfl, rfl⟩, by simp [Within], disj_nil,
        fun rd hlow hL ↦ absurd ⟨rd, hlow, by simpa using hL⟩ hex⟩
    obtain ⟨hlS, hLS⟩ := hS fp hex
    have hvS : ∀ s ∈ F.pre, VSH (coreProgram.RelIn (rdS fp)
        (RegionL (flatL F.name Lin sizes own fs fp))) (rdS fp) (σS fp) s := by
      rw [← hσS]; exact (hrun fp (rdS fp) hlS hLS).1
    obtain ⟨t, ht', rfl⟩ := List.mem_map.mp hc
    obtain ⟨s, hs, hst⟩ := List.mem_filterMap.mp ht'
    have hok := List.all_eq_true.mp F.hcall s hs
    cases s with
    | call f a r =>
      simp only [Stmt.callSF, Main.Stmt.callS, Option.some.injEq] at hst
      subst hst
      simp only [Main.mkCall]
      refine Lift.completeAtD_of_relIn F.hpure (by simpa [callOk] using hok)
        fun rd hlow hL ↦ ?_
      have h : coreProgram.RelIn rd (RegionL (flatL F.name Lin sizes own fs fp)) f
          (a.map (F.σ rd (w fp) args)) (r.map (F.σ rd (w fp) args)) := (hrun fp rd hlow hL).1 _ hs
      rwa [hmap fp rd hlow hL _ hs rfl a (fun v hv ↦ by simp [Stmt.vals, hv]),
        hmap fp rd hlow hL _ hs rfl r (fun v hv ↦ by simp [Stmt.vals, hv])] at h
    | callIf cnd f a =>
      simp only [Stmt.callSF, Main.Stmt.callS, Option.some.injEq] at hst
      subst hst
      simp only [Main.mkCall, decide_eq_true_eq, List.map_nil] at ht ⊢
      refine Lift.completeAtD_of_relIn F.hpure (by simpa [callOk] using hok)
        fun rd hlow hL ↦ ?_
      have h : IsInK (F.σ rd (w fp) args cnd) ∧ (F.σ rd (w fp) args cnd ≠ 0 →
          coreProgram.RelIn rd (RegionL (flatL F.name Lin sizes own fs fp)) f
            (a.map (F.σ rd (w fp) args)) []) := (hrun fp rd hlow hL).1 _ hs
      have e := hag fp rd hlow hL _ hs rfl cnd (by simp [Stmt.vals])
      have h2 := h.2 (by rw [e]; exact ht)
      rwa [hmap fp rd hlow hL _ hs rfl a (fun v hv ↦ by simp [Stmt.vals, hv])] at h2
    | dispatch x fs' a r =>
      simp only [Stmt.callSF, Option.some.injEq] at hst
      subst hst
      simp only [callOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hok
      obtain ⟨j, hj, hxj, -⟩ := hvS _ hs
      have hlog : logG (σS fp x) = j := by rw [hxj]; exact logG_spec (by omega)
      simp only [Main.mkCall, hlog, List.getD_eq_getElem _ _ hj]
      refine Lift.completeAtD_of_relIn F.hpure (by simpa using hok.1 _ (List.getElem_mem hj))
        fun rd hlow hL ↦ ?_
      obtain ⟨j', hj', hxj', h⟩ := ((hrun fp rd hlow hL).1 _ hs :
        ∃ (j' : ℕ) (h : j' < fs'.length), F.σ rd (w fp) args x = ofK (gpow j') ∧
          coreProgram.RelIn rd (RegionL (flatL F.name Lin sizes own fs fp)) fs'[j']
            (a.map (F.σ rd (w fp) args)) (r.map (F.σ rd (w fp) args)))
      have e := hag fp rd hlow hL _ hs rfl x (by simp [Stmt.vals])
      have hjj : j' = j := by
        have := congrArg logG (hxj'.symm.trans (e.trans hxj))
        rwa [logG_spec (by omega), logG_spec (by omega)] at this
      subst hjj
      rwa [hmap fp rd hlow hL _ hs rfl a (fun v hv ↦ by simp [Stmt.vals, hv]),
        hmap fp rd hlow hL _ hs rfl r (fun v hv ↦ by simp [Stmt.vals, hv])] at h
    | _ => simp [Stmt.callSF, Main.Stmt.callS] at hst
  refine completeAt_flatDT (fs := fs) (cert := cert) hf F.hloop κ Lin args rets hb' F.hflat
    F.haddrs sizes own hown
    (fun fp ↦ (flatCalls F.pre (σS fp)).map (kidOf (σS fp) (flatL F.name Lin sizes own fs fp)))
    Q Ts ?hkc ?hkl ?hkr ?hkm ?hσ
  case hkl =>
    intro fp
    rw [List.length_map, flatCalls_length]; exact hTl
  case hkr =>
    intro fp k hk _ i hi
    obtain ⟨c, -, rfl⟩ := List.mem_map.mp hk
    exact regionL_append hi
  case hkm =>
    intro fp rd hB hLin k hk
    obtain ⟨c, -, rfl⟩ := List.mem_map.mp hk
    exact Main.memL_append.mpr ⟨hLin, hB⟩
  case hkc =>
    intro fp
    refine kidsDT_of_getElem _ Ts fun i c hc ht ↦ ?_
    have hcm : c ∈ flatCalls F.pre (σS fp) := List.mem_of_getElem? hc
    refine (hkd fp c hcm ht).toT_on fun rd hlow hL t r hn hv hbo ↦ ?_
    have hc' : (flatCalls F.pre (F.σ rd (w fp) args))[i]? = some c := by
      rw [hcs fp rd hlow hL]; exact hc
    have ha : c.args.map (σS fp) = c.args.map (F.σ rd (w fp) args) :=
      List.map_congr_left fun v hv ↦ (hagc fp rd hlow hL c hcm v (List.mem_append_left _ hv)).symm
    rw [ha] at hv
    exact hT fp rd hlow hL i c hc' ht t r hn hv hbo
  case hσ =>
    intro fp outs ho rd hlow hB hLin
    have hL : MemL rd (flatL F.name Lin sizes own fs fp) := Main.memL_append.mpr ⟨hLin, hB⟩
    obtain ⟨hv, hld, hsz, hbs, hrt⟩ := hrun fp rd hlow hL
    have hvR : ∀ s ∈ F.pre, VSH (coreProgram.Rel rd) rd (F.σ rd (w fp) args) s := fun s hs ↦
      vsh_mono (fun _ _ _ h ↦ Program.RelIn.rel h) (hv s hs)
    have hpar := F.params (rd := rd) (w := w fp) hl
    have hag' := hagc fp rd hlow hL
    have hcs' := hcs fp rd hlow hL
    have hQ' := hQ fp rd hlow hL
    generalize F.σ rd (w fp) args = σ at hv hld hsz hbs hrt hvR hpar hag' hcs' hQ'
    refine ⟨σ, by rw [hp, List.map_map]; exact hpar, fun s hs ↦ ?_, ?_, hsz, hbs, ?_, ?_, hQ'⟩
    · have hok := List.all_eq_true.mp F.hcall s hs
      cases s with
      | dispatch x fs' a r =>
        simp only [callOk, Bool.and_eq_true, decide_eq_true_eq] at hok
        obtain ⟨j, hj, hxj, -⟩ := hvR _ hs
        exact ⟨j, hj, by omega, hxj⟩
      | _ => exact True.intro
    · rw [hb', holdsList_append]
      exact holdsList_of_vsh F.pre F.hiteOk hvR hrt
    · rw [hcs']
      exact callsMatch_kids _ outs hag' ho
    · intro q hq
      obtain ⟨d, hd⟩ := F.loadsEv_mem hq
      obtain ⟨i, hi, hr⟩ := inBuf_region (hbufs fp) (hld d q.1 q.2 hd)
      exact ⟨i, hi, regionL_append hr⟩

end
end LeanVM.Guest.B1.Tables
