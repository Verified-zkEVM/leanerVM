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

end
end LeanVM.Guest.B1.Tables
