/-
  LeanVM.Guest.B1.Gkr.VbgB

  `verify_bus_gkr`'s callee `__loop7` within its words on the honest buffers.
-/

module

public import LeanVM.Guest.B1.Gkr.Loop7T
public import LeanVM.Guest.B1.Gkr.VbgAt

/-!
# `verify_bus_gkr`'s callees, within their words

* `vbg_ly7Mem`: on the honest buffers (`vbgLay`), `__loop7`'s bounds' words (`Ly7Mem`): the
  `depth_shift` word `g^(depth % 2)`, each slot's `half` and `parity`.
* `vbg_loop7_total`: there, a valid tree of `__loop7` from `1` below `g^(depth/2)` has at most
  `ly7Total` words.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {fs : String → ℕ}

/-- **`__loop7`'s bounds' words on the honest buffers.** -/
theorem vbg_ly7Mem {depth : ℕ} (hd : depth ≤ 32) {cap0 xs : List E} {r : E × List E × List E} {cap' : List E}
    (hrun : RunsTo (gkrPhase depth) ⟨cap0, []⟩ xs r ⟨cap', []⟩)
    (hc : ∃ sp, (⟨cap0, []⟩ : Fs).Carries sp) {ec eL eR eP ePa eD : ℕ} {rd : Reader}
    (hm : MemLay rd (vbgLay depth cap0 xs (ofK (gpow ec)) eL eR eP ePa eD)) :
    Ly7Mem rd (ofK (gpow eD)) (gen ^ depth) (ofK (gpow eL)) (depth % 2) (depth / 2) := by
  obtain ⟨-, -, -, hsteps, -, -, -, -⟩ := gk_walk hrun hc
  obtain ⟨sp, hsp⟩ := hc
  have hsc : capOf sp.state = cap0 := hsp.1
  have hcl : cap0.length = 5 := by rw [← hsc]; simp [capOf]
  have hcan : AllCanonical cap0 := by rw [← hsc]; exact tb_capOf_canonical _
  unfold vbgLay at hm
  rw [memLay_append, memLay_append, memLay_append, memLay_append] at hm
  obtain ⟨⟨⟨⟨-, hmS⟩, hmP⟩, -⟩, hmT⟩ := hm
  set sh := depth % 2 with hsh
  set m := depth / 2 with hmm
  have hsh2 : sh < 2 := by omega
  have inv := gkSl_inv (xs := xs) (sh := sh) hcl hcan
  have hpl : ∀ j ≤ m, (gkSl cap0 xs sh j).2.1.point.length = 2 * j + sh :=
    gkSl_point_len (gkSl0_point_len cap0 xs sh hsh2) fun j hj => (hsteps j hj).1
  have hD := hmT _ (List.mem_cons_of_mem _ List.mem_cons_self)
  refine ⟨?_, fun j hj ↦ ?_⟩
  · rw [tb_loadHolds_mul_gen_pow, Nat.add_zero]
    have := hD depth (by simp; omega)
    simpa [hsh] using this
  · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hhalf, hpar⟩ :=
      gkSlotC_of (inv j).1 (inv j).2.1 (inv j).2.2.1 (inv j).2.2.2 (hpl j (by omega))
        (by rw [tb_ofK_gpow_mul]
            exact hmP _ (List.mem_map.mpr ⟨j, List.mem_range.mpr (by omega), rfl⟩))
        (hmS _ (List.mem_map.mpr ⟨j, List.mem_range.mpr (by omega), rfl⟩))
    exact ⟨hhalf, hpar⟩

/-- `__loop7`'s words from `1` below `g^(depth/2)`: the iterations' bounds and the last tail's
frame. -/
def ly7Total (fs : String → ℕ) (K29 R depth : ℕ) : ℕ :=
  Budget.iterSum (ly7B fs K29 R (depth % 2)) 0 (depth / 2) + fs "__loop7"

/-- **`__loop7`'s words on the honest buffers.** -/
theorem vbg_loop7_total {depth : ℕ} (hd : depth ≤ 32) {cap0 xs : List E}
    {r : E × List E × List E} {cap' : List E}
    (hrun : RunsTo (gkrPhase depth) ⟨cap0, []⟩ xs r ⟨cap', []⟩)
    (hc : ∃ sp, (⟨cap0, []⟩ : Fs).Carries sp) {ec eL eR eP ePa eD : ℕ} {rd : Reader}
    (hm : MemLay rd (vbgLay depth cap0 xs (ofK (gpow ec)) eL eR eP ePa eD)) {K29 R : ℕ}
    (h29 : TotalLeOn coreProgram fs "__loop29" LoopPre (fun a ↦ logG (a.getD 1 0) * K29))
    (hR1 : TotalLe coreProgram fs "gkr_rounds__L1" (fun _ ↦ R))
    (hR2 : TotalLe coreProgram fs "gkr_rounds__L2" (fun _ ↦ R))
    (hm0 : 0 < depth / 2) {t : Tree} {rets : List E} (hn : t.name = "__loop7")
    (hv : t.Valid coreProgram rd [1, gen ^ (depth / 2), ofK (gpow eD), gen ^ depth,
      ofK (gpow eL), ofK (gpow eR)] rets) (hb : t.BufsOk coreProgram) :
    t.total fs ≤ ly7Total fs K29 R depth := by
  rw [show (1 : E) = gen ^ 0 from (pow_zero _).symm] at hv
  have hch := ly7_chain (rounds := ofK (gpow eR)) (by omega : depth % 2 < 2) (by omega)
    (vbg_ly7Mem hd hrun hc hm) (depth / 2) 0 t rets (by omega) hm0 hn hv hb
  exact ly7_total fs (by omega) h29 hR1 hR2 _ _ t _ rets hch hv hb

end
end LeanVM.Guest.B1.Tables
