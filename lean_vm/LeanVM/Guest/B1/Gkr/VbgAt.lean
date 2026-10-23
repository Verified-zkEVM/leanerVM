/-
  LeanVM.Guest.B1.Gkr.VbgAt

  `verify_bus_gkr` is complete in the uniform placed form (`CompleteAtD`).
-/

module

public import LeanVM.Guest.B1.Gkr.VbgLoads
public import LeanVM.Guest.B1.Tables.Kids.Loop8

/-!
# `verify_bus_gkr`, placed (TRIAGE G #43)

`vbg_run`: on a memory defined below `2^κ` (`κ ≥ 6`, the range check of `g^depth`) holding the
cursor's words, the point at `zeta` and the five buffers whole (`vbgOwnW`), the honest valuation
(`vbgFlat.σ`, the allocations answered by the buffers' pointers) satisfies every statement with
its calls by relations loading from a region `R` holding the point and the rows, its loads land
inside the buffers (`vbg_loadOk`, `vbg_ptrs`), its allocations are the buffers and it returns the
accepting run's capacity, cursor and values. `__loop8`'s relation loads from `R`
(`loop8_relIn`); `__loop7`'s is a hypothesis (`hL7`).

`verify_bus_gkr_completeAt`: `flat_completeAt` for `vbgFlat`, the buffers at the bump allocator's
positions from `fp + fs "verify_bus_gkr"`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

/-! ## Kernel facts -/

/-- An atom, or an `ite` of atoms. -/
def atomsDeep : Stmt → Bool
  | .atom _ => true
  | .ite _ z n => (z ++ n).all fun t ↦ match t with
    | .atom _ => true
    | _ => false
  | _ => false

/-- `__loop7`'s call. -/
def vbgCall7 : Stmt := .callIf (.n 303) "__loop7" [.n 304, .n 306, .n 57, .n 6, .n 15, .n 16]

/-- `__loop8`'s call. -/
def vbgCall8 : Stmt := .callIf (.n 316) "__loop8" [.n 317, .n 6, .n 7, .n 314]

/-- Every statement is an atom, an `ite` of atoms, or one of the two calls. -/
def vbgKindB (s : Stmt) : Bool :=
  atomsDeep s || tbStmtsEqb [s] [vbgCall7] || tbStmtsEqb [s] [vbgCall8]

theorem vbg_kinds : vbgPre.all vbgKindB = true := by decide +kernel

theorem vbg_allocs : vbgPre.filterMap Main.Stmt.allocSz = [(.n 15, .inr (.n 14)),
    (.n 16, .inl 6034), (.n 17, .inl 1640), (.n 56, .inl 33), (.n 57, .inl 33)] := by
  decide +kernel

theorem vsh_atomsDeep {C C' : CallRel} {rd : Reader} {σ : Val} :
    ∀ {s : Stmt}, atomsDeep s = true → VSH C rd σ s → VSH C' rd σ s
  | .atom _, _, h => h
  | .ite c z n, hs, h => by
    simp only [atomsDeep, List.all_eq_true] at hs
    have ha : ∀ t ∈ z ++ n, SHolds C rd σ t → SHolds C' rd σ t := by
      intro t ht h'
      have := hs t ht
      cases t with
      | atom a => exact h'
      | _ => simp at this
    exact ⟨h.1, fun hc t ht ↦ ha t (List.mem_append_left _ ht) (h.2.1 hc t ht),
      fun hc t ht ↦ ha t (List.mem_append_right _ ht) (h.2.2 hc t ht)⟩

/-- The cursor's words reach `8`: two roots and the first step. -/
theorem gk_xs_len {depth : ℕ} (hd1 : 1 ≤ depth) {cap0 xs : List E} {r : E × List E × List E}
    {cap' : List E} (hrun : RunsTo (gkrPhase depth) ⟨cap0, []⟩ xs r ⟨cap', []⟩)
    (hc : ∃ sp, (⟨cap0, []⟩ : Fs).Carries sp) : 8 ≤ xs.length := by
  obtain ⟨-, hx2, hodd, hsteps, -, -, -, -⟩ := gk_walk hrun hc
  rcases Nat.mod_two_eq_zero_or_one depth with h0 | h1
  · obtain ⟨hok, hdr⟩ := hsteps 0 (by omega)
    have hpl0 := gkSl0_point_len cap0 xs (depth % 2) (by omega)
    have hl := gkStepD_xs_length hok
    have h02 : (gkSl cap0 xs (depth % 2) 0).2.2 = 2 := by rw [gkSl0_off]; simp [h0]
    have h1' : (gkSl cap0 xs (depth % 2) 1).2.2 = 14 := by
      show (gkSl cap0 xs (depth % 2) 0).2.2 + 4 * (2 * 0 + depth % 2) + 12 = 14
      rw [h02, h0]
    rw [h02, h1'] at hdr
    have := tb_drop_le hdr (by rw [hl, hpl0, h0]; norm_num) (by omega)
    omega
  · obtain ⟨hok, hdr⟩ := hodd h1
    have h6 : (gkOdd xs).xs.length = 6 := by rw [gkStepD_xs_length hok]; rfl
    have := tb_drop_le hdr (by rw [h6]) (by omega)
    omega

end
end LeanVM.Guest.B1.Tables
