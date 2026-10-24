/-
  LeanVM.Guest.B1.VerifySub.C.Hon

  `verify_sub`'s honest valuation on a memory: its evaluation list evaluated from the arguments,
  loads read from the memory, allocations, hints' and callees' words from an oracle. What it
  gives by position, and the statements that hold by it alone (after B1-c's `Hon`).
-/

module

public import LeanVM.Guest.B1.VerifySub.C.Flat
public import LeanVM.Guest.B1.Tables.VtC.Hon

/-!
# The honest valuation

`vsσ rd w args`: `vsEvL` evaluated (`Fwd.ev`) on the memory `rd` and the oracle `w` from the
arguments `args`. Each statement of the list satisfies its equations (`GoodS`) with the stores
`vsSL` (`vs_good`); the parameters are the arguments (`vsC_param`). `verify_sub` has no `ite`.

By position of `vsCPre` (the kernel comparing the statements read): `vs_goodL` (a block's
equations), `vs_read` (a read gives the word the memory holds), `vs_readH`, `vsh_store`.
`vs_block`: a block's statements satisfy `VSH` when the ones evaluation alone does not settle do.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Tables

@[expose] public section

/-- The stores of the evaluation list. -/
def vsSL : List Atom := storesOf 7 vsEvL

theorem vs_chk' : chk 7 vsEvL = some 1934 := by decide +kernel

/-- **The honest valuation** of `verify_sub`. -/
noncomputable def vsσ (rd : Reader) (w : ℕ → E) (args : List E) : Val :=
  B1.Val.ofArgs (ev rd w args vsEvL)

/-- The equations of a block, as one conjunction. -/
def VsGoodL (rd : Reader) (w : ℕ → E) (σ : Val) : List Stmt → Prop
  | [] => True
  | s :: ss => GoodS rd vsSL w σ (fixNe s) ∧ VsGoodL rd w σ ss

section
variable {rd : Reader} {w : ℕ → E} {args : List E}

theorem vs_good (hl : args.length = 7) : ∀ s ∈ vsEvL, GoodS rd vsSL w (vsσ rd w args) s := by
  have h := (ev_spec rd w vsEvL args (by rw [hl]; exact vs_chk')).2.2
  rw [hl] at h
  exact h

theorem vsC_param (hl : args.length = 7) {i : ℕ} (hi : i < 7) :
    vsσ rd w args (.n i) = args.getD i 0 :=
  ev_params rd w (by rw [hl]; exact vs_chk') (by rw [hl]; exact hi)

theorem vsC_params (hl : args.length = 7) :
    (List.range 7).map (fun k ↦ vsσ rd w args (.n k)) = args := by
  apply List.ext_getElem (by simp [hl])
  intro i h1 _
  simp only [List.getElem_map, List.getElem_range]
  rw [vsC_param hl (by simpa using h1), List.getD_eq_getElem _ _ (by simp at h1; omega)]

/-- A statement of the body is in the list as `fixNe` reads it (no `ite` in the body). -/
theorem vsEvL_mem {s : Stmt} (hs : s ∈ vsCPre) (hni : ∀ c z n, s ≠ .ite c z n) :
    fixNe s ∈ vsEvL :=
  List.mem_map_of_mem (mem_flatIte_of hni hs)

theorem vs_mem_slice {n : ℕ} {blk : List Stmt}
    (heq : tbStmtsEqb blk ((vsCPre.drop n).take blk.length) = true) {s : Stmt} (hs : s ∈ blk) :
    s ∈ vsCPre := by
  rw [tbStmtsEqb_sound heq] at hs
  exact List.mem_of_mem_drop (List.mem_of_mem_take hs)

theorem vs_goodS (hl : args.length = 7) {s : Stmt} (hs : s ∈ vsCPre) :
    GoodS rd vsSL w (vsσ rd w args) (fixNe s) := by
  by_cases hi : ∃ c z n, s = .ite c z n
  · obtain ⟨c, z, n, rfl⟩ := hi
    trivial
  · exact vs_good hl _ (vsEvL_mem hs fun c z n h ↦ hi ⟨c, z, n, h⟩)

/-- **A block's equations**, read at position `n`. -/
theorem vs_goodL (hl : args.length = 7) (n : ℕ) (blk : List Stmt)
    (heq : tbStmtsEqb blk ((vsCPre.drop n).take blk.length) = true) :
    VsGoodL rd w (vsσ rd w args) blk := by
  have h : ∀ s ∈ blk, GoodS rd vsSL w (vsσ rd w args) (fixNe s) :=
    fun s hs ↦ vs_goodS hl (vs_mem_slice heq hs)
  clear heq
  induction blk with
  | nil => trivial
  | cons s ss ih =>
    exact ⟨h s List.mem_cons_self, ih fun t ht ↦ h t (List.mem_cons_of_mem _ ht)⟩

/-- **A read** gives the word at its address (`0` if none). -/
theorem vs_read (hl : args.length = 7) (n : ℕ) {d p : V} {off : ℕ}
    (heq : tbStmtsEqb [.atom (.load d p off)] ((vsCPre.drop n).take 1) = true)
    (hS : Atom.load d p off ∉ vsSL) :
    vsσ rd w args d = rdAt rd (vsσ rd w args p) off := by
  have h := vs_goodS (rd := rd) (w := w) hl (vs_mem_slice (blk := [_]) heq List.mem_cons_self)
  simp only [fixNe, GoodS, Good] at h
  exact h.resolve_left hS

/-- A read of a word the memory holds holds, and reads it. -/
theorem vs_readH (hl : args.length = 7) (n : ℕ) {d p : V} {off : ℕ}
    (heq : tbStmtsEqb [.atom (.load d p off)] ((vsCPre.drop n).take 1) = true)
    (hS : Atom.load d p off ∉ vsSL) {v : E} (hm : LoadHolds rd (vsσ rd w args p) off v) :
    vsσ rd w args d = v ∧ VSH (coreProgram.Rel rd) rd (vsσ rd w args) (.atom (.load d p off)) := by
  have e : vsσ rd w args d = v := by
    rw [vs_read hl n heq hS, rdAt, hm.2]; rfl
  refine ⟨e, ?_⟩
  show LoadHolds rd _ _ _
  rw [e]; exact hm

/-- An atom evaluation alone settles (a constant, a sum, a copy, a product of older values, a
hint) holds. -/
theorem vs_auto (hl : args.length = 7) {s : Stmt} (hs : s ∈ vsCPre) (ha : autoB s = true) :
    VSH (coreProgram.Rel rd) rd (vsσ rd w args) s := by
  cases s with
  | atom a =>
    have hg := vs_goodS (rd := rd) (w := w) hl hs
    rw [fixNe_atom] at hg
    simp only [autoB, Bool.or_eq_true] at ha
    rcases ha with ha | ha
    · have e : fixA a = a := by
        cases a with
        | assertNe => simp [pureB] at ha
        | _ => rfl
      rw [e] at hg
      exact holds_of_pure (S := vsSL) (w := w) ha hg
    · cases a with
      | hint _ => exact True.intro
      | _ => simp only [hintB, Bool.false_eq_true] at ha
  | _ => simp only [autoB, Bool.false_eq_true] at ha

/-- **A block's statements hold** when the ones evaluation alone does not settle (`rest`) do. -/
theorem vs_block (hl : args.length = 7) (n : ℕ) (blk : List Stmt)
    (heq : tbStmtsEqb blk ((vsCPre.drop n).take blk.length) = true) (rest : List Stmt)
    (hrest : tbStmtsEqb (blk.filter (fun s ↦ !autoB s)) rest = true)
    (h : ∀ s ∈ rest, VSH (coreProgram.Rel rd) rd (vsσ rd w args) s) :
    ∀ s ∈ blk, VSH (coreProgram.Rel rd) rd (vsσ rd w args) s := by
  intro s hs
  cases ha : autoB s
  · exact h s (tbStmtsEqb_sound hrest ▸ List.mem_filter.mpr ⟨hs, by simp [ha]⟩)
  · exact vs_auto hl (vs_mem_slice heq hs) ha

end

end
end LeanVM.Guest.B1.VerifySub
