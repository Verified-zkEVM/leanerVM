/-
  LeanVM.Guest.B2C.CplRunB

  A function's run (`CplRun.lean`) under any semantics of `BLAKE2S`.
-/

module

public import LeanVM.Guest.B2C.CplRun
public import LeanVM.Guest.B2C.CplWalkB

/-!
# A function's run under any `BLAKE2S` semantics

`CplRun.lean`'s `FnH` with `S : BlakeSem` a parameter (`FnHB`: the callees run and the path's
events hold under `S`), `FnHB.ctx` and `whB_part` (the walk's hypotheses hold in every part). What
a soundness window's check gives (`checkWin_cpl`, …) is `CplRun.lean`'s.

* `fnHB_deployed`: at `blakeDeployed`, `FnHB` is `FnH`.
-/

namespace LeanVM.Guest.B2C

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Exec
open LeanVM.Guest.Check LeanVM.Guest.Memory

@[expose] public section

variable {S : BlakeSem}

/-! ## A part's hypotheses -/

section Part

variable {κ : ℕ} {L : MemImage κ} {j fp : ℕ} {σ : Val} {es : List Ev} {vs : List V}
  {kfps : List ℕ} {hdr : E × E} {ck : List (Opcode → ℕ)}

variable (S) in
/-- **What `cpl_run` assumes of function `j`'s instance.** -/
structure FnHB (L : MemImage κ) (j fp : ℕ) (σ : Val) (es : List Ev) (vs : List V) (kfps : List ℕ)
    (hdr : E × E) (ck : List (Opcode → ℕ)) : Prop where
  j1 : 1 ≤ j
  jn : j < nFns
  ok : CplOk j
  chk : ∀ i ≤ (certOf j).cuts.length, checkWin glob (fnOf j) (coreOf j) (certOf j) (j == 1) i = true
  pows : (certOf j).facts.pows.Ok
  le32 : κ ≤ 32
  jt : JTHolds glob L
  tab : ∀ q ∈ Memory.tableCells, L.read (gpow q.1) = some q.2
  main : j = 1 → fp = 0
  frame : FrameHolds L j fp σ es vs kfps hdr
  kids : KidsRunB S L σ es kfps ck
  hev : ∀ e ∈ es, e.HoldsB S L.read σ
  walk : walk σ (coreOf j).body = .ret es vs

theorem FnHB.ctx (F : FnHB S L j fp σ es vs kfps hdr ck) : Exec.Ctx (certOf j).facts κ (gpow fp) := by
  refine ⟨F.pows, fun h ↦ ?_, F.le32⟩
  have := checkWin_fpOne (F.chk 0 (Nat.zero_le _))
  rw [h] at this
  rw [F.main (by simpa using this), gpow_zero']

/-- **The walk's hypotheses hold in every part**, the part's atoms being events. -/
theorem whB_part (F : FnHB S L j fp σ es vs kfps hdr ck)
    (hlb : lastOkC (coreOf j).body = true) {i k : ℕ} (hi : i ≤ (certOf j).cuts.length) :
    WHB S L j fp (Xp j i k) (segsW j i) (wJW j i) (wenvW j i) σ es vs kfps hdr ck := by
  have hctx := F.ctx
  have hfet := guest_fetches (fnOf_memC F.jn)
  have hcw := checkWin_cpl (F.chk i hi)
  have hw0 := winOkC_of (F.ok i hi 0 (one_le_nParts j i))
  simp only [winOkC, Bool.and_eq_true] at hw0
  obtain ⟨⟨⟨⟨hpack, -⟩, -⟩, hpar⟩, -⟩ := hw0
  refine ⟨cxOk F.frame F.pows _ _ _ _, hctx, fun s hs ↦ execWinB_z hctx hfet hs,
    fun s hs ↦ (execWinB_good (S := S) (L := L) hctx hfet _ _ _ s hs).2.2, rfl, hcw.2.2.1,
    fun v c h ↦ clocW_get (cont_of F.chk) hi hcw.2.1 rfl hpack h, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, fun n hsel ↦ ?_, F.frame, F.kids, F.hev, fun hl ↦ lastCall_of F.walk hl hlb, F.jt,
    F.tab, F.j1, F.jn⟩
  simp only [Bool.or_eq_true, Nat.blt_eq] at hsel
  unfold namedOf
  rcases hsel with h | h
  · have hpe : (coreOf j).params = (List.range (coreOf j).params.length).map V.n := beq_iff_eq.mp hpar
    refine List.mem_append_left _ (List.mem_append_left _ ?_)
    have : (Xp j i k).nargs = (coreOf j).params.length := rfl
    rw [this] at h
    rw [hpe]
    exact List.mem_map.mpr ⟨n, List.mem_range.mpr h, rfl⟩
  · rw [bitK_eq] at h
    rcases nvOf_spec _ 0 n h with h' | ⟨a, ha, hm⟩
    · simp at h'
    · exact List.mem_append_left _ (List.mem_append_right _
        (List.mem_flatMap.mpr ⟨_, atoms_last hlb F.walk (fun h ↦ by cases h) ha, hm⟩))

end Part


/-! ## At the deployed semantics -/

section Deployed

variable {κ : ℕ} {L : MemImage κ}

/-- At the deployed semantics, `FnHB` is `CplRun.lean`'s `FnH`. -/
theorem fnHB_deployed (j fp : ℕ) (σ : Val) (es : List Ev) (vs : List V) (kfps : List ℕ)
    (hdr : E × E) (ck : List (Opcode → ℕ)) :
    FnHB blakeDeployed L j fp σ es vs kfps hdr ck = FnH L j fp σ es vs kfps hdr ck := by
  apply propext
  constructor <;> intro h <;> cases h <;> constructor <;>
    first | assumption | (simp only [kidsRunB_deployed, ev_holdsB_deployed] at *; assumption)

end Deployed

end
end LeanVM.Guest.B2C
