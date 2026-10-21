/-
  LeanVM.Guest.B2C.CplSemB

  The facts of a path (`CplSem.lean`) under any semantics of `BLAKE2S`.
-/

module

public import LeanVM.Guest.B2C.CplSem
public import LeanVM.Guest.B2C.CplJustB

/-!
# The facts of a path under any `BLAKE2S` semantics

`CplSem.lean`'s `locC_holds` and `fileB_ok` with `S : BlakeSem` a parameter (`locCB_holds`,
`fileBB_ok`): on a frame holding what the honest memory puts there, each atom of a path whose
events hold under `S` holds on its cells under `S`, so every book the walk files holds.
-/

namespace LeanVM.Guest.B2C

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Exec
open LeanVM.Guest.Check LeanVM.Guest.Memory

@[expose] public section

variable {S : BlakeSem}

/-! ## The atoms of a path hold -/

section Frame

variable {κ : ℕ} {L : MemImage κ} {j fp : ℕ} {σ : Val} {es : List Ev} {vs : List V}
  {kfps : List ℕ} {hdr : E × E} {loc : CLoc}

/-- **An atom of the path holds on its cells.** -/
theorem locCB_holds (hF : FrameHolds L j fp σ es vs kfps hdr) (hl : LocOk j loc)
    (hev : ∀ e ∈ es, e.HoldsB S L.read σ) {a : Core.Atom} (ha : Ev.atom a ∈ es)
    (hin : inFrame (fsN j) (cellsC (locC loc a)) = true) : LHoldsB S L fp (locC loc a) := by
  have hh := hev _ ha
  have V : ∀ v ∈ Ev.uses (.atom a), loc.cell v ∈ cellsC (locC loc a) →
      rdc L fp (loc.cell v) = some (σ v) := fun v hv hc ↦
    val_cell hF hl (uses_named ha hv) (inFrame_mem hin _ hc).1 (inFrame_mem hin _ hc).2
  cases a with
  | const d x =>
    exact (V d (by simp [Ev.uses, atomUses]) (by simp [locC, cellsC])).trans (by rw [hh])
  | add d x y =>
    refine ⟨σ x, σ y, V x (by simp [Ev.uses, atomUses]) (by simp [locC, cellsC]),
      V y (by simp [Ev.uses, atomUses]) (by simp [locC, cellsC]), ?_⟩
    rw [V d (by simp [Ev.uses, atomUses]) (by simp [locC, cellsC])]
    exact congrArg some hh
  | mul d x y =>
    refine ⟨σ x, σ y, V x (by simp [Ev.uses, atomUses]) (by simp [locC, cellsC]),
      V y (by simp [Ev.uses, atomUses]) (by simp [locC, cellsC]), ?_⟩
    rw [V d (by simp [Ev.uses, atomUses]) (by simp [locC, cellsC])]
    exact congrArg some hh
  | copy d x =>
    refine ⟨σ x, ?_, V x (by simp [Ev.uses, atomUses]) (by simp [locC, cellsC])⟩
    rw [V d (by simp [Ev.uses, atomUses]) (by simp [locC, cellsC])]
    exact congrArg some hh
  | load d p off =>
    obtain ⟨hK, hr⟩ := hh
    exact ⟨σ p, σ d, V p (by simp [Ev.uses, atomUses]) (by simp [locC, cellsC]), hK,
      V d (by simp [Ev.uses, atomUses]) (by simp [locC, cellsC]), hr⟩
  | assertEq x y =>
    refine ⟨σ x, V x (by simp [Ev.uses, atomUses]) (by simp [locC, cellsC]), ?_⟩
    rw [V y (by simp [Ev.uses, atomUses]) (by simp [locC, cellsC])]
    exact congrArg some (eq_of_add_eq_zero hh).symm
  | assertNe x i p =>
    obtain ⟨h1, h2⟩ := hh
    refine ⟨σ x, σ i, V x (by simp [Ev.uses, atomUses]) (by simp [locC, cellsC]),
      V i (by simp [Ev.uses, atomUses]) (by simp [locC, cellsC]), ?_, h1 ▸ h2⟩
    rw [V p (by simp [Ev.uses, atomUses]) (by simp [locC, cellsC]), h1]
  | rangeCheck x y t1 t2 k =>
    obtain ⟨⟨hKx, h1⟩, hk, ⟨hKy, h2⟩⟩ := hh
    have T : ∀ t ∈ [t1, t2], loc.cell t ∈ cellsC (locC loc (.rangeCheck x y t1 t2 k)) →
        rdc L fp (loc.cell t) = some (σ t) := fun t ht hc ↦
      tmp_cell hF hl ha (by simpa [Ev.tmps, atomTmps] using ht) (inFrame_mem hin _ hc).1
        (inFrame_mem hin _ hc).2
    refine ⟨σ x, σ y, σ t1, σ t2, V x (by simp [Ev.uses, atomUses]) (by simp [locC, cellsC]), hKx,
      V y (by simp [Ev.uses, atomUses]) (by simp [locC, cellsC]), hKy,
      T t1 (by simp) (by simp [locC, cellsC]), T t2 (by simp) (by simp [locC, cellsC]), h1, h2, ?_⟩
    rw [V k (by simp [Ev.uses, atomUses]) (by simp [locC, cellsC]), hk]
  | assertInK x y =>
    obtain ⟨hx, hy⟩ := hh
    exact ⟨σ x, σ y, V x (by simp [Ev.uses, atomUses]) (by simp [locC, cellsC]), hx,
      V y (by simp [Ev.uses, atomUses]) (by simp [locC, cellsC]), hy⟩
  | blake2s m0 m1 m2 m3 cv0 cv1 o0 o1 md =>
    exact ⟨_, _, _, _, _, _, _, _, _,
      V m0 (by simp [Ev.uses, atomUses]) (by simp [locC, cellsC]),
      V m1 (by simp [Ev.uses, atomUses]) (by simp [locC, cellsC]),
      V m2 (by simp [Ev.uses, atomUses]) (by simp [locC, cellsC]),
      V m3 (by simp [Ev.uses, atomUses]) (by simp [locC, cellsC]),
      V cv0 (by simp [Ev.uses, atomUses]) (by simp [locC, cellsC]),
      V cv1 (by simp [Ev.uses, atomUses]) (by simp [locC, cellsC]),
      V o0 (by simp [Ev.uses, atomUses]) (by simp [locC, cellsC]),
      V o1 (by simp [Ev.uses, atomUses]) (by simp [locC, cellsC]),
      V md (by simp [Ev.uses, atomUses]) (by simp [locC, cellsC]), hh⟩
  | frameAddr p run =>
    cases run with
    | nil => trivial
    | cons r rs =>
      have hr := inFrame_mem hin (loc.cell r) (by simp [locC, cellsC])
      have hp : (p, r) ∈ addrs es := List.mem_filterMap.mpr ⟨_, ha, rfl⟩
      refine ⟨loc.cell r, rs.map loc.cell, rfl, ?_⟩
      rw [V p (by simp [Ev.uses, atomUses]) (by simp [locC, cellsC]), hF.addr _ hp,
        loc_cell hl hr.1]
  | hint h => trivial

/-- **Every book the walk files from the path's atoms holds.** -/
theorem fileBB_ok (hF : FrameHolds L j fp σ es vs kfps hdr) (hl : LocOk j loc)
    (hev : ∀ e ∈ es, e.HoldsB S L.read σ) :
    ∀ (ss : List Stmt) (B : BookC), BookOkB S L fp B → (∀ a, Stmt.atom a ∈ ss → Ev.atom a ∈ es) →
      BookOkB S L fp (fileB loc (fsN j) ss B)
  | [], B, hB, _ => hB
  | .atom a :: ss, B, hB, ha => by
    simp only [fileB, LAtom.seq_eq]
    cases hin : inFrame (fsN j) (cellsC (locC loc a))
    · simp only [Bool.cond_false]
      exact fileBB_ok hF hl hev ss B hB fun b hb ↦ ha b (List.mem_cons_of_mem _ hb)
    · simp only [Bool.cond_true, Trie.seq_eq]
      exact fileBB_ok hF hl hev ss _
        (hB.file (locCB_holds hF hl hev (ha a List.mem_cons_self) hin))
        fun b hb ↦ ha b (List.mem_cons_of_mem _ hb)
  | .ite .. :: ss, B, hB, ha => fileBB_ok hF hl hev ss B hB fun b hb ↦ ha b (List.mem_cons_of_mem _ hb)
  | .match_ .. :: ss, B, hB, ha => fileBB_ok hF hl hev ss B hB fun b hb ↦ ha b (List.mem_cons_of_mem _ hb)
  | .call .. :: ss, B, hB, ha => fileBB_ok hF hl hev ss B hB fun b hb ↦ ha b (List.mem_cons_of_mem _ hb)
  | .callIf .. :: ss, B, hB, ha => fileBB_ok hF hl hev ss B hB fun b hb ↦ ha b (List.mem_cons_of_mem _ hb)
  | .dispatch .. :: ss, B, hB, ha => fileBB_ok hF hl hev ss B hB fun b hb ↦ ha b (List.mem_cons_of_mem _ hb)
  | .ret _ :: ss, B, hB, ha => fileBB_ok hF hl hev ss B hB fun b hb ↦ ha b (List.mem_cons_of_mem _ hb)

end Frame

end
end LeanVM.Guest.B2C
