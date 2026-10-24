/-
  LeanVM.Guest.B1.Da.VectorAt

  `da_vector_cell` placed at a frame pointer: its weights in its frame run, their digest's cells
  in its caller's region.
-/

module

public import LeanVM.Guest.B1.Da.AtBase
public import LeanVM.Guest.B1.Da.VectorComplete

/-!
# `da_vector_cell`, placed

`da_vector_cell` is atoms and a return (`vec_split`): no `HeapBuf`, one `frameAddr` of its `256`
weights' run at `cert "da_vector_cell" (.n 1)`, two loads of its argument's digest cells.
`vec_at`: at `fp`, on a memory holding the weights in that run and their digest's cells at the
argument `g^c` (words of the region `R`), it holds by its frame alone, returning the run's address
and claiming the run.
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Fwd

@[expose] public section

/-- `da_vector_cell`'s atoms. -/
noncomputable def vecAs : List Atom := ((splitBody (Fn.body Data.core28)).map (·.1)).getD []

set_option maxRecDepth 100000 in
theorem vec_rets : (splitBody (Fn.body Data.core28)).map (·.2) = some [.n 4462] := by
  decide +kernel

theorem vec_split : Fn.body Data.core28 = vecAs.map Stmt.atom ++ [.ret [.n 4462]] := by
  have h := vec_rets
  cases hs : splitBody (Fn.body Data.core28) with
  | none => rw [hs] at h; exact absurd h (by simp)
  | some p =>
    rw [hs] at h
    obtain ⟨A, vs⟩ := p
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    have : vecAs = A := by simp [vecAs, hs]
    rw [this]
    exact splitBody_eq hs

set_option maxRecDepth 100000 in
theorem vec_na : vecAs.all (fun a => !atomAllocB a) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem vec_addr : vecAs.filterMap atomAddr? = [(.n 4461, .n 1)] := by decide +kernel

set_option maxRecDepth 100000 in
theorem vec_run : vecAs.filterMap atomRun? = [(.n 1, 256)] := by decide +kernel

set_option maxRecDepth 100000 in
theorem vec_load : vecAs.filterMap atomLoad? = [(.n 0, 0), (.n 0, 1)] := by decide +kernel

set_option maxRecDepth 100000 in
theorem vec_copy : vecAs.contains (.copy (.n 4462) (.n 4461)) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem vec_loop : coreProgram.loop "da_vector_cell" = false := by
  rw [Program.loop_of_find? find_da_vector_cell]; decide +kernel

/-- The run of `da_vector_cell`'s weights at `fp`. -/
abbrev vecRun (cert : String → V → ℕ) (fp : ℕ) : ℕ := fp + cert "da_vector_cell" (.n 1)

/-- **`da_vector_cell` at `fp`**: its weights in its run, their digest's cells at `g^c` in `R`. -/
theorem vec_at (fs : String → ℕ) (cert : String → V → ℕ) {rd : Reader} {ws : List E}
    (hwl : ws.length = 256) {c fp : ℕ} {R : ℕ → Prop}
    (hrun : ReadsAt rd (ofK (gpow (vecRun cert fp))) ws)
    (hdig : ReadsAt rd (gen ^ c) (digestCells (keccak256 (ws.flatMap Node.eBytes))))
    (hR : R c ∧ R (c + 1)) :
    RelAtIn coreProgram fs cert rd R
      (fun i => vecRun cert fp ≤ i ∧ i < vecRun cert fp + 256) fp (fs "da_vector_cell")
      "da_vector_cell" [gen ^ c] [ofK (gpow (vecRun cert fp))] := by
  have hrel := da_vector_cell_complete rd (gen ^ c) (ofK (gpow (vecRun cert fp))) ws
    (by simpa [LeanDa.cellSymbols] using hwl) ((isInK_iff _).mpr ⟨_, rfl⟩)
    (fun k hk v hv => by
      have h := (hrun k (by simpa [LeanDa.cellSymbols, hwl] using hk)).2
      rw [hv] at h
      rw [List.getD_eq_getElem _ _ (by simpa [LeanDa.cellSymbols, hwl] using hk)]
      exact Option.some.inj h) hdig
  obtain ⟨σ, hp, hh⟩ := (rel_iff_sem find_da_vector_cell _ _).mp hrel
  rw [vec_split, holdsList_atoms_ret] at hh
  obtain ⟨hat, hr⟩ := hh
  have hcp := hat _ (List.contains_iff_mem.mp vec_copy)
  have h4461 : σ (.n 4461) = ofK (gpow (vecRun cert fp)) := by
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hr
    rw [← hr]; exact hcp.symm
  have h0 : σ (.n 0) = gen ^ c := by
    have : Data.core28.params = [.n 0] := rfl
    rw [this] at hp
    simpa using hp
  have hRun : ∀ k < 256, RunIn cert fp "da_vector_cell" vecAs (vecRun cert fp + k) := fun k hk =>
    ⟨(.n 1, 256), by rw [vec_run]; simp, by dsimp only [vecRun]; omega, by dsimp only [vecRun]; omega⟩
  refine relAtIn_atoms find_da_vector_cell vec_split vec_loop vec_na hp hat hr
    (fun q hq => ?_) (fun q hq => ?_) (fun i hi => ?_)
  · rw [vec_addr, List.mem_singleton] at hq
    subst hq
    exact h4461
  · rw [vec_load] at hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact ⟨c, by rw [h0, limb0_gen_pow_mul]; rfl, Or.inl hR.1⟩
    · exact ⟨c + 1, by rw [h0, limb0_gen_pow_mul], Or.inl hR.2⟩
  · obtain ⟨h1, h2⟩ := hi
    have := hRun (i - vecRun cert fp) (by omega)
    rwa [Nat.add_sub_cancel' h1] at this

end
end LeanVM.Guest.B1.Da
