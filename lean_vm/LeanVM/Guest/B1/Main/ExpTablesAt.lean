/-
  LeanVM.Guest.B1.Main.ExpTablesAt

  `exponent_tables` placed at a frame pointer: its two tables after its frame, returned.
-/

module

public import LeanVM.Guest.B1.Bits.Tables
public import LeanVM.Guest.B1.Da.AtBase

/-!
# `exponent_tables`, placed

`exponent_tables` allocates two `HeapBuf(34)`s from `b = fp + fs "exponent_tables"` and writes the
tables there (`etTabs`). `et_at`: on a memory holding them, it holds at `fp` by its frame and its
two buffers, returning `g^b` and `g^(b + 34)` and claiming both buffers.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen eOfNat)
open LeanVM.Guest.B1.Da (SlOk slEvs_holds limb0_gen_pow_mul)

@[expose] public section

/-- `exponent_tables`' atoms. -/
def etAs : List Atom :=
  [.hint (.alloc (.n 0) 34)] ++ (List.range 34).flatMap (fun j =>
    [.const (.n (1 + j)) (word (2 ^ j) 0 0), .load (.n (1 + j)) (.n 0) j]) ++
  [.hint (.alloc (.n 35) 34)] ++ (List.range 34).flatMap (fun j =>
    [.const (.n (36 + j)) (word (gSquaresBits.getD j 0) 0 0), .load (.n (36 + j)) (.n 35) j]) ++
  [.copy (.n 70) (.n 0), .copy (.n 71) (.n 35)]

set_option maxRecDepth 100000 in
theorem et_split : Fn.body Data.core2 = etAs.map Stmt.atom ++ [.ret [.n 70, .n 71]] := by
  rw [core2_body]; exact stmtsEqb_sound (by decide +kernel)

theorem et_straight : (etAs.map Stmt.atom).all Main.Stmt.straight = true := by
  simp [Main.Stmt.straight]

/-- The two tables' words. -/
def etTabs : List (List E) :=
  [(List.range 34).map (fun j => eOfNat (2 ^ j)), (List.range 34).map (fun j => gen ^ 2 ^ j)]

/-- The tables' first word at `fp`. -/
abbrev etB (fs : String → ℕ) (fp : ℕ) : ℕ := fp + fs "exponent_tables"

theorem expTables_of_reads {rd : Reader} {b : ℕ}
    (h1 : ReadsAt rd (gen ^ b) ((List.range 34).map (fun j => eOfNat (2 ^ j))))
    (h2 : ReadsAt rd (gen ^ (b + 34)) ((List.range 34).map (fun j => gen ^ 2 ^ j))) :
    ExpTables rd (gen ^ b) (gen ^ (b + 34)) := fun j hj => by
  have a := h1 j (by simpa using hj)
  have b := h2 j (by simpa using hj)
  simp only [List.getElem_map, List.getElem_range] at a b
  exact ⟨a, b⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- **`exponent_tables` at `fp`**, on a memory holding its two tables. -/
theorem et_at (fs : String → ℕ) (cert : String → V → ℕ) {rd : Reader} {fp : ℕ} {R : ℕ → Prop}
    (hm : ExpTables rd (gen ^ etB fs fp) (gen ^ (etB fs fp + 34))) :
    RelAtIn coreProgram fs cert rd R (fun i => etB fs fp ≤ i ∧ i < etB fs fp + 68) fp
      (fs "exponent_tables" + 68) "exponent_tables" [] [gen ^ etB fs fp, gen ^ (etB fs fp + 34)] := by
  have hrel := (exponent_tables_holds rd [] [gen ^ etB fs fp, gen ^ (etB fs fp + 34)]).mpr hm
  obtain ⟨σ, hp, hh⟩ := (rel_iff_sem find_exponent_tables _ _).mp hrel
  rw [et_split, Digest.holdsList_atoms_ret] at hh
  obtain ⟨hat, hr⟩ := hh
  have hc : ∀ {d s : V}, Atom.copy d s ∈ etAs → σ d = σ s := fun hm => hat _ hm
  have h0 : σ (.n 0) = gen ^ etB fs fp := by
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hr
    rw [← hc (d := .n 70) (s := .n 0) (by simp [etAs]), hr.1]
  have h35 : σ (.n 35) = gen ^ (etB fs fp + 34) := by
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hr
    rw [← hc (d := .n 71) (s := .n 35) (by simp [etAs]), hr.2]
  have hw := Main.walk_straight σ [.n 70, .n 71] (etAs.map Stmt.atom) et_straight
  rw [← et_split] at hw
  obtain ⟨hpd, hpa, hpad, hpc⟩ := Main.straight_parts σ _ et_straight
  have hal : allocs σ ((etAs.map Stmt.atom).flatMap (Main.slEvs σ)) = [34, 34] := by
    rw [hpa, show (etAs.map Stmt.atom).filterMap Main.Stmt.allocSz =
      [(.n 0, .inl 34), (.n 35, .inl 34)] by decide +kernel]
    rfl
  have hown : ∀ i, etB fs fp ≤ i → i < etB fs fp + 68 → ownData cert fp (fp + fs "exponent_tables")
      "exponent_tables" [34, 34] ((etAs.map Stmt.atom).flatMap (Main.slEvs σ)) i := by
    intro i h1 h2
    refine Or.inl ?_
    by_cases hi : i < etB fs fp + 34
    · exact ⟨(34, etB fs fp), by simp [bases], h1, hi⟩
    · exact ⟨(34, etB fs fp + 34), by simp [bases], by omega, by omega⟩
  have h := relAtIn_of_walk (P := coreProgram) (fs := fs) (cert := cert) (σ := σ) (rd := rd)
    (R := R) (D := fun i => etB fs fp ≤ i ∧ i < etB fs fp + 68) (Dk := fun _ => False) (N := 0)
    (fp := fp) (args := []) (rets := [gen ^ etB fs fp, gen ^ (etB fs fp + 34)])
    coreProgram_wf find_exponent_tables (Or.inl (by
      rw [Program.loop_of_find? find_exponent_tables]; decide +kernel)) hp hw hr
    (slEvs_holds fun s hs => by
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hs
      exact hat a ha)
    (by
      rw [hal, hpd, show (etAs.map Stmt.atom).filterMap Main.Stmt.allocSz =
        [(.n 0, .inl 34), (.n 35, .inl 34)] by decide +kernel]
      simp only [List.map_cons, List.map_nil, bases, h0, h35, gen_pow_eq_ofK, Nat.add_assoc])
    (fun q hq => by
      rw [hpad, show (etAs.map Stmt.atom).filterMap Main.Stmt.addrS = [] by decide +kernel] at hq
      simp at hq)
    (by
      rw [hpc, show (etAs.map Stmt.atom).filterMap Main.Stmt.callS = [] by decide +kernel]
      exact ⟨rfl, fun _ h => h⟩)
    (fun A hA => by
      rw [B1.loadAddrs_straight σ _ et_straight, show (etAs.map Stmt.atom).filterMap B1.Stmt.loadS =
        (List.range 34).map (fun j => (V.n 0, j)) ++ (List.range 34).map (fun j => (V.n 35, j)) by
          decide +kernel] at hA
      simp only [List.map_append, List.map_map, List.mem_append, List.mem_map, List.mem_range,
        Function.comp] at hA
      rcases hA with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
      · refine ⟨etB fs fp + j, by rw [h0, limb0_gen_pow_mul], Or.inl ?_⟩
        rw [hal]; exact hown _ (by omega) (by omega)
      · refine ⟨etB fs fp + 34 + j, by rw [h35, limb0_gen_pow_mul], Or.inl ?_⟩
        rw [hal]; exact hown _ (by omega) (by omega))
    (fun i hi => Or.inl (by rw [hal]; exact hown i hi.1 hi.2))
  rw [hal] at h
  simpa using h

end
end LeanVM.Guest.B1.Main
