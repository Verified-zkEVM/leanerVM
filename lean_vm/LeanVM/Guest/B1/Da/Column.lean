/-
  LeanVM.Guest.B1.Da.Column

  `da_verify_column` and its blob loop `__loop21`: what a run of a column establishes
  (G:3976-3990).
-/

module

public import LeanVM.Guest.B1.Da.ColumnDefs
public import LeanVM.Guest.B1.Da.VectorHolds

/-!
# `da_verify_column` (G:3976-3990)

`da_verify_column(xb, n_blob_g, rowbase, zs, top_leaves, cell_factors, offsets)` (`core27`), at
`xb = g^h`: the column's weights `lvals`, `da_expand__L7_L8` from the top leaf `h` with the cell
factors and the column's shifts `offsets·g^(8h)`, are the dual codeword's entries `256 h + e`
(`cellLeaf_eq`); then `__loop21` (`core374`) over the blobs `i < r`: a `da_verify_cell` run on
`lvals`, its sum added to the blob's running sum (word `512 + h` to `513 + h` of the region at
`rowbase[i]`), its digest the blob tree's leaf `h` (words `2h`, `2h + 1`). `colOk` and `l21Ok`
check the bodies (kernel evaluation in `ColumnChk`); `col_step` is a column's run.
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Main

@[expose] public section

variable {rd : Reader}

/-! ## The blob loop -/

theorem l21_step (hok : l21Ok (coreProgram.getD 374 default) = true)
    (hidx : coreProgram.indexOf? "__loop21" = some 374) {x : E} {ps : List E}
    (h : coreProgram.Rel rd "__loop21" (x :: ps) []) :
    (∀ N lv rb xb xb2, ps = [N, lv, rb, xb, xb2] → CellStepC rd lv rb xb xb2 x) ∧
      (x * gen + ps.headD 0 ≠ 0 → coreProgram.Rel rd "__loop21" (x * gen :: ps) []) := by
  simp only [l21Ok, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hshape, hlen⟩, hcall⟩, hm9⟩, hl10⟩, hm11⟩, hl12⟩, ha13⟩, hl13⟩, hm14⟩, hl6⟩,
    hl7⟩ := hok
  obtain ⟨σ, hx, hps, hall, hnext⟩ :=
    loop_stepF (find_of_idx hidx (by rw [coreProgram_length]; omega)) hshape h
  refine ⟨fun N lv rb xb xb2 hN ↦ ?_, hnext⟩
  have hat := atoms_of_flat hall
  have hpar : (coreProgram.getD 374 default).params = [V.n 0, V.n 1, V.n 2, V.n 3, V.n 4, V.n 5] := by
    rw [loop_params hshape hlen]; rfl
  rw [hpar, hN] at hps
  simp only [List.tail_cons, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hps
  obtain ⟨-, h2, h3, h4, h5⟩ := hps
  have c := call_of_flat hall hcall
  simp only [List.map_cons, List.map_nil] at c
  rw [h2] at c
  have l10 := load_sound hl10 hat
  rw [isMul_sound hm9 hat, h3, hx] at l10
  have p11 : σ (.n 11) = σ (.n 10) * xb := by rw [isMul_sound hm11 hat, h4]
  have l12 := load_sound hl12 hat
  have l13 := load_sound hl13 hat
  rw [p11] at l12 l13
  rw [add_sound ha13 hat] at l13
  have p14 : σ (.n 14) = σ (.n 10) * xb2 := by rw [isMul_sound hm14 hat, h5]
  have l6 := load_sound hl6 hat
  have l7 := load_sound hl7 hat
  rw [p14] at l6 l7
  exact ⟨_, _, _, _, _, c, l10, l12, l13, l6, l7⟩

/-! ## A column -/

/-- A frame run's word, read. -/
theorem runAt_load {p : E} {n : ℕ} {f : ℕ → E} (hr : RunAt rd p n f) {k : ℕ} (hk : k < n) {v : E}
    (h : LoadHolds rd p k v) : v = f k :=
  hr.2 k hk v h.2

/-- **A column's run** at `g^h`, with `da_vector`'s results for `z`: for every blob `i < r`, some
`256` symbols whose digest is leaf `h` of the region at `rowbase[i]` and whose inner product with
the dual codeword's entries `256 h + e` steps the region's running sum from word `512 + h` to
`513 + h`. -/
theorem col_step (hcol : colOk = true) (h21 : l21Ok (coreProgram.getD 374 default) = true)
    (hidx : coreProgram.indexOf? "__loop21" = some 374) {z zs tl cf off rb : E} {h r : ℕ}
    (hh : h < 128) (hr : r < ordG) (hvec : MeaningDaVector rd [z] [zs, tl, cf, off])
    (hrel : coreProgram.Rel rd "da_verify_column" [gen ^ h, gen ^ r, rb, zs, tl, cf, off] []) :
    ∀ i < r, ∃ (sy : List K) (base a : E), sy.length = 256 ∧ LoadHolds rd (rb * gen ^ i) 0 base ∧
      LoadHolds rd base (2 * h) (digestHalves (keccak256 (sy.flatMap K.toBytes))).1 ∧
      LoadHolds rd base (2 * h + 1) (digestHalves (keccak256 (sy.flatMap K.toBytes))).2 ∧
      LoadHolds rd base (h + 512) a ∧
      LoadHolds rd base (h + 513)
        (a + ∑ e ∈ Finset.range 256, dualAt z (256 * h + e) * ofK (sy.getD e 0)) := by
  obtain ⟨σ, hpar, hb⟩ := (rel_iff_sem find_da_verify_column _ _).mp hrel
  unfold colOk at hcol
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hcol
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hparams, hbody⟩, hflat⟩, hm7⟩, hl8⟩, hm12⟩, hce⟩, hm14⟩, hg⟩ := hcol
  rw [hparams] at hpar
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.cons_append, List.cons.injEq, and_true] at hpar
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := hpar
  rw [stmtsEqb_sound hbody, holdsList_append] at hb
  obtain ⟨hall, -⟩ := holdsList_flat colP hflat _ _ hb
  have hat := atoms_of_flat hall
  obtain ⟨hzs, htl, hcf, hoff⟩ := hvec
  -- the top leaf
  have l8 := load_sound hl8 hat
  rw [isMul_sound hm7 hat, h4, h0, loadHolds_mul_gen_pow, add_zero] at l8
  have e8 := runAt_load htl hh l8
  -- the weights
  have ce := call_of_flat hall hce
  simp only [List.map_cons, List.map_nil] at ce
  have hE := (da_expand_holds).2 rd _ _ ce
  simp only [MeaningDaExpand] at hE
  obtain ⟨F, Z, S, hF, hZ, hS, hrun⟩ := hE
  have p12 : σ (.n 12) = off * (gen ^ h) ^ 8 := by rw [monoIs_sound hm12 hat, h6, h0]
  have hlv : ∀ e < 256, ∀ w, rd ((σ (.n 13)).limb 0 * addressOfIndex e) = some w →
      w = dualAt z (256 * h + e) := by
    intro e he w hw
    rw [hrun.2 e (by norm_num; omega) w hw, e8, ← cellLeaf_eq z he]
    refine expandLeaf_congr (by norm_num; omega) (fun n n1 n2 ↦ ?_) (fun d hd ↦ ?_) (fun d hd ↦ ?_)
    · rw [h5] at hF
      exact loadHolds_unique (hF n n1 n2) (hcf n n1 (by norm_num at n2 ⊢; omega))
    · rw [h3] at hZ
      exact loadHolds_unique (hZ d hd) (hzs _ (by omega))
    · have := hS d hd
      rw [p12, ← pow_mul, loadHolds_mul_gen_pow] at this
      exact loadHolds_unique this (by
        rw [show h * 8 + (7 - d) = 8 * h + (7 - d) by ring]; exact hoff h hh (7 - d) (by omega))
  -- the blobs
  have hgs := guardK_sound hg hall
  simp only [List.map_cons, List.map_nil] at hgs
  rw [h1, h2, h0] at hgs
  have L := loop_sound (f := "__loop21") (ps := [gen ^ r, σ (.n 13), rb, gen ^ h, σ (.n 14)])
    (B := fun x ↦ CellStepC rd (σ (.n 13)) rb (gen ^ h) (σ (.n 14)) x) hr rfl
    (fun x hx ↦ by
      obtain ⟨k1, k2⟩ := l21_step h21 hidx hx
      exact ⟨k1 _ _ _ _ _ rfl, k2⟩) hgs
  have p14 : σ (.n 14) = (gen ^ h) ^ 2 := by rw [isMul_sound hm14 hat, h0, sq]
  intro i hi
  obtain ⟨d0, d1, s, base, a, hc, hbase, ha, has, hd0, hd1⟩ := L i hi
  obtain ⟨sy, ws, hsl, hrd, hwl, hrets⟩ := da_verify_cell_holds rd _ _ hc
  simp only [digestCells, List.cons_append, List.nil_append, List.cons.injEq, and_true] at hrets
  obtain ⟨e0, e1, es⟩ := hrets
  rw [p14, shift2] at hd0 hd1
  rw [loadHolds_mul_gen_pow] at ha has
  refine ⟨sy, base, a, hsl, hbase, ?_, ?_, ha, ?_⟩
  · rw [← e0]; simpa using hd0
  · rw [← e1]; simpa [Nat.mul_comm] using hd1
  · rw [es] at has
    convert has using 2
    rw [← list_sum_range]
    unfold LeanDa.cellSymbols
    have hwl' : ws.length = 256 := hwl
    refine congrArg _ (List.map_congr_left fun e he ↦ ?_)
    have he' := List.mem_range.mp he
    rw [List.getD_eq_getElem ws 0 (show e < ws.length by omega), hlv e he' _ (hrd e (by omega)).2]

end
end LeanVM.Guest.B1.Da
