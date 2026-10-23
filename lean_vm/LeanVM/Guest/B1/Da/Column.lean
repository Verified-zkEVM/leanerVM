/-
  LeanVM.Guest.B1.Da.Column

  What a run of `da_verify_column` establishes.
-/

module

public import LeanVM.Guest.B1.Da.ColumnChk

/-!
# A column

`col_step`: a run of `da_verify_column__L{store}` at `xb` with `n_blob_g = g^r` and
`gap_g = g^gp` gives the column's weights (`da_vector_cell`), a cell per row (`row_step`,
`RowStepC`: the cell's digest at node `i`, its dot product added to the row's running sum, the
digest into the row's prefix when `store`), the padding cells (`gap_step`, `GapStepC`), and the
root of the `2^L` nodes (`da_levels`, dispatched on `g_log_pad`) at `coltree·xb²`.
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Main

@[expose] public section

variable {rd : Reader}

/-- **Row `x`'s cell of a column**: a `da_verify_cell` run on the weights at `lv`, its sum added
to the row's running sum (through `rowbase[x]`, at `xb`), its digest at node `x` and, when
`store`, in the row's prefix (through `pb[x]`, at `xb²`). -/
def RowStepC (rd : Reader) (lv rowbase xb node pb : E) (store : Bool) (x : E) : Prop :=
  ∃ d0 d1 s : E, coreProgram.Rel rd "da_verify_cell" [lv] [d0, d1, s] ∧
    LoadHolds rd (rowbase * x) 0 (memAt rd (rowbase * x) 0) ∧
    LoadHolds rd (memAt rd (rowbase * x) 0 * xb) 1
      (memAt rd (memAt rd (rowbase * x) 0 * xb) 0 + s) ∧
    LoadHolds rd (node * x ^ 2) 0 d0 ∧ LoadHolds rd (node * x ^ 2) 1 d1 ∧
    (store = true → LoadHolds rd (memAt rd (pb * x) 0 * xb ^ 2) 0 d0 ∧
      LoadHolds rd (memAt rd (pb * x) 0 * xb ^ 2) 1 d1)

theorem row_step {f : String} {j : ℕ} {store : Bool} (hj : j < coreProgram.length)
    (hok : (rowOk (coreProgram.getD j default) f store &&
      decide (coreProgram.indexOf? f = some j)) = true) {x : E} {ps : List E}
    (h : coreProgram.Rel rd f (x :: ps) []) :
    (∀ N lv rowbase xb node pb, ps = [N, lv, rowbase, xb, node, pb] →
      RowStepC rd lv rowbase xb node pb store x) ∧
      (x * gen + ps.headD 0 ≠ 0 → coreProgram.Rel rd f (x * gen :: ps) []) := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hok, hidx⟩ := hok
  have hf := find_of_idx hidx hj
  unfold rowOk at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true'] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hshape, hlen⟩, hcall⟩, hm10⟩, hl11⟩, hm12⟩, hl13⟩, ha14⟩, hl14⟩, hm15⟩,
    hm16⟩, hl7⟩, hl8⟩, hst⟩ := hok
  obtain ⟨σ, hx, hps, hall, hnext⟩ := loop_stepF hf hshape h
  refine ⟨fun N lv rowbase xb node pb hN => ?_, hnext⟩
  have hat := atoms_of_flat hall
  have hpar : (coreProgram.getD j default).params =
      [V.n 0, V.n 1, V.n 2, V.n 3, V.n 4, V.n 5, V.n 6] := by
    have hs := hshape
    simp only [loopShapeF, Bool.and_eq_true, decide_eq_true_eq] at hs
    rw [hs.1.2, hlen]; rfl
  rw [hpar, hN] at hps
  simp only [List.tail_cons, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hps
  obtain ⟨-, h2, h3, h4, h5, h6⟩ := hps
  have c := call_of_flat hall hcall
  simp only [List.map_cons, List.map_nil] at c
  rw [h2] at c
  have p10 : σ (.n 10) = rowbase * x := by rw [isMul_sound hm10 hat, h3, hx]
  have l11 := load_sound hl11 hat
  rw [p10] at l11
  have e11 := memAt_of_load l11
  have p12 : σ (.n 12) = memAt rd (rowbase * x) 0 * xb := by rw [isMul_sound hm12 hat, e11, h4]
  have l13 := load_sound hl13 hat
  rw [p12] at l13
  have l14 := load_sound hl14 hat
  rw [p12, add_sound ha14 hat, ← memAt_of_load l13] at l14
  have p16 : σ (.n 16) = node * x ^ 2 := by rw [isMul_sound hm16 hat, isMul_sound hm15 hat, h5, hx, sq]
  have l7 := load_sound hl7 hat
  have l8 := load_sound hl8 hat
  rw [p16] at l7 l8
  refine ⟨σ (.n 7), σ (.n 8), σ (.n 9), c, by rw [e11]; exact l11, l14, l7, l8, fun hs => ?_⟩
  rcases hst with hs' | hst
  · rw [hs] at hs'; exact absurd hs' (by decide)
  obtain ⟨⟨⟨⟨⟨hm17, hl18⟩, hm19⟩, hm20⟩, hl7'⟩, hl8'⟩ := hst
  have l18 := load_sound hl18 hat
  rw [isMul_sound hm17 hat, h6, hx] at l18
  have p20 : σ (.n 20) = memAt rd (pb * x) 0 * xb ^ 2 := by
    rw [isMul_sound hm20 hat, isMul_sound hm19 hat, memAt_of_load l18, h4, sq]
  have l7' := load_sound hl7' hat
  have l8' := load_sound hl8' hat
  rw [p20] at l7' l8'
  exact ⟨l7', l8'⟩

/-- **A padding node**: the padding cell's two cells at node `n_blob + x`. -/
def GapStepC (rd : Reader) (node nb : E) (x : E) : Prop :=
  LoadHolds rd (node * nb ^ 2 * x ^ 2) 0 (digestScalars daPadCellDigest).1 ∧
    LoadHolds rd (node * nb ^ 2 * x ^ 2) 1 (digestScalars daPadCellDigest).2

theorem gap_step {f : String} {j : ℕ} (hj : j < coreProgram.length)
    (hok : (gapOk (coreProgram.getD j default) f padCellLo.1 padCellLo.2.1 padCellLo.2.2.1
      padCellLo.2.2.2 && decide (coreProgram.indexOf? f = some j)) = true) {x : E} {ps : List E}
    (h : coreProgram.Rel rd f (x :: ps) []) :
    (∀ N node nb, ps = [N, node, nb] → GapStepC rd node nb x) ∧
      (x * gen + ps.headD 0 ≠ 0 → coreProgram.Rel rd f (x * gen :: ps) []) := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hok, hidx⟩ := hok
  have hf := find_of_idx hidx hj
  unfold gapOk at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hshape, hlen⟩, hm4⟩, hm5⟩, hm6⟩, hm7⟩, hc8⟩, hl8⟩, hc9⟩, hl9⟩ := hok
  obtain ⟨σ, hx, hps, hall, hnext⟩ := loop_stepF hf hshape h
  refine ⟨fun N node nb hN => ?_, hnext⟩
  have hat := atoms_of_flat hall
  have hpar : (coreProgram.getD j default).params = [V.n 0, V.n 1, V.n 2, V.n 3] := by
    have hs := hshape
    simp only [loopShapeF, Bool.and_eq_true, decide_eq_true_eq] at hs
    rw [hs.1.2, hlen]; rfl
  rw [hpar, hN] at hps
  simp only [List.tail_cons, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hps
  obtain ⟨-, h2, h3⟩ := hps
  have p7 : σ (.n 7) = node * nb ^ 2 * x ^ 2 := by
    rw [isMul_sound hm7 hat, isMul_sound hm5 hat, isMul_sound hm4 hat, isMul_sound hm6 hat, h2, h3,
      hx, sq, sq]
  have l8 := load_sound hl8 hat
  have l9 := load_sound hl9 hat
  rw [p7, const_sound hc8 hat] at l8
  rw [p7, const_sound hc9 hat] at l9
  have e := daPadCell_cells
  unfold GapStepC
  rw [← e]
  exact ⟨l8, l9⟩

/-- **A column's run.** -/
theorem col_step {fname rl gl : String} {jc jr jg : ℕ} {store : Bool}
    (hjc : jc < coreProgram.length) (hjr : jr < coreProgram.length) (hjg : jg < coreProgram.length)
    (hcol : (colOk (coreProgram.getD jc default) rl gl &&
      decide (coreProgram.indexOf? fname = some jc)) = true)
    (hrow : (rowOk (coreProgram.getD jr default) rl store &&
      decide (coreProgram.indexOf? rl = some jr)) = true)
    (hgap : (gapOk (coreProgram.getD jg default) gl padCellLo.1 padCellLo.2.1 padCellLo.2.2.1
      padCellLo.2.2.2 && decide (coreProgram.indexOf? gl = some jg)) = true)
    {xb npad glp pb coltree rowbase cd : E} {r gp : ℕ} (hr : r < ordG) (hg : gp < ordG)
    (h : coreProgram.Rel rd fname [xb, gen ^ r, npad, gen ^ gp, glp, pb, coltree, rowbase, cd] []) :
    ∃ lv node c0 c1 : E, coreProgram.Rel rd "da_vector_cell" [cd * xb ^ 2] [lv] ∧
      (∀ i < r, RowStepC rd lv rowbase xb node pb store (gen ^ i)) ∧
      (∀ d < gp, GapStepC rd node (gen ^ r) (gen ^ d)) ∧
      (∃ k < 11, glp = ofK (Parameters.gpow k) ∧
        coreProgram.Rel rd (daLevelsName k) [node] [c0, c1]) ∧
      LoadHolds rd (coltree * xb ^ 2) 0 c0 ∧ LoadHolds rd (coltree * xb ^ 2) 1 c1 := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hcol
  obtain ⟨hok, hidx⟩ := hcol
  obtain ⟨σ, hpar, hb⟩ := (rel_iff_sem (find_of_idx hidx hjc) _ _).mp h
  unfold colOk at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hparams, hok⟩ := hok
  split at hok
  · rename_i P vs hsr
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨rfl, hflat⟩, hm9⟩, hm10⟩, hvc⟩, hg16⟩, hg19⟩, hdisp⟩, hm23⟩, hm24⟩, hl21⟩,
      hl22⟩ := hok
    rw [splitRet_eq hsr, holdsList_append] at hb
    obtain ⟨hall, -⟩ := holdsList_flat P hflat _ _ hb
    have hat := atoms_of_flat hall
    rw [hparams, show (List.range 9).map V.n = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7,
      .n 8] from rfl] at hpar
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hpar
    obtain ⟨h0, h1, -, h3, h4, h5, h6, h7, h8⟩ := hpar
    have c := call_of_flat hall hvc
    simp only [List.map_cons, List.map_nil] at c
    rw [isMul_sound hm10 hat, isMul_sound hm9 hat, h0, h8, ← sq] at c
    have L1 : ∀ i < r, RowStepC rd (σ (.n 11)) rowbase xb (σ (.n 14)) pb store (gen ^ i) :=
      loop_sound (f := rl) (ps := [gen ^ r, σ (.n 11), rowbase, xb, σ (.n 14), pb]) hr rfl
        (fun y hy => by
          obtain ⟨k1, k2⟩ := row_step hjr hrow hy
          exact ⟨k1 _ _ _ _ _ _ rfl, k2⟩)
        (fun hne => by
          have := guard_sound hg16 hall (by rw [h1]; exact hne)
          simpa [h1, h7, h0, h5] using this)
    have L2 : ∀ d < gp, GapStepC rd (σ (.n 14)) (gen ^ r) (gen ^ d) :=
      loop_sound (f := gl) (ps := [gen ^ gp, σ (.n 14), gen ^ r]) hg rfl
        (fun y hy => by
          obtain ⟨k1, k2⟩ := gap_step hjg hgap hy
          exact ⟨k1 _ _ _ rfl, k2⟩)
        (fun hne => by
          have := guard_sound hg19 hall (by rw [h3]; exact hne)
          simpa [h3, h1] using this)
    obtain ⟨k, hk, hk4, hrel⟩ := dispatch_of_flat hall hdisp
    simp only [dlNames, List.length_map, List.length_range] at hk
    have p24 : σ (.n 24) = coltree * xb ^ 2 := by
      rw [isMul_sound hm24 hat, isMul_sound hm23 hat, h6, h0, sq]
    have l21 := load_sound hl21 hat
    have l22 := load_sound hl22 hat
    rw [p24] at l21 l22
    refine ⟨σ (.n 11), σ (.n 14), σ (.n 21), σ (.n 22), c, L1, L2, ⟨k, hk, by rw [← h4, hk4], ?_⟩,
      l21, l22⟩
    simpa [dlNames] using hrel
  · exact absurd hok (by simp)

end
end LeanVM.Guest.B1.Da
