/-
  LeanVM.Guest.B1.Da.WitnessComplete

  `da_verify` on a LeanDA witness: a witness opening `(root, vd)` (`Da.MatrixWitness.Opens`), and the
  memory an honest run of it leaves, give `da_verify`'s relation returning the cells of `root` and
  `vd` (TRIAGE G #90).

  The witness and `Da.MatrixWitness.Opens` are Benedikt Wagner's LeanDA formalization, as ported here.
-/

module

public import LeanVM.Guest.B1.Da.VerifyComplete
public import LeanVM.Protocol.KeccakHash

/-!
# `da_verify` on a witness

`wSyms w`, `wWs w`: a witness's cells (`LeanDa.listCell` of each codeword) and columns of weights,
padded outside the matrix. `witness_eq`: the witness is `⟨daRows r (wSyms w), daVector (wWs w)⟩`;
`wDot`: its rows are orthogonal to its vector, cell by cell (`accSum … 128 = 0`); `opens_eq`: the
claim it opens is `(daRoot r L (wSyms w), daVd (wWs w))`. `da_verify_complete`: on the honest
memory of a witness opening `(root, vd)`, `da_verify` returns their cells.
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Main

@[expose] public section

/-- A witness's cells: cell `j` of codeword `i`, padded outside the matrix. -/
def wSyms (w : LeanVM.Da.MatrixWitness) (i j : ℕ) : List K :=
  if i < w.rows.length ∧ j < 128 then LeanDa.listCell (w.rows.getD i []) j else List.replicate 256 0

/-- A witness's columns of weights, padded outside the vector. -/
def wWs (w : LeanVM.Da.MatrixWitness) (j : ℕ) : List E :=
  if j < 128 then (w.vector.drop (256 * j)).take 256 else List.replicate 256 0

/-- The padded count's log. -/
def wLog (w : LeanVM.Da.MatrixWitness) : ℕ := LeanDa.logPad w.rows.length

/-- A list of `128` blocks of `256` is the flattening of its blocks. -/
theorem flatMap_blocks {α : Type} (l : List α) (d : α) (hl : l.length = 128 * 256) (f : ℕ → List α)
    (hf : ∀ j, (f j).length = 256) (hfj : ∀ j < 128, f j = (l.drop (256 * j)).take 256) :
    (List.range 128).flatMap f = l := by
  have hlen := length_flatMap_range f 256 128 hf
  refine List.ext_getElem (by rw [hlen, hl]) fun k h1 h2 => ?_
  have hk : k = 256 * (k / 256) + k % 256 := by omega
  rw [← List.getD_eq_getElem _ d h1, ← List.getD_eq_getElem _ d h2]
  conv_lhs => rw [hk]
  rw [flatMap_getD f 256 hf d 128 (k / 256) (k % 256) (by omega) (by omega), hfj _ (by omega)]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop]
  rw [ite_pos' (by omega)]
  congr 2
  omega

theorem wSyms_length (w : LeanVM.Da.MatrixWitness) (hrow : ∀ row ∈ w.rows, row.length = 2 ^ LeanDa.logM)
    (i j : ℕ) : (wSyms w i j).length = 256 := by
  unfold wSyms
  split
  · rename_i h
    have hl := hrow (w.rows.getD i []) (by rw [List.getD_eq_getElem _ _ h.1]; exact List.getElem_mem _)
    rw [LeanDa.listCell, LeanDa.cellSymbols, List.length_take, List.length_drop, hl]
    simp only [LeanDa.logM]
    omega
  · rw [List.length_replicate]

theorem wWs_length (w : LeanVM.Da.MatrixWitness) (hv : w.vector.length = 2 ^ LeanDa.logM) (j : ℕ) :
    (wWs w j).length = 256 := by
  unfold wWs
  split
  · rw [List.length_take, List.length_drop, hv]
    simp only [LeanDa.logM]
    omega
  · rw [List.length_replicate]

/-- **A witness is its cells and columns.** -/
theorem witness_eq {w : LeanVM.Da.MatrixWitness} {root vd : Digest} (hw : w.Opens root vd) :
    w = ⟨daRows w.rows.length (wSyms w), daVector (wWs w)⟩ := by
  obtain ⟨-, -, hrow, -, hv, -, -⟩ := hw
  obtain ⟨rows, vector⟩ := w
  simp only at hrow hv ⊢
  congr 1
  · refine List.ext_getElem (by simp [daRows]) fun i h1 h2 => ?_
    simp only [daRows, List.getElem_map, List.getElem_range]
    have hl := hrow _ (List.getElem_mem h1)
    simp only [LeanDa.logM] at hl
    refine (flatMap_blocks rows[i] 0 (by rw [hl]; rfl) _ (wSyms_length ⟨rows, vector⟩ hrow i)
      fun j hj => ?_).symm
    simp only [wSyms, h1, hj, and_self, ite_true, LeanDa.listCell, LeanDa.cellSymbols,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some, mul_comm j 256]
  · refine (flatMap_blocks vector 0 (by simpa [LeanDa.logM] using hv) _
      (wWs_length ⟨rows, vector⟩ hv) fun j hj => ?_).symm
    simp only [wWs, hj, ite_true]

theorem toBytes_inj {d d' : Digest} (h : LeanVM.Protocol.Digest.toBytes d = LeanVM.Protocol.Digest.toBytes d') : d = d' := by
  apply LeanVM.Protocol.KeccakHash.digestBytes_injective
  have := congrArg (fun x : Common.DigestBytes => x.toList) h
  simpa [LeanVM.Protocol.Digest.toBytes] using this

theorem wSyms_len {w : LeanVM.Da.MatrixWitness} {root vd : Digest} (hw : w.Opens root vd) (i j : ℕ) :
    (wSyms w i j).length = 256 := wSyms_length w hw.2.2.1 i j

theorem wWs_len {w : LeanVM.Da.MatrixWitness} {root vd : Digest} (hw : w.Opens root vd) (j : ℕ) :
    (wWs w j).length = 256 := wWs_length w hw.2.2.2.2.1 j

set_option maxRecDepth 20000 in
/-- **A witness's rows are orthogonal to its vector**, cell by cell. -/
theorem wDot {w : LeanVM.Da.MatrixWitness} {root vd : Digest} (hw : w.Opens root vd) :
    ∀ i < w.rows.length, ∑ j ∈ Finset.range 128, ∑ e ∈ Finset.range 256,
      (wWs w j).getD e 0 * ofK ((wSyms w i j).getD e 0) = 0 := by
  intro i hi
  have hw' := hw
  rw [witness_eq hw] at hw'
  have hlen : (daRows w.rows.length (wSyms w)).length = w.rows.length := by simp [daRows]
  have hrow := hw'.2.2.2.2.2.2 ((daRows w.rows.length (wSyms w))[i]'(by rw [hlen]; exact hi))
    (List.getElem_mem _)
  have he : (daRows w.rows.length (wSyms w))[i]'(by rw [hlen]; exact hi) =
      (List.range 128).flatMap (wSyms w i) := by simp [daRows]
  rw [he, LeanDa.dot, Fin.sum_univ_eq_sum_range (fun b => (daVector (wWs w)).getD b 0 *
    LeanDa.ι (((List.range 128).flatMap (wSyms w i)).getD b 0)) (2 ^ 15),
    show 2 ^ 15 = 128 * 256 by norm_num, sum_range_mul _ 256 128] at hrow
  refine (Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun e he => ?_).trans hrow
  have hj' := Finset.mem_range.mp hj
  have he' := Finset.mem_range.mp he
  rw [daVector, flatMap_getD (wWs w) 256 (wWs_len hw) 0 128 j e hj' he',
    flatMap_getD (wSyms w i) 256 (wSyms_len hw i) 0 128 j e hj' he']
  rfl

/-- **The claim a witness opens** is its cells' root and its columns' digest. -/
theorem opens_eq {w : LeanVM.Da.MatrixWitness} {root vd : Digest} (hw : w.Opens root vd) :
    root = daRoot w.rows.length (wLog w) (wSyms w) ∧ vd = daVd (wWs w) := by
  obtain ⟨hlo, -⟩ := nPad_bounds hw.1
  have ho := opens_of hw.1 hw.2.1 rfl hlo (wSyms_len hw) (wWs_len hw) (wDot hw)
  rw [← witness_eq hw] at ho
  exact ⟨toBytes_inj (hw.2.2.2.1.symm.trans ho.2.2.2.1),
    toBytes_inj (hw.2.2.2.2.2.1.symm.trans ho.2.2.2.2.2.1)⟩

/-- **`da_verify` is complete on a witness**: for a witness opening `(root, vd)`, on a memory
image with the exponent table at `gsq` and the honest memory of the witness at any choice of the
buffers `P`, `da_verify` returns the cells of `root` and `vd`. -/
theorem da_verify_complete {rd : Reader} (hm : MemOk rd) {gsq : E} (hsq : SquaresAt rd gsq)
    {w : LeanVM.Da.MatrixWitness} {root vd : Digest} (hw : w.Opens root vd) {P : DaPtrs}
    (hmem : DaMem w.rows.length (wLog w) (wSyms w) (wWs w) rd P) :
    coreProgram.Rel rd "da_verify" [gsq] (digestCells root ++ digestCells vd) := by
  obtain ⟨e1, e2⟩ := opens_eq hw
  rw [e1, e2]
  exact da_verify_complete_mem hm hsq hw.1 hw.2.1 rfl (wSyms_len hw) (wWs_len hw)
    (fun i hi => wDot hw i hi) hmem

end
end LeanVM.Guest.B1.Da
