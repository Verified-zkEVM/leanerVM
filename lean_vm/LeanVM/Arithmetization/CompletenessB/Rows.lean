/-
  LeanVM.Arithmetization.CompletenessB.Rows

  The row of an instruction executed under any semantics of `BLAKE2S` whose rows are canonical:
  what it sends, and that every cell it reads is an address.
-/

module

public import LeanVM.Arithmetization.Completeness.Rows
public import LeanVM.Arithmetization.Soundness.Rows

@[expose] public section

/-!
# Rows under a semantics of `BLAKE2S`

`Completeness/Rows.lean` with the execution under a semantics `S` (`executeWithB S`) whose
`BLAKE2S` check makes the nine cells canonical (`Canonical S`), as the Flock-blind semantics and
every table semantics do. The other five instructions execute as deployed (`executeWithB_ne`); a
`BLAKE2S` row's sends never read the compression, only its nine canonical cells
(`blake2sBindings_of_execB`), so `rowOf_sendsB` and `readAddrs_validB` are the deployed lemmas'.
-/

namespace LeanVM.Arithmetization

open LeanVM.Parameters LeanVM.Semantics

/-- **A semantics of canonical rows**: its check makes the nine cells canonical. -/
def Canonical (S : BlakeSem) : Prop :=
  ∀ {m : Fin 4 → E} {cv0 cv1 out0 out1 md : E}, S.check m cv0 cv1 out0 out1 md →
    CanonicalCells m cv0 cv1 out0 out1 md

/-- An instruction that is no `BLAKE2S` executes under any semantics as deployed. -/
theorem executeWithB_ne (S : BlakeSem) (read : K → Option E) (r : Regs K) {ins : Instr}
    (h : ins.opcode ≠ .blake2s) : executeWithB S read r ins = executeWith read r ins := by
  cases ins with
  | blake2s => exact absurd rfl h
  | _ => rfl

/-- A `BLAKE2S` executing under a semantics of canonical rows is bound to the image and falls
through. -/
theorem blake2sBindings_of_execB {S : BlakeSem} (hS : Canonical S) {κ : ℕ} {mem : MemImage κ}
    {pc fp om0 om1 om2 om3 ocv oout omd : K} {next : Regs K}
    (hexec : executeWithB S mem.read ⟨pc, fp⟩ (.blake2s ![om0, om1, om2, om3] ocv oout omd) =
      some next)
    (rm0 rm1 rm2 rm3 rcv0 rcv1 rout0 rout1 rmd rbc : K) :
    Blake2sBindings mem (blake2sRowOf mem pc fp om0 om1 om2 om3 ocv oout omd
      rm0 rm1 rm2 rm3 rcv0 rcv1 rout0 rout1 rmd rbc) ∧ next = Regs.next ⟨pc, fp⟩ := by
  have h := hexec
  simp only [executeWithB, Matrix.cons_val, Fin.isValue, Option.bind_eq_bind,
    Option.bind_eq_some_iff] at h
  obtain ⟨m0, hm0, m1, hm1, m2, hm2, m3, hm3, cv0, hcv0, cv1, hcv1, out0, hout0, out1, hout1,
    md, hmd, u, hu, hnext⟩ := h
  have hc : S.check ![m0, m1, m2, m3] cv0 cv1 out0 out1 md := by
    simpa [guard] using (show (@guard Option _ (S.check ![m0, m1, m2, m3] cv0 cv1 out0 out1 md)
      (S.dec _ _ _ _ _ _)) = some u from hu)
  obtain ⟨hcm, hccv0, hccv1, hcout0, hcout1, hcmd⟩ := hS hc
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · show mem.read (fp * om0) = some (E.ofCell (mem.cellAt (fp * om0)))
    rw [MemImage.ofCell_cellAt hm0 (by simpa using hcm 0)]; exact hm0
  · show mem.read (fp * om1) = some (E.ofCell (mem.cellAt (fp * om1)))
    rw [MemImage.ofCell_cellAt hm1 (by simpa using hcm 1)]; exact hm1
  · show mem.read (fp * om2) = some (E.ofCell (mem.cellAt (fp * om2)))
    rw [MemImage.ofCell_cellAt hm2 (by simpa using hcm 2)]; exact hm2
  · show mem.read (fp * om3) = some (E.ofCell (mem.cellAt (fp * om3)))
    rw [MemImage.ofCell_cellAt hm3 (by simpa using hcm 3)]; exact hm3
  · show mem.read (fp * ocv) = some (E.ofCell (mem.cellAt (fp * ocv)))
    rw [MemImage.ofCell_cellAt hcv0 hccv0]; exact hcv0
  · show mem.read (fp * (g * ocv)) = some (E.ofCell (mem.cellAt (fp * (g * ocv))))
    rw [MemImage.ofCell_cellAt hcv1 hccv1]; exact hcv1
  · show mem.read (fp * oout) = some (E.ofCell (mem.cellAt (fp * oout)))
    rw [MemImage.ofCell_cellAt hout0 hcout0]; exact hout0
  · show mem.read (fp * (g * oout)) = some (E.ofCell (mem.cellAt (fp * (g * oout))))
    rw [MemImage.ofCell_cellAt hout1 hcout1]; exact hout1
  · show mem.read (fp * omd) = some (E.ofCell (mem.cellAt (fp * omd)))
    rw [MemImage.ofCell_cellAt hmd hcmd]; exact hmd
  · simpa using hnext.symm

/-- The `BLAKE2S` row of an execution under a semantics of canonical rows sends the `BLAKE2S`
messages (`blake2s_exec_sends`). -/
theorem blake2s_exec_sendsB {S : BlakeSem} (hS : Canonical S) {κ : ℕ} {mem : MemImage κ}
    {pc fp om0 om1 om2 om3 ocv oout omd : K} {next : Regs K}
    (hexec : executeWithB S mem.read ⟨pc, fp⟩ (.blake2s ![om0, om1, om2, om3] ocv oout omd) =
      some next)
    (rm0 rm1 rm2 rm3 rcv0 rcv1 rout0 rout1 rmd rbc : K) (data : ProverData K) :
    rowSends ⟨blake2sTable⟩
        (Environment.fromArray (rawRow (blake2sRowOf mem pc fp om0 om1 om2 om3 ocv oout omd
          rm0 rm1 rm2 rm3 rcv0 rcv1 rout0 rout1 rmd rbc)) data) =
      sendsOf pc fp next rbc (entry (.blake2s ![om0, om1, om2, om3] ocv oout omd))
        [(fp * om0, rm0, mem.limbsAt (fp * om0)), (fp * om1, rm1, mem.limbsAt (fp * om1)),
          (fp * om2, rm2, mem.limbsAt (fp * om2)), (fp * om3, rm3, mem.limbsAt (fp * om3)),
          (fp * ocv, rcv0, mem.limbsAt (fp * ocv)),
          (fp * (g * ocv), rcv1, mem.limbsAt (fp * (g * ocv))),
          (fp * oout, rout0, mem.limbsAt (fp * oout)),
          (fp * (g * oout), rout1, mem.limbsAt (fp * (g * oout))),
          (fp * omd, rmd, mem.limbsAt (fp * omd))] := by
  obtain ⟨⟨hm0, hm1, hm2, hm3, hcv0, hcv1, hout0, hout1, hmd⟩, rfl⟩ :=
    blake2sBindings_of_execB hS hexec rm0 rm1 rm2 rm3 rcv0 rcv1 rout0 rout1 rmd rbc
  rw [rowSends_mk, blake2s_sends_gen _ _ _ _ (eval_rowVar _ data)]
  simp only [blake2sRowOf] at hm0 hm1 hm2 hm3 hcv0 hcv1 hout0 hout1 hmd ⊢
  simp [sendsOf, bcMsgOf, entry, Regs.next, memMsgOf_cell hm0, memMsgOf_cell hm1,
    memMsgOf_cell hm2, memMsgOf_cell hm3, memMsgOf_cell hcv0, memMsgOf_cell hcv1,
    memMsgOf_cell hout0, memMsgOf_cell hout1, memMsgOf_cell hmd]

/-- **The row of an instruction executing under a semantics of canonical rows sends `sendsOf`**
(`rowOf_sends`). -/
theorem rowOf_sendsB {S : BlakeSem} (hS : Canonical S) {κ : ℕ} {mem : MemImage κ} {pc fp : K}
    {ins : Instr} {next : Regs K} (hexec : executeWithB S mem.read ⟨pc, fp⟩ ins = some next)
    (cnt : ℕ → K) (rbc : K) (data : ProverData K) :
    rowSends (opComponent ins.opcode)
        (Environment.fromArray (rowOf mem pc fp cnt rbc ins) data) =
      sendsOf pc fp next rbc (entry ins) (readsOf mem fp cnt ins) := by
  cases ins with
  | blake2s om ocv oout omd =>
    have hom : om = ![om 0, om 1, om 2, om 3] := by funext i; fin_cases i <;> rfl
    have h := blake2s_exec_sendsB hS (hom ▸ hexec) (cnt 0) (cnt 1) (cnt 2) (cnt 3) (cnt 4)
      (cnt 5) (cnt 6) (cnt 7) (cnt 8) rbc data
    rw [← hom] at h
    simp only [Instr.opcode, opComponent]
    rw [rowOf, h]
    simp [readsOf, readAddrs]
  | _ =>
    exact rowOf_sends ((executeWithB_ne S mem.read _ (by simp [Instr.opcode])).symm.trans hexec)
      cnt rbc data

/-- Every cell an instruction executing under a semantics of canonical rows reads is an address
(`readAddrs_valid`). -/
theorem readAddrs_validB {S : BlakeSem} (hS : Canonical S) {κ : ℕ} {mem : MemImage κ} {pc fp : K}
    {ins : Instr} {next : Regs K} (hexec : executeWithB S mem.read ⟨pc, fp⟩ ins = some next) :
    ∀ a ∈ readAddrs mem fp ins, ∃ w, mem.read a = some w := by
  cases ins with
  | blake2s om ocv oout omd =>
    have hom : om = ![om 0, om 1, om 2, om 3] := by funext i; fin_cases i <;> rfl
    rw [hom] at hexec
    obtain ⟨⟨hm0, hm1, hm2, hm3, hcv0, hcv1, hout0, hout1, hmd⟩, -⟩ :=
      blake2sBindings_of_execB hS hexec 1 1 1 1 1 1 1 1 1 1
    simp only [readAddrs, List.mem_cons, List.not_mem_nil, or_false]
    rintro a (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    exacts [⟨_, hm0⟩, ⟨_, hm1⟩, ⟨_, hm2⟩, ⟨_, hm3⟩, ⟨_, hcv0⟩, ⟨_, hcv1⟩, ⟨_, hout0⟩,
      ⟨_, hout1⟩, ⟨_, hmd⟩]
  | _ =>
    exact readAddrs_valid ((executeWithB_ne S mem.read _ (by simp [Instr.opcode])).symm.trans hexec)

end LeanVM.Arithmetization
