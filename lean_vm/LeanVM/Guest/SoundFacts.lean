/-
  LeanVM.Guest.SoundFacts

  The certificate facts B2's soundness reads off the deployed bytecode's checks, semantics-free:
  the checked windows, the functions' names and their windows' hand-overs.
-/

module

public import LeanVM.Guest.Checked
public import LeanVM.Guest.CoreNames
public import LeanVM.Guest.JumpTable
public import LeanVM.Guest.CertName

/-!
# The checks' facts

What `Sound.lean` reads off the certificates and the kernel's checks (`Checked.all_ok`), none of
it about the semantics of `KECCAK`: every window of every function passes (`winOk_of`), the jump
table the checks read is the one `__jump_tables` writes (`jtHolds_of`), the windows hand nothing
on but in `main` (after `exponent_tables`, `main_cut`) and `verify_sub` (function `19`, before
`check_opening_terminal`, `vs_cut`), and `main`'s certificate (`main_facts`).
-/

namespace LeanVM.Guest.End

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Check
open LeanVM.Guest.Exec

@[expose] public section

theorem certOf_pows (j : ℕ) : (certOf j).facts.pows = Data.powTree := by
  unfold certOf
  split
  rfl

theorem certOf_pows_ok (j : ℕ) : (certOf j).facts.pows.Ok := by
  rw [certOf_pows]
  exact PowTree.ok_of_okW Checked.powTree_ok

theorem functions_length : Data.functions.length = nFns := by decide +kernel

theorem coreProgram_length' : coreProgram.length + 1 = nFns := by
  rw [coreProgram_length]; rfl

theorem fnOf_mem {j : ℕ} (h : j < nFns) : fnOf j ∈ Data.functions := by
  unfold fnOf
  rw [nth_eq (functions_length ▸ h)]
  exact List.getElem_mem _

theorem coreOf_find {j : ℕ} (h1 : 1 ≤ j) (h2 : j < nFns) :
    coreProgram.find? (coreOf j).name = some (coreOf j) := by
  have h : j - 1 < coreProgram.length := by have := coreProgram_length'; omega
  unfold coreOf
  rw [nth_eq h]
  exact coreProgram_find_getElem h

theorem winOk_of {j : ℕ} (h1 : 1 ≤ j) (h2 : j < nFns) :
    ∀ i ≤ (certOf j).cuts.length, checkWin glob (fnOf j) (coreOf j) (certOf j) (j == 1) i = true :=
  Checked.all_ok j h1 h2

theorem jtHolds_of {κ : ℕ} {L : MemImage κ} (h : JumpTables L) : JTHolds glob L :=
  JumpTable.jt_of_jumpTables h (PowTree.ok_of_okW Checked.powTree_ok)

theorem known_plain {j : ℕ} (h0j : 1 ≤ j) (hj : j < nFns) (h1 : j ≠ 1) (h19 : j ≠ 19) {κ : ℕ}
    {L : MemImage κ} {fp : K} {i : ℕ} (hi : i ≤ (certOf j).cuts.length) (h0 : 0 < i) :
    MemKnown L fp ((certOf j).cutAt i).known ∧ SemHolds glob L fp ((certOf j).cutAt i).sems := by
  obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  have hall := List.all_eq_true.mp (Checked.all_plain j h0j hj h1 h19)
    ((certOf j).cuts[i]'(by omega))
    (List.getElem_mem _)
  simp only [Bool.and_eq_true, List.isEmpty_iff] at hall
  have hc : (certOf j).cutAt (i + 1) = (certOf j).cuts[i]'(by omega) := by
    simp only [Cert.cutAt]
    exact nth_eq _
  rw [hc, hall.1, hall.2]
  exact ⟨fun _ h ↦ by simp at h, fun _ h ↦ by simp at h⟩

/-! ## `verify_sub`'s window -/

theorem vs_cuts : (certOf 19).cuts.length = 1 := by decide +kernel

theorem vs_cut : ((certOf 19).cutAt 1).start = 2098 ∧ ((certOf 19).cutAt 1).known = [(1340, 99, 29)] ∧
    ((certOf 19).cutAt 1).sems = [] := by decide +kernel

theorem vs_cells : (certOf 19).locs.getD 4 0 = 6 ∧ (certOf 19).locs.getD 5 0 = 7 ∧
    (certOf 19).locs.getD 1889 0 = 1340 := by
  decide +kernel

theorem vs_sem : (certOf 19).sem = [(6, 7)] := by decide +kernel

theorem coreOf_19 : coreOf 19 = Data.core18 := rfl

/-! ## `main`'s window -/

theorem main_cut : (certOf 1).cuts.length = 1 ∧ ((certOf 1).cutAt 1).known = [] ∧
    ((certOf 1).cutAt 1).sems = [((certOf 1).locs.getD 65 0, (certOf 1).locs.getD 66 0)] := by
  decide +kernel

theorem main_call : ((coreOf 1).body.take ((certOf 1).cutAt 1).start) =
    (coreOf 1).body.take (((certOf 1).cutAt 1).start - 1) ++
      [.call "exponent_tables" [] [.n 65, .n 66]] := by
  have h : ((coreOf 1).body[((certOf 1).cutAt 1).start - 1]?) =
      some (.call "exponent_tables" [] [.n 65, .n 66]) := rfl
  obtain ⟨m, hm⟩ : ∃ m, ((certOf 1).cutAt 1).start = m + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos (by decide +kernel)).symm⟩
  rw [hm, Nat.add_sub_cancel] at h ⊢
  rw [List.take_add_one, h]
  rfl

theorem main_facts : (certOf 1).facts.env = [] ∧ (certOf 1).pre = [] ∧ (certOf 1).mem = [] ∧
    (certOf 1).sem = [] ∧ (certOf 1).nret = 0 ∧ (coreOf 1).params = [] ∧ (coreOf 1).name = "main" := by
  decide +kernel

theorem fnOf_1 : (fnOf 1).entry = mainEntry := rfl

end
end LeanVM.Guest.End
