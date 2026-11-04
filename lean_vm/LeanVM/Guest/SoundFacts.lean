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
on but in `main` (after `exponent_tables`, `main_cut`) and `verify_sub` (function `19`, from its
call of `check_opening_terminal`, `vs_cut`), and `main`'s certificate (`main_facts`).
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

theorem jtHolds_of {κ : ℕ} {L : MemoryImage κ} (h : JumpTables L) : JTHolds glob L :=
  JumpTable.jt_of_jumpTables h (PowTree.ok_of_okW Checked.powTree_ok)

/-- A function's cuts hand nothing on (`Checked.Plain`): every cut's memory bounds and semantic pairs
hold, vacuously. -/
theorem known_of_plain {j : ℕ} (hp : Checked.Plain j) {κ : ℕ} {L : MemoryImage κ} {fp : K} {i : ℕ}
    (hi : i ≤ (certOf j).cuts.length) (h0 : 0 < i) :
    MemKnown L fp ((certOf j).cutAt i).known ∧ SemHolds glob L fp ((certOf j).cutAt i).sems := by
  obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  have hall := List.all_eq_true.mp hp ((certOf j).cuts[i]'(by omega)) (List.getElem_mem _)
  simp only [Bool.and_eq_true, List.isEmpty_iff] at hall
  have hc : (certOf j).cutAt (i + 1) = (certOf j).cuts[i]'(by omega) := by
    simp only [Cert.cutAt]
    exact nth_eq _
  rw [hc, hall.1, hall.2]
  exact ⟨fun _ h ↦ by simp at h, fun _ h ↦ by simp at h⟩

theorem known_plain {j : ℕ} (h0j : 1 ≤ j) (hj : j < nFns) (h1 : j ≠ 1) (h19 : j ≠ 19) {κ : ℕ}
    {L : MemoryImage κ} {fp : K} {i : ℕ} (hi : i ≤ (certOf j).cuts.length) (h0 : 0 < i) :
    MemKnown L fp ((certOf j).cutAt i).known ∧ SemHolds glob L fp ((certOf j).cutAt i).sems :=
  known_of_plain (Checked.all_plain j h0j hj h1 h19) hi h0

/-! ## `verify_sub`'s window -/

theorem vs_cuts : (certOf 19).cuts.length = 1 := by decide +kernel

/-- The bound of entry `c` of `kappa_base` (`lean_ethereum.py:3242-3250`): `kb[0] = g^0`, the
memory's log and the six tables' heights `kb[1..6]` below `g^29`, and `kb[7]`, keccak's `τ`,
below `g^23` (`τ + 6` is a column's log, at most `28`). -/
def vsKbBound (c : ℕ) : ℕ := [1, 29, 29, 29, 29, 29, 29, 23].getD c 0

/-- `verify_sub`'s second window starts at its call of `check_opening_terminal` (statement
`1592`) and takes the bound of each of the `8` entries of `kappa_base` (the value `139`). -/
theorem vs_cut : ((certOf 19).cutAt 1).start = 1592 ∧
    ((certOf 19).cutAt 1).known =
      (List.range 8).map (fun c ↦ ((certOf 19).locs.getD 139 0, c, vsKbBound c)) ∧
    ((certOf 19).cutAt 1).sems = [] := by decide +kernel

theorem vs_cells : (certOf 19).locs.getD 4 0 = 6 := by decide +kernel

theorem vs_sem : (certOf 19).sem = [(6, 6)] := by decide +kernel

theorem coreOf_19 : coreOf 19 = Data.core18 := rfl

/-! ## `main`'s window -/

/-- `main`'s one cut, after its call of `exponent_tables` (`main_call`), takes the exponent
table's relation on that call's return cell (`glob`'s relation reads a pair's first cell). -/
theorem main_cut : (certOf 1).cuts.length = 1 ∧ ((certOf 1).cutAt 1).known = [] ∧
    ((certOf 1).cutAt 1).sems = [((certOf 1).locs.getD 49 0, (certOf 1).locs.getD 49 0)] := by
  decide +kernel

/-- `main`'s statement `23` is its call of `exponent_tables`, before its cut, after no `ret`. -/
theorem main_exp : (coreOf 1).body[23]? = some (.call "exponent_tables" [] [.n 49]) := rfl

theorem main_exp_lt : 23 < ((certOf 1).cutAt 1).start := by decide +kernel

theorem main_exp_noRet : Stmt.noRetList ((coreOf 1).body.take 23) = true := by decide +kernel

/-- The statements before `main`'s cut, at its call of `exponent_tables` (wherever the cut is). -/
theorem main_call : (coreOf 1).body.take ((certOf 1).cutAt 1).start =
    (coreOf 1).body.take 23 ++ .call "exponent_tables" [] [.n 49] ::
      ((coreOf 1).body.take ((certOf 1).cutAt 1).start).drop 24 := by
  have h1 := main_exp
  have h2 := main_exp_lt
  generalize (coreOf 1).body = l at h1 ⊢
  generalize ((certOf 1).cutAt 1).start = n at h2 ⊢
  have h : (l.take n)[23]? = some (.call "exponent_tables" [] [.n 49]) := by
    rw [List.getElem?_take_of_lt h2, h1]
  have hl : 23 < (l.take n).length := (List.getElem?_eq_some_iff.mp h).1
  conv_lhs => rw [← List.take_append_drop 23 (l.take n)]
  rw [List.take_take, Nat.min_eq_left h2.le, List.drop_eq_getElem_cons hl]
  congr 2
  exact (List.getElem?_eq_some_iff.mp h).2

theorem main_facts : (certOf 1).facts.env = [] ∧ (certOf 1).pre = [] ∧ (certOf 1).mem = [] ∧
    (certOf 1).sem = [] ∧ (certOf 1).nret = 0 ∧ (coreOf 1).params = [] ∧ (coreOf 1).name = "main" := by
  decide +kernel

theorem fnOf_1 : (fnOf 1).entryPc = mainEntry := rfl

end
end LeanVM.Guest.End
