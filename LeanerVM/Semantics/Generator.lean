/-
  LeanerVM.Semantics.Generator

  The computable choices of witness generation: the fill blocks found in the bytecode, the
  height of the `JUMP` table, and the skeletons of a run, stepped forward once.
-/

module

public import LeanerVM.Semantics.Executable
public import LeanerVM.Semantics.PaddedRows

/-!
# The choices of witness generation

leanISA roadmap Layer 10 companion (`docs/architecture.md`, `T2`). Constraint completeness
(`Arithmetization.Completeness.Theorem`) takes the fill blocks of the bytecode and the exponent of
the `JUMP` table's height from propositions; a witness generator searches for them instead, and
uses them only through their specifications, so no equality with a chosen value is needed.

* `fillStarts prog` is, for each table and size, the first slot of the bytecode that starts a
  fill block of that table and size (`findStart`, decided by `isFillBlockB` over `prog.code`),
  tabulated once (`fillStartTable`); the tables are values, not closures, so that compiled code
  evaluates each search once. On well-formed bytecode every one is a fill block (`fillStarts_spec`).
* `jumpHeight owed` is the least `τ ≤ maxLogRows` with `owed ≤ 2^τ ≠ owed + 1`; it exists
  exactly when `JumpFeasible owed` (`jumpHeight_spec`, `jumpHeight_isSome`).
* `runSkelsBy` steps a run forward once from a state, at any fetch and execute functions,
  collecting the skeletons (state and fetched instruction) it steps from; `skelCountTable`
  tabulates the skeletons of each table. Their agreement with `Trace.runSkels` and `Trace.runRows` is proved
  where the run's states are named (`Arithmetization.WitnessGen`).

## Wrong readings excluded

* The search is no trust boundary: a found start is a fill block by `isFillBlockB_iff`, and a
  program without fill blocks makes the search fail, never return a wrong slot.
-/

namespace LeanerVM.Semantics

open LeanerVM.Parameters

@[expose] public section

/-! ## Fill blocks -/

/-- The instruction at slot `j` of the program, `none` past its end. -/
def codeAt (prog : Program) (j : ℕ) : Option Instr :=
  if h : j < 2 ^ prog.logSize then some (prog.code ⟨j, h⟩) else none

/-- Whether slot `p` starts a fill block of table `t` and size `s`; the closing jump is checked
first, since most slots fail there. -/
def isFillBlockB (prog : Program) (t : Opcode) (s p : ℕ) : Bool :=
  let d := fillDummy t
  decide (p + s + 1 < 2 ^ prog.logSize) && decide (codeAt prog (p + s) = some fillClose) &&
    ((List.range s).all fun i ↦ decide (codeAt prog (p + i) = some d))

/-- The first slot that starts a fill block of table `t` and size `s`. -/
def findStart (prog : Program) (t : Opcode) (s : ℕ) : Option ℕ :=
  (List.range (2 ^ prog.logSize)).find? (isFillBlockB prog t s)

/-- The starting slots of the fill blocks, searched once for the six tables and eight sizes: entry
`8 * tableIdx t + k` for table `t` and size `sizeAt k`, `0` where there is none. -/
def fillStartTable (prog : Program) : Array ℕ :=
  Array.ofFn (n := 48) fun c ↦
    (findStart prog (fillTables.getD (c / 8) .xor) (sizeAt (c % 8))).getD 0

/-- The starting slot of table `t` and size `s` in a table of starts. -/
def startsOf (tab : Array ℕ) (t : Opcode) (s : ℕ) : ℕ :=
  tab.getD (8 * tableIdx t + fillSizes.idxOf s) 0

/-- The starting slots of the fill blocks, searched once. Executable code should evaluate
`fillStartTable prog` once and use `startsOf` of it, as `witnessGen` does. -/
def fillStarts (prog : Program) : Opcode → ℕ → ℕ := startsOf (fillStartTable prog)

/-- Inside the program, `codeAt` is the reference fetch at the slot's address. -/
theorem fetch_gpow_eq_codeAt (prog : Program) {j : ℕ} (hj : j < 2 ^ prog.logSize) :
    prog.fetch (gpow j) = codeAt prog j := by
  rw [codeAt, dite_eq_left hj]
  exact Program.fetch_gpow prog ⟨j, hj⟩

/-- **The search decides fill blocks.** -/
theorem isFillBlockB_iff (prog : Program) (t : Opcode) (s p : ℕ) :
    isFillBlockB prog t s p = true ↔ IsFillBlock prog t s p := by
  simp only [isFillBlockB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range]
  constructor
  · rintro ⟨⟨hb, hc⟩, hd⟩
    exact ⟨hb, fun i hi ↦ (fetch_gpow_eq_codeAt prog (by omega)).trans (hd i hi),
      (fetch_gpow_eq_codeAt prog (by omega)).trans hc⟩
  · rintro ⟨hb, hd, hc⟩
    exact ⟨⟨hb, (fetch_gpow_eq_codeAt prog (by omega)).symm.trans hc⟩,
      fun i hi ↦ (fetch_gpow_eq_codeAt prog (by omega)).symm.trans (hd i hi)⟩

/-- A found start is a fill block. -/
theorem findStart_spec {prog : Program} {t : Opcode} {s p : ℕ}
    (h : findStart prog t s = some p) : IsFillBlock prog t s p :=
  (isFillBlockB_iff prog t s p).mp (List.find?_some h)

/-- A fill block is found when there is one. -/
theorem findStart_isSome {prog : Program} {t : Opcode} {s : ℕ}
    (h : ∃ p, IsFillBlock prog t s p) : (findStart prog t s).isSome := by
  obtain ⟨p, hp⟩ := h
  rw [findStart, List.find?_isSome]
  exact ⟨p, List.mem_range.mpr (by have := hp.below; omega), (isFillBlockB_iff prog t s p).mpr hp⟩

/-- The tabulated start of a table and a size of the ladder is the searched one. -/
theorem fillStarts_eq (prog : Program) (t : Opcode) {k : ℕ} (hk : k < 8) :
    fillStarts prog t (sizeAt k) = (findStart prog t (sizeAt k)).getD 0 := by
  have ht := tableIdx_lt t
  have hidx : fillSizes.idxOf (sizeAt k) = k := by interval_cases k <;> rfl
  have hc : 8 * tableIdx t + k < 48 := by omega
  have h8 : (8 * tableIdx t + k) / 8 = tableIdx t := by omega
  have h8' : (8 * tableIdx t + k) % 8 = k := by omega
  simp only [fillStarts, startsOf, fillStartTable, hidx, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, hc,
    ↓reduceDIte, Option.getD_some, h8, h8', fillTables_getD_tableIdx]

/-- **On bytecode with fill blocks, every tabulated start is a fill block.** -/
theorem fillStarts_spec {prog : Program} (h : HasFillBlocks prog) :
    ∀ t, ∀ k < 8, IsFillBlock prog t (sizeAt k) (fillStarts prog t (sizeAt k)) := by
  intro t k hk
  rw [fillStarts_eq prog t hk]
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp (findStart_isSome (h t _ (sizeAt_mem hk)))
  rw [hp, Option.getD_some]
  exact findStart_spec hp

/-! ## The height of the `JUMP` table -/

/-- The least exponent `τ ≤ maxLogRows` of a `JUMP` table that holds `owed` rows and is not one
more. -/
def jumpHeight (owed : ℕ) : Option ℕ :=
  (List.range (maxLogRows + 1)).find? fun τ ↦ decide (owed ≤ 2 ^ τ) && decide (2 ^ τ ≠ owed + 1)

/-- A found exponent is feasible. -/
theorem jumpHeight_spec {owed τ : ℕ} (h : jumpHeight owed = some τ) :
    τ ≤ maxLogRows ∧ owed ≤ 2 ^ τ ∧ 2 ^ τ ≠ owed + 1 := by
  have hm := List.mem_range.mp (List.mem_of_find?_eq_some h)
  have hp := List.find?_some h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
  exact ⟨by omega, hp⟩

/-- An exponent is found exactly when the table can be filled. -/
theorem jumpHeight_isSome {owed : ℕ} (h : JumpFeasible owed) : (jumpHeight owed).isSome := by
  obtain ⟨τ, hτ, h1, h2⟩ := h
  rw [jumpHeight, List.find?_isSome]
  exact ⟨τ, List.mem_range.mpr (by omega), by simp [h1, h2]⟩

/-! ## The skeletons of a run -/

/-- Step forward `n` times from `r` at the fetch `fetch` and the execution `exec`, appending to
`acc` the skeleton of every state stepped from; stop early where a fetch or a step fails. -/
def runSkelsBy (fetch : K → Option Instr) (exec : Regs K → Instr → Option (Regs K)) :
    ℕ → Regs K → Array Skel → Array Skel
  | 0, _, acc => acc
  | n + 1, r, acc =>
    match fetch r.pc with
    | none => acc
    | some ins =>
      match exec r ins with
      | none => acc.push ⟨r.pc, r.fp, ins⟩
      | some r' => runSkelsBy fetch exec n r' (acc.push ⟨r.pc, r.fp, ins⟩)

/-- The number of skeletons of each table, counted once: entry `tableIdx op` for `op`. -/
def skelCountTable (S : List Skel) : Array ℕ := (fillTables.map fun op ↦ Skel.count op S).toArray

/-- The count of table `op` in a table of counts. -/
def countsOf (tab : Array ℕ) (op : Opcode) : ℕ := tab.getD (tableIdx op) 0

/-- The tabulated counts are the counts. -/
theorem countsOf_skelCountTable (S : List Skel) :
    countsOf (skelCountTable S) = fun op ↦ Skel.count op S := by
  funext op
  cases op <;> rfl

end
end LeanerVM.Semantics
