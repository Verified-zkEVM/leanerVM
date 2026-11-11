/-
  LeanerVM.Semantics.PaddedRows

  The rows of a padded trace: the run's skeletons, the traversal counts of the fill plan, and the
  number of rows each table ends up with.
-/

module

public import LeanerVM.Semantics.FillRows
public import LeanerVM.Semantics.PaddedTrace

/-!
# The rows of a padded trace

leanISA roadmap Layer 10 (`docs/roadmap/leanisa-blueprint.md`), at leanVM pin
`a386121f84292f6fa663aaa3e570c15bc0240ea2`. Category A. A table's rows are the skeletons whose
instruction has its opcode. The rows of the padded trace are the run's skeletons (`Trace.runSkels`:
the states stepped from, with the instructions fetched there) and the skeletons of the fill
(`padSkels`) under the plan's traversal counts (`planCount`).

**The plan.** A table other than `JUMP` with `n` rows traverses its blocks as `fillGreedy` says for
`fillTarget n floor - n`, so its own dummies are the fill. The `JUMP` table owes `jumpOwed rows`
before its own fill, and fills the gap to `2^τ` with the size-one and size-two blocks as `jumpMix`
says: `a` traversals of two rows and `b` of three.

**The count.** `plan_rows`: for every table, its run rows and its fill rows add up to
`tableHeight`: `fillTarget n floor` for the tables other than `JUMP`, and `2^τ` for `JUMP`, whose
fill also takes one closing jump from every traversal of every other table. This is what makes
every table's height a power of two (`tableHeight_pow`), the form `Caps.heights` asks for, and it is
the arithmetic the witness of the next layer is built on.

## Wrong readings excluded

* The closing jumps are not the table's own rows: a traversal of a block of table `t` adds `s` rows
  to `t` and one to `JUMP`, so the rows of a table are counted by opcode, not by the cycle that
  produced them.
* A `JUMP` fill is not `fillGreedy`: its own blocks give it `s + 1` rows a traversal, and its gap is
  the owed rows' complement to a power of two, never one.
-/

namespace LeanerVM.Semantics

open LeanerVM.Parameters

@[expose] public section

/-! ## The rows of a table -/

/-- The skeletons of the run: the states stepped from, the final state dropped, each with the
instruction fetched there. -/
noncomputable def Trace.runSkels {prog : Program} (t : Trace prog) : List Skel :=
  t.regs.dropLast.filterMap fun r ↦ (prog.fetch r.pc).map fun ins ↦ ⟨r.pc, r.fp, ins⟩

/-- The rows of table `op` among the skeletons: those whose instruction has its opcode. -/
def Skel.onTable (op : Opcode) (l : List Skel) : List Skel :=
  l.filter fun s ↦ s.ins.opcode = op

/-- The number of rows of table `op` among the skeletons. -/
def Skel.count (op : Opcode) (l : List Skel) : ℕ := (Skel.onTable op l).length

/-- The run's skeletons on a table are the run's rows of it. -/
theorem Trace.count_runSkels {prog : Program} (t : Trace prog) (op : Opcode) :
    Skel.count op t.runSkels = t.runRows op := by
  unfold Skel.count Skel.onTable Trace.runSkels Trace.runRows
  generalize t.regs.dropLast = l
  induction l with
  | nil => rfl
  | cons r l ih =>
    cases hf : prog.fetch r.pc with
    | none => simpa [List.filterMap_cons, List.filter_cons, hf] using ih
    | some ins =>
      by_cases ho : ins.opcode = op <;> simp [hf, ho, ih]

/-- The rows of a table in a concatenation are the sum of the rows in the parts. -/
theorem Skel.count_append (op : Opcode) (a b : List Skel) :
    Skel.count op (a ++ b) = Skel.count op a + Skel.count op b := by
  simp [Skel.count, Skel.onTable, List.filter_append]

/-- The rows of a table in a family concatenated over a list are the sum over the list. -/
theorem Skel.count_flatMap {α : Type} (op : Opcode) (f : α → List Skel) (l : List α) :
    Skel.count op (l.flatMap f) = (l.map fun a ↦ Skel.count op (f a)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.flatMap_cons, Skel.count_append, ih, List.map_cons, List.sum_cons]

/-- `n` copies of a list of skeletons have `n` times its rows of a table. -/
theorem Skel.count_replicate_flatten (op : Opcode) (l : List Skel) (n : ℕ) :
    Skel.count op (List.replicate n l).flatten = n * Skel.count op l := by
  induction n with
  | zero => simp [Skel.count, Skel.onTable]
  | succ n ih =>
    rw [List.replicate_succ, List.flatten_cons, Skel.count_append, ih, Nat.succ_mul]
    omega

/-- A traversal of the cycle `(t, k)` gives table `t` its `s` dummies and the `JUMP` table its
closing jump; when `t` is `JUMP` the table has both. -/
theorem Skel.count_cycleSkels (κ : ℕ) (pcs : Opcode → ℕ → ℕ) (t : Opcode) (k : ℕ)
    (op : Opcode) :
    Skel.count op (cycleSkels κ pcs t k) =
      (if t = op then sizeAt k else 0) + if op = .jump then 1 else 0 := by
  have hsplit : cycleSkels κ pcs t k =
      (List.range (sizeAt k)).map (fun i ↦ (⟨gpow (pcs t (sizeAt k) + i),
        gpow (frameBase κ (8 * tableIdx t + k)), fillDummy t⟩ : Skel)) ++
      [⟨gpow (pcs t (sizeAt k) + sizeAt k), gpow (frameBase κ (8 * tableIdx t + k)),
        fillClose⟩] := by
    unfold cycleSkels
    rw [List.range_succ, List.map_append]
    congr 1
    · exact List.map_congr_left fun i hi ↦ by simp [List.mem_range.mp hi]
    · simp
  rw [hsplit, Skel.count_append]
  congr 1
  · unfold Skel.count Skel.onTable
    by_cases ht : t = op
    · have hall : ∀ a ∈ (List.range (sizeAt k)).map (fun i ↦ (⟨gpow (pcs t (sizeAt k) + i),
          gpow (frameBase κ (8 * tableIdx t + k)), fillDummy t⟩ : Skel)),
          decide (a.ins.opcode = op) = true := fun a ha ↦ by
        obtain ⟨i, -, rfl⟩ := List.mem_map.mp ha
        simp [fillDummy_opcode, ht]
      rw [List.filter_eq_self.mpr hall, List.length_map, List.length_range]
      simp [ht]
    · have hall : ∀ a ∈ (List.range (sizeAt k)).map (fun i ↦ (⟨gpow (pcs t (sizeAt k) + i),
          gpow (frameBase κ (8 * tableIdx t + k)), fillDummy t⟩ : Skel)),
          ¬ decide (a.ins.opcode = op) = true := fun a ha ↦ by
        obtain ⟨i, -, rfl⟩ := List.mem_map.mp ha
        simp [fillDummy_opcode, ht]
      rw [List.filter_eq_nil_iff.mpr hall]
      simp [ht]
  · by_cases hj : op = .jump
    · subst hj
      simp [Skel.count, Skel.onTable, fillClose_opcode]
    · have hj' : Opcode.jump ≠ op := fun h ↦ hj h.symm
      simp [Skel.count, Skel.onTable, fillClose_opcode, hj, hj']


/-! ## The plan -/

/-- The rows a plan gives table `t` from its own blocks: the dummies of its traversals. -/
def planDummies (count : Opcode → ℕ → ℕ) (t : Opcode) : ℕ :=
  ((List.range 8).map fun k ↦ count t k * sizeAt k).sum

/-- The traversals of the cycles of table `t`: each gives the `JUMP` table a closing jump. -/
def planTraversals (count : Opcode → ℕ → ℕ) (t : Opcode) : ℕ :=
  ((List.range 8).map fun k ↦ count t k).sum

/-- A sum of counts times a size plus a constant splits into the two sums. -/
theorem sum_map_mul_add (l : List ℕ) (c A : ℕ → ℕ) (B : ℕ) :
    (l.map fun k ↦ c k * (A k + B)).sum = (l.map fun k ↦ c k * A k).sum + B * (l.map c).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    ring

/-- The rows of a table in a fill: its own dummies, and for the `JUMP` table the closing jump of
every traversal. -/
theorem Skel.count_padSkels (κ : ℕ) (pcs : Opcode → ℕ → ℕ) (count : Opcode → ℕ → ℕ)
    (op : Opcode) :
    Skel.count op (padSkels κ pcs count) =
      (fillTables.map fun t ↦ (if t = op then planDummies count t else 0) +
        if op = .jump then planTraversals count t else 0).sum := by
  unfold padSkels
  rw [Skel.count_flatMap]
  congr 1
  refine List.map_congr_left fun t _ ↦ ?_
  rw [Skel.count_flatMap]
  simp only [Skel.count_replicate_flatten, Skel.count_cycleSkels]
  rw [sum_map_mul_add]
  unfold planDummies planTraversals
  by_cases hj : op = .jump
  · subst hj
    by_cases ht : t = .jump <;> simp [ht]
  · by_cases ht : t = op <;> simp [ht, hj]

/-- The traversal counts of the plan of a trace whose tables have `rows` rows, with the `JUMP`
table filled to `2^τ`: every table but `JUMP` as `fillGreedy` says, and `JUMP` as `jumpMix` says
(`a` of the size-one block, `k = 7`, and `b` of the size-two block, `k = 6`). -/
def planCount (rows : Opcode → ℕ) (τ : ℕ) (t : Opcode) (k : ℕ) : ℕ :=
  if t = .jump then
    (if k = 7 then (jumpMix (2 ^ τ - jumpOwed rows)).1
      else if k = 6 then (jumpMix (2 ^ τ - jumpOwed rows)).2 else 0)
  else (fillGreedy (fillTarget (rows t) (minRows t) - rows t)).getD k 0

/-- The height of the table of `op` once filled: the target of its rows, and `2^τ` for `JUMP`. -/
def tableHeight (rows : Opcode → ℕ) (τ : ℕ) (op : Opcode) : ℕ :=
  if op = .jump then 2 ^ τ else fillTarget (rows op) (minRows op)

/-- A table other than `JUMP` fills itself: its own dummies are the fill. -/
theorem planDummies_of_ne (rows : Opcode → ℕ) (τ : ℕ) {t : Opcode} (ht : t ≠ .jump) :
    planDummies (planCount rows τ) t = fillTarget (rows t) (minRows t) - rows t := by
  simp only [planDummies, planCount, ht, ↓reduceIte]
  simp [List.range_succ, sizeAt, fillSizes, fillGreedy]
  generalize fillTarget (rows t) (minRows t) - rows t = p
  omega

/-- The closing jumps the fill of table `op` adds to the `JUMP` table: one per traversal. -/
def fillJumps (rows : Opcode → ℕ) (op : Opcode) : ℕ :=
  fillTraversals (fillTarget (rows op) (minRows op) - rows op)

/-- The rows the `JUMP` table owes: its own, and the closing jumps of every other table's fill. -/
theorem jumpOwed_eq (rows : Opcode → ℕ) :
    jumpOwed rows = rows .jump + (fillJumps rows .xor + (fillJumps rows .mulNative +
      (fillJumps rows .setConstant + (fillJumps rows .deref + (fillJumps rows .blake2s + 0))))) :=
  rfl

/-- The traversals of a table other than `JUMP` are the plan's. -/
theorem planTraversals_of_ne (rows : Opcode → ℕ) (τ : ℕ) {t : Opcode} (ht : t ≠ .jump) :
    planTraversals (planCount rows τ) t = fillJumps rows t := by
  unfold fillJumps
  simp only [planTraversals, planCount, ht, ↓reduceIte]
  simp [List.range_succ, fillTraversals, fillGreedy]

/-- The `JUMP` table's own dummies: one per traversal of the size-one block, two of the size-two
block. -/
theorem planDummies_jump (rows : Opcode → ℕ) (τ : ℕ) :
    planDummies (planCount rows τ) .jump =
      (jumpMix (2 ^ τ - jumpOwed rows)).1 + 2 * (jumpMix (2 ^ τ - jumpOwed rows)).2 := by
  simp [planDummies, planCount, List.range_succ, sizeAt, fillSizes]
  omega

/-- The traversals of the `JUMP` table's own blocks. -/
theorem planTraversals_jump (rows : Opcode → ℕ) (τ : ℕ) :
    planTraversals (planCount rows τ) .jump =
      (jumpMix (2 ^ τ - jumpOwed rows)).1 + (jumpMix (2 ^ τ - jumpOwed rows)).2 := by
  simp [planTraversals, planCount, List.range_succ]
  omega


/-! ## The count -/

/-- A table other than `JUMP` has its target: its run rows and its fill add up. -/
theorem plan_rows_of_ne (κ : ℕ) (pcs : Opcode → ℕ → ℕ) (rows : Opcode → ℕ) (τ : ℕ) {op : Opcode}
    (hop : op ≠ .jump) :
    rows op + Skel.count op (padSkels κ pcs (planCount rows τ)) =
      fillTarget (rows op) (minRows op) := by
  have key : Skel.count op (padSkels κ pcs (planCount rows τ)) =
      planDummies (planCount rows τ) op := by
    rw [Skel.count_padSkels]
    cases op
    all_goals first | exact absurd rfl hop | simp [fillTables]
  rw [key, planDummies_of_ne rows τ hop]
  have := le_fillTarget (rows op) (minRows op)
  omega

/-- The `JUMP` table has `2^τ` rows: its run rows, the closing jump of every traversal of every
other table, and the rows of its own blocks, which fill the gap exactly. -/
theorem plan_rows_jump (κ : ℕ) (pcs : Opcode → ℕ → ℕ) (rows : Opcode → ℕ) {τ : ℕ}
    (h1 : jumpOwed rows ≤ 2 ^ τ) (h2 : 2 ^ τ ≠ jumpOwed rows + 1) :
    rows .jump + Skel.count .jump (padSkels κ pcs (planCount rows τ)) = 2 ^ τ := by
  have hspec := jumpMix_spec (gap := 2 ^ τ - jumpOwed rows) (by omega)
  have hJ := jumpOwed_eq rows
  rw [Skel.count_padSkels]
  simp only [fillTables, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  simp only [planTraversals_of_ne rows τ (show Opcode.xor ≠ .jump by decide),
    planTraversals_of_ne rows τ (show Opcode.mulNative ≠ .jump by decide),
    planTraversals_of_ne rows τ (show Opcode.setConstant ≠ .jump by decide),
    planTraversals_of_ne rows τ (show Opcode.deref ≠ .jump by decide),
    planTraversals_of_ne rows τ (show Opcode.blake2s ≠ .jump by decide),
    planTraversals_jump, planDummies_jump]
  simp
  generalize 2 ^ τ = T at *
  omega

/-- **Every table has its height.** The run rows of a table and the rows of the fill add up to
`tableHeight`. -/
theorem plan_rows (κ : ℕ) (pcs : Opcode → ℕ → ℕ) (rows : Opcode → ℕ) {τ : ℕ}
    (h1 : jumpOwed rows ≤ 2 ^ τ) (h2 : 2 ^ τ ≠ jumpOwed rows + 1) (op : Opcode) :
    rows op + Skel.count op (padSkels κ pcs (planCount rows τ)) = tableHeight rows τ op := by
  by_cases hop : op = .jump
  · subst hop
    simpa only [tableHeight, ↓reduceIte] using plan_rows_jump κ pcs rows h1 h2
  · simpa only [tableHeight, hop, ↓reduceIte] using plan_rows_of_ne κ pcs rows τ hop

/-- **The padded trace's tables.** The run's skeletons and the fill's, on each table, number the
table's height. -/
theorem Trace.count_rows {prog : Program} (t : Trace prog) (κ : ℕ) (pcs : Opcode → ℕ → ℕ) {τ : ℕ}
    (h1 : t.owed ≤ 2 ^ τ) (h2 : 2 ^ τ ≠ t.owed + 1) (op : Opcode) :
    Skel.count op (t.runSkels ++ padSkels κ pcs (planCount t.runRows τ)) =
      tableHeight t.runRows τ op := by
  rw [Skel.count_append, t.count_runSkels]
  exact plan_rows κ pcs t.runRows h1 h2 op

/-- Every table's height is a power of two within the row cap, the form `Caps.heights` asks for,
when the trace fits. -/
theorem tableHeight_pow {rows : Opcode → ℕ} {τ : ℕ} (hτ : τ ≤ maxLogRows)
    (hrows : ∀ op, op ≠ .jump → fillTarget (rows op) (minRows op) ≤ 2 ^ maxLogRows)
    (op : Opcode) : ∃ σ ≤ maxLogRows, tableHeight rows τ op = 2 ^ σ := by
  by_cases hop : op = .jump
  · subst hop
    exact ⟨τ, hτ, by simp [tableHeight]⟩
  · refine ⟨Nat.clog 2 (max (max (rows op) (minRows op)) 1), ?_,
      by simp [tableHeight, hop, fillTarget]⟩
    have := hrows op hop
    unfold fillTarget at this
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp this

end
end LeanerVM.Semantics
