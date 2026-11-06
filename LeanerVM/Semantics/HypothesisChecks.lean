/-
  LeanerVM.Semantics.HypothesisChecks

  Decision procedures for the program-shape and size hypotheses of completeness: well formed
  bytecode, and a trace that fits, from its rows per table.
-/

module

public import LeanerVM.Semantics.Generator

/-!
# Checking the hypotheses of completeness

Besides `ValidExecution`, which `checkTrace` decides, completeness takes
`WellFormedBytecode prog` and `t.Fits`. Both are decided here by Boolean functions proved
equivalent to them, so a compiled program and its execution can be checked to meet the hypotheses
by running code.

* `wellFormedB prog` decides `WellFormedBytecode prog` (`wellFormedB_eq_true_iff`), and gives it a
  `Decidable` instance. The fill blocks are found in one pass over the bytecode: a block of size
  `128` contains, as its tail, a block of every smaller size (`hasFillBlocks_iff_largest`), so it
  suffices to find, for each table, one closing jump preceded by `128` dummies. The pass reads
  `prog.code` by slot (`codeAt`), never `Program.fetch`, whose address search is a discrete log.
* `JumpFeasible` is decided by the search `jumpHeight` (`jumpFeasible_iff`).
* `fitsRowsB κ rows` decides `t.Fits` at `κ = t.κ` and `rows = t.runRows`
  (`fitsRowsB_eq_true_iff`). The rows of a run are computed by the generator's forward pass;
  their agreement with `Trace.runRows` is proved where the run's states are named
  (`Arithmetization.HypothesisChecks`).

## Wrong readings excluded

* `hasFillBlocksB` is not a check of the compiler's ladder layout: any `128`-block per table
  suffices, exactly as `HasFillBlocks` allows overlapping blocks.
-/

namespace LeanerVM.Semantics

open LeanerVM.Parameters

@[expose] public section

/-! ## Well formed bytecode -/

/-- **One block per table suffices**: every table has a block of every size exactly when it has
one of the largest size, whose tails are the smaller blocks. -/
theorem hasFillBlocks_iff_largest (prog : Program) :
    HasFillBlocks prog ↔ ∀ t, ∃ p, IsFillBlock prog t 128 p := by
  refine ⟨fun h t ↦ h t 128 (by simp [fillSizes]), fun h t s hs ↦ ?_⟩
  have hs128 : s ≤ 128 := by
    simp only [fillSizes, List.mem_cons, List.not_mem_nil, or_false] at hs
    omega
  obtain ⟨p, hb, hd, hc⟩ := h t
  refine ⟨p + (128 - s), by omega, fun i hi ↦ ?_, ?_⟩
  · rw [show p + (128 - s) + i = p + (128 - s + i) by omega]
    exact hd _ (by omega)
  · rwa [show p + (128 - s) + s = p + 128 by omega]

/-- The slots of the bytecode that hold the closing jump of a fill block. -/
def closeSlots (prog : Program) : List ℕ :=
  (List.range (2 ^ prog.logSize)).filter fun q ↦ decide (codeAt prog q = some fillClose)

/-- Whether every table has a fill block of size `128`: one pass to collect the closing jumps,
then, per table, a check of the `128` slots before one of them. -/
def hasFillBlocksB (prog : Program) : Bool :=
  let closes := closeSlots prog
  fillTables.all fun t ↦ closes.any fun q ↦ decide (128 ≤ q) && isFillBlockB prog t 128 (q - 128)

/-- **The pass decides the fill blocks.** -/
theorem hasFillBlocksB_eq_true_iff (prog : Program) :
    hasFillBlocksB prog = true ↔ HasFillBlocks prog := by
  rw [hasFillBlocks_iff_largest]
  simp only [hasFillBlocksB, closeSlots, List.all_eq_true, List.any_eq_true, List.mem_filter,
    List.mem_range, Bool.and_eq_true, decide_eq_true_eq, isFillBlockB_iff]
  constructor
  · intro h t
    obtain ⟨q, -, h128, hq⟩ := h t (mem_fillTables t)
    exact ⟨_, hq⟩
  · intro h t _
    obtain ⟨p, hp⟩ := h t
    have hb := hp.below
    refine ⟨p + 128, ⟨by omega, ?_⟩, by omega, by rwa [Nat.add_sub_cancel]⟩
    rw [← fetch_gpow_eq_codeAt prog (by omega)]
    exact hp.close

/-- Whether the bytecode is well formed: the sentinel slot is not a `JUMP`, and the fill blocks
are present. -/
def wellFormedB (prog : Program) : Bool :=
  decide (SentinelSafe prog) && hasFillBlocksB prog

/-- **The check decides well formed bytecode.** -/
theorem wellFormedB_eq_true_iff (prog : Program) :
    wellFormedB prog = true ↔ WellFormedBytecode prog := by
  rw [wellFormedB, Bool.and_eq_true, decide_eq_true_eq, hasFillBlocksB_eq_true_iff]
  exact ⟨fun ⟨h1, h2⟩ ↦ ⟨h1, h2⟩, fun ⟨h1, h2⟩ ↦ ⟨h1, h2⟩⟩

/-- Well formed bytecode is decided by `wellFormedB`. -/
instance (prog : Program) : Decidable (WellFormedBytecode prog) :=
  decidable_of_iff _ (wellFormedB_eq_true_iff prog)

/-! ## Traces that fit -/

/-- The `JUMP` table can be filled exactly when the search finds an exponent. -/
theorem jumpFeasible_iff (owed : ℕ) : JumpFeasible owed ↔ (jumpHeight owed).isSome := by
  refine ⟨jumpHeight_isSome, fun h ↦ ?_⟩
  obtain ⟨τ, hτ⟩ := Option.isSome_iff_exists.mp h
  exact ⟨τ, jumpHeight_spec hτ⟩

/-- Feasibility of the `JUMP` table is decided by `jumpHeight`. -/
instance (owed : ℕ) : Decidable (JumpFeasible owed) :=
  decidable_of_iff _ (jumpFeasible_iff owed).symm

/-- Whether a trace of memory log-size `κ` whose run has `rows op` rows of each table `op` fits:
room above the image, every table but `JUMP` within the row cap, and the `JUMP` table feasible. -/
def fitsRowsB (κ : ℕ) (rows : Opcode → ℕ) : Bool :=
  decide (κ < maxLogMem) &&
    fillTables.all (fun op ↦ decide (op = .jump) ||
      decide (fillTarget (rows op) (minRows op) ≤ 2 ^ maxLogRows)) &&
    (jumpHeight (jumpOwed rows)).isSome

/-- **The check decides `Fits` from the run's rows.** -/
theorem fitsRowsB_eq_true_iff {prog : Program} (t : Trace prog) :
    fitsRowsB t.κ t.runRows = true ↔ t.Fits := by
  simp only [fitsRowsB, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, List.all_eq_true,
    ← jumpFeasible_iff]
  constructor
  · rintro ⟨⟨hroom, hrows⟩, hjump⟩
    exact ⟨hroom, fun op hop ↦ (hrows op (mem_fillTables op)).resolve_left hop, hjump⟩
  · rintro ⟨hroom, hrows, hjump⟩
    refine ⟨⟨hroom, fun op _ ↦ ?_⟩, hjump⟩
    by_cases hop : op = .jump
    · exact .inl hop
    · exact .inr (hrows op hop)

end
end LeanerVM.Semantics
