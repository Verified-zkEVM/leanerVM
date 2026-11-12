/-
  LeanerVM.Protocol.LeanIsa.ExecutionStack

  The stack of an execution: the sizes of the witness the generator returns for a valid
  execution, when leanVM's stack at those sizes fits, and a check that decides it.
-/

module

public import LeanerVM.Protocol.LeanIsa
public import LeanerVM.Arithmetization.HypothesisChecks

/-!
# The stack of an execution

The generated witness has memory log-size `t.κ + 1` and each table at its filled height
(`sizes_witnessGen`, `execSizes`), so the stack's height is a formula of `t.κ`, the run's rows and
the `JUMP` exponent (`LeanIsa.blocks_total_eq`). `StackFits prog t` says it is at most `2^maxMu`.

* `StackFits` is exactly the condition `prove` needs on the generated witness's sizes
  (`stackFits_iff`).
* It fails from `t.κ ≥ 25` on (`not_stackFits_of_le`: the four memory columns alone hold
  `2^(t.κ+3) ≥ 2^28` cells, and the bytecode column is more), and holds when `t.κ ≤ 24`, the
  program has at most `2^25` slots and the run at most `2^16` steps (`StackFits.of_short`).
* It implies `Trace.Fits` (`StackFits.fits`), so a theorem that assumes it needs no `Fits`.
* `stackFitsB` decides it on a valid execution (`stackFitsB_eq_true_iff`) by one forward pass,
  after the constant-time bounds `t.κ ≤ 24` and `prog.logSize ≤ 27` (`StackFits.bounds`), so that
  no table of powers is built for a trace whose memory or bytecode alone is too large.
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Arithmetization LeanIsa
open Air.Flat (EnsembleWitness)

@[expose] public section

/-- The sizes of the witness `witnessGen` returns for a trace of memory log-size `κ` whose run
has `rows op` rows of each table, at the `JUMP` exponent `τ`: memory log-size `κ + 1`, each
opcode table at its filled log-height. -/
def execSizes (κ : ℕ) (rows : Opcode → ℕ) (τ : ℕ) : Sizes :=
  ⟨κ + 1, Nat.succ_pos κ, fun j ↦ tableLog rows τ (fillTables.getD j .xor)⟩

/-- **The sizes of the generated witness.** On a valid execution, the witness `witnessGen`
returns has the sizes `execSizes` of the trace's memory log-size, the run's rows and the `JUMP`
exponent `jumpHeight t.owed`. -/
theorem sizes_witnessGen {prog : Program} {input : PublicInput} {t : Trace prog}
    {w : EnsembleWitness (leanIsaEnsemble prog (t.κ + 1))}
    (h : ValidExecution prog input t) (hw : witnessGen prog input t = some w) :
    ∃ τ, jumpHeight t.owed = some τ ∧ Sizes.ofWitness w = some (execSizes t.κ t.runRows τ) := by
  obtain ⟨τ, hτ, hl⟩ := witnessGen_heights h hw
  refine ⟨τ, hτ, ?_⟩
  unfold Sizes.ofWitness
  rw [dite_eq_left (Nat.succ_pos _)]
  simp only [execSizes, Option.some.injEq, Sizes.mk.injEq, true_and]
  funext j
  rw [hl j, tableHeight_eq_pow, Nat.log_pow (by norm_num)]

/-- **The stack of an execution fits**: the `JUMP` table can be filled, at the exponent
`jumpHeight t.owed`, and the sizes `execSizes` of the generated witness keep leanVM's stack
within `2^maxMu` cells, which `prove` needs to return a proof. A predicate on the trace: the
stack's height is `LeanIsa.blocks_total_eq` at these sizes. -/
def StackFits (prog : Program) (t : Trace prog) : Prop :=
  ∃ τ, jumpHeight t.owed = some τ ∧ leanIsaμ prog (execSizes t.κ t.runRows τ) ≤ maxMu

/-- **No stack fits from `t.κ ≥ 25` on**: the generated memory has log-size `t.κ + 1`, so its four
columns alone hold `2^(t.κ+3) ≥ 2^28` cells, and the bytecode column is one more block. -/
theorem not_stackFits_of_le {prog : Program} {t : Trace prog} (h : 25 ≤ t.κ) :
    ¬ StackFits prog t := by
  rintro ⟨τ, -, hμ⟩
  rw [leanIsaμ_le_iff, blocks_total_eq] at hμ
  have hm : 2 ^ 28 ≤ 4 * 2 ^ (t.κ + 1) := by
    rw [show 4 * 2 ^ (t.κ + 1) = 2 ^ (t.κ + 3) by ring]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hb := Nat.one_le_two_pow (n := prog.logSize)
  simp only [execSizes, maxMu, pow_add] at hμ hm
  omega

/-- A stack that fits bounds the memory and the bytecode alone: `t.κ ≤ 24` and
`prog.logSize ≤ 27`. -/
theorem StackFits.bounds {prog : Program} {t : Trace prog} (h : StackFits prog t) :
    t.κ ≤ 24 ∧ prog.logSize ≤ 27 := by
  refine ⟨Nat.le_of_not_lt fun hc ↦ not_stackFits_of_le hc h, Nat.le_of_not_lt fun hc ↦ ?_⟩
  obtain ⟨τ, -, hμ⟩ := h
  rw [leanIsaμ_le_iff, blocks_total_eq] at hμ
  have hb : 2 ^ 28 ≤ 2 ^ prog.logSize := Nat.pow_le_pow_right (by norm_num) hc
  have hm := Nat.one_le_two_pow (n := t.κ)
  simp only [execSizes, maxMu, pow_add] at hμ
  omega

/-- **A stack that fits makes a trace that fits**: the memory, at most `2^25` cells, leaves room;
every opcode table has at least eight columns, so its filled height is at most `2^25` rows; and
the `JUMP` exponent is found. -/
theorem StackFits.fits {prog : Program} {t : Trace prog} (h : StackFits prog t) : t.Fits := by
  have hκ := h.bounds.1
  obtain ⟨τ, hτ, hμ⟩ := h
  obtain ⟨hτm, h1, h2⟩ := jumpHeight_spec hτ
  rw [leanIsaμ_le_iff, blocks_total_eq] at hμ
  simp only [execSizes, maxMu] at hμ
  change 4 * 2 ^ (t.κ + 1) + 2 ^ prog.logSize + 2 ^ (8 + tableLog t.runRows τ .blake2s) +
    15 * 2 ^ tableLog t.runRows τ .xor + 15 * 2 ^ tableLog t.runRows τ .mulNative +
    8 * 2 ^ tableLog t.runRows τ .setConstant + 15 * 2 ^ tableLog t.runRows τ .deref +
    14 * 2 ^ tableLog t.runRows τ .jump + 19 * 2 ^ tableLog t.runRows τ .blake2s ≤ 2 ^ 28 at hμ
  have hp : ∀ op, op ≠ .jump →
      fillTarget (t.runRows op) (minRows op) = 2 ^ tableLog t.runRows τ op := by
    intro op hop
    rw [← tableHeight_eq_pow]
    simp [tableHeight, hop]
  have h32 : (268435456 : ℕ) ≤ 2 ^ maxLogRows := by decide
  refine ⟨by unfold maxLogMem; omega, fun op hop ↦ ?_, ⟨τ, hτm, h1, h2⟩⟩
  rw [hp op hop]
  generalize 2 ^ maxLogRows = R at h32 ⊢
  generalize hx : 2 ^ tableLog t.runRows τ .xor = x at hμ
  generalize hm : 2 ^ tableLog t.runRows τ .mulNative = m at hμ
  generalize hs : 2 ^ tableLog t.runRows τ .setConstant = sc at hμ
  generalize hd : 2 ^ tableLog t.runRows τ .deref = dd at hμ
  generalize hb : 2 ^ tableLog t.runRows τ .blake2s = bb at hμ
  generalize 2 ^ tableLog t.runRows τ .jump = jj at hμ
  generalize 2 ^ (8 + tableLog t.runRows τ .blake2s) = ff at hμ
  generalize 2 ^ prog.logSize = pl at hμ
  generalize 2 ^ (t.κ + 1) = X at hμ
  cases op
  · rw [hx]; norm_num at hμ; omega
  · rw [hm]; norm_num at hμ; omega
  · rw [hs]; norm_num at hμ; omega
  · rw [hd]; norm_num at hμ; omega
  · exact absurd rfl hop
  · rw [hb]; norm_num at hμ; omega

/-- **A short run's stack fits**: a run of at most `2^16` steps over a memory of log-size at most
`24`, of a program of at most `2^25` slots. A sufficient condition, so `25` is the exact bound on
`t.κ`. -/
theorem StackFits.of_short {prog : Program} {t : Trace prog} {rf : Regs K}
    (h : run prog t.image t.steps Regs.initial = some rf) (hκ : t.κ ≤ 24)
    (hL : prog.logSize ≤ 25) (hs : t.steps ≤ 2 ^ 16) : StackFits prog t := by
  have hrows : ∀ op, t.runRows op ≤ 2 ^ 16 := fun op ↦ (t.runRows_le_steps h op).trans hs
  have howed : t.owed ≤ 2 ^ 17 :=
    (jumpOwed_le (rows := t.runRows) (k := 16) (by norm_num) hrows).trans (by norm_num)
  obtain ⟨τ, hτ⟩ := Option.isSome_iff_exists.mp
    (jumpHeight_isSome (jumpFeasible_of_le (howed.trans (by norm_num))))
  have hτ18 : τ ≤ 18 := jumpHeight_le hτ howed
  have hlog : ∀ op, op ≠ .jump → tableLog t.runRows τ op ≤ 16 := fun op hop ↦ by
    simp only [tableLog, hop, ↓reduceIte]
    rw [Nat.clog_le_iff_le_pow (by norm_num)]
    refine max_le (max_le (hrows op) ?_) (by norm_num)
    cases op <;> simp [minRows]
  refine ⟨τ, hτ, ?_⟩
  rw [leanIsaμ_le_iff, blocks_total_eq]
  have p : ∀ {a b : ℕ}, a ≤ b → 2 ^ a ≤ 2 ^ b := fun h ↦ Nat.pow_le_pow_right (by norm_num) h
  have e0 := p (hlog .xor (by decide))
  have e1 := p (hlog .mulNative (by decide))
  have e2 := p (hlog .setConstant (by decide))
  have e3 := p (hlog .deref (by decide))
  have e4 : 2 ^ tableLog t.runRows τ .jump ≤ 2 ^ 18 := p (by simpa [tableLog] using hτ18)
  have e5 := p (hlog .blake2s (by decide))
  have e8 : 2 ^ (8 + tableLog t.runRows τ .blake2s) ≤ 2 ^ 24 :=
    p (by have := hlog .blake2s (by decide); omega)
  have em : 4 * 2 ^ (t.κ + 1) ≤ 2 ^ 27 := by
    rw [show 4 * 2 ^ (t.κ + 1) = 2 ^ (t.κ + 3) by ring]
    exact p (by omega)
  have eb := p hL
  simp only [execSizes, maxMu]
  change 4 * 2 ^ (t.κ + 1) + 2 ^ prog.logSize + 2 ^ (8 + tableLog t.runRows τ .blake2s) +
    15 * 2 ^ tableLog t.runRows τ .xor + 15 * 2 ^ tableLog t.runRows τ .mulNative +
    8 * 2 ^ tableLog t.runRows τ .setConstant + 15 * 2 ^ tableLog t.runRows τ .deref +
    14 * 2 ^ tableLog t.runRows τ .jump + 19 * 2 ^ tableLog t.runRows τ .blake2s ≤ 2 ^ 28
  norm_num at e0 e1 e2 e3 e4 e5 e8 em eb ⊢
  omega

/-- Whether the stack of a trace of memory log-size `κ` whose run has `rows op` rows of each
table fits. -/
def stackFitsRowsB (prog : Program) (κ : ℕ) (rows : Opcode → ℕ) : Bool :=
  match jumpHeight (jumpOwed rows) with
  | some τ => decide (leanIsaμ prog (execSizes κ rows τ) ≤ maxMu)
  | none => false

/-- The check decides `StackFits` from the run's rows. -/
theorem stackFitsRowsB_eq_true_iff {prog : Program} (t : Trace prog) :
    stackFitsRowsB prog t.κ t.runRows = true ↔ StackFits prog t := by
  unfold stackFitsRowsB StackFits Trace.owed
  rcases jumpHeight (jumpOwed t.runRows) with _ | τ <;> simp

/-- Whether the stack of a trace fits: first the bounds `StackFits.bounds`, in constant time,
then the run's rows counted by the generator's forward pass, through a table of powers as large
as the address space. -/
def stackFitsB (prog : Program) (t : Trace prog) : Bool :=
  decide (t.κ ≤ 24 ∧ prog.logSize ≤ 27) &&
    stackFitsRowsB prog t.κ
      (countsOf (runCountTableBy prog t (powTable (2 ^ max t.κ prog.logSize))))

/-- **The check decides `StackFits` on a valid execution.** -/
theorem stackFitsB_eq_true_iff {prog : Program} {input : PublicInput} {t : Trace prog}
    (h : ValidExecution prog input t) : stackFitsB prog t = true ↔ StackFits prog t := by
  rw [stackFitsB, countsOf_runCountTableBy h, Bool.and_eq_true, decide_eq_true_eq,
    stackFitsRowsB_eq_true_iff]
  exact ⟨And.right, fun hs ↦ ⟨hs.bounds, hs⟩⟩

/-- **`StackFits` is the stack of the generated witness fitting**: for well-formed bytecode and
a valid execution, it holds exactly when the generator returns a witness whose sizes keep the
stack within `2^maxMu`, the condition of `prove_ne_none` and `honestGame_rom_rejects_le`. -/
theorem stackFits_iff {prog : Program} {input : PublicInput} {t : Trace prog}
    (hwf : WellFormedBytecode prog) (ht : ValidExecution prog input t) :
    StackFits prog t ↔ ∃ w s, witnessGen prog input t = some w ∧ Sizes.ofWitness w = some s ∧
      leanIsaμ prog s ≤ maxMu := by
  constructor
  · rintro hst
    obtain ⟨w, hw, -⟩ := witnessGen_correct hwf ht hst.fits
    obtain ⟨τ, hτ, hs⟩ := sizes_witnessGen ht hw
    obtain ⟨τ', hτ', hμ⟩ := hst
    obtain rfl := Option.some.inj (hτ.symm.trans hτ')
    exact ⟨w, _, hw, hs, hμ⟩
  · rintro ⟨w, s, hw, hs, hμ⟩
    obtain ⟨τ, hτ, hs'⟩ := sizes_witnessGen ht hw
    obtain rfl := Option.some.inj (hs'.symm.trans hs)
    exact ⟨τ, hτ, hμ⟩

end

end LeanerVM.Protocol
