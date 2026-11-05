/-
  LeanerVM.Arithmetization.HypothesisChecks

  A trace that fits, decided from its execution by the generator's forward pass.
-/

module

public import LeanerVM.Semantics.HypothesisChecks
public import LeanerVM.Arithmetization.WitnessGen

/-!
# Deciding that a trace fits

leanISA roadmap Layer 10 companion (`docs/architecture.md`, `T2`). `Trace.Fits` reads the rows of
the run (`Trace.runRows`), which are defined from the run's register sequence and the reference
fetch and so cannot be evaluated. `fitsBy prog t P` counts them instead with the witness
generator's forward pass (`runSkelsBy`, read through the table of powers `P`, whose index guesses
are checked) and decides `Fits` from the counts (`fitsRowsB`). On a valid execution the counts are
the run's rows (`runSkelsBy_eq_runSkels`), so the check decides `Fits` for every table
(`fitsBy_eq_true_iff`).
-/

namespace LeanerVM.Arithmetization

open LeanerVM.Parameters LeanerVM.Semantics

@[expose] public section

/-- The rows of each table in the run of `t`, counted by one forward pass through the table of
powers `P`: entry `tableIdx op` for `op` (read with `countsOf`). An array, not a function, so that
compiled code steps the run once. -/
def runCountTableBy (prog : Program) (t : Trace prog) (P : PowTable) : Array ℕ :=
  skelCountTable (runSkelsBy (fetchBy prog P) (executeWith (readBy t.image P))
    t.steps Regs.initial #[]).toList

/-- Whether the trace fits, from the rows counted by the forward pass. -/
def fitsBy (prog : Program) (t : Trace prog) (P : PowTable) : Bool :=
  fitsRowsB t.κ (countsOf (runCountTableBy prog t P))

/-- On a valid execution the forward pass counts the run's rows, whatever the table. -/
theorem countsOf_runCountTableBy {prog : Program} {input : PublicInput} {t : Trace prog}
    (h : ValidExecution prog input t) (P : PowTable) :
    countsOf (runCountTableBy prog t P) = t.runRows := by
  have hκ64 : t.κ < 64 := lt_of_le_of_lt h.1.2.1 (by decide)
  rw [runCountTableBy, runSkelsBy_eq_runSkels h.2 (funext (fetchBy_eq_fetch prog P))
    (executeWith_readBy hκ64 t.image P), countsOf_skelCountTable]
  funext op
  exact t.count_runSkels op

/-- **The check decides `Fits` on a valid execution**, for every table of powers. -/
theorem fitsBy_eq_true_iff {prog : Program} {input : PublicInput} {t : Trace prog}
    (h : ValidExecution prog input t) (P : PowTable) :
    fitsBy prog t P = true ↔ t.Fits := by
  rw [fitsBy, countsOf_runCountTableBy h P]
  exact fitsRowsB_eq_true_iff t

/-- Whether the trace fits, reading addresses through one table of powers. -/
def fitsB (prog : Program) (t : Trace prog) : Bool :=
  fitsBy prog t (powTable (2 ^ max t.κ prog.logSize))

/-- **The check decides `Fits` on a valid execution.** -/
theorem fitsB_eq_true_iff {prog : Program} {input : PublicInput} {t : Trace prog}
    (h : ValidExecution prog input t) : fitsB prog t = true ↔ t.Fits :=
  fitsBy_eq_true_iff h _

end
end LeanerVM.Arithmetization
