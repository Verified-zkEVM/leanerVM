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
fetch and so cannot be evaluated. `fitsBy prog t guess` counts them instead with the witness
generator's forward pass (`runSkelsBy`, read through the checked guess `guess`) and decides `Fits`
from the counts (`fitsRowsB`). On a valid execution the counts are the run's rows
(`runSkelsBy_eq_runSkels`), so the check decides `Fits` for every guess (`fitsBy_eq_true_iff`).
-/

namespace LeanerVM.Arithmetization

open LeanerVM.Parameters LeanerVM.Semantics

@[expose] public section

/-- The rows of each table in the run of `t`, counted by one forward pass through the guess: entry
`tableIdx op` for `op` (read with `countsOf`). A table, not a function, so that compiled code
steps the run once. -/
def runCountTableBy (prog : Program) (t : Trace prog) (guess : K → Option ℕ) : Array ℕ :=
  skelCountTable (runSkelsBy (fetchBy prog guess) (executeWith (readBy t.image guess))
    t.steps Regs.initial #[]).toList

/-- Whether the trace fits, from the rows counted by the forward pass. -/
def fitsBy (prog : Program) (t : Trace prog) (guess : K → Option ℕ) : Bool :=
  fitsRowsB t.κ (countsOf (runCountTableBy prog t guess))

/-- On a valid execution the forward pass counts the run's rows, whatever the guess. -/
theorem countsOf_runCountTableBy {prog : Program} {input : PublicInput} {t : Trace prog}
    (h : ValidExecution prog input t) (guess : K → Option ℕ) :
    countsOf (runCountTableBy prog t guess) = t.runRows := by
  have hκ64 : t.κ < 64 := lt_of_le_of_lt h.1.2.1 (by decide)
  rw [runCountTableBy, runSkelsBy_eq_runSkels h.2 (funext (fetchBy_eq_fetch prog guess))
    (executeWith_readBy hκ64 t.image guess), countsOf_skelCountTable]
  funext op
  exact t.count_runSkels op

/-- **The check decides `Fits` on a valid execution**, for every guess. -/
theorem fitsBy_eq_true_iff {prog : Program} {input : PublicInput} {t : Trace prog}
    (h : ValidExecution prog input t) (guess : K → Option ℕ) :
    fitsBy prog t guess = true ↔ t.Fits := by
  rw [fitsBy, countsOf_runCountTableBy h guess]
  exact fitsRowsB_eq_true_iff t

/-- Whether the trace fits, guessing addresses from one table of powers. -/
def fitsB (prog : Program) (t : Trace prog) : Bool :=
  fitsBy prog t (guessOf (powTable (2 ^ max t.κ prog.logSize)))

/-- **The check decides `Fits` on a valid execution.** -/
theorem fitsB_eq_true_iff {prog : Program} {input : PublicInput} {t : Trace prog}
    (h : ValidExecution prog input t) : fitsB prog t = true ↔ t.Fits :=
  fitsBy_eq_true_iff h _

end
end LeanerVM.Arithmetization
