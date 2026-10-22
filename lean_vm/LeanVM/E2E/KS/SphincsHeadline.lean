import LeanVM.E2E.Headline
import LeanVM.E2E.KS.Sphincs

/-!
# The leanSPHINCS part of the deployed game at a proved parameter set

`prEvent_knownForgedS_le_set`: at a proved leanSPHINCS parameter set (`SphincsSet`), with its
closed multi-user bound `n q / 2^127` (`SphincsSet.multi`), a known leanSPHINCS forgery in the
deployed game before verification has probability at most `n_s (q + 686) / 2^127`, `q` the game's
hash evaluations before verification (`preQueries`); `0` without leanSPHINCS keys.

`SphincsSet` lives in `Headline.lean`, which is not a module, so neither is this file.
-/

namespace LeanVM.E2E.KS

open LeanVM.E2E
open scoped ENNReal

/-- **A known leanSPHINCS forgery at a proved parameter set**: at most
`n_s (q + 686) / 2^127`, `q = preQueries n_x n_s qH sX sS`. -/
theorem prEvent_knownForgedS_le_set [P : Sphincs.Params] [S : SphincsSet P] {nx ns : ℕ}
    (A : DAdversary nx ns) {qH sX sS : ℕ} (hA : DAdvBounds A qH sX sS) :
    Pr{let z ← pGame A}[KnownForgedS z.1] ≤
      (ns : ℝ≥0∞) * (((preQueries nx ns qH sX sS + 686 : ℕ) : ℝ≥0∞) /
        ((2 ^ 127 : ℕ) : ℝ≥0∞)) :=
  prEvent_knownForgedS_le_rate (S.multi ns) A hA

end LeanVM.E2E.KS
