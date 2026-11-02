import Sphincs.H0MomCert

/-! **The moment tables' stages, for the kernel.** `P1Q`, `P2Q` and `PHQ` read the stages `μL`, `hL`,
`νL` and `gL` of `H0MomCert.lean`, each a map over `n ≤ 150`. Evaluated within one table, every
stage is evaluated again for it, and its memory adds to the table's. So each stage is checked
once against a literal table of its own (`H0PTab/`: `μL = μTab`, `hL = hTab`, `νL = νTab`,
`gL = gTab`), and the next stage reads that literal: `νQOf hTab`, `gQOf μTab`, `P1QOf μTab`,
`P2QOf νTab gTab`, `PHQOf μTab`, the same functions of the table they read (`νQ_eq_of`, …, by
`rfl`). A table too large for one declaration is checked in ranges of rows, joined by
`map_range_chunks`. -/

namespace SphincsLayered.Security.H0

open SphincsFors.Security.H0

/-- `νQ`, reading `h` for `hL`. -/
def νQOf (h : List ℚ) (i : ℕ) : ℚ :=
  rup (1 / 8 * ((List.range (i + 1)).map fun u => binQ i u (1 / 8) (7 / 8) * f2Q u).sum +
    7 / 8 * ((List.range (i + 1)).map fun s => binQ i s (1 / 8) (6 / 8) * h.getD s 0).sum) 128

theorem νQ_eq_of : νQ = νQOf hL := rfl

/-- `gQ`, reading `μ` for `μL`. -/
def gQOf (μ : List ℚ) (s : ℕ) : ℚ :=
  rup (((List.range (s + 1)).map fun i => (chooseF s i : ℚ) * μ.getD i 0 ^ 2 * μ.getD (s - i) 0 ^ 2).sum) 128

theorem gQ_eq_of : gQ = gQOf μL := rfl

/-- `P1Q`, reading `μ` for `μL`. -/
def P1QOf (μ : List ℚ) (n : ℕ) : ℚ :=
  rup (((List.range (n + 1)).map fun i => binQ n i (1 / 16) (15 / 16) * μ.getD i 0 ^ 2).sum) 128

theorem P1Q_eq_of : P1Q = P1QOf μL := rfl

/-- `P2Q`, reading `ν` and `g` for `νL` and `gL`. -/
def P2QOf (ν g : List ℚ) (n : ℕ) : ℚ :=
  rup (1 / 16 * ((List.range (n + 1)).map fun i => binQ n i (1 / 16) (15 / 16) * ν.getD i 0 ^ 2).sum +
    15 / 16 * ((List.range (n + 1)).map fun s => binQ n s (1 / 16) (14 / 16) * g.getD s 0).sum) 128

theorem P2Q_eq_of : P2Q = P2QOf νL gL := rfl

/-- The bound of `ΨH(n)` (`PHQ`, `H0NTab.lean`), reading `μ` for `μL`. -/
def PHQOf (μ : List ℚ) (n : ℕ) : ℚ :=
  rup (((List.range (n + 1)).map fun i => binQ n i (1 / 16) (15 / 16) * μ.getD i 0).sum) 128

/-- A table checked in two ranges of rows, `[0, m)` and `[m, m + k)`. -/
theorem map_range_chunks {α : Type} (f : ℕ → α) (L : List α) (m k : ℕ)
    (h1 : (List.range' 0 m).map f = L.take m) (h2 : (List.range' m k).map f = L.drop m) :
    (List.range (m + k)).map f = L := by
  rw [List.range_eq_range', ← List.range'_append, List.map_append, Nat.zero_add, Nat.one_mul, h1, h2,
    List.take_append_drop]

end SphincsLayered.Security.H0
