/-
  LeanerVM.Parameters.Whir

  leanVM's WHIR parameters: the fold factors, the rate schedule, the residual size, the grinding
  budget, the stacking window, the tabulated query counts, and the ladder of levels an opening of
  a given size and rate runs.
-/

module

public import Mathlib.Data.Nat.Notation

/-!
# WHIR parameters

Category B. The constants are transcribed from `crates/pcs/src/whir_config.rs:38-86` of the
pinned leanVM (`a386121f84292f6fa663aaa3e570c15bc0240ea2`), the ladder geometry from its
`derive_ladder` and `derive_ladder_shape` (`:260-311`), the stacking window from
`crates/lean_vm/src/pcs.rs:49-51`, and the query counts from the second verifier,
`python-verifier/verifier.py:900-935` (`WHIR_QUERIES`, `derive_config`). The specification
describes the protocol these parameters instantiate (Annex B, Protocol B.1,
`doc/leanvm/body/b-polynomial-commitment-scheme.tex`) and gives no numbers.

An opening of a stack of `2^μ` elements of `K` at rate `2^-R` runs a *ladder* of levels. Level 0
folds `initialFold = 6` variables; every later level folds `subsequentFold = 4`, or what remains,
until at most `residualMaxLog = 5` variables remain, which are sent in the clear. The rate
exponent of a level is the previous one plus the previous fold minus a domain reduction,
`initialReduction = 3` after level 0 and `subsequentReduction = 1` after every later level. Each
level opens `queries` positions after `queryGrindingBits = 17` bits of grinding; from level 1 on,
one out-of-domain sample binds the level's commitment (`oodSamples`).

The query counts are the Rust's *output*, not its derivation: `optimize_johnson_level`
(`whir_config.rs:639-707`) minimises the queries of each level subject to the 128-bit
round-by-round targets of Annex B's Theorem B.2 under a floating-point MCA formula, and this
module does not restate that search. The table is the one the Python verifier carries, indexed
by rate exponent `1..4` and stack size `15..28`; outside that window `ladder` is `none`, as both
verifiers reject (`validate_log_inv_rate`, `whir_config.rs:48-56`; `verifier.py:923`).

The Rust API takes the witness size as `m = μ + LOG_PACKING` bits, `LOG_PACKING = 6`
(`crates/pcs/src/pack.rs:7`); `ladder` takes the stack size `μ`, as the Python `derive_config`
does. `LOG_INV_RATE_0 = 1` (`whir_config.rs:41`) is the rate the Rust test suite proves at, not a
verifier parameter: the rate exponent is announced with the sizes.
-/

namespace LeanerVM.Parameters.Whir

@[expose] public section

/-! ## Constants (`whir_config.rs`) -/

/-- Variables folded at level 0: the lane fold (`INITIAL_FOLDING_FACTOR`, `whir_config.rs:67`). -/
def initialFold : ℕ := 6

/-- Variables folded at every later level (`SUBSEQUENT_FOLDING_FACTOR`, `whir_config.rs:68`). -/
def subsequentFold : ℕ := 4

/-- Bits the Reed–Solomon domain shrinks by after level 0, so that the rate exponent rises by
`initialFold - initialReduction` (`RS_DOMAIN_INITIAL_REDUCTION_FACTOR`, `whir_config.rs:73`). -/
def initialReduction : ℕ := 3

/-- Bits the domain shrinks by after every later level (`RS_DOMAIN_SUBSEQUENT_REDUCTION_FACTOR`,
`whir_config.rs:78`). -/
def subsequentReduction : ℕ := 1

/-- Folding stops once at most this many variables remain; the residual multilinear is sent in
the clear (`RESIDUAL_MAX_LOG`, `whir_config.rs:86`). -/
def residualMaxLog : ℕ := 5

/-- Grinding bits before each level's query positions are sampled (`QUERY_GRINDING_BITS`,
`whir_config.rs:60`). -/
def queryGrindingBits : ℕ := 17

/-- The round-by-round security target the query counts were derived for, in bits
(`SECURITY_BITS`, `whir_config.rs:38`). -/
def securityBits : ℕ := 128

/-- The smallest stack the PCS commits: `MIN_MU` (`pcs.rs:49`;
`MIN_STACKED_LOG`, `verifier.py:907`). A
smaller witness is padded up to it. -/
def minLogStack : ℕ := 15

/-- The largest stack the PCS commits: `MAX_MU` (`pcs.rs:51`;
`MAX_STACKED_LOG`, `verifier.py:908`). -/
def maxLogStack : ℕ := 28

/-- The smallest rate exponent of level 0 (`MIN_LOG_INV_RATE`, `whir_config.rs:44`). -/
def minLogInvRate : ℕ := 1

/-- The largest rate exponent of level 0 (`MAX_LOG_INV_RATE`, `whir_config.rs:45`). -/
def maxLogInvRate : ℕ := 4

/-- Out-of-domain samples taken after a level's commitment: none at level 0, whose commitment the
opening's own evaluation claim binds, and one at every later level (`whir_config.rs:108-115`).
The Rust production test fixes the count for stack sizes 22 to 28 (`whir_config.rs:1021, 1033`);
for 15 to 21 it is the second verifier's, which takes one sample per level after the first
(`verifier.py:1033-1037`). -/
def oodSamples (level : ℕ) : ℕ := if level = 0 then 0 else 1

/-- `whir_config.rs:80`: the first reduction never exceeds the first fold. -/
theorem initialReduction_le_initialFold : initialReduction ≤ initialFold := by decide

/-- `whir_config.rs:81`: a later reduction never exceeds a later fold. -/
theorem subsequentReduction_le_subsequentFold : subsequentReduction ≤ subsequentFold := by
  decide

/-- `whir_config.rs:92`: the residual is never longer than the lane fold. -/
theorem residualMaxLog_le_initialFold : residualMaxLog ≤ initialFold := by decide

/-! ## The ladder -/

/-- One level of an opening: the number of sumcheck rounds it folds (`ℓ_i`), the rate exponent
of the code its commitment is in (`R_i`), and the number of positions queried (`t_i`), in the
notation of Annex B. -/
structure Level where
  fold : ℕ
  logInvRate : ℕ
  queries : ℕ
  deriving DecidableEq

/-- The levels after the first, as pairs (fold, rate exponent): while more than `residualMaxLog`
variables remain, fold `subsequentFold` of them (or all that remain) at the rate exponent the
previous level's fold and the pending domain reduction give (`derive_ladder`,
`whir_config.rs:260-299`, with `derive_ladder_shape`'s rate rule, `:302-311`). `fuel` bounds the
recursion; every level folds at least one variable, so `remaining` fuel is enough. -/
def levelsFrom : (fuel remaining prevFold prevRate reduction : ℕ) → List (ℕ × ℕ)
  | 0, _, _, _, _ => []
  | fuel + 1, remaining, prevFold, prevRate, reduction =>
    if remaining ≤ residualMaxLog then []
    else
      let rate := prevRate + prevFold - reduction
      let fold := min subsequentFold remaining
      (fold, rate) :: levelsFrom fuel (remaining - fold) fold rate subsequentReduction

/-- The ladder geometry of a `μ`-variable stack at rate exponent `logInvRate`: level 0 folds
`initialFold` at that rate, then `levelsFrom` (`derive_config`, `verifier.py:920-935`). -/
def shape (μ logInvRate : ℕ) : List (ℕ × ℕ) :=
  (initialFold, logInvRate) ::
    levelsFrom μ (μ - initialFold) initialFold logInvRate initialReduction

/-- The variables left after every fold: the size of the residual sent in the clear. -/
def residualLog (μ logInvRate : ℕ) : ℕ := μ - ((shape μ logInvRate).map Prod.fst).sum

/-- The query counts `WHIR_QUERIES` of `verifier.py:910`, verbatim: row `R - 1` for the rate
exponent `R`, entry `μ - 15` for the stack size `μ`, one count per level. -/
def queryTable : List (List (List ℕ)) := [
  [[223, 55], [223, 56, 30], [223, 56, 31], [224, 56, 32], [224, 56, 32], [224, 56, 32, 22],
   [224, 56, 32, 22], [225, 56, 32, 23], [225, 56, 32, 23], [225, 56, 32, 23, 17],
   [226, 56, 32, 23, 17], [226, 56, 32, 23, 18], [227, 56, 32, 23, 18],
   [228, 56, 32, 23, 18, 14]],
  [[112, 45], [112, 45, 27], [112, 45, 28], [112, 45, 28], [112, 45, 28], [112, 45, 28, 20],
   [112, 45, 28, 20], [112, 45, 28, 21], [112, 45, 28, 21], [113, 45, 28, 21, 16],
   [113, 45, 28, 21, 16], [113, 45, 28, 21, 16], [113, 45, 28, 21, 16],
   [113, 45, 28, 21, 17, 13]],
  [[75, 37], [75, 37, 24], [75, 38, 25], [75, 38, 25], [75, 38, 25], [75, 38, 25, 18],
   [75, 38, 25, 19], [75, 38, 25, 19], [75, 38, 25, 19], [75, 38, 25, 19, 15],
   [75, 38, 25, 19, 15], [75, 38, 25, 19, 15], [75, 38, 25, 19, 15],
   [76, 38, 25, 19, 16, 13]],
  [[56, 32], [56, 32, 22], [56, 32, 22], [56, 32, 23], [56, 32, 23], [56, 32, 23, 17],
   [56, 32, 23, 17], [56, 32, 23, 18], [56, 32, 23, 18], [57, 32, 23, 18, 14],
   [57, 32, 23, 18, 14], [57, 32, 23, 18, 15], [57, 33, 23, 18, 15],
   [57, 33, 23, 18, 15, 12]]]

/-- The window the parameters are defined on: the stacking window and the rate range
(`verifier.py:923`; `cpu/mod.rs:130-178` checks the stack, `whir_config.rs:48-56` the rate). -/
def Admissible (μ logInvRate : ℕ) : Prop :=
  minLogStack ≤ μ ∧ μ ≤ maxLogStack ∧ minLogInvRate ≤ logInvRate ∧ logInvRate ≤ maxLogInvRate

instance {μ logInvRate : ℕ} : Decidable (Admissible μ logInvRate) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- The ladder of an admissible stack size and rate: the geometry of `shape` paired with the
tabulated query counts, level by level. `none` outside the window, and `none` if the table did
not have one count per level (`verifier.py:934`), so that no level is silently dropped. -/
def ladder (μ logInvRate : ℕ) : Option (List Level) :=
  if Admissible μ logInvRate then
    let geometry := shape μ logInvRate
    let queries := (queryTable.getD (logInvRate - minLogInvRate) []).getD (μ - minLogStack) []
    if geometry.length = queries.length then
      some (List.zipWith (fun (g : ℕ × ℕ) q ↦ ⟨g.1, g.2, q⟩) geometry queries)
    else none
  else none

/-- The log block lengths `κ_i + R_i` of the levels' codes: the message log after a level's fold
plus its rate exponent (`LevelShapes.block_len`, `whir_config.rs:124-159`). -/
def blockLogs (μ : ℕ) : List Level → List ℕ
  | [] => []
  | l :: rest => (μ - l.fold + l.logInvRate) :: blockLogs (μ - l.fold) rest

/-! ## Structure of the table

Each fact below is decided over the 56 admissible pairs; the general statement follows by
bounding the quantifiers. -/

private theorem admissible_bounded {μ logInvRate : ℕ} (h : Admissible μ logInvRate) :
    μ < maxLogStack + 1 ∧ logInvRate < maxLogInvRate + 1 := by
  obtain ⟨_, h2, _, h4⟩ := h
  exact ⟨Nat.lt_succ_of_le h2, Nat.lt_succ_of_le h4⟩

/-- The table has one query count per level of the geometry: `ladder` is defined on the whole
window. -/
theorem ladder_isSome {μ logInvRate : ℕ} (h : Admissible μ logInvRate) :
    (ladder μ logInvRate).isSome := by
  have key : ∀ μ < maxLogStack + 1, ∀ r < maxLogInvRate + 1, Admissible μ r → (ladder μ r).isSome :=
    by decide +kernel
  obtain ⟨h1, h2⟩ := admissible_bounded h
  exact key μ h1 logInvRate h2 h

/-- Every ladder has at least two levels (`whir_config.rs:291-293`). -/
theorem ladder_length {μ logInvRate : ℕ} (h : Admissible μ logInvRate) :
    ∀ levels, ladder μ logInvRate = some levels → 2 ≤ levels.length := by
  have key : ∀ μ < maxLogStack + 1, ∀ r < maxLogInvRate + 1, Admissible μ r →
      ∀ levels, ladder μ r = some levels → 2 ≤ levels.length := by decide +kernel
  obtain ⟨h1, h2⟩ := admissible_bounded h
  exact key μ h1 logInvRate h2 h

/-- The residual is at most `residualMaxLog` variables. -/
theorem residualLog_le {μ logInvRate : ℕ} (h : Admissible μ logInvRate) :
    residualLog μ logInvRate ≤ residualMaxLog := by
  have key : ∀ μ < maxLogStack + 1, ∀ r < maxLogInvRate + 1, Admissible μ r →
      residualLog μ r ≤ residualMaxLog := by decide +kernel
  obtain ⟨h1, h2⟩ := admissible_bounded h
  exact key μ h1 logInvRate h2 h

/-- Every level's code fits in `K`: its block length is at most `2^64` (Annex B, §B.2 requires
`κ_i + R_i ≤ 64`), and its query count is at most its block length (`whir_config.rs:673`). -/
theorem ladder_blocks {μ logInvRate : ℕ} (h : Admissible μ logInvRate) :
    ∀ levels, ladder μ logInvRate = some levels →
      ∀ p ∈ List.zip (blockLogs μ levels) levels, p.1 ≤ 64 ∧ p.2.queries ≤ 2 ^ p.1 := by
  have key : ∀ μ < maxLogStack + 1, ∀ r < maxLogInvRate + 1, Admissible μ r →
      ∀ levels, ladder μ r = some levels →
        (List.zip (blockLogs μ levels) levels).all
          (fun p ↦ decide (p.1 ≤ 64 ∧ p.2.queries ≤ 2 ^ p.1)) = true := by
    decide +kernel
  obtain ⟨h1, h2⟩ := admissible_bounded h
  intro levels hl p hp
  exact of_decide_eq_true ((List.all_eq_true.mp (key μ h1 logInvRate h2 h levels hl)) p hp)

end
end LeanerVM.Parameters.Whir
