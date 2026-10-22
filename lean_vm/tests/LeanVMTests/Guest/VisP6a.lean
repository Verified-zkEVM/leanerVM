import LeanVM.E2E.Vis.Bound

/-!
# Tests: W-vis P6a, the bound on the bad events with the visible accounting

`LeanVM.E2E.Vis.Bound`: the chain's bad events (`AggBadV`: T1's, W6's and E5's at the final log,
T3 restricted to non-hidden entries, the statement's format event) have probability at most
`visError Q_v Q (n_x + n_s)` in the game with V_I's trace. The examples check the error's shape
and the bound's form at the deployed guest; the pins check that the theorems rest on Lean's three
standard axioms only.
-/

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Blake2sHash LeanVM.Protocol.EndToEnd.Sound
open LeanVM.E2E OracleComp
open scoped ENNReal

/-- With no query, the error is the format event's and the failure terms' zero. -/
example (n : ℕ) : visError 0 0 n = 0 := by simp [visError]

/-- The visible rate is T1's `2^-128` plus W6's `2/2^192`; the format event's rate counts every
key's `2^64` addresses and the parameter derivation. -/
example (Qv Q n : ℕ) : visError Qv Q n =
    Qv * (εLean + 2 / 2 ^ 192) + Q * (14 / 2 ^ 192) + Qv * (Qv + 1) / 2 ^ 193 +
      Q * (failBound leanVmSeeds (Q + 1) + 4 * (Q + 2) / 2 ^ 256 + 4 * (Q + 1) / 2 ^ 256 +
        (n * 2 ^ 64 + 1) / 2 ^ 256) := rfl

/-- The tight form is below the plan's. -/
example (Qv Q n : ℕ) : visErrorTight Qv Q n ≤ visError Qv Q n := visErrorTight_le_visError Qv Q n

/-- `AggBadV` is P5's events, `PredS` at the guest's offset, and `FormatT`. -/
example {nx ns : ℕ} [Sphincs.Params] (keys : Keys nx ns) (ℓ : Log) :
    AggBadV keys ℓ ↔ AggBadT ℓ ∨ PredS keys
      (predOffset (LeanVM.bytecodeWords LeanVM.Guest.guest)) ℓ ∨
      FormatT keys ℓ := Iff.rfl

/-- A hidden prefix is one of at most `n · 2^64 + 1` digests. -/
example {nx ns : ℕ} [Sphincs.Params] (keys : Keys nx ns) :
    ∑ u : Digest, ind (InPfx keys u) ≤ (((nx + ns) * 2 ^ 64 + 1 : ℕ) : ℝ≥0∞) :=
  sum_ind_inPfx_le keys

/-- info: 'LeanVM.E2E.avg_ind_fail_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.avg_ind_fail_le

/-- info: 'LeanVM.E2E.digestBytes_drop16_take8' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.digestBytes_drop16_take8

/-- info: 'LeanVM.E2E.sum_ind_addrPfx_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.sum_ind_addrPfx_le

/-- info: 'LeanVM.E2E.sum_ind_inPfx_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.sum_ind_inPfx_le

/-- info: 'LeanVM.E2E.formatI_append_cases' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.formatI_append_cases

/-- info: 'LeanVM.E2E.avg_ind_formatI_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.avg_ind_formatI_le

/-- info: 'LeanVM.E2E.length_le_of_mem_support_runGame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.length_le_of_mem_support_runGame

/-- info: 'LeanVM.E2E.prEvent_runGame_le_budgeted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.prEvent_runGame_le_budgeted

/-- info: 'LeanVM.E2E.prEvent_runGame_le_lin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.prEvent_runGame_le_lin

/-- info: 'LeanVM.E2E.lintegral_keygenPhase_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.lintegral_keygenPhase_le

/-- info: 'LeanVM.E2E.KgPre.append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.KgPre.append

/-- info: 'LeanVM.E2E.prEvent_runGame_t1_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.prEvent_runGame_t1_le

/-- info: 'LeanVM.E2E.prEvent_runGame_w6_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.prEvent_runGame_w6_le

/-- info: 'LeanVM.E2E.prEvent_runGame_e5_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.prEvent_runGame_e5_le

/-- info: 'LeanVM.E2E.prEvent_runGame_fmt_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.prEvent_runGame_fmt_le

/-- info: 'LeanVM.E2E.prEvent_runGame_t3_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.prEvent_runGame_t3_le

/-- info: 'LeanVM.E2E.visErrorTight_le_visError' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.visErrorTight_le_visError

/-- info: 'LeanVM.E2E.prEvent_gameRec_aggBadV_le_tight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.prEvent_gameRec_aggBadV_le_tight

/-- info: 'LeanVM.E2E.prEvent_gameRec_aggBadV_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.prEvent_gameRec_aggBadV_le

/-- info: 'LeanVM.E2E.rankOK_of_not_aggBadV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.rankOK_of_not_aggBadV

/-- info: 'LeanVM.E2E.not_aggBadT_of_not_aggBadV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.not_aggBadT_of_not_aggBadV
