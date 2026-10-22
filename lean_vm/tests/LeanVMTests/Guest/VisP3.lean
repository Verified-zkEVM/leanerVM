import LeanVM.E2E.Vis.DaDecoder

/-!
# Tests: the decoder invariants of W-vis (P3a, P3b)

P3a (`LeanVM.E2E.Vis.Decoder`): without the format event, T1's and W6's decoders decode no hidden
prefix, so a fresh hidden query raises T1's potential and the batching's only by their failure
terms, and on the key-generation log both are at most the failure indicator. P3b
(`LeanVM.E2E.Vis.DaDecoder`): E5's potential, stopped at the format event, at its full rate for
every query. The examples instantiate the statements at the deployed seedings; the pins check
that the theorems rest on Lean's three standard axioms only.
-/

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Blake2sHash LeanVM.E2E
open scoped ENNReal

section Examples

variable {nx ns : ℕ} [Sphincs.Params] (keys : Keys nx ns)

/-- T1's hidden step at leanVM's seedings: the failure term has `4 + 1` per entry. -/
example (D : List Ev → Prop) (P : Prog Bool) {ℓ : Log} {k0 : ℕ}
    (hkg : ∀ (i : ℕ) (hi : i < ℓ.length), i < k0 → Hid keys ℓ[i].1) {t : Bytes}
    (ht : Hid keys t) (hfresh : t ∉ ℓ.map Prod.fst) :
    (∑ u, pot D EndToEnd.Sound.leanVmSeeds P (ℓ ++ [(t, u)]) *
        ind (¬ FormatI keys k0 (ℓ ++ [(t, u)]))) / Fintype.card Digest ≤
      pot D EndToEnd.Sound.leanVmSeeds P ℓ * ind (¬ FormatI keys k0 ℓ) +
        ((5 * (ℓ.length + 1) : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  refine (potStop_step_hid D _ P (seedsNotHid_leanVmSeeds keys) hkg ht hfresh).trans
    (le_of_eq ?_)
  rfl

/-- On the key-generation log, T1's potential at leanVM's seedings is only failure. -/
example (D : List Ev → Prop) (P : Prog Bool) {ℓ : Log} (hall : ∀ e ∈ ℓ, Hid keys e.1) :
    pot D EndToEnd.Sound.leanVmSeeds P ℓ ≤ ind (Fail EndToEnd.Sound.leanVmSeeds ℓ) :=
  pot_le_of_allHid D (seedsNotHid_leanVmSeeds keys) hall

/-- On the key-generation log, the batching's potential is only failure, for a start that is no
hidden prefix. -/
example {s0 : Digest} (hs0 : ¬ InPfx keys s0) (bytecode : List K) {ℓ : Log}
    (hall : ∀ e ∈ ℓ, Hid keys e.1) :
    batchPot s0 bytecode ℓ ≤ ind (Fail batchSeedsAll (startLog s0 ℓ)) :=
  batchPot_le_of_allHid hs0 bytecode hall

/-- A chain input from a state that is no hidden prefix is not hidden. -/
example {c : Digest} (hc : ¬ InPfx keys c) (x : E) (tag : ℕ) :
    ¬ Hid keys (digestBytes c ++ blockOf x tag) :=
  not_hid_chain_of_not_inPfx hc x tag

end Examples

example : paramPrefix.length = 32 := paramPrefix_length

/-- info: 'LeanVM.E2E.decode_info_not_inPfx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.decode_info_not_inPfx

/-- info: 'LeanVM.E2E.potStop_step_hid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.potStop_step_hid

/-- info: 'LeanVM.E2E.pot_le_of_allHid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.pot_le_of_allHid

/-- info: 'LeanVM.E2E.termSum_eq_zero_of_allHid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.termSum_eq_zero_of_allHid

/-- info: 'LeanVM.E2E.batchPotStop_step_hid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.batchPotStop_step_hid

/-- info: 'LeanVM.E2E.batchPot_le_of_allHid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.batchPot_le_of_allHid

/-- info: 'LeanVM.E2E.seedsNotHid_leanVmSeeds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.seedsNotHid_leanVmSeeds

/-- info: 'LeanVM.E2E.seedsNotHid_batchSeedsAll' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.seedsNotHid_batchSeedsAll

/-- info: 'LeanVM.E2E.daPotStop_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.daPotStop_step

/-- info: 'LeanVM.E2E.hid_of_daRootOf_hid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.hid_of_daRootOf_hid

/-- info: 'LeanVM.E2E.paramPrefix_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.paramPrefix_length
