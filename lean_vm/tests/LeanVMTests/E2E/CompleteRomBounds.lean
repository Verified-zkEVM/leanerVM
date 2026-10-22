import LeanVM.E2E.Complete.Rom.Bounds

/-!
# T6-prob's bounds, locked

Statement locks of `LeanVM/E2E/Complete/Rom/Bounds.lean` (`docs/roadmap/t6-prob.md` §4.5, §4.6,
P4): the error and its numbers, G1 from a failed proof-of-work search, the guest's `17` bits, the
two potentials' step and the engine at them; each at Lean's three axioms.
-/

open LeanVM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Rom
open LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Verifier
open LeanVM.E2E LeanVM.E2E.Complete
open OracleComp OracleSpec
open scoped ENNReal

/-! ## The error -/

example (Q pfuel : ℕ) : completeError Q pfuel =
    Q * (missProb 17 ^ pfuel + Q / 2 ^ 256) +
      Q * ((2 : ℝ≥0∞)⁻¹ ^ 192 + failBound batchSeedsAll (Q + 1)) := rfl

example {Q : ℕ} (hQ : Q ≤ 2 ^ 64) : completeError Q (2 ^ 25) ≤ (2 : ℝ≥0∞)⁻¹ ^ 124 :=
  completeError_le hQ

/-- info: 'LeanVM.E2E.Complete.completeError_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms completeError_le

example {Q Q' pfuel : ℕ} (h : Q ≤ Q') : completeError Q pfuel ≤ completeError Q' pfuel :=
  completeError_mono h

/-- info: 'LeanVM.E2E.Complete.completeError_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms completeError_mono

/-! ## G1 -/

example {ℓ : Log} {P : Prog Bool} {S : Strategy} {seed : Digest} {pfuel : ℕ}
    (hg : ∀ h b k, P.after h = some (.grind b k) → b = 17)
    (h : proveFromM (look ℓ) S pfuel P seed [] = some none) : 1 ≤ powPot 17 pfuel ℓ :=
  one_le_powPot_of_proveFromM hg h

/-- info: 'LeanVM.E2E.Complete.one_le_powPot_of_proveFromM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms one_le_powPot_of_proveFromM

example (bc : List K) (pd : Digest) :
    ∀ h b k, (blindProgram bc pd).after h = some (.grind b k) → b = 17 :=
  grind17_blindProgram bc pd

/-- info: 'LeanVM.E2E.Complete.grind17_blindProgram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms grind17_blindProgram

/-! ## The two potentials -/

attribute [local irreducible] instFintypeDigest in
example {pfuel : ℕ} (hpf : pfuel ≤ 2 ^ 64) {ℓ : Log} {t : Bytes} (ht : look ℓ t = none) :
    (∑ u, (powPot 17 pfuel (ℓ ++ [(t, u)]) + weightsPot (ℓ ++ [(t, u)]))) /
        Fintype.card Digest ≤
      (powPot 17 pfuel ℓ + weightsPot ℓ) +
        (missProb 17 ^ pfuel + ℓ.length / Fintype.card Digest +
          ((2 : ℝ≥0∞)⁻¹ ^ 192 + failBound batchSeedsAll (ℓ.length + 2))) :=
  sumPot_step hpf ht

/-- info: 'LeanVM.E2E.Complete.sumPot_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sumPot_step

example {α : Type} (oa : OracleComp HashSpec α) {Q pfuel : ℕ} (hpf : pfuel ≤ 2 ^ 64)
    (hQ : IsTotalQueryBound oa Q) (ev : α → Log → Prop)
    (hev : ∀ z ∈ support ((simulateQ loggedRO oa).run []), ev z.1 z.2 →
      1 ≤ powPot 17 pfuel z.2 + weightsPot z.2) :
    Pr{let z ← (simulateQ loggedRO oa).run []}[ev z.1 z.2] ≤ completeError Q pfuel :=
  prEvent_le_completeError oa hpf hQ ev hev

/-- info: 'LeanVM.E2E.Complete.prEvent_le_completeError' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms prEvent_le_completeError
