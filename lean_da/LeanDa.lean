import LeanDa.Commitment
import LeanDa.Dual
import LeanDa.Security
import LeanDa.RpmSecurity
import LeanDa.RpmWagner
import PqDas

/-!
# LeanDA's security

Benedikt Wagner's theorems for his erasure code commitment from a vector commitment, a code
checker and an argument of knowledge (`PqDas`, ported from https://github.com/b-wagn/fv-pq-da; his
post: https://ethresear.ch/t/formally-verified-security-for-pq-das-leanda/25746), instantiated with LeanDA as `crates/lean_da` computes it, for
any number `r ≥ 1` of rows and any hash `H` (the crate's is Keccak-256): completeness, position
binding by reduction to a collision of `H`, and code binding with the membership test's
soundness `δ = 14 / 2^192` over `|E^14| = 2^2688` challenges. The argument `ps` and its extractor `ext` are parameters: knowledge soundness enters
as the probability that the explicit reduction `ksReduction` breaks it.

In the random-permutation model (`LeanDa.RpmSecurity`: `H` Keccak-256 over a random permutation
`π`, the challenges the deployed duplex over `π`, the adversary querying `π` and `π⁻¹`), position
binding holds with the bound `Q² / 2^256 + Q² / 2^508` for `Q` permutation calls
(`leanDa_positionBinding_rpm`), and code binding moves to the two-oracle random-oracle model
within `Q² / 2^508` (`leanDa_codeBinding_rpm`), where the duplex lemma (`LeanRpm.Duplex`) and
sampling `H` in advance give Wagner's bound, averaged over `H`, plus `2 (Q + 15)² / 2^576`
(`leanDa_codeBinding_rpm_bound`).
-/

open PqDas PqDas.CommittedSoundness OracleComp OracleSpec ENNReal

namespace LeanDa

variable (r : ℕ) (H : List UInt8 → Digest) {Crs Proof : Type} (ps : Argument r H Crs Proof)

/-- **Completeness**: with a perfectly complete argument, every cell of an honest commitment
opens and verifies. -/
theorem leanDa_perfectlyComplete (hps : ps.PerfectlyComplete) :
    (leanDa r H ps).PerfectlyComplete (code r) (roRuntime Digest Challenges) :=
  scheme_perfectlyComplete (code r) (merkleVC r H) (checker r) ps
    (merkleVC_perfectlyComplete r H) (checker_complete r) hps

/-- **Position binding**: an adversary opening a commitment at one cell to two different cells
gives, through the explicit reduction, a collision of `H`. -/
theorem leanDa_positionBinding
    (A : ErasureCodeCommitment.PosBindingAdv (OracleComp (unifSpec + (Digest →ₒ Challenges))) Cell
      (r * 128) (Unit × Crs) (Digest × Proof) Opening) :
    (leanDa r H ps).posBindingExp (roRuntime Digest Challenges) A {true} ≤
      Pr{let b ← hashCollisionExp H
          (merkleCollider r H (posBindingReduction ps A))}[b = true] :=
  (scheme_positionBinding (code r) (merkleVC r H) (checker r) ps A).trans
    (posBindingExp_le_hashCollisionExp r H _)

/-- **Code binding**: for an adversary making at most `Q` random-oracle queries,
`(Pr[code-bind] - (ε_ks + ε₁))² ≤ (Q + 2) (ε₂ + 14 / 2^192 + 2^-2688)`, with `ε_ks` the success of
the reduction against the argument's knowledge soundness and `ε₁`, `ε₂` those of two explicit
reductions finding collisions of `H`. -/
theorem leanDa_codeBinding [NeZero r]
    (ext : Nark.Extractor (Unit × Digest × Challenges) (Fin (r * 128) → Cell) Crs Proof)
    (A : ErasureCodeCommitment.CodeBindingAdv (OracleComp (unifSpec + (Digest →ₒ Challenges))) Cell
      (r * 128) (Unit × Crs) (Digest × Proof) Opening) {Q : ℕ} (hA : ∀ ck, HashQueryBound (A ck) Q) :
    ((leanDa r H ps).codeBindingExp (code r) (roRuntime Digest Challenges) A {true} -
        (Pr{let b ← ps.knowledgeSoundnessExp ext (ksReduction (merkleVC r H) A)}[b = true] +
          Pr{let b ← hashCollisionExp H (merkleCollider r H
            ((wpbReduction ps ext A).toPosBindingAdv (merkleVC r H)))}[b = true])) ^ 2 ≤
      ((Q : ℝ≥0∞) + 2) *
        (Pr{let b ← hashCollisionExp H (merkleCollider r H
            ((forkCollisionReduction (code r) (merkleVC r H) (checker r)
              (csReduction ps ext A) (Q + 1)).toPosBindingAdv (merkleVC r H)))}[b = true] +
          14 / 2 ^ 192 + (2 ^ 2688)⁻¹) := by
  have h := scheme_codeBinding_concrete_posBinding (code r) (merkleVC r H) (checker r) ps
    ext A (merkleVC_perfectlyComplete r H) (checker_sound r) hA
  have hcard : (Fintype.card Challenges : ℝ≥0∞)⁻¹ = (2 ^ 2688)⁻¹ := by
    rw [card_challenges, Nat.cast_pow, Nat.cast_ofNat, show 192 * 14 = 2688 from rfl]
  rw [hcard] at h
  unfold leanDa
  have h₁ := posBindingExp_le_hashCollisionExp r H
    ((wpbReduction ps ext A).toPosBindingAdv (merkleVC r H))
  have h₂ := posBindingExp_le_hashCollisionExp r H
    ((forkCollisionReduction (code r) (merkleVC r H) (checker r)
      (csReduction ps ext A) (Q + 1)).toPosBindingAdv (merkleVC r H))
  refine le_trans ?_ (h.trans ?_)
  · exact pow_le_pow_left₀ zero_le (tsub_le_tsub_left (add_le_add le_rfl h₁) _) 2
  · exact mul_le_mul' le_rfl (add_le_add (add_le_add h₂ le_rfl) le_rfl)

section CodeBindingRpm

open LeanRpm

variable (r : ℕ) {Crs Proof : Type} {rel : Unit × Digest × Challenges → (Fin (r * 128) → Cell) → Bool}
  (ps : Nark (Unit × Digest × Challenges) (Fin (r * 128) → Cell) Crs Proof rel)

/-- **LeanDA is code binding in the random-permutation model.** For every argument `ps` (any
verifier, for any relation; an oracle-free parameter, as in Wagner's model), every extractor
`ext`, and every adversary whose game, verifications included, makes at most `Q` permutation
calls (`permCalls2`),

`(Pr[code-bind] − (Q²/2^508 + 2(Q+15)²/2^576 + ε_ks + ε₁))² ≤ (Q + 2)(ε₂ + 14/2^192 + 2^-2688)`,

where, for a uniformly random table `h` of `H` on the strings of at most `2048` bytes (`Hh h`
its hash) and Wagner's adversary `advH h` built from the RPM adversary, `ε_ks` is the success of
Wagner's reduction against the knowledge soundness of `ps` for the relation with the hash `Hh h`
(`ksExpH`), and `ε₁`, `ε₂` those of his two reductions finding a collision of `Hh h`
(`wpbCollExpH`, `forkCollExpH`).

`Q²/2^508` is the two-oracle transfer, `2(Q+15)²/2^576` the duplex lemma (the challenges' sponge
is a random oracle of the roots unless two of at most `Q + 15` states share their 576-bit
capacity), and the rest is Wagner's bound for each `h`, averaged over `h`. -/
theorem leanDa_codeBinding_rpm_bound [NeZero r]
    (ext : Nark.Extractor (Unit × Digest × Challenges) (Fin (r * 128) → Cell) Crs Proof)
    (A : CodeBindingAdvRpm r Crs Proof) (Q : ℕ)
    (hQ : IsWeightBound (codeBindingGame r ps A) permCalls2 Q) :
    (Pr{let b ← codeBindingExpRpm r ps A}[b = true] -
        ((Q ^ 2 : ℝ≥0∞) / 2 ^ 508 + 2 * ((Q + 15 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 576 +
          (Pr{let b ← ($ᵗ HTab : ProbComp HTab) >>= ksExpH r ps ext A}[b = true] +
            Pr{let b ← ($ᵗ HTab : ProbComp HTab) >>= wpbCollExpH r ps ext A}[b = true]))) ^ 2 ≤
      ((Q : ℝ≥0∞) + 2) *
        (Pr{let b ← ($ᵗ HTab : ProbComp HTab) >>= forkCollExpH r ps ext A Q}[b = true] +
          14 / 2 ^ 192 + (2 ^ 2688)⁻¹) := by
  set εks := Pr{let b ← ($ᵗ HTab : ProbComp HTab) >>= ksExpH r ps ext A}[b = true]
  set ε₁ := Pr{let b ← ($ᵗ HTab : ProbComp HTab) >>= wpbCollExpH r ps ext A}[b = true]
  set ε₂ := Pr{let b ← ($ᵗ HTab : ProbComp HTab) >>= forkCollExpH r ps ext A Q}[b = true]
  set cb : ProbComp Bool := ($ᵗ HTab : ProbComp HTab) >>= fun h ↦ ps.setup >>= fun crs ↦
    (simulateQ (Digest →ₒ Challenges).romImpl (gameW r ps A h crs)).run' ∅
  -- Wagner's bound, averaged over `H`
  have hW : (prT cb - (εks + ε₁)) ^ 2 ≤ ((Q : ℝ≥0∞) + 2) * (ε₂ + (14 / 2 ^ 192 + (2 ^ 2688)⁻¹)) := by
    refine sq_tsub_avg_le _ _ _ _ _ _ _ fun h ↦ ?_
    rw [prT_gameW r ps A h, ← add_assoc]
    exact leanDa_codeBinding r (Hh h) (argH r ps (Hh h)) ext (advH r ps A h)
      (hashQueryBound_advH r ps A Q hQ h)
  -- the RPM game against the simulated world
  have hG := codeBindingExpRpm_le_G r ps A Q hQ
  rw [show Pr{let b ← codeBindingExpG r ps A}[b = true] = prT cb from prT_codeBindingExpG r ps A]
    at hG
  have hdup : ((Q + 14 + 1 : ℕ) : ℝ≥0∞) * (2 * ((Q + 14 + 1 : ℕ) : ℝ≥0∞) * (2 ^ 576 : ℝ≥0∞)⁻¹) =
      2 * ((Q + 15 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 576 := by
    rw [div_eq_mul_inv]; ring
  rw [hdup, add_assoc] at hG
  rw [← add_assoc ε₂] at hW
  refine le_trans (pow_le_pow_left₀ zero_le ?_ 2) hW
  rw [tsub_le_iff_right]
  calc Pr{let b ← codeBindingExpRpm r ps A}[b = true]
      ≤ prT cb + ((Q ^ 2 : ℝ≥0∞) / 2 ^ 508 + 2 * ((Q + 15 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 576) := hG
    _ ≤ (prT cb - (εks + ε₁) + (εks + ε₁)) +
          ((Q ^ 2 : ℝ≥0∞) / 2 ^ 508 + 2 * ((Q + 15 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 576) := by
        gcongr; exact le_tsub_add
    _ = _ := by ring

end CodeBindingRpm

end LeanDa

/-! The build fails if a front-page theorem's axiom footprint ever grows beyond Lean's three
standard axioms. -/

/-- info: 'LeanDa.leanDa_perfectlyComplete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanDa.leanDa_perfectlyComplete

/-- info: 'LeanDa.leanDa_positionBinding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanDa.leanDa_positionBinding

/-- info: 'LeanDa.leanDa_codeBinding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanDa.leanDa_codeBinding

/-- info: 'LeanDa.checker_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanDa.checker_sound

/-- info: 'LeanDa.commitCodewords_eq_commitCells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanDa.commitCodewords_eq_commitCells

/-- info: 'LeanDa.dualCodeword_eq_dual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanDa.dualCodeword_eq_dual

/-- info: 'LeanDa.membershipVector_eq_dual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanDa.membershipVector_eq_dual

/-- info: 'LeanDa.leanDa_positionBinding_rpm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanDa.leanDa_positionBinding_rpm

/-- info: 'LeanDa.leanDa_codeBinding_rpm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanDa.leanDa_codeBinding_rpm

/-- info: 'LeanDa.leanDa_codeBinding_rpm_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanDa.leanDa_codeBinding_rpm_bound

/-- info: 'LeanDa.membershipChallengesM_id' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanDa.membershipChallengesM_id

/-- info: 'LeanDa.verifyCellM_id' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanDa.verifyCellM_id
