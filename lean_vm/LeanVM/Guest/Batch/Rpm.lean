/-
  LeanVM.Guest.Batch.Rpm

  The batching in the random-permutation model: an adversary querying `π` and `π⁻¹` outputs a
  proof, and the batching program, with Keccak-256 the sponge over `π` and Keccak-f[1600] `π`,
  accepts children with a false claim with probability at most the random-oracle bound of
  `batch_rom` plus `q² / 2^508` for `q` permutation calls.
-/

import LeanVM.Guest.Batch.Rom
import LeanVM.Protocol.Rpm.Generic

/-!
# The batching in the random-permutation model

`batch_rom` bounds the batching with Keccak-256 and Keccak-f[1600] independent random oracles.
Here both are built from one random permutation `π`, which the adversary queries forward and
inverse (`Rpm.rpmRun`): `batch_rpm` bounds the probability that the batching program
(`batchAny M bytecode`, from its seeding `batchSeedOf`) accepts a proof that begins with fewer than
`M` children of the bytecode's shapes one of whose claims is false (`FalseChildren`) by
`batch_rom`'s bound at the adversary's `QA` queries, plus `rpmError (QA + QV · 2^32)`, `QV` the
program's query bound, each query at most `2^32` permutation calls. `batch_rpm_bits`: for
`QA + QV ≤ 2^64`, at most `(QA + QV) · 2^-188`. `batch_sound_rpm` and `batch_sound_rpm_bits`
are the two as the end statements `BatchSoundRpm` and `BatchSoundRpmBits` of
`Statement/LeanVmGuest.lean` state them: the verifier written out (`batchVerifier`, the seeding
`F(H(label) ‖ 0)` then the program) and the failure term the explicit `5N/2^256`.

The proof is `Rpm.rpmRun_le_rom` with `batch_rom`: the program follows the duplex discipline (its
seed is the permutation of `seedInput`, zero from lane `8` on, then the duplex sponge,
`duplexVm_batch`), it hashes only its label (`31` bytes) and commits nothing, so each of its
queries costs at most `2^32` permutation calls (`isWeightBound_batch`).
-/

namespace LeanVM.Guest.Batch

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Sound LeanVM.Node LeanVM.Rpm OracleComp OracleSpec
open scoped ENNReal

/-! ## The program commits nothing -/

theorem movesOK_readCount (M : ℕ) : MovesOK (· ≤ 64) False (readCount M) := by
  unfold readCount
  exact MovesOK.seq (MovesOK.readN _) fun _ ↦ MovesOK.seq (movesOK_require _ _) fun _ ↦
    MovesOK.liftOption _

theorem movesOK_readChild (nB : ℕ) : MovesOK (· ≤ 64) False (readChild nB) := by
  unfold readChild
  exact MovesOK.seq (MovesOK.readN _) fun _ ↦ MovesOK.seq (movesOK_require _ _) fun _ ↦
    MovesOK.liftOption _

theorem movesOK_readChildren (nB : ℕ) : ∀ n, MovesOK (· ≤ 64) False (readChildren nB n)
  | 0 => trivial
  | n + 1 => MovesOK.seq (movesOK_readChild nB) fun _ ↦
      MovesOK.seq (movesOK_readChildren nB n) fun _ ↦ trivial

theorem movesOK_batchAny (M : ℕ) (bytecode : List K) :
    MovesOK (· ≤ 64) False (batchAny M bytecode) := by
  unfold batchAny batchProg
  exact MovesOK.seq (movesOK_readCount M) fun n ↦
    MovesOK.seq (movesOK_readChildren _ n) fun cs ↦ movesOK_batchRest bytecode cs

/-! ## The duplex discipline -/

theorem hOnly_hsRun : ∀ (fs : List (List Digest → Bytes)) (ds : List Digest),
    HOnly (Seed.hsRun queryH fs ds)
  | [], _ => hOnly_pure _
  | f :: fs, ds => by
    simp only [Seed.hsRun]
    exact (hOnly_queryH _).bind fun _ ↦ hOnly_hsRun fs _

theorem duplexP_batchSeed (h : List KState) :
    DuplexP (batchSeedOf.run queryH queryF) h fun seed h' ↦ seed ∈ h' := by
  simp only [Seed.run, batchSeedOf]
  refine ((hOnly_hsRun _ _).duplexP h).bind fun ds h' hh ↦ ?_
  subst hh
  exact (duplexP_queryF_bind _ _ _ _).mpr
    ⟨admissibleVm_seedInput _ _ _, fun y ↦ List.mem_cons_self⟩

/-- **The batching program follows the duplex discipline.** -/
theorem duplexVm_batch (M : ℕ) (bytecode : List K) (z : Unit × Proof) :
    DuplexVm (verifierFam batchSeeds (batchAny M bytecode) z) [] := by
  rw [duplexVm_iff_duplexP, verifierFam_batch]
  change DuplexP (do
    let seed ← batchSeedOf.run queryH queryF
    runProof queryH queryF (batchAny M bytecode) seed z.2) [] _
  exact (duplexP_batchSeed []).bind fun seed h' hs ↦ duplexP_runProof _ hs _

/-! ## The permutation calls -/

theorem batchLabel_length : batchLabel.length ≤ 2 ^ 39 := by decide +kernel

theorem allQ_batchSeed : AllQueriesSatisfy (batchSeedOf.run queryH queryF) Short := by
  refine allQueriesSatisfy_bind (allQ_hsRun _ _ fun f hf ds ↦ ?_) fun _ ↦ allQ_queryF _
  simp only [batchSeedOf, List.mem_cons, List.not_mem_nil, or_false] at hf
  subst hf
  exact batchLabel_length

theorem allQ_batch (M : ℕ) (bytecode : List K) (z : Unit × Proof) :
    AllQueriesSatisfy (verifierFam batchSeeds (batchAny M bytecode) z) Short := by
  rw [verifierFam_batch]
  exact allQueriesSatisfy_bind allQ_batchSeed fun seed ↦
    allQ_runProof _ seed z.2 (WidthsLE.of_moves (movesOK_batchAny M bytecode))

/-- **The batching program makes at most `QV · 2^32` permutation calls**, `QV` its query
bound. -/
theorem isWeightBound_batch (M : ℕ) (bytecode : List K) (z : Unit × Proof) :
    Common.IsWeightBound (verifierFam batchSeeds (batchAny M bytecode) z) hashBlocks
      (batchQueryBound bytecode M * 2 ^ 32) :=
  isWeightBound_of_isTotalQueryBound hashBlocks (2 ^ 32) (isTotalQueryBound_batchFam M bytecode z)
    ((allQ_batch M bytecode z).mono fun _ h ↦ hashBlocks_le_of_short h)

/-! ## The batching in the random-permutation model -/

variable {M : ℕ} {bytecode : List K}

/-- **The batching in the random-permutation model.** An adversary of `QA` queries to `π` and
`π⁻¹` outputs a proof; the probability that the batching program, Keccak-256 the sponge over `π`
and Keccak-f[1600] `π`, accepts it while it begins with fewer than `M` children of the bytecode's
shapes one of whose claims is false is at most `batch_rom`'s bound,
`(QA + QV) · (2/|E| + failBound (QA + QV))`, plus `rpmError (QA + QV · 2^32)`, `QV` the program's
query bound. -/
theorem batch_rpm (hb : bytecode.length = 2 ^ Nat.log2 bytecode.length) (hM : M ≤ 2 ^ 64 - 1)
    (A : OracleComp PermSpec (Unit × Proof)) (QA : ℕ) (hA : A.IsTotalQueryBound QA) :
    Pr{let z ← rpmRun A (verifierFam batchSeeds (batchAny M bytecode))}[
      z.2 = true ∧ FalseChildren bytecode M z.1.2] ≤
      ((QA + batchQueryBound bytecode M : ℕ) : ℝ≥0∞) *
          (batchε + failBound batchSeeds (QA + batchQueryBound bytecode M)) +
        rpmError (QA + batchQueryBound bytecode M * 2 ^ 32) := by
  obtain ⟨A', hA', hle⟩ := rpmRun_le_rom A (verifierFam batchSeeds (batchAny M bytecode))
    (duplexVm_batch M bytecode) hA (isWeightBound_batch M bytecode)
    (fun z ↦ z.2 = true ∧ FalseChildren bytecode M z.1.2)
  refine hle.trans (add_le_add (le_of_eq_of_le ?_ (batch_rom hb hM A' QA hA')) le_rfl)
  rw [romStep_eq, prEvent_map]

/-- `batchε + failBound` at `N ≤ 2^64` queries is at most `2^-189`. -/
theorem batchε_add_failBound_le {N : ℕ} (hN : N ≤ 2 ^ 64) :
    batchε + failBound batchSeeds N ≤ (2 : ℝ≥0∞)⁻¹ ^ 189 := by
  rw [batchε_eq_pow, failBound_batchSeeds]
  have h2 : (2 : ℝ≥0∞) ^ 256 = ((2 ^ 256 : ℕ) : ℝ≥0∞) := by rw [Nat.cast_pow, Nat.cast_ofNat]
  rw [h2, inv_pow_eq_div 191 256 (by norm_num), ENNReal.div_add_div_same, ← Nat.cast_add,
    inv_pow_eq_div 189 256 (by norm_num)]
  refine ENNReal.div_le_div_right (Nat.cast_le.2 ?_) _
  rw [show 256 - 191 = 65 from rfl, show 256 - 189 = 67 from rfl]
  calc 2 ^ 65 + 5 * N ≤ 2 ^ 65 + 5 * 2 ^ 64 := by omega
    _ ≤ 2 ^ 67 := by norm_num

/-- `(QA + QV · 2^32)² ≤ (QA + QV) · c` for `QA + QV ≤ 2^64` and `c ≥ 2^128`. -/
theorem sq_batch_le {QA QV c : ℕ} (hN : QA + QV ≤ 2 ^ 64) (hc : 2 ^ 128 ≤ c) :
    (QA + QV * 2 ^ 32) ^ 2 ≤ (QA + QV) * c := by
  have h1 : QA + QV * 2 ^ 32 ≤ (QA + QV) * 2 ^ 32 := by omega
  have h2 : (QA + QV) * 2 ^ 32 ≤ 2 ^ 96 :=
    calc (QA + QV) * 2 ^ 32 ≤ 2 ^ 64 * 2 ^ 32 := Nat.mul_le_mul_right _ hN
      _ = 2 ^ 96 := by norm_num
  calc (QA + QV * 2 ^ 32) ^ 2 = (QA + QV * 2 ^ 32) * (QA + QV * 2 ^ 32) := Nat.pow_two _
    _ ≤ ((QA + QV) * 2 ^ 32) * 2 ^ 96 := Nat.mul_le_mul h1 (h1.trans h2)
    _ = (QA + QV) * 2 ^ 128 := by ring
    _ ≤ (QA + QV) * c := Nat.mul_le_mul_left _ hc

/-- `rpmError (QA + QV · 2^32)` is at most `(QA + QV) · 2^-189` for `QA + QV ≤ 2^64`. -/
theorem rpmError_batch_le {QA QV : ℕ} (hN : QA + QV ≤ 2 ^ 64) :
    rpmError (QA + QV * 2 ^ 32) ≤ ((QA + QV : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 189 := by
  rw [rpmError_eq, inv_pow_eq_div 189 508 (by norm_num), ← mul_div_assoc, ← Nat.cast_mul]
  refine ENNReal.div_le_div_right (Nat.cast_le.2 ?_) _
  rw [show 508 - 189 = 128 + 191 from rfl, pow_add]
  exact sq_batch_le hN (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _))

theorem two_mul_inv_pow_189 : 2 * (2 : ℝ≥0∞)⁻¹ ^ 189 = (2 : ℝ≥0∞)⁻¹ ^ 188 := by
  rw [pow_succ, ← mul_assoc, mul_comm 2, mul_assoc,
    ENNReal.mul_inv_cancel (by norm_num) (by norm_num), mul_one]

/-- **The batching in the random-permutation model, in bits**: for `QA + QV ≤ 2^64` (the
adversary's queries to `π` and `π⁻¹` and the program's query bound), the program accepts children
with a false claim with probability at most `(QA + QV) · 2^-188`. -/
theorem batch_rpm_bits (hb : bytecode.length = 2 ^ Nat.log2 bytecode.length)
    (hM : M ≤ 2 ^ 64 - 1) (A : OracleComp PermSpec (Unit × Proof)) (QA : ℕ)
    (hA : A.IsTotalQueryBound QA) (hQ : QA + batchQueryBound bytecode M ≤ 2 ^ 64) :
    Pr{let z ← rpmRun A (verifierFam batchSeeds (batchAny M bytecode))}[
      z.2 = true ∧ FalseChildren bytecode M z.1.2] ≤
      ((QA + batchQueryBound bytecode M : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 188 := by
  refine (batch_rpm hb hM A QA hA).trans ?_
  calc ((QA + batchQueryBound bytecode M : ℕ) : ℝ≥0∞) *
          (batchε + failBound batchSeeds (QA + batchQueryBound bytecode M)) +
        rpmError (QA + batchQueryBound bytecode M * 2 ^ 32)
      ≤ ((QA + batchQueryBound bytecode M : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 189 +
          ((QA + batchQueryBound bytecode M : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 189 :=
        add_le_add (by gcongr; exact batchε_add_failBound_le hQ) (rpmError_batch_le hQ)
    _ = ((QA + batchQueryBound bytecode M : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 188 := by
        rw [← mul_add, ← two_mul, two_mul_inv_pow_189]

/-! ## The end statements -/

/-- The batching's statement family run on a proof is the batching's verifier
(`Statement/LeanVmGuest.lean`) with the oracle calls. -/
theorem verifierFam_eq_batchVerifier (M : ℕ) (bytecode : List K) :
    verifierFam batchSeeds (batchAny M bytecode) =
      fun z ↦ batchVerifier queryH queryF M bytecode z.2 := by
  funext z
  rw [verifierFam_batch]
  simp only [verifierComp, Rom.verify, Seed.run, batchSeedOf, Seed.hsRun, batchVerifier,
    bind_assoc, pure_bind, List.nil_append, List.getD_cons_zero]

/-- **`BatchSoundRpm`** (`Statement/LeanVmGuest.lean`): `batch_rpm`, its failure term
`failBound batchSeeds` the explicit `5N/2^256`, and `rpmError (QA + QV · 2^32)` at most
`(QA + QV · 2^32) · 2^-379` for `QA ≤ 2^128` and `QV ≤ 2^96` (`rpmError_le_linear`). -/
theorem batch_sound_rpm : BatchSoundRpm := by
  intro M bytecode hb hM A QA hA hQA hQV
  rw [← verifierFam_eq_batchVerifier, ← failBound_batchSeeds]
  refine (batch_rpm hb hM A QA hA).trans (add_le_add le_rfl (rpmError_le_linear ?_))
  refine add_le_two_pow_129 hQA ?_
  calc batchQueryBound bytecode M * 2 ^ 32 ≤ 2 ^ 96 * 2 ^ 32 := Nat.mul_le_mul_right _ hQV
    _ = 2 ^ 128 := by norm_num

/-- **`BatchSoundRpmBits`** (`Statement/LeanVmGuest.lean`): `batch_rpm_bits`. -/
theorem batch_sound_rpm_bits : BatchSoundRpmBits := by
  intro M bytecode hb hM A QA hA hQ
  rw [← verifierFam_eq_batchVerifier]
  exact batch_rpm_bits hb hM A QA hA hQ

end LeanVM.Guest.Batch
