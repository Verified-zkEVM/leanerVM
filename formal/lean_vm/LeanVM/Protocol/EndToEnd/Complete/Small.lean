/-
  LeanVM.Protocol.EndToEnd.Complete.Small

  Completeness in the ISA's terms: a valid execution small enough in steps, memory and bytecode
  has a witness at sizes the verifier admits, and the honest prover's proof of it is accepted.
-/

module

public import LeanVM.Protocol.EndToEnd.Completeness

/-!
# Completeness for small executions

The completeness theorems of `EndToEnd.Completeness` start from a witness at admissible sizes
(`Sizes.Admissible`), an arithmetization notion. This file closes the gap to the ISA: a valid
execution (`ValidExecution`) that is small in the ISA's own terms (`Trace.Small`) has a witness
representing it at admissible sizes (`exists_admissible_witness`), and the honest proof of that
witness (`honestProofOf`) is accepted (`verify_honestProofOf`), and exists as soon as the
proof-of-work searches succeed (`honestProofOf_isSome`).

## The sizes of the witness

The witness is `constraintCompleteness_rows`'s: its memory is the trace's, `2^κ` words, and each
opcode table holds the run's rows of its opcode, at most `2^n` for a run of at most `2^n` steps,
so its log-height `⌈log₂ rows⌉` is at most `n`. The stacked size counts every committed column at
its table's height (`blocks_total_eq`):

  `4·2^logMem + 2^logSize + 2^(8 + τ₅) + 15·2^τ₀ + 15·2^τ₁ + 8·2^τ₂ + 15·2^τ₃ + 14·2^τ₄ + 19·2^τ₅`

(the four memory columns, `BFCNT`, the Flock region of `2^8` rows per `BLAKE2S` row, and the
committed columns of `XOR`, `MUL_NATIVE`, `SET_CONSTANT`, `DEREF`, `JUMP`, `BLAKE2S`, the last
without its eighteen limbs). At the witness's sizes it is at most
`4·2^κ + 2^logSize + (86 + 256)·2^n = 4·2^κ + 2^logSize + 342·2^n`, and the verifier admits it
when that is at most `2^maxMu = 2^28` (`exists_admissible_witness_of_budget`).

## The constants

`Trace.Small` takes `n = 19`, `κ ≤ 23` and `logSize ≤ 23`:
`4·2^23 + 2^23 + 342·2^19 = 221 249 536 ≤ 268 435 456 = 2^28`. The budget has room: with the other
two fixed, `κ = 24` or `logSize = 25` still fits, `2^20` steps does not
(`tests/LeanVMTests/Protocol/EndToEnd/Complete/Small.lean`): a run of `2^20` `BLAKE2S` steps
alone fills the Flock region to `2^28` rows.

## Wrong readings excluded

* `Trace.Small` is sufficient, not necessary, and its three bounds trade against each other: a
  memory of `2^25` words with a run of `2^6` steps is within the budget of
  `exists_admissible_witness_of_budget`, which `Trace.Small` excludes.
* The honest prover is a specification: `honestProofOf` chooses its witness classically, and is
  `none` only for an invalid rate, an execution without an admissible witness, or a proof-of-work
  search that finds no nonce below the fuel.
-/

namespace LeanVM.Semantics

open LeanVM.Parameters

@[expose] public section

/-- **An execution small enough for the deployed parameters**, in the ISA's terms: at most `2^19`
steps, a memory of at most `2^23` words, and a bytecode of at most `2^23` instructions. -/
structure Trace.Small {prog : Program} (t : Trace prog) : Prop where
  /-- At most `2^19` steps. -/
  steps_le : t.steps ≤ 2 ^ 19
  /-- A memory of at most `2^23` words. -/
  mem_le : t.κ ≤ 23
  /-- A bytecode of at most `2^23` instructions. -/
  code_le : prog.logSize ≤ 23

end
end LeanVM.Semantics

namespace LeanVM.Protocol.EndToEnd.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.LeanIsa LeanVM.Protocol.EndToEnd.Front
open Air.Flat (EnsembleWitness)

@[expose] public section

/-! ## The stacked size -/

/-- The committed columns, by table: four of the memory, `BFCNT`, `QFLOCK`, then those of the six
opcode tables (`15, 15, 8, 15, 14` and `19` for `BLAKE2S`, whose eighteen limbs are read off the
Flock region). -/
theorem committedColumns_tables : committedColumns.map (fun c ↦ c.1) =
    List.replicate 4 0 ++ [1, 2] ++ List.replicate 15 3 ++ List.replicate 15 4 ++
      List.replicate 8 5 ++ List.replicate 15 6 ++ List.replicate 14 7 ++ List.replicate 19 8 := by
  decide +kernel

/-- **The stacked size**: every committed column at its table's height. -/
theorem blocks_total_eq (prog : Program) (s : Sizes) : (LeanIsa.blocks prog s).total =
    4 * 2 ^ s.logMem + 2 ^ prog.logSize + 2 ^ (8 + s.τ 5) + 15 * 2 ^ s.τ 0 + 15 * 2 ^ s.τ 1 +
      8 * 2 ^ s.τ 2 + 15 * 2 ^ s.τ 3 + 14 * 2 ^ s.τ 4 + 19 * 2 ^ s.τ 5 := by
  rw [Blocks.total_eq_sum]
  have h1 : ∑ b : Fin (LeanIsa.blocks prog s).n, 2 ^ (LeanIsa.blocks prog s).size b =
      ((LeanIsa.stackOrder prog s).map fun c ↦ 2 ^ kappa prog s c).sum :=
    Fin.sum_univ_fun_getElem (LeanIsa.stackOrder prog s) (fun c ↦ 2 ^ kappa prog s c)
  rw [h1, LeanIsa.stackOrder, ((List.mergeSort_perm _ _).map _).sum_eq]
  have h2 : (committedColumns.map fun c ↦ 2 ^ kappa prog s c) =
      (committedColumns.map fun c ↦ c.1).map fun j ↦ 2 ^ LeanIsa.height prog s j := by
    rw [List.map_map]
    rfl
  rw [h2, committedColumns_tables]
  simp only [List.map_append, List.map_replicate, List.sum_append, List.sum_replicate,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, smul_eq_mul, LeanIsa.height,
    Nat.add_zero, ← Nat.add_assoc]
  rfl

/-- The stacked size is within the cap when the blocks fit on `2^maxMu` cells. -/
theorem leanIsaμ_le_of_total_le {prog : Program} {s : Sizes}
    (h : (LeanIsa.blocks prog s).total ≤ 2 ^ maxMu) : leanIsaμ prog s ≤ maxMu :=
  max_le (Nat.clog_le_of_le_pow h) (by decide)

/-! ## The admissible witness -/

/-- An opcode table of `rows ≤ 2^n` rows has log-height at most `n`. -/
theorem pow_clog_le {rows n : ℕ} (h : rows ≤ 2 ^ n) : 2 ^ Nat.clog 2 rows ≤ 2 ^ n :=
  Nat.pow_le_pow_right (by norm_num) (Nat.clog_le_of_le_pow h)

/-- **An admissible witness, under a budget.** A valid execution of at most `2^n` steps, whose
memory, bytecode and steps fit the stacked size's cap as `4·2^κ + 2^logSize + 342·2^n ≤ 2^28`, has a
witness representing it that satisfies leanISA's constraint system at sizes the verifier admits. -/
theorem exists_admissible_witness_of_budget {prog : Program} {input : PublicInput}
    {t : Trace prog} {n : ℕ} (hv : ValidExecution prog input t) (hn : t.steps ≤ 2 ^ n)
    (hbudget : 4 * 2 ^ t.κ + 2 ^ prog.logSize + 342 * 2 ^ n ≤ 2 ^ maxMu) :
    ∃ w s, SatisfiedBy prog input w ∧ AssignmentRepresents w t ∧
      Sizes.ofWitness w = some s ∧ s.Admissible prog := by
  have hmax : 2 ^ maxMu = 2 ^ 28 := rfl
  rw [hmax] at hbudget
  -- `omega` takes `2 ^ x` for an atom without its sign: the bounds it needs, stated.
  have hL : 0 < 2 ^ prog.logSize := Nat.two_pow_pos _
  have hcap : 2 ^ n ≤ 2 ^ maxLogRows := by
    have : 2 ^ n ≤ 2 ^ 28 := by omega
    exact this.trans (Nat.pow_le_pow_right (by norm_num) (by unfold maxLogRows; omega))
  have hrows : ∀ op, t.runRows op ≤ 2 ^ n := fun op ↦ (t.runRows_le_steps hv.2 op).trans hn
  obtain ⟨w, hw, hrep, hlen⟩ := constraintCompleteness_rows hv fun op ↦ (hrows op).trans hcap
  obtain ⟨s, hs⟩ := sizes_of_satisfiedBy hw
  refine ⟨w, s, hw, hrep, hs, ?_⟩
  obtain ⟨hpos, rfl⟩ := eq_of_ofWitness hs
  -- The sizes: the trace's memory, and each table's row count that of the run.
  have hmem : (witnessSizes w hpos).logMem = t.κ := hrep.κ_eq
  have hr : ∀ j : Fin 6, (witnessSizes w hpos).rows j = t.runRows (tableOpcode j) := hlen
  have hle : ∀ j : Fin 6, 2 ^ (witnessSizes w hpos).τ j ≤ 2 ^ n := fun j ↦
    pow_clog_le ((hr j).trans_le (hrows _))
  refine ⟨?_, ?_, fun j ↦ ((hr j).trans_le (hrows _)).trans hcap, ?_⟩
  · rw [hmem]
    exact hv.1.1
  · rw [hmem]
    exact hv.1.2.1
  · refine leanIsaμ_le_of_total_le ?_
    rw [blocks_total_eq, hmem, pow_add 2 8]
    have h0 := hle 0
    have h1 := hle 1
    have h2 := hle 2
    have h3 := hle 3
    have h4 := hle 4
    have h5 := hle 5
    generalize 2 ^ (witnessSizes w hpos).τ 0 = a0 at *
    generalize 2 ^ (witnessSizes w hpos).τ 1 = a1 at *
    generalize 2 ^ (witnessSizes w hpos).τ 2 = a2 at *
    generalize 2 ^ (witnessSizes w hpos).τ 3 = a3 at *
    generalize 2 ^ (witnessSizes w hpos).τ 4 = a4 at *
    generalize 2 ^ (witnessSizes w hpos).τ 5 = a5 at *
    rw [hmax]
    omega

/-- **An admissible witness for a small execution.** A valid execution that is small
(`Trace.Small`: at most `2^19` steps, `2^23` words of memory and `2^23` instructions) has a witness
representing it that satisfies leanISA's constraint system at sizes the verifier admits. -/
theorem exists_admissible_witness {prog : Program} {input : PublicInput} {t : Trace prog}
    (hv : ValidExecution prog input t) (hsmall : t.Small) :
    ∃ w s, SatisfiedBy prog input w ∧ AssignmentRepresents w t ∧
      Sizes.ofWitness w = some s ∧ s.Admissible prog := by
  have hm : 2 ^ t.κ ≤ 2 ^ 23 := Nat.pow_le_pow_right (by norm_num) hsmall.mem_le
  have hc : 2 ^ prog.logSize ≤ 2 ^ 23 := Nat.pow_le_pow_right (by norm_num) hsmall.code_le
  exact exists_admissible_witness_of_budget (n := 19) hv hsmall.steps_le (by unfold maxMu; omega)

/-! ## The honest proof of an execution -/

/-- The honest prover's witness for an execution `t` at rate `ρ`: the rate is valid, and `w`
satisfies leanISA's constraint system at sizes `s` the verifier admits and represents `t`. -/
def HonestFor (prog : Program) (input : PublicInput) (t : Trace prog) (ρ : ℕ)
    (w : EnsembleWitness (leanIsaEnsemble prog)) (s : Sizes) : Prop :=
  validRate ρ ∧ SatisfiedBy prog input w ∧ Sizes.ofWitness w = some s ∧ s.Admissible prog ∧
    AssignmentRepresents w t

open Classical in
/-- **The honest proof of an execution**: the compiled honest prover's proof, with the hash `H`, of
a witness for `t` at rate `ρ` (`HonestFor`, chosen classically); `none` when there is none, or
when a proof-of-work search finds no nonce below `fuel`. A specification. -/
noncomputable def honestProofOf (H : Bytes → Digest) (prog : Program) (input : PublicInput)
    (t : Trace prog) (ρ fuel : ℕ) : Option Proof :=
  if h : ∃ w s, HonestFor prog input t ρ w s then
    prove H (leanVmProgram (bytecodeWords prog) (publicDigest input))
      (leanVmProver prog h.choose_spec.choose ρ
        (stackOf Blake2sFlock.blake2sFlockSpec prog h.choose_spec.choose h.choose))
      (Id.run (seedWith H (bytecodeWords prog) (publicDigest input))) fuel
  else none

/-- **The honest proof is accepted**, for every hash function: whenever the honest prover outputs
a proof, the verifier accepts it. -/
theorem verify_honestProofOf (H : Bytes → Digest) {prog : Program} {input : PublicInput}
    {t : Trace prog} {ρ fuel : ℕ} {proof : Proof}
    (h : honestProofOf H prog input t ρ fuel = some proof) :
    verifyWith (m := Id) H (bytecodeWords prog) (publicDigest input) proof = true := by
  unfold honestProofOf at h
  split_ifs at h with hc
  obtain ⟨hρ, hw, hs, hadm, -⟩ := hc.choose_spec.choose_spec
  have hq := m3Honest_stackOf (F := Blake2sFlock.blake2sFlockSpec) hw hs padLimbs_compress
  have hrun := runI_leanVmProgram hadm hρ hq walkFaithful_blake2sFlockSpec
  exact runProof_prove H _ _ _ fuel (fun chal ↦ (hrun chal).1) (fun chal ↦ (hrun chal).2) h

/-- **The honest prover succeeds on a small execution.** For a valid execution that is small, at a
valid rate, the honest proof exists as soon as every
proof-of-work search the verifier program asks for finds a nonce below `fuel`. -/
theorem honestProofOf_isSome {prog : Program} {input : PublicInput} {t : Trace prog} {ρ : ℕ}
    (hv : ValidExecution prog input t) (hsmall : t.Small)
    (hρ : validRate ρ) (H : Bytes → Digest) (fuel : ℕ)
    (hpow : ∀ hist bits k cv,
      (leanVmProgram (bytecodeWords prog) (publicDigest input)).after hist =
          some (.grind bits k) → findNonce H bits cv fuel ≠ none) :
    (honestProofOf H prog input t ρ fuel).isSome := by
  obtain ⟨w, s, hw, hrep, hs, hadm⟩ := exists_admissible_witness hv hsmall
  have hex : ∃ w s, HonestFor prog input t ρ w s := ⟨w, s, hρ, hw, hs, hadm, hrep⟩
  unfold honestProofOf
  split_ifs
  exact Option.isSome_iff_ne_none.mpr (prove_ne_none H _ _ _ fuel hpow)

/-- **Completeness for a small execution.** A valid execution that is small, at a valid rate: when every proof-of-work search succeeds below `fuel`, the honest
prover outputs a proof, and the verifier accepts it, for every hash function. -/
theorem complete_of_small {prog : Program} {input : PublicInput} {t : Trace prog} {ρ : ℕ}
    (hv : ValidExecution prog input t) (hsmall : t.Small)
    (hρ : validRate ρ) (H : Bytes → Digest) (fuel : ℕ)
    (hpow : ∀ hist bits k cv,
      (leanVmProgram (bytecodeWords prog) (publicDigest input)).after hist =
          some (.grind bits k) → findNonce H bits cv fuel ≠ none) :
    ∃ proof, honestProofOf H prog input t ρ fuel = some proof ∧
      verifyWith (m := Id) H (bytecodeWords prog) (publicDigest input) proof = true := by
  obtain ⟨proof, h⟩ := Option.isSome_iff_exists.mp
    (honestProofOf_isSome hv hsmall hρ H fuel hpow)
  exact ⟨proof, h, verify_honestProofOf H h⟩

end
end LeanVM.Protocol.EndToEnd.Complete
