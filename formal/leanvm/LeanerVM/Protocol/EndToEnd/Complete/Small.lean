/-
  LeanerVM.Protocol.EndToEnd.Complete.Small

  Completeness in the ISA's terms: a valid execution of a program that has the fill blocks, small
  enough in steps, memory and bytecode, has a witness at sizes the verifier admits, and the honest
  prover's proof of it is accepted.
-/

module

public import LeanerVM.Protocol.EndToEnd.Completeness

/-!
# Completeness for small executions

The completeness theorems of `EndToEnd.Completeness` start from a witness at admissible sizes
(`Sizes.Admissible`), an arithmetization notion. This file closes the gap to the ISA: a valid
execution (`ValidExecution`) of a program with the fill blocks the deployed prover pads with
(`HasFillBlocks`), which is small in the ISA's own terms (`Trace.Small`), has a padded execution and
a witness representing it at admissible sizes (`exists_admissible_witness`), and the honest proof of
that witness (`honestProofOf`) is accepted (`verify_honestProofOf`), and exists as soon as the
proof-of-work searches succeed (`honestProofOf_isSome`).

## The sizes of the witness

The witness is `constraintCompleteness_heights`'s, with the `JUMP` table filled to `2^(n + 1)` for a
run of at most `2^n` steps. Its memory log-size is `κ + 1` (the padded image), and its tables have
log-heights at most `n`, `n + 1` for `JUMP`, at least `3` for `BLAKE2S`. The stacked size counts
every committed column at its table's height (`blocks_total_eq`):

  `4·2^logMem + 2^logSize + 2^(8 + τ₅) + 15·2^τ₀ + 15·2^τ₁ + 8·2^τ₂ + 15·2^τ₃ + 14·2^τ₄ + 19·2^τ₅`

(the four memory columns, `BFCNT`, the Flock region of `2^8` rows per `BLAKE2S` row, and the
committed columns of `XOR`, `MUL_NATIVE`, `SET_CONSTANT`, `DEREF`, `JUMP`, `BLAKE2S`, the last
without its eighteen limbs). At the witness's sizes it is at most
`8·2^κ + 2^logSize + (72 + 28 + 256)·2^n = 8·2^κ + 2^logSize + 356·2^n`, and the verifier admits it
when that is at most `2^maxMu = 2^28` (`exists_admissible_witness_of_budget`).

## The constants

`Trace.Small` takes `n = 19`, `κ ≤ 23` and `logSize ≤ 23`:
`8·2^23 + 2^23 + 356·2^19 = 262 144 000 ≤ 268 435 456 = 2^28`. Each constant is the largest the
budget allows with the other two fixed (`tests/LeanerVMTests/Protocol/EndToEnd/Complete/
Small.lean`), and `2^20` steps is past every bound: a run of `2^20` `BLAKE2S` steps alone fills
the Flock region to `2^28` rows.

## Wrong readings excluded

* The witness does not represent `t`: it represents a padding of `t` (`Trace.PaddedFrom`), the same
  run over a memory twice the size, whose upper half holds the fill frames.
* `Trace.Small` is sufficient, not necessary, and its three bounds trade against each other: a
  memory of `2^24` words with a run of `2^6` steps is within the budget of
  `exists_admissible_witness_of_budget`, which `Trace.Small` excludes.
* The honest prover is a specification: `honestProofOf` chooses its witness classically, and is
  `none` only for an invalid rate, an execution without an admissible witness, or a proof-of-work
  search that finds no nonce below the fuel.
-/

namespace LeanerVM.Semantics

open LeanerVM.Parameters

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
end LeanerVM.Semantics

namespace LeanerVM.Protocol.EndToEnd.Complete

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Arithmetization LeanerVM.Protocol.Compile
open LeanerVM.Protocol.Verifier LeanerVM.Protocol.LeanIsa LeanerVM.Protocol.EndToEnd.Front
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

/-- A table of a run of at most `2^n` steps, `n ≥ 3`, other than `JUMP`, is filled to at most
`2^n` rows. -/
theorem tableHeight_le {prog : Program} {t : Trace prog} {rf : Regs K} {n τ : ℕ}
    (hrun : run prog t.image t.steps Regs.initial = some rf) (hn : t.steps ≤ 2 ^ n) (h3 : 3 ≤ n)
    {op : Opcode} (hop : op ≠ .jump) : tableHeight t.runRows τ op ≤ 2 ^ n := by
  have h8 : 8 ≤ 2 ^ n := (Nat.pow_le_pow_right (by norm_num) h3).trans_eq' (by norm_num)
  simp only [tableHeight, hop, ↓reduceIte]
  refine fillTarget_le ((t.runRows_le_steps hrun op).trans hn) ?_
  cases op <;> simp only [minRows] <;> omega

/-- The `JUMP` table of a run of at most `2^n` steps, `n ≥ 6`, owes at most `2^(n + 1) - 2` rows:
it can be filled to `2^(n + 1)`. -/
theorem owed_add_two_le {prog : Program} {t : Trace prog} {rf : Regs K} {n : ℕ}
    (hrun : run prog t.image t.steps Regs.initial = some rf) (hn : t.steps ≤ 2 ^ n) (h6 : 6 ≤ n) :
    t.owed + 2 ≤ 2 ^ (n + 1) := by
  have h := jumpOwed_le (rows := t.runRows) (k := n) (by omega)
    fun op ↦ (t.runRows_le_steps hrun op).trans hn
  have h64 : 64 ≤ 2 ^ n := (Nat.pow_le_pow_right (by norm_num) h6).trans_eq' (by norm_num)
  have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
  unfold Trace.owed
  omega

/-- **An admissible witness, under a budget.** A valid execution of a program with the fill blocks,
of at most `2^n` steps (`n ≥ 6`), whose memory, bytecode and steps fit the stacked size's cap as
`8·2^κ + 2^logSize + 356·2^n ≤ 2^28`, has a padded valid execution and a witness representing it
that satisfies leanISA's constraint system at sizes the verifier admits. -/
theorem exists_admissible_witness_of_budget {prog : Program} {input : PublicInput}
    {t : Trace prog} {n : ℕ} (hfill : HasFillBlocks prog) (hv : ValidExecution prog input t)
    (hn : t.steps ≤ 2 ^ n) (h6 : 6 ≤ n)
    (hbudget : 8 * 2 ^ t.κ + 2 ^ prog.logSize + 356 * 2 ^ n ≤ 2 ^ maxMu) :
    ∃ t', t'.PaddedFrom t ∧ ValidExecution prog input t' ∧
      ∃ w s, SatisfiedBy prog input w ∧ AssignmentRepresents w t' ∧
        Sizes.ofWitness w = some s ∧ s.Admissible prog := by
  have hrun := hv.2
  have hmax : 2 ^ maxMu = 2 ^ 28 := rfl
  rw [hmax] at hbudget
  -- `omega` takes `2 ^ x` for an atom without its sign: the bounds it needs, stated.
  have hL : 0 < 2 ^ prog.logSize := Nat.two_pow_pos _
  have h64 : 64 ≤ 2 ^ n := (Nat.pow_le_pow_right (by norm_num) h6).trans_eq' (by norm_num)
  -- The budget bounds the memory below `2^32` cells and the steps below `2^20`.
  have hκ : t.κ < maxLogMem := by
    have : 2 ^ t.κ < 2 ^ 25 := by omega
    have := (Nat.pow_lt_pow_iff_right (by norm_num)).mp this
    unfold maxLogMem
    omega
  have hn20 : n < 20 := by
    have : 2 ^ n < 2 ^ 20 := by omega
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp this
  have hnrows : 2 ^ n ≤ 2 ^ maxLogRows :=
    Nat.pow_le_pow_right (by norm_num) (by unfold maxLogRows; omega)
  have hrows : ∀ op, op ≠ .jump → fillTarget (t.runRows op) (minRows op) ≤ 2 ^ maxLogRows :=
    fun op hop ↦ by
      have := tableHeight_le (τ := 0) hrun hn (by omega) hop
      simp only [tableHeight, hop, ↓reduceIte] at this
      exact this.trans hnrows
  have howed := owed_add_two_le hrun hn h6
  obtain ⟨t', hp, hκ', hv', w, hw, hrep, hlen⟩ :=
    constraintCompleteness_heights hfill hv hκ hrows (τ := n + 1) (by unfold maxLogRows; omega)
      (by omega) (by omega)
  obtain ⟨s, hs⟩ := sizes_of_satisfiedBy hw
  refine ⟨t', hp, hv', w, s, hw, hrep, hs, ?_⟩
  obtain ⟨hpos, rfl⟩ := eq_of_ofWitness hs
  -- The sizes: memory `κ + 1`, and each table's log-height that of its fill-plan height.
  have hmem : (witnessSizes w hpos).logMem = t.κ + 1 := hrep.κ_eq.trans hκ'
  have hτ : ∀ j : Fin 6, 2 ^ (witnessSizes w hpos).τ j =
      tableHeight t.runRows (n + 1) (fillTables.getD j .xor) := by
    intro j
    show 2 ^ Nat.log 2 (tableAt w ⟨j, by omega⟩).table.length = _
    rw [hlen j]
    obtain ⟨σ, -, hσ⟩ := tableHeight_pow (τ := n + 1) (by unfold maxLogRows; omega) hrows
      (fillTables.getD j .xor)
    rw [hσ, Nat.log_pow (by norm_num)]
  have hle : ∀ j : Fin 6, j ≠ 4 → 2 ^ (witnessSizes w hpos).τ j ≤ 2 ^ n := by
    intro j hj
    rw [hτ j]
    refine tableHeight_le hrun hn (by omega) ?_
    fin_cases j <;> first | exact absurd rfl hj | decide
  have h4 : 2 ^ (witnessSizes w hpos).τ 4 = 2 ^ (n + 1) := by
    rw [hτ 4]
    rfl
  have h5 : 2 ^ 3 ≤ 2 ^ (witnessSizes w hpos).τ 5 := by
    rw [hτ 5]
    exact (floor_le_fillTarget _ _).trans_eq' rfl
  have hcap : ∀ j : Fin 6, (witnessSizes w hpos).τ j ≤ maxLogRows := by
    intro j
    have : 2 ^ (witnessSizes w hpos).τ j ≤ 2 ^ (n + 1) := by
      by_cases hj : j = 4
      · subst hj
        exact h4.le
      · exact (hle j hj).trans (Nat.pow_le_pow_right (by norm_num) (by omega))
    have := (Nat.pow_le_pow_iff_right (by norm_num)).mp this
    unfold maxLogRows
    omega
  refine ⟨?_, ?_, hcap, (Nat.pow_le_pow_iff_right (by norm_num)).mp h5, ?_⟩
  · rw [hmem]
    have := hv.1.1
    omega
  · rw [hmem]
    exact hκ
  · refine leanIsaμ_le_of_total_le ?_
    rw [blocks_total_eq, hmem, pow_add 2 8, h4]
    have h0 := hle 0 (by decide)
    have h1 := hle 1 (by decide)
    have h2 := hle 2 (by decide)
    have h3 := hle 3 (by decide)
    have h5' := hle 5 (by decide)
    have e1 : 2 ^ (t.κ + 1) = 2 * 2 ^ t.κ := by ring
    have e2 : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
    rw [e1, e2]
    generalize 2 ^ (witnessSizes w hpos).τ 0 = a0 at *
    generalize 2 ^ (witnessSizes w hpos).τ 1 = a1 at *
    generalize 2 ^ (witnessSizes w hpos).τ 2 = a2 at *
    generalize 2 ^ (witnessSizes w hpos).τ 3 = a3 at *
    generalize 2 ^ (witnessSizes w hpos).τ 5 = a5 at *
    omega

/-- **An admissible witness for a small execution.** A valid execution of a program with the fill
blocks that is small (`Trace.Small`: at most `2^19` steps, `2^23` words of memory and `2^23`
instructions) has a witness satisfying leanISA's constraint system at sizes the verifier admits. -/
theorem exists_admissible_witness {prog : Program} {input : PublicInput} {t : Trace prog}
    (hfill : HasFillBlocks prog) (hv : ValidExecution prog input t) (hsmall : t.Small) :
    ∃ w s, SatisfiedBy prog input w ∧ Sizes.ofWitness w = some s ∧ s.Admissible prog := by
  have hm : 2 ^ t.κ ≤ 2 ^ 23 := Nat.pow_le_pow_right (by norm_num) hsmall.mem_le
  have hc : 2 ^ prog.logSize ≤ 2 ^ 23 := Nat.pow_le_pow_right (by norm_num) hsmall.code_le
  obtain ⟨-, -, -, w, s, hw, -, hs, hadm⟩ := exists_admissible_witness_of_budget (n := 19) hfill hv
    hsmall.steps_le (by norm_num) (by unfold maxMu; omega)
  exact ⟨w, s, hw, hs, hadm⟩

/-! ## The honest proof of an execution -/

/-- The honest prover's witness for an execution `t` at rate `ρ`: the rate is valid, and `w`
satisfies leanISA's constraint system at sizes `s` the verifier admits and represents a padded
valid execution of `t`. -/
def HonestFor (prog : Program) (input : PublicInput) (t : Trace prog) (ρ : ℕ)
    (w : EnsembleWitness (leanIsaEnsemble prog)) (s : Sizes) : Prop :=
  validRate ρ ∧ SatisfiedBy prog input w ∧ Sizes.ofWitness w = some s ∧ s.Admissible prog ∧
    ∃ t', t'.PaddedFrom t ∧ ValidExecution prog input t' ∧ AssignmentRepresents w t'

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
  have hq := m3Holds_stackOf (F := Blake2sFlock.blake2sFlockSpec) hw hs
  have hrun := runI_leanVmProgram hadm hρ hq walkFaithful_blake2sFlockSpec
  exact runProof_prove H _ _ _ fuel (fun chal ↦ (hrun chal).1) (fun chal ↦ (hrun chal).2) h

/-- **The honest prover succeeds on a small execution.** For a valid execution of a program with
the fill blocks that is small, at a valid rate, the honest proof exists as soon as every
proof-of-work search the verifier program asks for finds a nonce below `fuel`. -/
theorem honestProofOf_isSome {prog : Program} {input : PublicInput} {t : Trace prog} {ρ : ℕ}
    (hfill : HasFillBlocks prog) (hv : ValidExecution prog input t) (hsmall : t.Small)
    (hρ : validRate ρ) (H : Bytes → Digest) (fuel : ℕ)
    (hpow : ∀ hist bits k cv,
      (leanVmProgram (bytecodeWords prog) (publicDigest input)).after hist =
          some (.grind bits k) → findNonce H bits cv fuel ≠ none) :
    (honestProofOf H prog input t ρ fuel).isSome := by
  have hm : 2 ^ t.κ ≤ 2 ^ 23 := Nat.pow_le_pow_right (by norm_num) hsmall.mem_le
  have hc : 2 ^ prog.logSize ≤ 2 ^ 23 := Nat.pow_le_pow_right (by norm_num) hsmall.code_le
  obtain ⟨t', hp, hv', w, s, hw, hrep, hs, hadm⟩ := exists_admissible_witness_of_budget (n := 19)
    hfill hv hsmall.steps_le (by norm_num) (by unfold maxMu; omega)
  have hex : ∃ w s, HonestFor prog input t ρ w s := ⟨w, s, hρ, hw, hs, hadm, t', hp, hv', hrep⟩
  unfold honestProofOf
  split_ifs
  exact Option.isSome_iff_ne_none.mpr (prove_ne_none H _ _ _ fuel hpow)

/-- **Completeness for a small execution.** A valid execution of a program with the fill blocks
that is small, at a valid rate: when every proof-of-work search succeeds below `fuel`, the honest
prover outputs a proof, and the verifier accepts it, for every hash function. -/
theorem complete_of_small {prog : Program} {input : PublicInput} {t : Trace prog} {ρ : ℕ}
    (hfill : HasFillBlocks prog) (hv : ValidExecution prog input t) (hsmall : t.Small)
    (hρ : validRate ρ) (H : Bytes → Digest) (fuel : ℕ)
    (hpow : ∀ hist bits k cv,
      (leanVmProgram (bytecodeWords prog) (publicDigest input)).after hist =
          some (.grind bits k) → findNonce H bits cv fuel ≠ none) :
    ∃ proof, honestProofOf H prog input t ρ fuel = some proof ∧
      verifyWith (m := Id) H (bytecodeWords prog) (publicDigest input) proof = true := by
  obtain ⟨proof, h⟩ := Option.isSome_iff_exists.mp
    (honestProofOf_isSome hfill hv hsmall hρ H fuel hpow)
  exact ⟨proof, h, verify_honestProofOf H h⟩

end
end LeanerVM.Protocol.EndToEnd.Complete
