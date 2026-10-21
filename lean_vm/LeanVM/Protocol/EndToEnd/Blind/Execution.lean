/-
  LeanVM.Protocol.EndToEnd.Blind.Execution

  From a stack satisfying the leanISA relation without Flock to an execution under the
  Flock-blind semantics, the witness read off the stack representing it; the extractor of such an
  execution, and knowledge soundness of V° for executions.
-/

module

public import LeanVM.Protocol.EndToEnd.Blind.Statements
public import LeanVM.Arithmetization.Soundness.Theorem

/-!
# The execution V° extracts

Without Flock's R1CS nothing binds a `BLAKE2S` row's output cells to the compression: what a stack
satisfying `M3HoldsBlind` carries is an execution under the Flock-blind semantics `blakeFree`
(`LeanVM.Spec.IsaWith`), whose `BLAKE2S` asks only that the nine cells be canonical. The table
stores every cell as two limbs (`E.ofCell`), so they are canonical by construction.

* `constraintSoundnessBlind`: a witness satisfying the constraint statement without its BLAKE2s
  validity (`SatisfiedByB`) represents (`AssignmentRepresentsB`) an execution valid under
  `blakeFree` (`ValidExecutionB`): `constraintSoundness` with the rows' steps under `blakeFree`
  (`rowsStep_free`, whose `BLAKE2S` rows read their cells through the table's bindings alone);
* `execution_of_extractedBlind`: a stack satisfying `M3HoldsBlind` at admissible sizes reads
  back (`witnessOf`) to such a witness (`satisfiedByB_witnessOf`), so to such an execution, whose
  image is the witness's;
* `extractBlind`, `BreaksBlind`, `blindKnowledgeSoundness_execution`: the extractor of an
  execution (the image of the extracted stack, run under `blakeFree` until it halts), and the
  probability that V° accepts, the last instruction is not a `JUMP`, and the extracted execution
  is not valid under `blakeFree`: at most `soundnessError Q`.
-/

namespace LeanVM.Protocol.EndToEnd.Blind

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Protocol
open LeanVM.Protocol.Compile LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Verifier
open LeanVM.Protocol.LeanIsa LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.EndToEnd.Sound
open LeanVM.Protocol.EndToEnd.Complete (publicDigest)
open LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Rom
open Air.Flat (EnsembleWitness)
open OracleComp OracleSpec
open scoped ENNReal

@[expose] public section

/- The enumeration of `Digest` must never be unfolded by unification. -/
attribute [local irreducible] instFintypeDigest

/-! ## Constraint soundness without the BLAKE2s validity -/

/-- **The witness `w` represents the trace `t` under the semantics `S`**: the image the data names
is the trace's, and each step of the trace's run under `S` occurs as the state pull and push of
some row (`AssignmentRepresents`, the register sequence read off the run under `S`). -/
structure AssignmentRepresentsB (S : BlakeSem) {prog : Program}
    (w : EnsembleWitness (leanIsaEnsemble prog)) (t : Trace prog) : Prop where
  /-- The memory log-size is the trace's. -/
  κ_eq : (imageOf w.data).1 = t.κ
  /-- Every word of the image is the trace's. -/
  image_eq : ∀ i (hi : i < 2 ^ t.κ), (imageOf w.data).2 ⟨i, κ_eq ▸ hi⟩ = t.image ⟨i, hi⟩
  /-- Each step of the run occurs as some row's state pull and push. -/
  steps_embed : ∀ k < t.steps, ∃ r r', runB S prog t.image k Regs.initial = some r ∧
    runB S prog t.image (k + 1) Regs.initial = some r' ∧ RowSteps w r r'

/-- **Constraint soundness without the BLAKE2s validity.** A witness satisfying the constraint
statement of well-formed bytecode on `input` but for the BLAKE2s validity represents an execution
of the program on `input` valid under the Flock-blind semantics: the trace is the image the data
names and the run the state channel's balance contains, each of whose steps is a row. -/
theorem constraintSoundnessBlind {prog : Program} {input : PublicInput}
    {w : EnsembleWitness (leanIsaEnsemble prog)} (hsafe : SentinelSafe prog)
    (h : SatisfiedByB prog input w) :
    ∃ t, AssignmentRepresentsB blakeFree w t ∧ ValidExecutionB blakeFree prog input t := by
  obtain ⟨f, hf, n, hn, hsteps⟩ := exists_walkB blakeFree hsafe h fun _ hf ↦ rowsStep_free h hf
  let t : Trace prog := ⟨(imageOf w.data).1, (imageOf w.data).2, n⟩
  refine ⟨t, ⟨rfl, fun _ _ ↦ rfl, fun k hk ↦ ?_⟩,
    ⟨h.caps.minLogMem_le, h.caps.le_maxLogMem, h.word0_eq, h.word1_eq⟩, hn⟩
  obtain ⟨p, hp, h1, h2⟩ := hsteps k hk
  obtain ⟨ht, hrow⟩ := mem_opPairs hp
  refine ⟨(f p).src, (f p).next, h1, h2, p.1, List.mem_of_mem_take ht, p.2, hrow, ?_, ?_⟩
  · rw [rowMessagesOn_eq_rowSends, (hf p hp).1, RowRec.sends, Channel.toRaw_name,
      sendsOf_statePull]
    rfl
  · rw [rowMessagesOn_eq_rowSends, (hf p hp).1, RowRec.sends, Channel.toRaw_name,
      sendsOf_statePush]

/-- **The stack V° extracts has a Flock-blind execution.** On admissible sizes and well-formed
bytecode, a stack satisfying the leanISA relation without Flock reads back to a witness that
represents an execution of the program on the input valid under the Flock-blind semantics. -/
theorem execution_of_extractedBlind (F : FlockSpec) {prog : Program} {input : PublicInput}
    {s : Sizes} {q : Column (leanIsaμ prog s)} (hsafe : SentinelSafe prog)
    (hs : s.Admissible prog) (h : M3HoldsBlind (leanIsaInstance F prog s) input q) :
    ∃ t, AssignmentRepresentsB blakeFree (witnessOf F prog s q) t ∧
      ValidExecutionB blakeFree prog input t :=
  constraintSoundnessBlind hsafe (satisfiedByB_witnessOf F prog s q hs h.1 h.2.1 h.2.2.1 h.2.2.2)

/-! ## The extractor of an execution -/

open Classical in
/-- The execution of `prog` on a memory image under the semantics `S`: the image, run from
`(1, 1)` for the least number of steps after which it halts; `none` if it never does
(`LeanVM.haltingRun` under `S`). -/
noncomputable def haltingRunB (S : BlakeSem) (prog : Program) {κ : ℕ} (image : MemImage κ) :
    Option (Trace prog) :=
  if h : ∃ n, runB S prog image n Regs.initial = some (Regs.final prog) then
    some ⟨κ, image, Nat.find h⟩
  else none

/-- A witness representing an execution valid under `S` has its image's halting run under `S`,
valid. -/
theorem haltingRunB_valid {S : BlakeSem} {prog : Program} {input : PublicInput}
    {w : EnsembleWitness (leanIsaEnsemble prog)} {t : Trace prog}
    (hrep : AssignmentRepresentsB S w t) (hv : ValidExecutionB S prog input t) :
    ∃ t', haltingRunB S prog (imageOf w.data).2 = some t' ∧ ValidExecutionB S prog input t' := by
  obtain ⟨κ, image, steps⟩ := t
  obtain ⟨hκ, himage, -⟩ := hrep
  generalize imageOf w.data = p at hκ himage ⊢
  obtain ⟨κ', image'⟩ := p
  dsimp only at hκ himage ⊢
  subst hκ
  obtain rfl : image' = image := funext fun i ↦ himage i i.isLt
  have h : ∃ n, runB S prog image' n Regs.initial = some (Regs.final prog) := ⟨steps, hv.2⟩
  exact ⟨⟨_, image', Nat.find h⟩, by simp only [haltingRunB, h, ↓reduceDIte], hv.1,
    Nat.find_spec h⟩

/-- **The extractor of V°'s executions**: the memory image of the stack `extractStackBlind`
extracts, run under the Flock-blind semantics until it halts. -/
noncomputable def extractBlind (prog : Program) (input : PublicInput)
    (answers : HashSpec.QueryCache) (proof : Proof) : Option (Trace prog) :=
  (extractStackBlind prog input answers proof).bind fun x ↦
    haltingRunB blakeFree prog (imageOf (witnessOf F₀ prog x.1 x.2).data).2

/-- **The adversary breaks V°**: V° accepts its statement and proof, the program's last
instruction is not a `JUMP`, and the extracted execution is not valid under the Flock-blind
semantics. -/
def BreaksBlind (z : Outcome) : Prop :=
  z.accepted ∧ SentinelSafe z.program ∧
    ¬ ∃ t, extractBlind z.program z.input z.cache z.proof = some t ∧
      ValidExecutionB blakeFree z.program z.input t

/-- **Knowledge soundness of V° for executions.** For an adversary making at most `Q` queries,
which chooses the program, the public input and the proof, V° accepts while the program's last
instruction is not a `JUMP` and the extracted execution is not valid under the Flock-blind
semantics with probability at most `soundnessError Q`. -/
theorem blindKnowledgeSoundness_execution {A : Adversary} {Q : ℕ} (hA : A.IsTotalQueryBound Q) :
    Pr{let z ← experimentBlind A}[BreaksBlind z] ≤ soundnessError Q := by
  have hV : (fun z : Statement × Proof ↦
      verifyBlindWith queryH (bytecodeWords z.1.1) (publicDigest z.1.2) z.2) =
      verifierFam leanVmSeeds anyProgramBlind :=
    funext fun z ↦ (verifierFam_blind z).symm
  have h := romSound_of_imp anyProgramBlind anyCertBlind leanVmSeeds
    (fun x ↦ rootOk_stmtHistoryOf _ x) εLean anyCertBlind_bound A Q hA
    leanVmQueryBound isTotalQueryBound_blindFam
    (fun z c ↦ SentinelSafe z.1.1 ∧
      ¬ ∃ t, extractBlind z.1.1 z.1.2 c z.2 = some t ∧ ValidExecutionB blakeFree z.1.1 z.1.2 t)
    (fun z c hv hb ↦ by
      simp only [leanVmSeeds, nodeAt_stmtHistoryOf] at hv
      refine doomed_of_doomedRunOf blindProgram (fun x ↦ blindCert x.1 x.2) hv
        (doomed_of_not_extractedBlind z.1.1 z.1.2 hv fun ⟨s, q, hx, hs, hM⟩ ↦ hb.2 ?_)
      obtain ⟨t, hrep, ht⟩ := execution_of_extractedBlind F₀ hb.1 hs hM
      obtain ⟨t', ht', hv'⟩ := haltingRunB_valid hrep ht
      exact ⟨t', by simp only [extractBlind, hx, Option.bind_some]; exact ht', hv'⟩)
  rw [leanVmQueryBound_eq] at h
  have he : experimentBlind A = Rom.romExperiment A (verifierFam leanVmSeeds anyProgramBlind) := by
    rw [← hV]; rfl
  rw [he]
  refine (le_of_eq ?_).trans (h.trans (le_of_eq ?_))
  · rfl
  · rw [soundnessError, failBound]
    rfl

end
end LeanVM.Protocol.EndToEnd.Blind
