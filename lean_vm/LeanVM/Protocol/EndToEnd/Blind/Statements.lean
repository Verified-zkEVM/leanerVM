/-
  LeanVM.Protocol.EndToEnd.Blind.Statements

  Knowledge soundness of the Flock-blind verifier V° against an adversary that chooses the
  statement: the program of every statement and its certificate, the cache form of the
  random-oracle theorem's final inequality, and the probability bound.
-/

module

public import LeanVM.Protocol.EndToEnd.Blind.Theorem
public import LeanVM.Protocol.EndToEnd.Blind.Cost
public import LeanVM.Protocol.EndToEnd.Sound.Statements
public import LeanVM.Protocol.LeanVM

/-!
# Knowledge soundness of V° for adversarially chosen statements

The deployed verifier's statement-universal program (`Sound.anyProgram`: the statement's scalars
read, then its verifier program) and certificate (`Sound.anyCert`) are built here for any family of
programs `P bytecode publicInput` with a certificate per statement (`anyProgramOf`, `anyCertOf`),
from the deployed lemmas on statement histories; V°'s are the family `blindProgram`
(`anyProgramBlind`, `anyCertBlind`). The seedings are the deployed ones (`leanVmSeeds`): V° runs
from the deployed seed.

* `blind_knowledge_cache` (**the cache form**): for an oracle log `ℓ` without failure and any
  statement and proof that V° accepts with every hash answered by `look ℓ`, either the potential
  of `anyCertBlind` on `ℓ` is at least `1`, or the extractor `extractStackBlind`, reading `ℓ`'s
  answers (`cacheOf ℓ`, whose lookup is `look ℓ`),
  returns admissible sizes and a stack satisfying the leanISA relation without Flock
  (`ExtractedBlind`). It is `final_ineq` (`LeanVM.Protocol.Compile.Rom.Final`) at V°'s
  certificate, the engine's last step, for later packages to run in their own engine.
* `blindKnowledgeSoundness` (**the probability form**): in the random-oracle experiment of
  `LeanVM/Spec/Statement.lean` with V° (`experimentBlind`), an adversary of `Q` queries makes V°
  accept while the extractor fails with probability at most `soundnessError Q`, the deployed
  bound.
-/

namespace LeanVM.Protocol.EndToEnd.Blind

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Protocol
open LeanVM.Protocol.Compile LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Verifier
open LeanVM.Protocol.LeanIsa LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.EndToEnd.Sound
open LeanVM.Protocol.EndToEnd.Complete (publicDigest)
open LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Rom
open OracleComp OracleSpec
open scoped ENNReal

@[expose] public section

/- The enumeration of `Digest` must never be unfolded by unification. -/
attribute [local irreducible] instFintypeDigest

/-! ## The program of every statement, for a family of programs -/

section Family

variable (P : List K → Digest → Prog Bool)

/-- **The verifier program of every statement**, for the family `P`: the bytecode's length and
words and the public input's lanes, read as scalars, then `P` of that bytecode and public input
(`Sound.anyProgram` is the family `leanVmProgram`). -/
def anyProgramOf : Prog Bool :=
  .read fun n ↦ readWords (kNat (n.limb 0)) fun ws ↦ readWords 4 fun ls ↦
    P ws (publicDigest ⟨fun i ↦ ls.getD i 0⟩)

/-- **The root of a statement leads to the statement's program.** -/
theorem after_stmtHistoryOf (x : Statement) :
    (anyProgramOf P).after (stmtHistory x) = some (P (bytecodeWords x.1) (publicDigest x.2)) := by
  simp only [stmtHistory, stmtScalars, List.map_cons, anyProgramOf, Prog.after, limb_wordE,
    kNat_ofBits (length_bytecodeWords_lt x.1), List.map_append]
  rw [after_readWords]
  rw [← List.append_nil ((List.map Ev.read (List.map wordE (List.ofFn x.2.lanes)))),
    after_readWords' _ _ List.length_ofFn]
  have hpi : (⟨fun i ↦ (List.ofFn x.2.lanes).getD i 0⟩ : PublicInput) = x.2 := by
    obtain ⟨lanes⟩ := x.2
    congr 1
    funext i
    fin_cases i <;> simp
  rw [hpi]
  cases P (bytecodeWords x.1) (publicDigest x.2) <;> rfl

/-- The node of `anyProgramOf P` at a statement's root is the statement's program. -/
theorem nodeAt_stmtHistoryOf (x : Statement) :
    nodeAt (anyProgramOf P) (stmtHistory x) = P (bytecodeWords x.1) (publicDigest x.2) := by
  simp [nodeAt, after_stmtHistoryOf]

/-- A statement's root is a root of `anyProgramOf P`. -/
theorem rootOk_stmtHistoryOf (x : Statement) : RootOk (anyProgramOf P) (stmtHistory x) := by
  have ha := after_stmtHistoryOf P x
  exact ⟨reachable_of_after_reads _ ha, boundary_map_read (by simp [stmtScalars]),
    grindBits_map_read _, commits_map_read _, by simp [ha]⟩

variable (C : (x : Statement) → Cert (P (bytecodeWords x.1) (publicDigest x.2)))

/-- **Doom for every statement**: past a statement's root, its certificate's doom on the rest. -/
def anyDOf (h : List Ev) : Prop :=
  ∃ x, stmtHistory x <+: h ∧ (C x).D (h.drop (stmtHistory x).length)

open Classical in
/-- The escape bound for every statement: its certificate's past its root, `0` elsewhere. -/
noncomputable def anyεOf (h : List Ev) : ℝ≥0∞ :=
  if hx : ∃ x, stmtHistory x <+: h then
    (C hx.choose).ε (h.drop (stmtHistory hx.choose).length)
  else 0

/-- Past a statement's root, doom for every statement is the statement's. -/
theorem anyDOf_iff (x : Statement) (h' : List Ev) :
    anyDOf P C (stmtHistory x ++ h') ↔ (C x).D h' := by
  constructor
  · rintro ⟨x', hx', hD⟩
    obtain rfl := stmt_eq_of_prefix hx' (List.prefix_append _ _)
    simpa using hD
  · intro hD
    exact ⟨x, List.prefix_append _ _, by simpa using hD⟩

/-- Past a statement's root, the escape bound is the statement's. -/
theorem anyεOf_eq (x : Statement) (h' : List Ev) :
    anyεOf P C (stmtHistory x ++ h') = (C x).ε h' := by
  unfold anyεOf
  split
  · rename_i hx
    rw [stmt_eq_of_prefix hx.choose_spec (List.prefix_append _ _)]
    simp
  · rename_i hx
    exact absurd ⟨x, List.prefix_append _ _⟩ hx

/-- A doomed history is past a root. -/
theorem anyDOf_split {h : List Ev} (hD : anyDOf P C h) :
    ∃ x h', h = stmtHistory x ++ h' ∧ (C x).D h' := by
  obtain ⟨x, ⟨h', rfl⟩, hD⟩ := hD
  exact ⟨x, h', rfl, by simpa using hD⟩

/-- **The certificate of every statement**, from a certificate per statement. -/
noncomputable def anyCertOf : Cert (anyProgramOf P) where
  D := anyDOf P C
  ε := anyεOf P C
  read := by
    intro h k e hr ha hD
    obtain ⟨x, h', rfl, hDx⟩ := anyDOf_split P C hD
    have hax := after_stmtHistoryOf P x
    rw [List.append_assoc, anyDOf_iff]
    exact (C x).read e
      (reachable_drop hax (commits_stmtHistory x) hr h' rfl) (by rwa [after_drop hax] at ha) hDx
  grind := by
    intro h b k hr ha hD
    obtain ⟨x, h', rfl, hDx⟩ := anyDOf_split P C hD
    have hax := after_stmtHistoryOf P x
    rw [List.append_assoc, anyDOf_iff]
    exact (C x).grind
      (reachable_drop hax (commits_stmtHistory x) hr h' rfl) (by rwa [after_drop hax] at ha) hDx
  commit := by
    intro h ht w k word hr ha hw hD
    obtain ⟨x, h', rfl, hDx⟩ := anyDOf_split P C hD
    have hax := after_stmtHistoryOf P x
    rw [List.append_assoc, anyDOf_iff]
    exact (C x).commit word
      (reachable_drop hax (commits_stmtHistory x) hr h' rfl) (by rwa [after_drop hax] at ha) hw hDx
  group := by
    intro h p hr hb ha hp hD
    obtain ⟨x, h', rfl, hDx⟩ := anyDOf_split P C hD
    have hax := after_stmtHistoryOf P x
    rw [esc_drop (h₀ := stmtHistory x) (commits_stmtHistory x) (anyDOf_iff P C x), anyεOf_eq]
    exact (C x).group (reachable_drop hax (commits_stmtHistory x) hr h' rfl)
      (boundary_drop hb) (by rwa [after_drop hax] at ha) hp hDx
  final := by
    intro h hr ha hD
    obtain ⟨x, h', rfl, hDx⟩ := anyDOf_split P C hD
    have hax := after_stmtHistoryOf P x
    exact (C x).final (reachable_drop hax (commits_stmtHistory x) hr h' rfl)
      (by rwa [after_drop hax] at ha) hDx

/-- **The certificate's bound**, from every statement's. -/
theorem anyCertOf_bound {εmax : ℝ≥0∞}
    (hC : ∀ x h, (2 : ℝ≥0∞)⁻¹ ^ min (grindBits h) 64 * (C x).ε h ≤ εmax) (h : List Ev) :
    (2 : ℝ≥0∞)⁻¹ ^ min (grindBits h) 64 * (anyCertOf P C).ε h ≤ εmax := by
  by_cases hx : ∃ x, stmtHistory x <+: h
  · obtain ⟨x, h', rfl⟩ : ∃ x h', h = stmtHistory x ++ h' := by
      obtain ⟨x, h', he⟩ := hx
      exact ⟨x, h', he.symm⟩
    show _ * anyεOf P C _ ≤ _
    rw [anyεOf_eq, grindBits_stmt]
    exact hC x h'
  · show _ * anyεOf P C _ ≤ _
    simp only [anyεOf, hx, ↓reduceDIte, mul_zero, zero_le]

/-- The verifier of the statement and proof `z` is the statement's seeded program. -/
theorem verifierFam_of (z : Statement × Proof) :
    verifierFam leanVmSeeds (anyProgramOf P) z =
      verifierComp (leanVmSeed (bytecodeWords z.1.1) (publicDigest z.1.2))
        (P (bytecodeWords z.1.1) (publicDigest z.1.2)) z.2 := by
  simp only [verifierFam, leanVmSeeds, nodeAt_stmtHistoryOf]

/-- **A statement's doom is doom for every statement.** -/
theorem doomed_of_doomedRunOf {x : Statement} {π : Proof} {c : HashSpec.QueryCache}
    (hv : Rom.verify (fun y ↦ c y) (leanVmSeed (bytecodeWords x.1) (publicDigest x.2))
      (P (bytecodeWords x.1) (publicDigest x.2)) π = some true)
    (hd : DoomedRun (C x) (leanVmSeed (bytecodeWords x.1) (publicDigest x.2)) π c) :
    Doomed (anyCertOf P C) leanVmSeeds (x, π) c := by
  obtain ⟨h₀, hh₀, hb, hD⟩ := hd
  refine ⟨stmtHistory x ++ h₀, ?_,
    by show (stmtHistory x).length ≤ _; rw [List.length_append]; omega, ?_,
    (anyDOf_iff P C x h₀).mpr hD⟩
  · change stmtHistory x ++ h₀ <+: extractedFrom (fun y ↦ c y)
      (leanVmSeed (bytecodeWords x.1) (publicDigest x.2)) (nodeAt (anyProgramOf P) (stmtHistory x))
      (stmtHistory x) π
    rw [nodeAt_stmtHistoryOf, extractedFrom_eq _ _ _ _ _ hv]
    exact (List.prefix_append_right_inj _).mpr hh₀
  · rcases List.eq_nil_or_concat h₀ with rfl | ⟨h'', e, rfl⟩
    · rw [List.append_nil]; exact (rootOk_stmtHistoryOf P x).2.1
    · rw [List.concat_eq_append] at hb ⊢
      rw [← List.append_assoc]
      exact boundary_append_of hb

end Family

/-! ## V° for every statement -/

/-- **V° for every statement**: the statement's scalars, then its Flock-blind verifier program. -/
abbrev anyProgramBlind : Prog Bool := anyProgramOf blindProgram

/-- **The certificate of V° for every statement.** -/
noncomputable abbrev anyCertBlind : Cert anyProgramBlind :=
  anyCertOf blindProgram fun x ↦ blindCert x.1 x.2

/-- Every escape bound of `anyCertBlind`, discounted by the proof of work before its group, is at
most `2^-128`. -/
theorem anyCertBlind_bound (h : List Ev) :
    (2 : ℝ≥0∞)⁻¹ ^ min (grindBits h) 64 * anyCertBlind.ε h ≤ εLean :=
  anyCertOf_bound _ _ (fun x ↦ blindCert_bound x.1 x.2) h

/-- The verifier of the statement and proof `z` is V°, with the hash a query. -/
theorem verifierFam_blind (z : Statement × Proof) :
    verifierFam leanVmSeeds anyProgramBlind z =
      verifyBlindWith queryH (bytecodeWords z.1.1) (publicDigest z.1.2) z.2 := by
  rw [verifierFam_of, verifierComp_blind]

/-- V° makes at most `leanVmQueryBound` queries on every statement and proof. -/
theorem isTotalQueryBound_blindFam (z : Statement × Proof) :
    IsTotalQueryBound (verifierFam leanVmSeeds anyProgramBlind z) leanVmQueryBound := by
  rw [verifierFam_of]
  exact isTotalQueryBound_blind _ _ _

/-! ## The cache form -/

/-- **Knowledge soundness of V°, the cache form.** For an oracle log `ℓ` without failure, if V°
accepts the statement `x` and the proof `π` with every hash answered by `look ℓ`, then either the
potential of V°'s certificate on `ℓ` is at least `1`, or the extractor reading `ℓ`'s answers returns
admissible sizes and a stack satisfying the leanISA relation without Flock. -/
theorem blind_knowledge_cache {ℓ : Log} (hf : ¬ Fail leanVmSeeds ℓ) {x : Statement} {π : Proof}
    (hv : Rom.verify (look ℓ) (leanVmSeed (bytecodeWords x.1) (publicDigest x.2))
      (blindProgram (bytecodeWords x.1) (publicDigest x.2)) π = some true) :
    1 ≤ pot anyCertBlind.D leanVmSeeds anyProgramBlind ℓ ∨
      ExtractedBlind x.1 x.2 (cacheOf ℓ) π := by
  by_cases hx : ExtractedBlind x.1 x.2 (cacheOf ℓ) π
  · exact Or.inr hx
  refine Or.inl (final_ineq anyCertBlind hf (rootOk_stmtHistoryOf _ x) ?_
    (doomed_of_doomedRunOf blindProgram (fun x ↦ blindCert x.1 x.2) (c := cacheOf ℓ) hv
      (doomed_of_not_extractedBlind x.1 x.2 (c := cacheOf ℓ) hv hx)))
  show Rom.verify (look ℓ) _ (nodeAt (anyProgramOf blindProgram) (stmtHistory x)) π = some true
  rw [nodeAt_stmtHistoryOf]
  exact hv

/-- **The cache form, with V° as `LeanVM/Spec` states it** (`verifyBlindWith` with the hash
`look ℓ`). -/
theorem blind_knowledge_cache' {ℓ : Log} (hf : ¬ Fail leanVmSeeds ℓ) {x : Statement}
    {π : Proof}
    (hv : verifyBlindWith (look ℓ) (bytecodeWords x.1) (publicDigest x.2) π = some true) :
    1 ≤ pot anyCertBlind.D leanVmSeeds anyProgramBlind ℓ ∨
      ExtractedBlind x.1 x.2 (cacheOf ℓ) π := by
  refine blind_knowledge_cache hf ?_
  rw [← hv]
  simp only [Rom.verify, verifyBlindWith, seedRun_leanVmSeed]

/-! ## The probability form -/

/-- **The random-oracle experiment with V°**: the adversary, then V° on its statement and proof,
both querying one lazily sampled random oracle (`LeanVM.experiment` with `verifyBlindWith`). -/
noncomputable def experimentBlind (A : Adversary) : ProbComp Outcome :=
  (simulateQ HashSpec.randomOracle
    (A >>= fun z ↦ (z, ·) <$> verifyBlindWith queryH (bytecodeWords z.1.1) (publicDigest z.1.2)
      z.2)).run ∅

/-- **Knowledge soundness of V° in the random-oracle model.** For an adversary making at most
`Q` queries, which chooses the program, the public input and the proof, V° accepts while the
extractor finds no admissible sizes and stack satisfying the leanISA relation without Flock with
probability at most `soundnessError Q`. -/
theorem blindKnowledgeSoundness {A : Adversary} {Q : ℕ} (hA : A.IsTotalQueryBound Q) :
    Pr{let z ← experimentBlind A}[z.accepted ∧ ¬ ExtractedBlind z.program z.input z.cache z.proof]
      ≤ soundnessError Q := by
  have hV : (fun z : Statement × Proof ↦
      verifyBlindWith queryH (bytecodeWords z.1.1) (publicDigest z.1.2) z.2) =
      verifierFam leanVmSeeds anyProgramBlind :=
    funext fun z ↦ (verifierFam_blind z).symm
  have h := romSound_of_imp anyProgramBlind anyCertBlind leanVmSeeds
    (fun x ↦ rootOk_stmtHistoryOf _ x) εLean anyCertBlind_bound A Q hA
    leanVmQueryBound isTotalQueryBound_blindFam
    (fun z c ↦ ¬ ExtractedBlind z.1.1 z.1.2 c z.2)
    (fun z c hv hb ↦ by
      simp only [leanVmSeeds, nodeAt_stmtHistoryOf] at hv
      exact doomed_of_doomedRunOf blindProgram (fun x ↦ blindCert x.1 x.2) hv
        (doomed_of_not_extractedBlind z.1.1 z.1.2 hv hb))
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
