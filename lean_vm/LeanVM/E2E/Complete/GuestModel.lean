/-
  LeanVM.E2E.Complete.GuestModel

  L2's end: the guest's completeness over every completeness model, from what group B1 proves over
  the model (`B1CompHyps`), and at the deployed model the deployed completeness re-derived.
-/

module

public import LeanVM.Guest.B1.Main.MainBudgetC
public import LeanVM.Guest.B1.Main.RowsCModel
public import LeanVM.Guest.EndFinalComplete
public import LeanVM.Guest.Count.MainS
public import LeanVM.Guest.B1.Sig.ArmCostB2CS
public import LeanVM.Guest.EndCompleteAssembly
public import LeanVM.Guest.DeferredCaps
public import LeanVM.Guest.B2C.KRetemp
public import LeanVM.Guest.B2C.KFacts

/-!
# The guest's completeness over a completeness model

`GuestCompleteModel` (`Interfaces.lean`, package L2 of `docs/roadmap/t6-completeness.md`) less its
decoding conjunct is `GuestCompleteModelExec`: for every completeness model `CM`, a node relation
answered by `CM.H` within the deployed limits, the caps and the budget has a valid execution under
`CM.sem` within the committed size. It rests on what group B1 proves over the model, collected in
`B1CompHyps CM` (each field the shape of its deployed lemma over the model):

* `callees`: `main`'s callees complete under `CM.sem` over `CM.H`, placed, within the deployed
  callee bounds (`CalleesAtC`, the shape of `calleesAt_proved`);
* `VsGood`, `vs_inv`: a child's proof accepted with every hash answered by `CM.H` (within the
  limits' stack log and stream, its openings agreeing in the caps under `Ht`) has a run in
  `VsGood` of its fixed claims, of the guest's fresh shape (the shape of `vs_inversion` with
  `deferredCaps` and `ea_freshShaped`).

The inline Fiat-Shamir rows and the batching sumchecks over the model are B1's merged hash sites
(`fsRowsC_model`, `bsRowsC_model`). `guestCompleteModelExec_of`: `∀ CM, B1CompHyps CM` gives
`GuestCompleteModelExec`, by `mainCompleteC_of` at the deployed frame sizes, certificates, budget
`b2cBudget'` and k4's weights under the model (`Count.kcWtS`), `honest_of_mainC` and
`validB_of_honestC`.

**At the deployed model** every field is its deployed lemma (`b1CompHyps_deployed`: the callees
from `calleesAt_proved`, the runs from `vs_inversion`), and `guest_complete_of_model` re-derives
the deployed `End.guest_complete` (`GuestCompleteWithin b2cBudget'`) from the model theorem.
-/

namespace LeanVM.E2E.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Node LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main

@[expose] public section

/-- **What `main`'s completeness over a completeness model takes of group B1**: `main`'s callees
complete under the model's semantics over its answered hash (`CalleesAtC`), and every child's
accepted proof run by a run in `VsGood`. -/
structure B1CompHyps (CM : CompModel) : Type where
  /-- The good runs of `verify_sub`. -/
  VsGood : B1.VerifySub.VsData → Prop
  /-- `main`'s callees under `CM.sem` over `CM.H`, at the deployed frame sizes, certificates and
  callee bounds (`calleesAt_proved` over the model). -/
  callees : CalleesAtC CM.H CM.sem B2C.fs B2C.cert 16 VsGood (calleeBd B2C.fs B2C.calleesHyps_b2c)
  /-- **A child's accepted proof has a good run** (`vs_inversion` over the model): within the
  limits' stack log and stream, its openings agreeing in the caps under a total `Ht` agreeing
  with `CM.H`, accepted with every hash answered by `CM.H`, its fixed claims are of the guest's
  shape and a good run has them, its digest and the seed. -/
  vs_inv : ∀ (Ht : Compile.Bytes → Digest), (∀ x d, CM.H x = some d → d = Ht x) →
    ∀ (seed pi : Digest) (fresh : FixedClaims) (proof : Proof),
    (∀ layout r, announced End.bytecode proof.stream = some (layout, r) →
      22 ≤ layout.stackLog ∧ layout.stackLog ≤ 28) →
    proof.stream.length ≤ Hints.streamCap →
    verifyDeferredWith CM.H End.bytecode seed pi fresh proof = some true →
    (∀ b ∈ queriesOfWith Ht (deferredProgram fresh End.bytecode pi)
        ⟨Ht (digestBytes seed ++ digestBytes pi), proof.stream, proof.openings, []⟩,
      BatchAgreesWith Ht b.1 b.2) →
    FreshShaped fresh ∧ ∃ D : B1.VerifySub.VsData, VsGood D ∧ D.pi = pi ∧ D.seed = seed ∧
      D.fresh = fresh

/-- **L2 without the decoding**: `GuestCompleteModel`'s first two conclusions. -/
def GuestCompleteModelExec : Prop :=
  ∀ (CM : CompModel) (Ht : Compile.Bytes → Digest), (∀ x d, CM.H x = some d → d = Ht x) →
    ∀ (seed : Digest) (s : NodeStatement) (w : NodeWitness) (pi : Digest),
      statementDigestWith CM.H seed s = some pi →
      NodeRelWith CM.H aggSeedD daPadCell daPadRow End.bytecode seed s w →
      End.Limits s w → CapsAgreeWith Ht seed w →
      B2C.b2cBudget'.size (End.work s w) ≤ 2 ^ 28 →
      ∃ t : Trace Guest.guest,
        ValidExecutionB CM.sem Guest.guest (End.publicInputOf pi) t ∧ t.committedSizeB CM.sem ≤ 2 ^ 28

/-! ## The budget's clauses at the honest words over a hash -/

theorem childBd_honestC (fs : String → ℕ) (Bd : CalleeBounds) (Ht : Compile.Bytes → Digest) (seed : Digest)
    (s : NodeStatement) (w : NodeWitness) (c : ℕ) :
    childBd fs Bd ((honestWordsC Ht seed s w).child c) = childBd fs Bd ((honestWords seed s w).child c) := by
  simp only [honestWordsC, honestWords]
  split <;> simp only [childBd, childWordsOfC, childWordsOf]

theorem mainBound_honestC (fs : String → ℕ) (Bd : CalleeBounds) (Ht : Compile.Bytes → Digest)
    (seed : Digest) (s : NodeStatement) (w : NodeWitness) :
    mainBound fs Bd (honestWordsC Ht seed s w) = mainBound fs Bd (honestWords seed s w) := by
  have h : (fun c => childBd fs Bd ((honestWordsC Ht seed s w).child c)) =
      fun c => childBd fs Bd ((honestWords seed s w).child c) :=
    funext (childBd_honestC fs Bd Ht seed s w)
  simp only [mainBound, mainKidsBound, h]
  simp only [mainBs8, MainWords.sizes, MainWords.total, honestWordsC, honestWords]
  rfl

theorem mainWeightS_honestC {S : BlakeSem} (Ht : Compile.Bytes → Digest) (seed : Digest) (s : NodeStatement)
    (w : NodeWitness) (op : Opcode) (Bd : CalleeBounds) :
    mainWeightS S (B2C.ωArm B1.Sig.xmssArmC op) Bd (Count.kcWtS S op) (honestWordsC Ht seed s w) =
      mainWeight (B2C.ωArm B1.Sig.xmssArmC op) Bd (Count.kcWt op) (honestWords seed s w) := by
  have h : (fun c => childWS S (B2C.ωArm B1.Sig.xmssArmC op) Bd (Count.kcWtS S op)
      ((honestWordsC Ht seed s w).child c)) =
      fun c => childW (B2C.ωArm B1.Sig.xmssArmC op) Bd (Count.kcWt op) ((honestWords seed s w).child c) := by
    funext c
    simp only [honestWordsC, honestWords]
    split <;> simp only [childWS, childW, childWordsOfC, childWordsOf] <;> rfl
  simp only [mainWeightS, mainWeight, h]
  simp only [honestWordsC, honestWords]
  rfl

/-! ## `main` within the deployed budget over a model -/

/-- **`main`'s completeness within the deployed budget over a completeness model**, from group B1's
facts over it. -/
theorem mainCompleteC_b2c (CM : CompModel) (hB : B1CompHyps CM) (Ht : Compile.Bytes → Digest)
    (hag : ∀ x d, CM.H x = some d → d = Ht x) :
    End.MainCompleteC CM.sem CM.H Ht B2C.fs B2C.cert B2C.cnt B2C.b2cBudget' := by
  refine mainCompleteC_of hag B2C.fs B2C.cert B2C.cnt B2C.b2cBudget' hB.callees (fsRowsC_model CM)
    (bsRowsC_model CM) (fun op => B2C.ωArm B1.Sig.xmssArmC op) (fun op => Count.kcWtS CM.sem op) B2C.jtSets
    (B2C.two_le_fs _) ?_ ?_ ?_ ?_
  · intro seed s w pi hpi hN hlim hcaps c hc
    obtain ⟨-, pic, hpic, hver⟩ := hN.2.1 c hc
    obtain ⟨-, rfl⟩ := stmtAns_of hag hpic
    exact hB.vs_inv Ht hag seed _ c.fresh c.proof (fun layout r h => hlim.stackLog c hc layout r h)
      (hlim.stream c hc) hver (hcaps c hc)
  · intro seed s w _ hlim
    rw [mainBound_honestC]
    exact ea_words B2C.fs B2C.calleesHyps_b2c (fun q => loop86_bound_le q) (seed := seed) hlim
  · exact B2C.cntB_le_weight_arm B1.Sig.xmssArmC B1.Sig.xmssArmCS_spec
  · intro seed s w _ hlim op
    rw [mainWeightS_honestC]
    have := ea_weight (B2C.ωArm B1.Sig.xmssArmC op) (Count.kcWt op)
      (ea_wordsOk B2C.fs B2C.calleesHyps_b2c (fun q => loop86_bound_le q)) (seed := seed) hlim
    simp only [B2C.b2cBudget', B2C.b2cBudget, eaBudget, eaInstrs, End.Linear.eval] at this ⊢
    omega

/-- **The guest's completeness over a completeness model, its execution**, from group B1's facts
over the model. -/
theorem guestCompleteModelExec_at (CM : CompModel) (hB : B1CompHyps CM) (Ht : Compile.Bytes → Digest)
    (hag : ∀ x d, CM.H x = some d → d = Ht x) (seed : Digest) (s : NodeStatement) (w : NodeWitness)
    (pi : Digest) (hpi : statementDigestWith CM.H seed s = some pi)
    (hrel : NodeRelWith CM.H aggSeedD daPadCell daPadRow End.bytecode seed s w)
    (hlim : End.Limits s w) (hcap : CapsAgreeWith Ht seed w)
    (hbudget : B2C.b2cBudget'.size (End.work s w) ≤ 2 ^ 28) :
    ∃ t : Trace Guest.guest,
      ValidExecutionB CM.sem Guest.guest (End.publicInputOf pi) t ∧ t.committedSizeB CM.sem ≤ 2 ^ 28 := by
  obtain ⟨rd, T, hn, hH, hw, hc⟩ := End.honest_of_mainC (mainCompleteC_b2c CM hB Ht hag)
    (B2C.b2c_kfactsAll fun hdr T _ ↦ B2C.kfacts_run hdr T) B2C.cntRetemp seed s w pi hpi hrel hlim hcap
    hbudget
  obtain ⟨n, hv, hsz⟩ := End.validB_of_honestC (fun h h' => CM.functional h h') hn hH hw hc
  exact ⟨_, hv, hsz.trans hbudget⟩

/-- **The guest's completeness over every completeness model, its execution** (L2 without the
decoding), from group B1's facts over every model. -/
theorem guestCompleteModelExec_of (hB : ∀ CM, B1CompHyps CM) : GuestCompleteModelExec :=
  fun CM Ht hag seed s w pi hpi hrel hlim hcap hbudget =>
    guestCompleteModelExec_at CM (hB CM) Ht hag seed s w pi hpi hrel hlim hcap hbudget

end
end LeanVM.E2E.Complete
