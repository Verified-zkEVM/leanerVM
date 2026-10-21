/-
  LeanVM.Guest.EndKnowB

  The guest's knowledge soundness over any hash model (T2 of `docs/roadmap/e2e-security.md`):
  every valid execution under the model's semantics decodes to a statement whose answered digest
  is the public input's and a witness holding it with every hash answered by the model.
-/

module

public import LeanVM.Guest.EndKnow
public import LeanVM.Guest.SoundB
public import LeanVM.Guest.Located.MainB
public import LeanVM.Guest.B1.VerifySub.KnownB
public import LeanVM.E2E.Runs

/-!
# The guest's witness, named, over a hash model

`EndKnow.lean` over a hash model `M` (`Value.HashModel`).

**The decoder.** `decodeAt S fr` is `decode` with the frames of the located calls under the
semantics `S` at the frames `fr` names (`Located.frameOfB S fr`, decision E2E-5): the seed, the
statement and the children's statements are read off `main`'s frame exactly as `decode` reads
them, and each witness (signature, blob matrix, child proof, hints) off the frame `fr` names for
its call when its callee's code holds there *under `S`*, else off the first frame at which it
does. `decodeB S` names no frame (`decodeAt S (fun _ _ ↦ none)`). It computes no hash; at the
deployed semantics it is `decode` (`decodeB_deployed`). It depends on `S` because a located call
under `S` ran at a frame where its code holds under `S`, which under another semantics need not
be the first frame `decode`'s test (the deployed semantics) finds; it takes `fr` because the first
such frame need not be the one an honest prover's call ran at, which V_I must follow (E2E-5).

**What a valid execution decodes to over the model** (`DecodesOnWith M s0 pc pr`): the decoded
statement's digest under the decoded seed is answered and is the public input's
(`statementDigestWith M.H … = some (publicDigest input)`), and the decoded witness holds it with
every hash answered (`NodeRelWith M.H s0 pc pr`), the batching from `s0` and the DA padding
digests `pc`, `pr`.

**`guest_knowledge_model_at` (T2)**: for every hash model whose open callees are sound over it
(`Located.GuestHypsM M`, the groups still converting) and every frame chooser `fr`, every valid
execution of the guest under `M.sem` decodes, with `decodeAt M.sem fr`, over the model, from the baked start `s0 = aggSeedD` (the
cells `AGG_SEED`) and the baked padding digests `pc = daPadCell`, `pr = daPadRow` (D5). The proof
is `guest_knowledge`'s: B2 under `M.sem` gives `main`'s body at its frame, its calls located
(`End.mainBodyLB_of`, its windows' facts `VsKnownB M.sem` from GKR and the tables over the model
and `ExpKnownB M.sem` by transfer); B1 over the model gives `main`'s meaning over the decoded
witness (`B1.Main.main_sound_wM`) from the callees located over the model
(`Located.calleesWM_located`, `Located.vsWit_outM`), which only use that every decoded frame
holds its callee's code (`Located.frameDecB_spec`), whatever `fr` names.
`guest_knowledge_model` is its corollary for `decodeB`.

**The deployed re-derivation** (`guest_knowledge_of_model`): at `HashModel.deployed`, where every
open callee is its deployed lemma (`Located.guestHypsM_deployed`), the conclusion is the deployed
`DecodesOn` of `decode` (`decodesOnWith_deployed`: `statementDigestWith_some`,
`verifyDeferredWith_some`, `xmssVerifyWith_some_blake2s`, `sphincsVerifyWith_some_blake2s`,
`opensWith_deployed_iff`, `childClaimsWith_some`, `batchWith_some` with `aggSeedD_eq`), which is
`GuestKnowledge guest decode`, `guest_knowledge`'s statement, proved again from the model theorem.
-/

namespace LeanVM.Guest.End

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Check LeanVM.Node
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.EndToEnd LeanVM.Guest.Value
open LeanVM.Protocol.Verifier

@[expose] public section

/-- **The guest's decoder under the semantics `S`, at the frames `fr` names** (`decode`, its
frames under `S`, a call's named frame used when its callee's code holds there; E2E-5). -/
noncomputable def decodeAt (S : BlakeSem) (fr : String → List E → Option ℕ) : Decoder := fun {_} L ↦
  let σ := valG L 1 (certOf 1)
  ⟨B1.Main.decSeed σ, B1.Main.decStmt σ L.read,
    B1.Main.decWit σ L.read (Located.xmssWitB S fr L) (Located.sphincsWitB S fr L)
      (Located.wDaLB S fr L) (fun args ↦ Located.wVsLB S fr L args []) (Located.wALB S fr L)⟩

/-- **The guest's decoder under the semantics `S`** (`decode`, its frames under `S`): no frame
named. -/
noncomputable def decodeB (S : BlakeSem) : Decoder := decodeAt S (fun _ _ ↦ none)

/-- **At the deployed semantics the decoder is `decode`.** -/
theorem decodeB_deployed {κ : ℕ} (L : MemImage κ) : decodeB blakeDeployed L = decode L := by
  simp only [decodeB, decodeAt, decode, Located.xmssWitB_deployed, Located.sphincsWitB_deployed,
    Located.wDaLB_deployed, Located.wVsLB_deployed, Located.wALB_deployed]

/-- **What a valid execution of `guest` on `input` decodes to over a hash model** (`DecodesOn`
over `M`): the decoded statement's answered digest under the decoded seed is the input's, and the
decoded witness holds it with every hash answered by `M.H`, the batching from `s0`, the DA padding
digests `pc`, `pr`. -/
def DecodesOnWith (M : HashModel) (s0 : Digest) (pc pr : LeanDa.Digest) (guest : Semantics.Program)
    (input : PublicInput) (d : Decoded) : Prop :=
  statementDigestWith M.H d.seed d.statement = some (publicDigest input) ∧
    NodeRelWith M.H s0 pc pr (bytecodeWords guest) d.seed d.statement d.witness

/-- A located call under `S` is its callee's body under `S` (`B1.Main.UnfoldsB`). -/
theorem unfolds_RLB {S : BlakeSem} {κ : ℕ} (L : MemImage κ) :
    B1.Main.UnfoldsB S L.read (RLB S coreProgram L certByName) :=
  fun f args rets h ↦ by
    obtain ⟨fn, fp, hf, -, hp, hb⟩ := (relLB_iff coreProgram f args rets).mp h
    exact ⟨fn, _, hf, hp, hb⟩

set_option maxRecDepth 100000 in
/-- **The guest's knowledge soundness over a hash model, at any named frames** (T2;
`guest_knowledge` over `M`): for every hash model whose open callees are sound over it and every
frame chooser `fr`, every valid execution of the guest under the model's semantics on a public
input decodes, from its memory under `M.sem` at the frames `fr` names, to a statement whose
answered digest under the decoded seed is the input's and a witness holding it with every hash
answered by the model: the batching from the guest's baked start `aggSeedD`, the DA padding
digests the guest bakes. -/
theorem guest_knowledge_model_at (M : HashModel) (H : Located.GuestHypsM M)
    (fr : String → List E → Option ℕ) :
    ∀ input (t : Trace guest), ValidExecutionB M.sem guest input t →
      DecodesOnWith M B1.Main.aggSeedD B1.Main.daPadCell B1.Main.daPadRow guest input
        (decodeAt M.sem fr t.image) := by
  intro input t hv
  have hvs : VsKnownB M.sem := B1.VerifySub.vsKnownB_model H.gkr H.tables
  obtain ⟨hb, h0, h1⟩ := mainBodyLB_of hvs (B1.expKnownB M.sem) hv
  have h16 : 16 ≤ t.κ := hv.1.1
  have h32 : t.κ ≤ 32 := hv.1.2.1
  have hm : B1.Main.MemOk t.image.read := ⟨t.κ, h16, h32, t.image, rfl⟩
  have Hc := Located.calleesWM_located hm (H.batch_sumcheck _ hm)
    (fr := fr) (wV := fun args ↦ Located.wVsLB M.sem fr t.image args [])
    (fun _ _ _ _ _ _ _ ht h ↦ Located.vsWit_outM h32 (by omega) (H.gkr _ hm) (H.tables _ hm)
      (H.flock _ hm) (H.open_stacked fr t.image h16 h32) ht h)
  exact B1.Main.main_sound_wM bytecode_length hm (unfolds_RLB t.image) Hc h0 h1 hb

/-- **The guest's knowledge soundness over a hash model** (T2 with no frame named,
`guest_knowledge_model_at`): every valid execution of the guest under the model's semantics
decodes with `decodeB M.sem` over the model. -/
theorem guest_knowledge_model (M : HashModel) (H : Located.GuestHypsM M) :
    ∀ input (t : Trace guest), ValidExecutionB M.sem guest input t →
      DecodesOnWith M B1.Main.aggSeedD B1.Main.daPadCell B1.Main.daPadRow guest input
        (decodeB M.sem t.image) :=
  guest_knowledge_model_at M H (fun _ _ ↦ none)

/-! ## The deployed statement, recovered -/

/-- At the deployed hash the leanXMSS claim's holder over the model is its deployed holder. -/
theorem xmssHeldWith_deployed (chs : List Child) (c : XmssClaim) (h : Holder LeanXmss.Signature) :
    XmssHeldWith HashModel.deployed.H chs c h ↔ XmssHeld chs c h := by
  cases h with
  | direct σ =>
    show xmssVerifyWith (fun x ↦ some (blake2sBytes x)) c.1 c.2 σ = some true ↔ _
    rw [LeanVM.E2E.xmssVerifyWith_some_blake2s, Option.some.injEq]
    rfl
  | child i => exact Iff.rfl

/-- At the deployed hash the leanSPHINCS claim's holder over the model is its deployed holder. -/
theorem sphincsHeldWith_deployed (chs : List Child) (c : SphincsClaim)
    (h : Holder Sphincs.Signature) :
    SphincsHeldWith HashModel.deployed.H chs c h ↔ SphincsHeld chs c h := by
  cases h with
  | direct σ =>
    show sphincsVerifyWith (fun x ↦ some (blake2sBytes x)) c.1 c.2 σ = some true ↔ _
    rw [LeanVM.E2E.sphincsVerifyWith_some_blake2s, Option.some.injEq]
    rfl
  | child i => exact Iff.rfl

/-- At the deployed hash and the baked padding the DA claim's holder over the model is its
deployed holder. -/
theorem daHeldWith_deployed (chs : List Child) (c : DaClaim) (h : Holder Da.Witness) :
    DaHeldWith HashModel.deployed.H B1.Main.daPadCell B1.Main.daPadRow chs c h ↔ DaHeld chs c h := by
  cases h with
  | direct w => exact B1.Digest.opensWith_deployed_iff c.1 c.2 w
  | child i => exact Iff.rfl

theorem forall₂_congr_iff {α β : Type} {R R' : α → β → Prop} (h : ∀ a b, R a b ↔ R' a b)
    {l₁ : List α} {l₂ : List β} : List.Forall₂ R l₁ l₂ ↔ List.Forall₂ R' l₁ l₂ :=
  ⟨fun h' => h'.imp fun a b => (h a b).mp, fun h' => h'.imp fun a b => (h a b).mpr⟩

/-- **At the deployed model, the baked start and padding, `NodeRelWith` is `NodeRel`.** -/
theorem nodeRelWith_deployed (bc : List K) (seed : Digest) (s : NodeStatement) (w : NodeWitness) :
    NodeRelWith HashModel.deployed.H B1.Main.aggSeedD B1.Main.daPadCell B1.Main.daPadRow bc seed s w ↔
      NodeRel bc seed s w := by
  have hH : HashModel.deployed.H = someBlake := rfl
  have hkids : ∀ c : Child, (c.statement.defer.Shaped bc ∧ ∃ pi,
      statementDigestWith HashModel.deployed.H seed c.statement = some pi ∧
      verifyDeferredWith HashModel.deployed.H bc seed pi c.fresh c.proof = some true) ↔
      (c.statement.defer.Shaped bc ∧
        verifyDeferred bc seed (statementDigest seed c.statement) c.fresh c.proof = true) := by
    intro c
    rw [hH, statementDigestWith_some]
    simp only [Option.some.injEq, exists_eq_left', verifyDeferredWith_some]
  unfold NodeRelWith NodeRel
  rw [forall₂_congr_iff (xmssHeldWith_deployed w.children),
    forall₂_congr_iff (sphincsHeldWith_deployed w.children),
    forall₂_congr_iff (daHeldWith_deployed w.children)]
  simp only [hkids]
  split_ifs
  · exact Iff.rfl
  · rw [hH, childClaimsWith_some, B1.Main.aggSeedD_eq]
    simp only [Option.some.injEq, exists_eq_left', batchWith_some]

/-- **At the deployed model a decoding over the model is the deployed decoding.** -/
theorem decodesOnWith_deployed (guest : Semantics.Program) (input : PublicInput) (d : Decoded) :
    DecodesOnWith HashModel.deployed B1.Main.aggSeedD B1.Main.daPadCell B1.Main.daPadRow guest input d ↔
      DecodesOn guest input d := by
  have hH : HashModel.deployed.H = someBlake := rfl
  unfold DecodesOnWith DecodesOn
  rw [nodeRelWith_deployed, hH, statementDigestWith_some, Option.some.injEq]

set_option maxRecDepth 100000 in
/-- **The deployed guest's knowledge soundness, re-derived from the model theorem**
(`guest_knowledge`'s statement): `guest_knowledge_model` at the deployed model, whose open callees
are the deployed lemmas, is `GuestKnowledge guest decode`. -/
theorem guest_knowledge_of_model : GuestKnowledge guest decode := by
  intro input t hv
  have h := guest_knowledge_model HashModel.deployed Located.guestHypsM_deployed input t
    ((validExecutionB_deployed guest input t).mpr hv)
  rw [show HashModel.deployed.sem = blakeDeployed from rfl, decodeB_deployed] at h
  exact (decodesOnWith_deployed guest input _).mp h

end
end LeanVM.Guest.End
