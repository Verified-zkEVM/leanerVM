/-
  LeanerVM.Protocol.LeanVmReader

  The reader of leanVM's chain histories: the announcement a history opens with, the compiled
  protocol at it, the words read off a log under the roots the history carries, the decoder, and
  each challenge read off its squeezes; and the random-oracle bound at leanVM, whose only
  hypothesis is the adversary's query bound.
-/

module

public import LeanerVM.Protocol.LeanVmSlots
public import LeanerVM.Protocol.ProofRoots
public import LeanerVM.Protocol.VerifierQueries
public import LeanerVM.Protocol.HashMisbehaves
public import LeanerVM.Protocol.ListBindingBudget
public import LeanerVM.Protocol.ChainLog
public import LeanerVM.Protocol.DecodeAgree

/-!
# The reader of leanVM's chain histories

`leanVmReader prog input` is the `SlotReader` of leanVM's verifier on `prog` and `input`:

* **The announcement** (`announcementOf`): a history's first eight readings' scalars, decoded
  (`decodeAnnouncement`) to sizes and a rate that pass the setup checks.
* **The protocol** at an announcement: the compiled protocol of the leanISA instance at WHIR's
  deployed chain (`deployedSpec`), its challenges sampled by the schedule's own samplers, its
  decoder `DecodeChain.decodePrefix`, its bad challenges `Bad` on the statement `input`, its marks
  the query positions (`listBindingMark`), after `queryGrindingBits` of grinding.
* **The words** (`wordsOf`): read off the log under the roots the history carries where the
  decoder reads them (`rootAt`, at the offsets `rootOffsets readingCounts`), zero for a root the
  history does not carry yet. They depend on the log only through the rows under the history's
  roots (`wordsOf_congr`).
* **The slots** (`LeanVmSlots.compiledFam`, on the schedule's samplers by `UniformSlot.slotAt`):
  every challenge read off its squeezes by the decoder (`readsWell_compiledDec`), at least one
  squeeze each, since every deployed level's positions fit a squeeze (`posOk_leanIsaChain`, a
  decision on the window, which also gives `shapes_leanIsaChain`: the levels the verifier walks
  are the chain's).

`leanVmReader_density`: every challenge is bad with probability at most `εquery = 2^-128`, the
query positions after their 17 bits of grinding (`bad_density`,
`listBindingError_deployed_le_of_mark`, `listBindingError_deployed_le_of_not_mark`,
`prEvent_lowBitsZero`). `leanVm_misbehaves_rom` is `misbehaves_rom` at the reader, the verifier
`verifyWith`, its query bound `verifierQueries` and the proof's roots `rootsOf`.

An accepted proof's history decodes, at the sizes and rate it announces
(`walkChainLogged_proof_decodes`, `walkChain_proof_decodes`), and so does the history an accepted
replay logs (`decodes_of_replay`). `verifierQueries_le_bound`: the verifier asks at most
`verifierQueriesBound = 13697` queries whatever the program and the input, `μ_bus` at most `55`,
the tables' heights at most `2^40`, and WHIR's walk and openings at most `8839` over the window.

Classification: T4 (the non-interactive compilation), soundness direction; the random-oracle
model's half, the hash's misbehaviour bounded for every adversary with a query bound.
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters LeanerVM.Semantics Blake2sHash LeanIsa OracleComp OracleSpec ProtocolSpec
open StepSchedule Verify DecodeChain Whir LeanVmSlots ProofRoots SlotDecoder VerifierQueries
  ChainLog
open scoped NNReal ENNReal

@[expose] public section

namespace LeanVmReader

/-! ## The window -/

/-- A level's shape as a tuple, for a decision. -/
private def shapeKey (sh : LevelShape) : ℕ × ℕ × ℕ × ℕ × Bool :=
  (sh.fold, sh.msgLog, sh.rate, sh.queries, sh.final)

private theorem shapeKey_injective : Function.Injective shapeKey := by
  rintro ⟨_, _, _, _, _⟩ ⟨_, _, _, _, _⟩ h
  simp only [shapeKey, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
  rfl

/-- Every admissible chain's positions fit squeezes, and its levels are the ladder's: one decision
on the window. -/
private theorem deployed_posOk_shapes {μ r : ℕ} (h : Parameters.Whir.Admissible μ r) :
    (deployed μ r).all fun c ↦ posOk c.ladder && (Parameters.Whir.ladder μ r).all fun ls ↦
      c.ladder.shapes.map shapeKey == (levelShapes μ ls).map shapeKey := by
  have key : ∀ μ < Parameters.Whir.maxLogStack + 1, ∀ r < Parameters.Whir.maxLogInvRate + 1,
      Parameters.Whir.Admissible μ r →
      (deployed μ r).all fun c ↦ posOk c.ladder && (Parameters.Whir.ladder μ r).all fun ls ↦
        c.ladder.shapes.map shapeKey == (levelShapes μ ls).map shapeKey := by
    decide +kernel
  exact key μ (Nat.lt_succ_of_le h.2.1) r (Nat.lt_succ_of_le h.2.2.2) h

private theorem deployedChain_posOk_shapes {μ r : ℕ} (h : Parameters.Whir.Admissible μ r) :
    posOk (deployedChain μ r h).ladder = true ∧ ∀ ls, Parameters.Whir.ladder μ r = some ls →
      (deployedChain μ r h).ladder.shapes = levelShapes μ ls := by
  have := (Option.all_eq_true_iff_get _ _).mp (deployed_posOk_shapes h) (deployed_isSome h)
  rw [Bool.and_eq_true] at this
  refine ⟨this.1, fun ls hl ↦ ?_⟩
  have h₂ := this.2
  rw [hl, Option.all_some, beq_iff_eq] at h₂
  exact List.map_injective_iff.mpr shapeKey_injective h₂

variable {prog : Program} {s : Sizes} (hs : s.Admissible prog) {ρ : ℕ} (hρ : validRate ρ)

/-- Every level of leanVM's chain draws positions that fit squeezes. -/
theorem posOk_leanIsaChain : posOk (leanIsaChain prog s hs ρ hρ).ladder = true :=
  (deployedChain_posOk_shapes (admissible_of_sizes hs hρ)).1

/-- **The levels the verifier walks are the chain's.** -/
theorem shapes_leanIsaChain {levels : List Parameters.Whir.Level}
    (hl : ladderOf prog s ρ = some levels) :
    (leanIsaChain prog s hs ρ hρ).ladder.shapes = levelShapes (stackMu prog s) levels :=
  (deployedChain_posOk_shapes (admissible_of_sizes hs hρ)).2 levels hl

/-! ## The words under a history's roots -/

/-- A root a history carries is one of its roots. -/
private theorem mem_historyRoots_of_rootAt : ∀ {hist : List Reading} {o : ℕ} {d : Digest},
    rootAt hist o = some d → d ∈ historyRoots hist
  | [], _, _, h => by simp [rootAt] at h
  | r :: rest, o + 1, _, h =>
    List.mem_append_right _
      (mem_historyRoots_of_rootAt ((rootAt_cons_succ r rest o).symm.trans h))
  | r :: rest, 0, _, h => List.mem_append_left _ (by
    rcases r with ⟨_ | _ | _, _⟩ <;> rcases rest with _ | ⟨⟨_ | _ | _, _⟩, _⟩ <;>
      simp_all [rootAt])

/-- The level-0 word under a root, read off a log: its rows' committed lanes; zero with no
root. -/
def level0Word (prog : Program) (s : Sizes) (c : Chain) (l : hashSpec.QueryLog) :
    Option Digest → KWord c.sh.ℓ (c.κ + c.sh.R) c.sh.t
  | some root => logWord l root (c.κ + c.sh.R) (level0Lanes prog s c.κ) c.sh.ℓ c.sh.t
  | none => ⟨fun _ ↦ Vector.replicate _ 0⟩

/-- A later level's word under a root, read off a log: its rows, three words a lane; zero with no
root. -/
def laterWord (l : hashSpec.QueryLog) (sh : Whir.Shape) (κ : ℕ) : Option Digest → WordOf sh κ
  | some root =>
    let rows := (extractAllRows l root (κ + sh.R) (3 * 2 ^ sh.ℓ) (3 * 2 ^ sh.ℓ)).toArray
    ⟨fun y ↦
      (((rows[y.val]?).bind id).bind (Verify.laneRow false sh.ℓ)).getD (Vector.replicate _ 0)⟩
  | none => ⟨fun _ ↦ Vector.replicate _ 0⟩

/-- The later levels' words under their roots, in order. -/
def laterWords (l : hashSpec.QueryLog) : {sh : Whir.Shape} → {κ : ℕ} → (L : Ladder sh κ) →
    List (Option Digest) → L.Words
  | _, _, .last _ _, _ => ⟨⟩
  | _, _, @Ladder.cons _ sh' κ' L, rs =>
    (laterWord l sh' κ' (rs.headD none), laterWords l L rs.tail)

/-- **The words read off a log** under the roots a history carries where the decoder reads them:
the level-0 root after the announcement, each later level's after the readings before it. -/
def wordsOf (prog : Program) (input : PublicInput) (s : Sizes) (hs : s.Admissible prog) (ρ : ℕ)
    (hρ : validRate ρ) (l : hashSpec.QueryLog) (hist : List Reading) : LeanWords prog s hs ρ hρ :=
  ⟨level0Word prog s _ l (rootAt hist 8),
    laterWords l _ ((levelRootOffsets readingCounts (whirStart readingCounts prog s input)
      (leanIsaChain prog s hs ρ hρ).ladder.shapes).map (rootAt hist))⟩

/-- The rows under a root agree in two logs. -/
def RowsAgree (l l' : hashSpec.QueryLog) (root : Digest) : Prop :=
  ∀ depth rowWords leafWords p, extractRows l' root depth rowWords leafWords p =
    extractRows l root depth rowWords leafWords p

private theorem extractAllRows_congr {l l' : hashSpec.QueryLog} {root : Digest}
    (h : RowsAgree l l' root) (depth rowWords leafWords : ℕ) :
    extractAllRows l' root depth rowWords leafWords =
      extractAllRows l root depth rowWords leafWords := by
  rw [extractAllRows_eq, extractAllRows_eq]
  exact List.map_congr_left fun p _ ↦ h depth rowWords leafWords p

private theorem level0Word_congr (c : Chain) {l l' : hashSpec.QueryLog} :
    ∀ {r : Option Digest}, (∀ root, r = some root → RowsAgree l l' root) →
      level0Word prog s c l' r = level0Word prog s c l r
  | none, _ => rfl
  | some root, h => by
    simp only [level0Word, logWord, wordRows, extractAllRows_congr (h root rfl)]

private theorem laterWord_congr {l l' : hashSpec.QueryLog} (sh : Whir.Shape) (κ : ℕ) :
    ∀ {r : Option Digest}, (∀ root, r = some root → RowsAgree l l' root) →
      laterWord l' sh κ r = laterWord l sh κ r
  | none, _ => rfl
  | some root, h => by
    simp only [laterWord, extractAllRows_congr (h root rfl)]

private theorem laterWords_congr {l l' : hashSpec.QueryLog} :
    ∀ {sh : Whir.Shape} {κ : ℕ} (L : Ladder sh κ) {rs : List (Option Digest)},
      (∀ root, some root ∈ rs → RowsAgree l l' root) → laterWords l' L rs = laterWords l L rs
  | _, _, .last _ _, _, _ => rfl
  | _, _, @Ladder.cons _ sh' κ' L, rs, h => by
    simp only [laterWords]
    congr 1
    · refine laterWord_congr sh' κ' fun root hr ↦ h root ?_
      rcases rs with _ | ⟨r, rs⟩
      · simp at hr
      · simp only [List.headD_cons] at hr
        rw [← hr]
        exact List.mem_cons_self
    · exact laterWords_congr L fun root hr ↦ h root (List.mem_of_mem_tail hr)

/-- **The words depend on the log only through the rows under the history's roots.** -/
theorem wordsOf_congr (prog : Program) (input : PublicInput) (s : Sizes) (hs : s.Admissible prog)
    (ρ : ℕ) (hρ : validRate ρ) (l l' : hashSpec.QueryLog) (hist : List Reading)
    (h : ∀ root ∈ historyRoots hist, RowsAgree l l' root) :
    wordsOf prog input s hs ρ hρ l' hist = wordsOf prog input s hs ρ hρ l hist := by
  have hr : ∀ o root, rootAt hist o = some root → RowsAgree l l' root :=
    fun _ _ ho ↦ h _ (mem_historyRoots_of_rootAt ho)
  simp only [wordsOf]
  rw [level0Word_congr _ fun root ho ↦ hr 8 root ho, laterWords_congr _ fun root hm ↦ ?_]
  obtain ⟨o, -, ho⟩ := List.mem_map.mp hm
  exact hr o root ho

/-! ## The announcement -/

/-- The announcements of `prog`: sizes and a rate that pass the setup checks. -/
abbrev Ann (prog : Program) : Type := {p : Sizes × ℕ // p.1.Admissible prog ∧ validRate p.2}

/-- The announcement a history opens with: its first eight readings' scalars, decoded, when they
pass the setup checks. -/
def announcementOf (prog : Program) (hist : List Reading) : Option (Ann prog) :=
  (decodeAnnouncement (streamOf (hist.take 8))).bind fun p ↦
    if h : p.1.Admissible prog ∧ validRate p.2 then some ⟨p, h⟩ else none

/-- The chain at an announcement. -/
abbrev chainAt (a : Ann prog) : Chain := leanIsaChain prog a.1.1 a.2.1 a.1.2 a.2.2

/-- The challenges of the compiled protocol at an announcement. -/
abbrev famAt (a : Ann prog) : ChalSlots (deployedSpec Blake2sFlock.blake2sFlockSpec prog a.1.1 a.2.1
    a.1.2 a.2.2) :=
  compiledFam (leanVm prog a.1.1) (chainAt a) (posOk_leanIsaChain a.2.1 a.2.2)

/-! ## The marks follow the nonces -/

/-- No marked challenge, then marks that follow their flags. -/
private theorem markAfter_skip {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
    {pre : Bool} {b₂ : pSpec₂.ChallengeIdx → Bool} {N₁ : Fin m → Bool} {N₂ : Fin n → Bool}
    (h : MarkAfter (lastFlag pre N₁) b₂ N₂) :
    MarkAfter (pSpec := pSpec₁ ++ₚ pSpec₂) pre (markAppend (fun _ ↦ false) b₂) (Fin.append N₁ N₂) :=
  markAfter_append (markAfter_none _ _) h

private theorem markAfter_finalMark (sh : Whir.Shape) (nf : ℕ) (pre : Bool) :
    MarkAfter pre (finalMark (sh := sh) (nf := nf)) (finalFlags sh nf).toFlags :=
  markAfter_skip <| markAfter_skip <| markAfter_skip <| markAfter_skip <| markAfter_skip <|
  markAfter_append (markAfter_draw rfl _) <| markAfter_skip <| markAfter_skip <| markAfter_skip <|
  markAfter_skip <| markAfter_skip <| markAfter_skip <| markAfter_none _ _

private theorem markAfter_levelMark (sh sh' : Whir.Shape) (κ' : ℕ) {k : List Step}
    {bR : (seqSpec k).ChallengeIdx → Bool} {N : SeqFlags k} (hR : ∀ pre, MarkAfter pre bR N.toFlags)
    (pre : Bool) :
    MarkAfter pre (levelMark (sh := sh) (sh' := sh') (κ' := κ') bR)
      (levelFlags sh sh' κ' N).toFlags :=
  markAfter_skip <| markAfter_skip <| markAfter_skip <| markAfter_skip <| markAfter_skip <|
  markAfter_skip <| markAfter_skip <| markAfter_skip <| markAfter_append (markAfter_draw rfl _) <|
  markAfter_skip <| markAfter_skip <| markAfter_skip <| markAfter_skip <| hR _

private theorem markAfter_ladder : ∀ {sh : Whir.Shape} {κ : ℕ} (L : Ladder sh κ) (pre : Bool),
    MarkAfter pre L.mark (ladderFlags L).toFlags
  | _, _, .last sh nf, pre => markAfter_finalMark sh nf pre
  | _, _, @Ladder.cons sh sh' κ' L, pre => markAfter_levelMark sh sh' κ' (markAfter_ladder L) pre

/-- **Every marked challenge of the compiled protocol follows a nonce round.** -/
theorem markAfter_compiled (I : M3Instance) (c : Chain) :
    MarkAfter false (listBindingMark I c.ladder) (compiledFlags I c) :=
  markAfter_skip <| markAfter_skip <| markAfter_skip (markAfter_ladder c.ladder _)

/-! ## The reader -/

variable (prog) (input : PublicInput)

/-- The decoder at an announcement reads well. -/
theorem readsWell_decoder (a : Ann prog) (W : LeanWords prog a.1.1 a.2.1 a.1.2 a.2.2) :
    (decoder prog input a.1.1 a.2.1 a.1.2 a.2.2 W).ReadsWell (famAt a) (compiledFlags _ _) :=
  readsWell_compiledDec _ _ _ _ _ W _

/-- **The reader of leanVM's chain histories** on `prog` and `input`. -/
def leanVmReader : SlotReader where
  seed := (FsState.seed prog input).cv
  powBits := Parameters.Whir.queryGrindingBits
  Ann := Ann prog
  announcementOf := announcementOf prog
  -- spelled as `deployedSpec`'s length, so that the two unify syntactically
  n a := 1 + busRounds (leanIsaInstance Blake2sFlock.blake2sFlockSpec prog a.1.1) +
    tableRounds (leanIsaInstance Blake2sFlock.blake2sFlockSpec prog a.1.1) + 2 +
    flockRounds (leanIsaInstance Blake2sFlock.blake2sFlockSpec prog a.1.1)
      (leanIsaInstance Blake2sFlock.blake2sFlockSpec prog a.1.1).flock + 1 + 0 +
    seqRounds (.skip :: .msg (SumcheckRound.Message E 2) ::
      (leanIsaChain prog a.1.1 a.2.1 a.1.2 a.2.2).ladder.steps)
  spec a := deployedSpec Blake2sFlock.blake2sFlockSpec prog a.1.1 a.2.1 a.1.2 a.2.2
  sampleable _ _ := inferInstance
  Words a := LeanWords prog a.1.1 a.2.1 a.1.2 a.2.2
  wordsAt a l hist := wordsOf prog input a.1.1 a.2.1 a.1.2 a.2.2 l hist
  decodePrefix a W hist := DecodeChain.decodePrefix prog input a.1.1 a.2.1 a.1.2 a.2.2 W hist
  slot a i := (famAt a i.1 i.2).slotAt _
  mark a i := listBindingMark (leanVm prog a.1.1) (chainAt a).ladder i
  Bad a i tr := Bad Blake2sFlock.blake2sFlockSpec prog a.1.1 a.2.1 a.1.2 a.2.2
    (input, fun j ↦ j.elim0) i tr
  wordsAt_congr a l l' hist h := wordsOf_congr prog input a.1.1 a.2.1 a.1.2 a.2.2 l l' hist h
  squeezeSlot_read a W _ i _ h ds rest _ _ h' :=
    squeezeSlot_read_of (readsWell_decoder prog input a W).squeezes i h
      (pos_compiledFam _ _ _ i.1 i.2) ds rest h'
  decodePrefix_digest_indep a W hist _ d d' rest hb :=
    (readsWell_decoder prog input a W).blind.decodePrefix_digest_indep hist d d' rest hb
  mark_afterNonce a W _ i _ h hm :=
    mark_afterNonce_of (readsWell_decoder prog input a W).nonce (markAfter_compiled _ _) i h hm
  slot_pos _ i := pos_compiledFam _ _ _ i.1 i.2

/-! ## The density of the bad challenges -/

/-- A uniform event's bound does not depend on the sampler. -/
private theorem prEvent_le_of_inst {C : Type} {p : C → Prop} {e : ℝ≥0∞} (i₂ : SampleableType C)
    (h : (letI := i₂; Pr{let x ← $ᵗ C}[p x]) ≤ e) (i₁ : SampleableType C) :
    (letI := i₁; Pr{let x ← $ᵗ C}[p x]) ≤ e :=
  (@SampleableType.prEvent_uniformSample_equiv C C i₁ i₂ (Equiv.refl C) p).trans_le h

/-- **Every challenge of leanVM's compiled protocol is bad with probability at most `2^-128`**,
the query positions counted after their grinding. -/
theorem leanVmReader_density : (leanVmReader prog input).Density εquery := by
  rintro ⟨⟨s, ρ⟩, hs, hρ⟩ i tr
  have hP := bad_density Blake2sFlock.blake2sFlockSpec prog s hs ρ hρ (input, fun j ↦ j.elim0) i tr
  by_cases hm : (leanVmReader prog input).mark ⟨(s, ρ), hs, hρ⟩ i = true
  · obtain ⟨-, hm'⟩ := listBindingError_deployed_le_of_mark _ prog s hs ρ hρ i hm
    simp only [hm, ↓reduceIte]
    dsimp only [leanVmReader]
    generalize (leanVmReader prog input).sampleable ⟨(s, ρ), hs, hρ⟩ i = I₀
    rw [prEvent_lowBitsZero (bits := Parameters.Whir.queryGrindingBits) (by decide)]
    refine (mul_le_mul_of_nonneg_left (prEvent_le_of_inst _ hP I₀) (by positivity)).trans
      (le_of_eq_of_le ?_ (ENNReal.coe_le_coe.mpr hm'))
    rw [ENNReal.coe_mul, ENNReal.coe_inv (pow_ne_zero _ two_ne_zero), ENNReal.coe_pow,
      ENNReal.coe_ofNat]
  · have hm' := listBindingError_deployed_le_of_not_mark _ prog s hs ρ hρ i
      (Bool.eq_false_iff.mpr hm)
    simp only [hm, Bool.false_eq_true, ↓reduceIte, one_mul]
    dsimp only [leanVmReader]
    generalize (leanVmReader prog input).sampleable ⟨(s, ρ), hs, hρ⟩ i = I₀
    exact (prEvent_le_of_inst _ hP I₀).trans (ENNReal.coe_le_coe.mpr hm')

/-! ## The bound -/

/-- **The random-oracle bound at leanVM**: on every adversary asking at most `Q` queries, the hash
misbehaves in the game of leanVM's verifier with probability at most
`niError εquery (verifierQueries prog input) Q`: a collision, a hit on a digest in play, or a
flip of a challenge to a bad one. The bound is selective: the program and the public input are
fixed before the adversary runs. -/
theorem leanVm_misbehaves_rom (A : Adversary) {Q : ℕ} (hQ : IsTotalQueryBound A Q) :
    Pr{let z ← runRandom (loggedGame verifyWith prog input A)}[
      HashMisbehaves (rootsOf prog input) (leanVmReader prog input).Flip prog input z.1] ≤
      niError εquery (verifierQueries prog input) Q :=
  misbehaves_rom (leanVmReader prog input) prog input rfl (leanVmReader_density prog input)
    verifyWith (verifierQueries_bound prog input) (rootsOf prog input)
    (length_rootsOf_le prog input) A hQ

/-! ## An accepted proof's history decodes -/

variable {prog input}

/-- The sizes and the rate the setup accepts are the proof's announcement. -/
theorem announced?_of_setup {M : Type} {p : Proof M} {s : Sizes} {ρ : ℕ}
    (h : setup? prog p = some (s, ρ)) : p.announced? = some (s, ρ) := by
  unfold setup? at h
  split at h
  · split at h
    · cases h
      assumption
    · cases h
  · cases h

/-- **The verifier's logged chain walk on a proof decodes**: if the setup accepts the proof's
announcement and the logged chain walk at the announced ladder succeeds on the proof from the
statement's seed, the history it logged decodes, with any words, to a transcript whose wire is the
walk's, viewed. -/
theorem walkChainLogged_proof_decodes {proof : Proof PrunedMerklePaths} {s : Sizes} {ρ : ℕ}
    {levels : List Parameters.Whir.Level} (hsetup : setup? prog proof = some (s, ρ))
    (hl : ladderOf prog s ρ = some levels) {H : List UInt8 → Id Digest}
    {st' : ReaderState PrunedMerklePaths} {w : Wire} {hist : List Reading}
    (h : walkChainLogged prog s input (levelShapes (stackMu prog s) levels) H
      ⟨FsState.seed prog input, proof.stream, proof.merkle⟩ = .ok ((w, hist), st')) :
    ∃ (hs : s.Admissible prog) (hρ : validRate ρ), ∀ W : LeanWords prog s hs ρ hρ,
      ∃ tr, decode prog input s hs ρ hρ W hist = some tr ∧
        wireOf (leanVm prog s) (leanIsaChain prog s hs ρ hρ).ladder tr =
          Wire.view (levelShapes (stackMu prog s) levels) w := by
  obtain ⟨hs, hρ⟩ := of_decide_eq_true (setupOk_of_setup hsetup)
  refine ⟨hs, hρ, fun W ↦ ?_⟩
  rw [← shapes_leanIsaChain hs hρ hl] at h ⊢
  exact walkChainLogged_decodes prog input s hs ρ hρ W h
    (take_eq_announcement_of_announced? (announced?_of_setup hsetup))

/-- **The verifier's chain walk on a proof decodes**: if the setup accepts the proof's
announcement and the chain walk on the proof reader at the announced ladder succeeds from the
statement's seed, the logged walk succeeds with the same wire, and its history decodes, with any
words, to a transcript whose wire is the walk's, viewed. -/
theorem walkChain_proof_decodes {proof : Proof PrunedMerklePaths} {s : Sizes} {ρ : ℕ}
    {levels : List Parameters.Whir.Level} (hsetup : setup? prog proof = some (s, ρ))
    (hl : ladderOf prog s ρ = some levels) {H : List UInt8 → Id Digest}
    {st' : ReaderState PrunedMerklePaths} {w : Wire}
    (h : runPlain (walkChain (readerOps H) prog s input (levelShapes (stackMu prog s) levels))
      ⟨FsState.seed prog input, proof.stream, proof.merkle⟩ = .ok (w, st')) :
    ∃ hist, walkChainLogged prog s input (levelShapes (stackMu prog s) levels) H
        ⟨FsState.seed prog input, proof.stream, proof.merkle⟩ = .ok ((w, hist), st') ∧
      ∃ (hs : s.Admissible prog) (hρ : validRate ρ), ∀ W : LeanWords prog s hs ρ hρ,
        ∃ tr, decode prog input s hs ρ hρ W hist = some tr ∧
          wireOf (leanVm prog s) (leanIsaChain prog s hs ρ hρ).ladder tr =
            Wire.view (levelShapes (stackMu prog s) levels) w := by
  obtain ⟨hist, hlog⟩ := walkChainLogged_of_walkChain H h
  exact ⟨hist, hlog, walkChainLogged_proof_decodes hsetup hl hlog⟩

/-- **An accepted replay's history decodes**: if the verifier replayed on a log accepts a proof,
recording `logV`, then at the sizes, rate and levels the proof announces, the chain walk with its
steps logged at the log's hash succeeds on the proof with a wire `w` and a history in `logV` from
the statement's seed, and the history decodes, with any words, to a transcript whose wire is `w`,
viewed. -/
theorem decodes_of_replay {log logV : hashSpec.QueryLog} {proof : Proof PrunedMerklePaths}
    (h : replay log prog input proof = some (true, logV)) :
    ∃ s ρ levels w st₁ hist, setup? prog proof = some (s, ρ) ∧
      ladderOf prog s ρ = some levels ∧
      walkChainLogged prog s input (levelShapes (stackMu prog s) levels)
        (hashOf (MerkleTree.logAnswer log)) ⟨FsState.seed prog input, proof.stream, proof.merkle⟩ =
        .ok ((w, hist), st₁) ∧
      (∀ e ∈ HashChain.queries Block.input (FsState.seed prog input).cv hist, e ∈ logV) ∧
      ∃ (hs : s.Admissible prog) (hρ : validRate ρ), ∀ W : LeanWords prog s hs ρ hρ,
        ∃ tr, decode prog input s hs ρ hρ W hist = some tr ∧
          wireOf (leanVm prog s) (leanIsaChain prog s hs ρ hρ).ladder tr =
            Wire.view (levelShapes (stackMu prog s) levels) w := by
  obtain ⟨s, ρ, levels, w, st₁, hist, hsetup, hl, hw, hq⟩ := chain_in_log_of_replay h
  exact ⟨s, ρ, levels, w, st₁, hist, hsetup, hl, hw, hq,
    walkChainLogged_proof_decodes hsetup hl hw⟩

/-! ## The reader's facts on the verifier's history -/

private theorem laterWords_agree (l : hashSpec.QueryLog) {N : ℕ} {f g : ℕ → Option Digest} :
    ∀ {sh : Whir.Shape} {κ : ℕ} (L : Ladder sh κ) (offs : List ℕ),
      (∀ o ∈ offs, o + 2 ≤ N → f o = g o) →
      DecodeAgree.LaterAgree N L offs (laterWords l L (offs.map f)) (laterWords l L (offs.map g))
  | _, _, .last _ _, _, _ => trivial
  | _, _, @Ladder.cons _ _ _ L, [], _ =>
    ⟨(fun _ ho ↦ nomatch ho), laterWords_agree (f := f) (g := g) l L [] fun _ ho ↦ nomatch ho⟩
  | _, _, @Ladder.cons _ _ _ L, o :: offs, h =>
    ⟨fun o' ho hN ↦ by
        obtain rfl : o = o' := Option.some.inj ho
        show laterWord l _ _ (f o) = laterWord l _ _ (g o)
        rw [h o List.mem_cons_self hN],
      laterWords_agree l L offs fun o' ho hN ↦ h o' (List.mem_cons_of_mem _ ho) hN⟩

/-- **A prefix of a history reads the words of the history** at every root it carries: the words
read off a log under the roots of `hist` and of `hist ++ rest` agree within `hist`. -/
theorem wordsOf_prefix (prog : Program) (input : PublicInput) (s : Sizes)
    (hs : s.Admissible prog) (ρ : ℕ) (hρ : validRate ρ) (l : hashSpec.QueryLog)
    (hist rest : List Reading) :
    DecodeAgree.WordsAgree prog input s hs ρ hρ hist.length (wordsOf prog input s hs ρ hρ l hist)
      (wordsOf prog input s hs ρ hρ l (hist ++ rest)) := by
  refine ⟨fun h10 ↦ ?_,
    laterWords_agree l _ _ fun o _ ho ↦ (rootAt_prefix hist rest (by omega)).symm⟩
  show level0Word prog s _ l (rootAt hist 8) = level0Word prog s _ l (rootAt (hist ++ rest) 8)
  rw [rootAt_prefix hist rest (by omega)]

/-- **The history of a state on the verifier's chain**: on a log with no collision and no answer
equal to the seed, holding every step of the verifier's history from the seed, the chain history of
the state after any prefix of it is that prefix. -/
theorem chainHistory_of_log {log : hashSpec.QueryLog} {seed : FsState}
    (hcoll : ¬ QueryLog.HasCollision log) (hseed : ∀ e ∈ log, e.2 ≠ seed.cv)
    {hist : List (Block × Digest)}
    (hchain : ∀ e ∈ HashChain.queries Block.input seed.cv hist, e ∈ log) (j : ℕ) :
    chainHistory log seed ⟨HashChain.last seed.cv (hist.take j)⟩ = some (hist.take j) := by
  refine chainHistory_of_noCollision_noSeed hcoll hseed _ fun e he ↦ hchain e ?_
  rw [← List.take_append_drop j hist, HashChain.queries_append]
  exact List.mem_append_left _ he

/-- **A grinding check passed on a log's answers passes in the log**: if the verifier's check of
the nonce `n` at the state `cv`, its hash answered from the log `l`, passes, its base and its check
are answered there and the check has `bits` low zero bits. -/
theorem powPasses_of_checkPow {l : hashSpec.QueryLog} {cv : Digest} {bits : ℕ} (hb : bits ≠ 0)
    {n : E} {pre post : hashSpec.QueryLog} {s' : FsState}
    (h : (FsState.checkPow (QueryLog.replayImpl (MerkleTree.logAnswer l)) ⟨cv⟩ bits n).run pre =
      some ((true, s'), post)) :
    PowPasses bits l cv n := by
  simp only [FsState.checkPow, FsState.powBase, FsState.powOk, FsState.absorbNonce, hb,
    ↓reduceIte, QueryLog.replayImpl, StateT.run_bind] at h
  rcases hbase : MerkleTree.logAnswer l (FsState.stepBytes cv 0 FsState.powBaseTag) with _ | base
  · simp [hbase, StateT.run_lift] at h
  rcases hchk : MerkleTree.logAnswer l (FsState.stepBytes base n FsState.powNonceTag) with _ | d
  · simp [hbase, hchk, StateT.run_lift] at h
  refine ⟨base, d, hbase, hchk, ?_⟩
  simp [hbase, hchk, StateT.run_lift] at h
  rcases habs : MerkleTree.logAnswer l (FsState.stepBytes cv n FsState.powNonceTag) with _ | u
  · simp [habs] at h
  · simp only [habs, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
    exact h.1.1

/-! ## The verifier's queries, in closed form -/

/-- The most queries WHIR's walk and openings ask over the window. -/
def whirQueriesMax : ℕ := 8839

/-- WHIR's walk and openings ask at most `whirQueriesMax` queries: one decision on the window. -/
private theorem whirQueries_le {μ ρ : ℕ} {levels : List Parameters.Whir.Level}
    (h : Parameters.Whir.ladder μ ρ = some levels) :
    queryCounts.whir (levelShapes μ levels) + openingsCount (levelShapes μ levels) ≤
      whirQueriesMax := by
  have hadm : Parameters.Whir.Admissible μ ρ := by
    unfold Parameters.Whir.ladder at h
    split_ifs at h with h'
    exact h'
  have key : ∀ μ < Parameters.Whir.maxLogStack + 1, ∀ ρ < Parameters.Whir.maxLogInvRate + 1,
      ∀ ls ∈ Parameters.Whir.ladder μ ρ,
        queryCounts.whir (levelShapes μ ls) + openingsCount (levelShapes μ ls) ≤
          whirQueriesMax := by
    decide +kernel
  exact key μ (Nat.lt_succ_of_le hadm.2.1) ρ (Nat.lt_succ_of_le hadm.2.2.2) levels h

/-- **A bound on the verifier's queries whatever the program and the input**: the setup, the bus
phase at `μ_bus = 55`, the table sumcheck at `τ_max = 40`, the public input's two sent lines, the
Flock phase at `τ_BLAKE2S = 32`, `λ`, and WHIR's most over the window. -/
def verifierQueriesBound : ℕ :=
  queryCounts.setup + queryCounts.bus 55 192 + queryCounts.tables 40 110 + queryCounts.pub 2 +
    queryCounts.flock maxLogRows + queryCounts.sample + whirQueriesMax

/-- The queries at sizes within the box are at most `verifierQueriesBound`. -/
private theorem queryCountAt_le_bound (prog : Program) (input : PublicInput) {s : Sizes} (ρ : ℕ)
    (hm : s.logMem ≤ maxLogMem) (hτ : ∀ j, s.τ j ≤ maxLogRows) :
    queryCountAt prog input s ρ ≤ verifierQueriesBound := by
  unfold queryCountAt
  split
  · exact Nat.zero_le _
  rename_i levels hl
  have hw := whirQueries_le hl
  have hbus : queryCounts.bus (leanVm prog s).μBus (leanVm prog s).busClaims ≤
      queryCounts.bus 55 192 := by
    have hμ : (leanVm prog s).μBus ≤ 55 :=
      leanIsa_μBus_le_of Blake2sFlock.blake2sFlockSpec (prog := prog) hm hτ
    have hc := busClaims_le (leanVm prog s)
    rw [show (leanVm prog s).boundary.length = 6 from rfl] at hc
    have key : ∀ m < 56, queryCounts.layers (gkrRadices m) 0 ≤
        queryCounts.layers (gkrRadices 55) 0 := by decide +kernel
    have := key _ (Nat.lt_succ_of_le hμ)
    simp only [StepCounts.bus, queryCounts] at this ⊢
    omega
  have hτmax : (leanVm prog s).τmax ≤ 40 :=
    Finset.sup_le fun j _ ↦ leanIsa_height_le_of hm hτ j.1
  have htab : queryCounts.tables (leanVm prog s).τmax (leanVm prog s).tableColumns ≤
      queryCounts.tables 40 110 := by
    have hw : ∑ j, (leanVm prog s).width j = 110 := by
      show ∑ j : Fin 9, LeanIsa.width j = 110
      decide +kernel
    have hc : (leanVm prog s).tableColumns ≤ 110 :=
      (sum_sumcheckTables_le (leanVm prog s) (leanVm prog s).width).trans hw.le
    simp only [StepCounts.tables, StepCounts.rounds, StepCounts.round, queryCounts]
    omega
  have hfl : queryCounts.flock (s.τ 5) ≤ queryCounts.flock maxLogRows := by
    have := hτ 5
    simp only [StepCounts.flock, StepCounts.rounds, StepCounts.round, queryCounts]
    omega
  have hpub : PublicInput.sentCount (leanVm prog s) ((leanVm prog s).publicLines input) = 2 := rfl
  simp only [queryCount, StepCounts.chain, hpub, verifierQueriesBound]
  omega

/-- **The verifier asks at most `verifierQueriesBound` queries**, whatever the program and the
input. -/
theorem verifierQueries_le_bound (prog : Program) (input : PublicInput) :
    verifierQueries prog input ≤ verifierQueriesBound := by
  unfold verifierQueries
  refine Finset.sup_le fun p hp ↦ ?_
  unfold sizesBox at hp
  simp only [Finset.mem_product, Finset.mem_range, Finset.mem_univ, true_and] at hp
  unfold queryCountOf
  split_ifs
  · exact queryCountAt_le_bound prog input _ (Nat.lt_succ_iff.mp hp.1)
      fun j ↦ Nat.lt_succ_iff.mp (p.2.1 j).isLt
  · exact Nat.zero_le _

/-- `verifierQueriesBound` as a numeral. -/
theorem verifierQueriesBound_eq : verifierQueriesBound = 13697 := by decide

/-- **The random-oracle bound at leanVM, in closed form**: on every adversary asking at most `Q`
queries, the hash misbehaves with probability at most `(Q + 13697) / 2^128` for the challenges and
`hashTerm 13697 Q = (Q + 13697) (4 (Q + 13697) + 8) / 2^256` for collisions and hits, whatever the
program and the public input, fixed before the adversary runs. -/
theorem leanVm_misbehaves_rom_closed (prog : Program) (input : PublicInput) (A : Adversary)
    {Q : ℕ} (hQ : IsTotalQueryBound A Q) :
    Pr{let z ← runRandom (loggedGame verifyWith prog input A)}[
      HashMisbehaves (rootsOf prog input) (leanVmReader prog input).Flip prog input z.1] ≤
      ((Q + 13697 : ℕ) / 2 ^ 128 + hashTerm 13697 Q : ℝ≥0) := by
  refine (leanVm_misbehaves_rom prog input A hQ).trans (ENNReal.coe_le_coe.mpr ?_)
  refine (niError_mono_left _ (verifierQueries_le_bound prog input) Q).trans ?_
  rw [verifierQueriesBound_eq]
  exact (niError_le 13697 Q).trans (le_of_eq (by norm_num))

end LeanVmReader

end

end LeanerVM.Protocol
