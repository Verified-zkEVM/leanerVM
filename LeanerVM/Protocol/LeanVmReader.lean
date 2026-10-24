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

Classification: T4 (the non-interactive compilation), soundness direction; the random-oracle
model's half, the hash's misbehaviour bounded for every adversary with a query bound.
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters LeanerVM.Semantics Blake2sHash LeanIsa OracleComp OracleSpec ProtocolSpec
open StepSchedule Verify DecodeChain Whir LeanVmSlots ProofRoots SlotDecoder VerifierQueries
open scoped NNReal ENNReal

@[expose] public section

namespace LeanVmReader

/-! ## The window -/

/-- A level's shape as a tuple, for a decision. -/
def shapeKey (sh : LevelShape) : ℕ × ℕ × ℕ × ℕ × Bool :=
  (sh.fold, sh.msgLog, sh.rate, sh.queries, sh.final)

theorem shapeKey_injective : Function.Injective shapeKey := by
  rintro ⟨_, _, _, _, _⟩ ⟨_, _, _, _, _⟩ h
  simp only [shapeKey, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
  rfl

/-- Every admissible chain's positions fit squeezes, and its levels are the ladder's: one decision
on the window. -/
theorem deployed_posOk_shapes {μ r : ℕ} (h : Parameters.Whir.Admissible μ r) :
    (deployed μ r).all fun c ↦ posOk c.ladder && (Parameters.Whir.ladder μ r).all fun ls ↦
      c.ladder.shapes.map shapeKey == (levelShapes μ ls).map shapeKey := by
  have key : ∀ μ < Parameters.Whir.maxLogStack + 1, ∀ r < Parameters.Whir.maxLogInvRate + 1,
      Parameters.Whir.Admissible μ r →
      (deployed μ r).all fun c ↦ posOk c.ladder && (Parameters.Whir.ladder μ r).all fun ls ↦
        c.ladder.shapes.map shapeKey == (levelShapes μ ls).map shapeKey := by
    decide +kernel
  exact key μ (Nat.lt_succ_of_le h.2.1) r (Nat.lt_succ_of_le h.2.2.2) h

theorem deployedChain_posOk_shapes {μ r : ℕ} (h : Parameters.Whir.Admissible μ r) :
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

/-- The readings each primitive takes: a scalar one, a challenge one, a root two, a nonce one. -/
def readingCounts : StepCounts := ⟨1, 1, 2, fun _ ↦ 1⟩

/-- The root a history carries at reading `o`: two observes there, read as a digest. -/
def rootAt (hist : List Reading) (o : ℕ) : Option Digest :=
  match hist[o]?, hist[o + 1]? with
  | some (.observe x₁, _), some (.observe x₂, _) => digestOfScalars (x₁, x₂)
  | _, _ => none

theorem rootAt_cons_succ (r : Reading) (hist : List Reading) (o : ℕ) :
    rootAt (r :: hist) (o + 1) = rootAt hist o := rfl

/-- A root a history carries is one of its roots. -/
theorem mem_historyRoots_of_rootAt : ∀ {hist : List Reading} {o : ℕ} {d : Digest},
    rootAt hist o = some d → d ∈ historyRoots hist
  | [], _, _, h => by simp [rootAt] at h
  | r :: rest, o + 1, _, h =>
    List.mem_append_right _
      (mem_historyRoots_of_rootAt ((rootAt_cons_succ r rest o).symm.trans h))
  | (.observe x₁, _) :: (.observe x₂, _) :: _, 0, _, h =>
    List.mem_append_left _ (by simp_all [rootAt])
  | [(.observe _, _)], 0, _, h => by simp [rootAt] at h
  | (.observe _, _) :: (.squeeze, _) :: _, 0, _, h => by simp [rootAt] at h
  | (.observe _, _) :: (.nonce _, _) :: _, 0, _, h => by simp [rootAt] at h
  | (.squeeze, _) :: _, 0, _, h => by simp [rootAt] at h
  | (.nonce _, _) :: _, 0, _, h => by simp [rootAt] at h

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
    ⟨fun y ↦ (((rows[y.val]?).bind id).bind (Verify.laneRow false sh.ℓ)).getD (Vector.replicate _ 0)⟩
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

theorem extractAllRows_congr {l l' : hashSpec.QueryLog} {root : Digest} (h : RowsAgree l l' root)
    (depth rowWords leafWords : ℕ) :
    extractAllRows l' root depth rowWords leafWords =
      extractAllRows l root depth rowWords leafWords := by
  rw [extractAllRows_eq, extractAllRows_eq]
  exact List.map_congr_left fun p _ ↦ h depth rowWords leafWords p

theorem level0Word_congr (c : Chain) {l l' : hashSpec.QueryLog} :
    ∀ {r : Option Digest}, (∀ root, r = some root → RowsAgree l l' root) →
      level0Word prog s c l' r = level0Word prog s c l r
  | none, _ => rfl
  | some root, h => by
    simp only [level0Word, logWord, wordRows, extractAllRows_congr (h root rfl)]

theorem laterWord_congr {l l' : hashSpec.QueryLog} (sh : Whir.Shape) (κ : ℕ) :
    ∀ {r : Option Digest}, (∀ root, r = some root → RowsAgree l l' root) →
      laterWord l' sh κ r = laterWord l sh κ r
  | none, _ => rfl
  | some root, h => by
    simp only [laterWord, extractAllRows_congr (h root rfl)]

theorem laterWords_congr {l l' : hashSpec.QueryLog} :
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

theorem markAfter_finalMark (sh : Whir.Shape) (nf : ℕ) (pre : Bool) :
    MarkAfter pre (finalMark (sh := sh) (nf := nf)) (finalFlags sh nf).toFlags :=
  markAfter_append (markAfter_none _ _) <| markAfter_append (markAfter_none _ _) <|
  markAfter_append (markAfter_none _ _) <| markAfter_append (markAfter_none _ _) <|
  markAfter_append (markAfter_none _ _) <| markAfter_append (markAfter_draw rfl _) <|
  markAfter_append (markAfter_none _ _) <| markAfter_append (markAfter_none _ _) <|
  markAfter_append (markAfter_none _ _) <| markAfter_append (markAfter_none _ _) <|
  markAfter_append (markAfter_none _ _) <| markAfter_append (markAfter_none _ _) <|
  markAfter_none _ _

theorem markAfter_levelMark (sh sh' : Whir.Shape) (κ' : ℕ) {k : List Step}
    {bR : (seqSpec k).ChallengeIdx → Bool} {N : SeqFlags k} (hR : ∀ pre, MarkAfter pre bR N.toFlags)
    (pre : Bool) :
    MarkAfter pre (levelMark (sh := sh) (sh' := sh') (κ' := κ') bR)
      (levelFlags sh sh' κ' N).toFlags :=
  markAfter_append (markAfter_none _ _) <| markAfter_append (markAfter_none _ _) <|
  markAfter_append (markAfter_none _ _) <| markAfter_append (markAfter_none _ _) <|
  markAfter_append (markAfter_none _ _) <| markAfter_append (markAfter_none _ _) <|
  markAfter_append (markAfter_none _ _) <| markAfter_append (markAfter_none _ _) <|
  markAfter_append (markAfter_draw rfl _) <| markAfter_append (markAfter_none _ _) <|
  markAfter_append (markAfter_none _ _) <| markAfter_append (markAfter_none _ _) <|
  markAfter_append (markAfter_none _ _) <| hR _

theorem markAfter_ladder : ∀ {sh : Whir.Shape} {κ : ℕ} (L : Ladder sh κ) (pre : Bool),
    MarkAfter pre L.mark (ladderFlags L).toFlags
  | _, _, .last sh nf, pre => markAfter_finalMark sh nf pre
  | _, _, @Ladder.cons sh sh' κ' L, pre => markAfter_levelMark sh sh' κ' (markAfter_ladder L) pre

/-- **Every marked challenge of the compiled protocol follows a nonce round.** -/
theorem markAfter_compiled (I : M3Instance) (c : Chain) :
    MarkAfter false (listBindingMark I c.ladder) (compiledFlags I c) :=
  markAfter_append (markAfter_none _ _) <| markAfter_append (markAfter_none _ _) <|
    markAfter_append (markAfter_none _ _) (markAfter_ladder c.ladder _)

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
  n a := 1 + busRounds (leanVm prog a.1.1) + tableRounds (leanVm prog a.1.1) + 2 +
    flockRounds (leanVm prog a.1.1) (leanVm prog a.1.1).flock + 1 + 0 +
    seqRounds (.skip :: .msg (SumcheckRound.Message E 2) :: (chainAt a).ladder.steps)
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
theorem prEvent_le_of_inst {C : Type} {p : C → Prop} {e : ℝ≥0∞} (i₂ : SampleableType C)
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
    replace hP := prEvent_le_of_inst _ hP I₀
    rw [prEvent_lowBitsZero (bits := Parameters.Whir.queryGrindingBits) (by decide)]
    calc _ ≤ (2 ^ Parameters.Whir.queryGrindingBits : ℝ≥0∞)⁻¹ *
          ↑(listBindingError (leanVm prog s) (leanIsaChain prog s hs ρ hρ).ladder
            (leanIsaChain prog s hs ρ hρ).pars i) :=
        mul_le_mul_of_nonneg_left hP (by positivity)
      _ = ↑((2 ^ Parameters.Whir.queryGrindingBits : ℝ≥0)⁻¹ *
          listBindingError (leanVm prog s) (leanIsaChain prog s hs ρ hρ).ladder
            (leanIsaChain prog s hs ρ hρ).pars i) := by
        rw [ENNReal.coe_mul, ENNReal.coe_inv (pow_ne_zero _ two_ne_zero), ENNReal.coe_pow,
          ENNReal.coe_ofNat]
      _ ≤ _ := ENNReal.coe_le_coe.mpr hm'
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
flip of a challenge to a bad one. -/
theorem leanVm_misbehaves_rom (A : Adversary) {Q : ℕ} (hQ : IsTotalQueryBound A Q) :
    Pr{let z ← runRandom (loggedGame verifyWith prog input A)}[
      HashMisbehaves (rootsOf prog input) (leanVmReader prog input).Flip prog input z.1] ≤
      niError εquery (verifierQueries prog input) Q :=
  misbehaves_rom (leanVmReader prog input) prog input rfl (leanVmReader_density prog input)
    verifyWith (verifierQueries_bound prog input) (rootsOf prog input)
    (length_rootsOf_le prog input) A hQ

end LeanVmReader

end

end LeanerVM.Protocol
