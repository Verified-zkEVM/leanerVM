/-
  LeanerVM.Protocol.Core

  The deterministic heart of leanVM's knowledge soundness in the random-oracle model: on a run of
  the game whose verifier accepts and from whose prover's log the extractor finds no stack, the
  hash misbehaves.
-/

module

public import LeanerVM.Protocol.Core.History
public import LeanerVM.Protocol.Core.Flip
public import LeanerVM.Protocol.Core.Grinding
public import LeanerVM.Protocol.Core.Solved
public import LeanerVM.Protocol.ToArkLib.StateWalk
public import LeanerVM.Protocol.Replay

/-!
# The core of knowledge soundness in the random-oracle model

On a run of the logged game (`Run`) whose joint log is consistent and whose verifier, replayed on
that log, accepts, either the extractor finds a stack with `M3Holds` from the prover's log
(`Extracts`), or the hash misbehaves on the run (`HashMisbehaves`): a collision on the joint log,
a hit, or a flip of the verifier's own chain (`core`, and `core_of_mem_support` on a possible run
of the game). With the random-oracle bound on misbehaving this is knowledge soundness in the
random-oracle model (`verify_knowledgeSound_rom`).

The argument is by contradiction: no collision, no hit and no flip. The accepted replay walks the
chain and the openings, and the algebra accepts their wire and rows (`ChainLog.accepts_of_replay`).
The chain walk's history decodes, with the words read off the joint log under the roots the
history carries, to a transcript of the compiled protocol whose wire is the walk's
(`LeanVmReader.walkChainLogged_proof_decodes`) and whose rows are those the openings authenticate
(`rows_eq_ladderRows`, by Merkle binding on the log). The decoded transcript is solved
(`solved_of_decode`), so the compiled verifier accepts it (`Compile.compiled_of_algebra`). The
state function of the compiled protocol's round-by-round knowledge soundness is then true at the
transcript's end. Walking it back, a challenge that turns it from false to true is bad and its
group flips (`flipAt_of_bad`); with no flip it is true after the commitment, where it says the
commitment's pick finds a stack (`listBinding_deployed_kSF_one`). The committed word is the
level-0 word read off the joint log under the proof's level-0 root, which with no hit is the word
read off the prover's log (`extractRows_determined`): the word the extractor picks from.
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters LeanerVM.Semantics Blake2sHash LeanIsa ProtocolSpec StepSchedule Verify
open DecodeChain Whir ProofRoots LeanVmReader OracleComp OracleSpec
open scoped NNReal ENNReal

@[expose] public section

namespace Core

-- The stack's size is never computed here: sealed, unification does not evaluate it on a
-- symbolic program.
attribute [local irreducible] LeanIsa.leanIsaμ LeanIsa.blocks

/-! ## The level-0 word -/

/-- The level-0 word read off a log at a chain's indices, carried to equal indices, is the word
read off the log at those. -/
private theorem cast_logWord (l : hashSpec.QueryLog) (root : Digest) (prog : Program)
    (s : Sizes) {sh sh' : Whir.Shape} {κ κ' : ℕ} (hsh : sh = sh') (hκ : κ = κ')
    (hℓ : sh.ℓ = sh'.ℓ) (hb : κ + sh.R = κ' + sh'.R) (ht : sh.t = sh'.t) :
    Whir.KWord.cast hℓ hb ht (logWord l root (κ + sh.R) (level0Lanes prog s κ) sh.ℓ sh.t) =
      logWord l root (κ' + sh'.R) (level0Lanes prog s κ') sh'.ℓ sh'.t := by
  subst hsh hκ
  rfl

/-- The word read off two logs whose rows under its root agree is the same. -/
private theorem logWord_congr {l l' : hashSpec.QueryLog} {root : Digest}
    (h : ∀ depth rowWords leafWords p, extractRows l' root depth rowWords leafWords p =
      extractRows l root depth rowWords leafWords p) (depth n ℓ t : ℕ) :
    logWord l' root depth n ℓ t = logWord l root depth n ℓ t := by
  have h' : extractRows l' root depth n (2 ^ ℓ) = extractRows l root depth n (2 ^ ℓ) :=
    funext (h depth n (2 ^ ℓ))
  simp only [logWord, wordRows, extractAllRows_eq, h']

/-- **The proof's roots are not hit fresh by the verifier**: with no hit, no query of the
verifier fresh with respect to the prover's log is answered by a root of the proof, or by a
child of a node the prover asked. -/
private theorem not_freshHit_roots {prog : Program} {input : PublicInput} {g : Run}
    (hcons : QueryLog.Consistent g.log) (hhit : ¬ Hit (rootsOf prog input) prog input g) :
    ¬ MerkleTree.FreshHit nodeOfBytes? (rootsOf prog input g.proof) g.logA g.logV := by
  intro h
  obtain ⟨k, hk, hfresh, hfirst, hknown⟩ := h.first hcons
  have hlen : g.logA.length + k < g.log.length := by simp [Run.log]; omega
  have htake : g.log.take (g.logA.length + k) = g.logA ++ g.logV.take k := by
    simp [Run.log, List.take_append]
  have hget : g.log[(⟨g.logA.length + k, hlen⟩ : Fin g.log.length)] = g.logV[k] := by
    simp [Run.log, List.getElem_append_right]
  have hfr : QueryLog.Fresh (g.log.take (g.logA.length + k))
      g.log[(⟨g.logA.length + k, hlen⟩ : Fin g.log.length)].1 := by
    intro e he
    rw [htake, List.mem_append] at he
    rw [hget]
    rcases he with he | he
    · exact hfresh e he
    · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp he
      simp only [List.length_take] at hj
      simpa using hfirst j (by omega)
  refine hhit ?_
  rcases hknown with hr | ⟨e, he, hd⟩
  · refine .inr ⟨⟨g.logA.length + k, hlen⟩, by simp, hfr, ?_⟩
    rw [hget]
    exact hr
  · refine .inl ⟨⟨g.logA.length + k, hlen⟩, hfr, ?_⟩
    rw [hget]
    show g.logV[k].2 ∈ inPlay (seedDigests prog input) (g.log.take (g.logA.length + k))
    rw [htake]
    obtain ⟨p, hp, rfl⟩ := List.mem_iff_getElem.mp he
    refine inPlay_mono _ (g.logA.take p ++ [g.logA[p]]) _ ?_ _
      (queryChildren_mem_inPlay _ _ _ _ hd)
    rw [← List.take_succ_eq_append_getElem hp]
    exact (List.take_prefix _ _).trans (List.prefix_append _ _)

/-- A cast along an equation of types is heterogeneously equal to its argument. -/
private theorem heq_mp {α β : Sort _} (h : α = β) (a : α) : HEq (Eq.mp h a) a := by
  cases h
  rfl

/-- The first half of an appended transcript at a round is the whole's at that round. -/
private theorem fst_heq {m n : ℕ} {p₁ : ProtocolSpec m} {p₂ : ProtocolSpec n}
    (T : FullTranscript (p₁ ++ₚ p₂)) (i : Fin m) : HEq (T.fst i) (T (Fin.castAdd n i)) := by
  unfold FullTranscript.fst
  exact heq_mp _ _

/-- The word committed in the first round, read off a full transcript cut after it, is the
transcript's level-0 word. -/
private theorem committedWord_take_one {I : M3Instance} {sh : Whir.Shape} {κ : ℕ}
    {L : Ladder sh κ} (full : (listBindingSpec I sh κ L).FullTranscript) (k : Fin _)
    (h₁ : k.val ≤ _) (hk : 0 < k.val) (hk1 : k.val = 1) :
    committedWord (k := k) (full.take k.val h₁) hk = Prove.level0Word full := by
  obtain ⟨k, hk2⟩ := k
  dsimp only at hk1
  subst hk1
  apply eq_of_heq
  refine (cast_heq _ _).trans ?_
  refine HEq.symm ?_
  exact (fst_heq _ _).trans ((fst_heq _ _).trans ((fst_heq _ _).trans ((fst_heq _ _).trans
    ((fst_heq _ _).trans ((fst_heq _ _).trans (fst_heq _ _))))))

/-- The compiled verifier, as the state function of `listBinding_deployed` reads it. -/
private theorem compiledDef_verifier (prog : Program) (s : Sizes) (hs : s.Admissible prog) (ρ : ℕ)
    (hρ : validRate ρ) :
    (Prove.compiledDef prog s hs ρ hρ).red.toReduction.verifier =
      (listBindingDef (leanVmPhases (leanIsaInstance Blake2sFlock.blake2sFlockSpec prog s)
        (leanIsa_conditions Blake2sFlock.blake2sFlockSpec prog s))
        (leanIsaChain_height Blake2sFlock.blake2sFlockSpec prog s hs ρ hρ)
        (leanIsaChain prog s hs ρ hρ).ladder).red.verifier.toVerifier := by
  unfold Prove.compiledDef Verify.leanVm
  rfl

/-- A property of some witness that does not depend on the witness. -/
private theorem of_exists_iff {α : Sort _} {P : α → Prop} {Q : Prop} (h : ∀ w, P w ↔ Q)
    (he : ∃ w, P w) : Q :=
  he.elim fun w hw ↦ (h w).mp hw

/-- **The commitment's pick finds a stack** in a transcript's level-0 word when the state function
of `listBinding_deployed` holds, for some witness, at every round of the transcript. -/
private theorem pick_of_walk (F : FlockSpec) (prog : Program) (s : Sizes) (hs : s.Admissible prog)
    (ρ : ℕ) (hρ : validRate ρ) (st : (leanIsaInstance F prog s).Stmt × ∀ i, NoOracle i)
    (tr : (listBindingSpec (leanIsaInstance F prog s) (leanIsaChain prog s hs ρ hρ).sh
      (leanIsaChain prog s hs ρ hρ).κ (leanIsaChain prog s hs ρ hρ).ladder).FullTranscript)
    (h : ∀ m : Fin _, ∃ w, ((listBinding_deployed F prog s hs ρ hρ).kSF (pure ())
      noSharedOracle).toFun m st (tr.take m.val m.is_le) w)
    {x : KWord (leanIsaChain prog s hs ρ hρ).sh.ℓ
      ((leanIsaChain prog s hs ρ hρ).κ + (leanIsaChain prog s hs ρ hρ).sh.R)
      (leanIsaChain prog s hs ρ hρ).sh.t} (hx : Prove.level0Word tr = x) :
    (deployedPick (leanIsaInstance F prog s) (admissible_of_sizes hs hρ) st.1
      (headWord (admissible_of_sizes hs hρ) x)).isSome := by
  subst hx
  have h1 := of_exists_iff (listBinding_deployed_kSF_one F prog s hs ρ hρ (pure ()) noSharedOracle
    st ⟨1, by omega⟩ rfl _) (h ⟨1, by omega⟩)
  have h2 := committedWord_take_one tr ⟨1, by omega⟩ (Fin.is_le _) Nat.one_pos rfl
  exact (congrArg (fun x ↦ (deployedPick (leanIsaInstance F prog s) (admissible_of_sizes hs hρ) st.1
    (headWord (admissible_of_sizes hs hρ) x)).isSome = true) h2).mp h1

/-- **The extractor succeeds** on a log whose level-0 word under the proof's level-0 root has a
stack the commitment's pick finds. -/
private theorem extract_isSome (F : FlockSpec) (prog : Program) (input : PublicInput)
    (proof : Proof PrunedMerklePaths) (log : hashSpec.QueryLog) {s : Sizes} {ρ : ℕ}
    (hs : s.Admissible prog) (hρ : validRate ρ) (hsetup : setup? prog proof = some (s, ρ))
    {root : Digest} (hroot : level0Root proof = some root)
    (h : (deployedPick (leanIsaInstance F prog s) (admissible_of_sizes hs hρ) input
      (headWord (admissible_of_sizes hs hρ) (logWord log root
        ((leanIsaChain prog s hs ρ hρ).κ + (leanIsaChain prog s hs ρ hρ).sh.R)
        (level0Lanes prog s (leanIsaChain prog s hs ρ hρ).κ) (leanIsaChain prog s hs ρ hρ).sh.ℓ
        (leanIsaChain prog s hs ρ hρ).sh.t))).isSome) :
    (extract F prog input proof log).isSome := by
  have hhead := deployedChain_head (admissible_of_sizes hs hρ)
  unfold extract
  rw [announced?_of_setup hsetup]
  simp only [dite_eq_left (show s.Admissible prog ∧ validRate ρ from ⟨hs, hρ⟩), hroot,
    Option.isSome_map]
  convert h using 3
  exact (cast_logWord log root prog s hhead.1 hhead.2.1 _ _ _).symm

/-! ## The core -/

/-- **The core of knowledge soundness in the random-oracle model**: on a run of the game whose
joint log is consistent, whose verifier replayed on the joint log accepts, and from whose prover's
log the extractor finds no stack with `M3Holds`, the hash misbehaves: a collision on the joint log,
a hit, or a flip of the verifier's own chain. -/
theorem core {prog : Program} {input : PublicInput} {g : Run}
    (hc : QueryLog.Consistent g.log)
    (hV : replay g.log prog input g.proof = some (true, g.logV))
    (hX : ¬ Extracts Blake2sFlock.blake2sFlockSpec prog input g.proof g.logA) :
    HashMisbehaves (rootsOf prog input) (leanVmReader prog input).Flip prog input g := by
  by_contra hmis
  simp only [HashMisbehaves, not_or] at hmis
  obtain ⟨hcoll, hhit, hflip⟩ := hmis
  -- the accepted replay
  obtain ⟨s, ρ, levels, w, st₁, log₁, rows, st₂, log₂, hsetup, hl, hrc, hro, halg, hpre⟩ :=
    ChainLog.accepts_of_replay hV
  obtain ⟨hist, hwl, ⟨L₁, hL₁, hq₁⟩, -⟩ := ChainLog.walkChain_log _ hrc
  obtain ⟨L₂, hL₂, hinv⟩ := nonceChecked_of_walkChain hrc
  obtain rfl : L₁ = L₂ := by simpa using hL₁.symm.trans hL₂
  obtain ⟨hs, hρ, hdecW⟩ := walkChainLogged_proof_decodes hsetup hl hwl
  obtain ⟨hread, hst⟩ := DecodeChain.walkChain_history _ hwl
  have hshapes := shapes_leanIsaChain hs hρ hl
  -- the history: in the log, opening with the announcement, its nonces passing their checks
  have hchain : ∀ e ∈ HashChain.queries Block.input (FsState.seed prog input).cv hist,
      e ∈ g.log := fun e he ↦
    List.mem_append_right _ (hpre.subset (by rw [hL₁]; exact List.mem_append_right _ (hq₁ e he)))
  have hobs := observes_of_walkChain hread
  have hann := announcementOf_of_setup hsetup hs hρ hst hobs
  have hseed := seed_not_answer hc fun h ↦ hhit (.inl h)
  have hpow := powPasses_of_history hcoll hseed hchain fun e he ↦ hinv e (hq₁ e he)
  -- the transcript decoded with the words read off the joint log
  obtain ⟨W, hW⟩ : ∃ W, W = wordsOf prog input s hs ρ hρ g.log hist := ⟨_, rfl⟩
  obtain ⟨tr, hdec, hwire⟩ := hdecW W
  have hroots := walkChain_rootAt hread
  have h8 : rootAt hist 8 = some w.root := (List.cons.inj hroots).1
  have hW0 : W.level0 =
      LeanVmReader.level0Word prog s (leanIsaChain prog s hs ρ hρ) g.log (some w.root) := by
    rw [hW, ← h8]
    rfl
  have hWl : W.later = laterWords g.log (leanIsaChain prog s hs ρ hρ).ladder
      ((w.whir.filterMap (·.root)).map some) := by
    rw [hW]
    show laterWords _ _ (List.map _ _) = _
    rw [hshapes]
    exact congrArg _ (List.cons.inj hroots).2
  have hfront := (front_of_decode hdec).1
  have hwords := words_of_decode hdec
  rw [hWl] at hwords
  have hLR := ladderRoots_of _ _ w.whir hwords
    (by rw [hshapes]; exact rootsShaped_of_walkChain hread)
  -- the rows the openings authenticate are the transcript's
  have hok := openingsOk_of_run _ _ _ _ _ _ _ _ _ (openings_opt_of_replay hro)
  have hcnt := rowCounts_of_algebra halg
  have hwire' : ladderWire (leanIsaChain prog s hs ρ hρ).ladder (Prove.ladderPart tr) =
      List.zipWith WhirLevel.view (leanIsaChain prog s hs ρ hρ).ladder.shapes w.whir := by
    rw [hshapes]
    exact congrArg Wire.whir hwire
  have hκ : (leanIsaChain prog s hs ρ hρ).κ = leanIsaμ prog s - Parameters.Whir.initialFold :=
    (deployedChain_head (admissible_of_sizes hs hρ)).2.1.trans
      (deployedHeadKap_eq (admissible_of_sizes hs hρ))
  have hleaf : rowWordsOf (nLanes prog s) true ⟨(leanIsaChain prog s hs ρ hρ).sh.ℓ,
        (leanIsaChain prog s hs ρ hρ).κ, (leanIsaChain prog s hs ρ hρ).sh.R,
        (leanIsaChain prog s hs ρ hρ).sh.t, false⟩ ≤
      leafWordsOf true ⟨(leanIsaChain prog s hs ρ hρ).sh.ℓ, (leanIsaChain prog s hs ρ hρ).κ,
        (leanIsaChain prog s hs ρ hρ).sh.R, (leanIsaChain prog s hs ρ hρ).sh.t, false⟩ →
      ∀ (p : Fin (2 ^ ((leanIsaChain prog s hs ρ hρ).κ + (leanIsaChain prog s hs ρ hρ).sh.R)))
        row, extractRows g.log w.root
          ((leanIsaChain prog s hs ρ hρ).κ + (leanIsaChain prog s hs ρ hρ).sh.R)
          (rowWordsOf (nLanes prog s) true ⟨(leanIsaChain prog s hs ρ hρ).sh.ℓ,
            (leanIsaChain prog s hs ρ hρ).κ, (leanIsaChain prog s hs ρ hρ).sh.R,
            (leanIsaChain prog s hs ρ hρ).sh.t, false⟩)
          (leafWordsOf true ⟨(leanIsaChain prog s hs ρ hρ).sh.ℓ, (leanIsaChain prog s hs ρ hρ).κ,
            (leanIsaChain prog s hs ρ hρ).sh.R, (leanIsaChain prog s hs ρ hρ).sh.t, false⟩) p =
          some row →
        ((Prove.level0Word tr).row p).toList.reverse =
          leafImage (leafWordsOf true ⟨(leanIsaChain prog s hs ρ hρ).sh.ℓ,
            (leanIsaChain prog s hs ρ hρ).κ, (leanIsaChain prog s hs ρ hρ).sh.R,
            (leanIsaChain prog s hs ρ hρ).sh.t, false⟩) row := by
    intro hle p row hrow
    have hn : nLanes prog s = level0Lanes prog s (leanIsaChain prog s hs ρ hρ).κ := by
      rw [hκ]
      rfl
    simp only [rowWordsOf, leafWordsOf, ↓reduceIte, hn] at hle hrow ⊢
    rw [hfront, hW0]
    exact logWord_row_reverse hle p hrow
  have hrows : rows = Prove.rowsOf (leanVm prog s) (leanIsaChain prog s hs ρ hρ).ladder tr :=
    rows_eq_ladderRows hc hcoll (nLanes prog s) _ true w.root _ _ w.whir rows hleaf hLR
      (by rw [hshapes]; exact hok) hwire' (by rw [hshapes]; exact hcnt)
  have halg' : algebra prog s input (leanIsaChain prog s hs ρ hρ).ladder.shapes
      (wireOf (leanVm prog s) (leanIsaChain prog s hs ρ hρ).ladder tr)
      (Prove.rowsOf (leanVm prog s) (leanIsaChain prog s hs ρ hρ).ladder tr) = true := by
    rw [hshapes, hwire, algebra_view, ← hrows]
    exact halg
  obtain ⟨so, hso⟩ := Compile.compiled_of_algebra prog s hs ρ hρ input tr (solved_of_decode hdec)
    halg'
  rw [compiledDef_verifier] at hso
  -- the announcement as one value
  obtain ⟨a, rfl, rfl⟩ : ∃ a : Ann prog, a.1.1 = s ∧ a.1.2 = ρ := ⟨⟨(s, ρ), hs, hρ⟩, rfl, rfl⟩
  obtain rfl : hs = a.2.1 := rfl
  obtain rfl : hρ = a.2.2 := rfl
  -- the state function, true at the end, is true after the commitment
  have hfull := ((listBinding_deployed Blake2sFlock.blake2sFlockSpec prog a.1.1 a.2.1 a.1.2
    a.2.2).kSF (pure ()) noSharedOracle).toFun_full (input, fun i ↦ i.elim0) tr ()
      (Verifier.probEvent_pos_of_runNoOracle _ (pure ()) noSharedOracle _ tr hso _ trivial)
  have hall := Verifier.KnowledgeStateFunction.exists_toFun_take_of_good
    ((listBinding_deployed Blake2sFlock.blake2sFlockSpec prog a.1.1 a.2.1 a.1.2 a.2.2).kSF
      (pure ()) noSharedOracle) _ tr hfull
    fun i w' h ↦ Classical.byContradiction fun hneg ↦
      hflip (flipAt_of_bad (a := a) hc hcoll hseed hchain hobs hann hpow hW hdec i (by
        unfold Bad
        dsimp only [deployedSpec] at hneg h ⊢
        exact ⟨w', hneg, h⟩))
  -- the word the extractor picks from
  have hroot : w.root ∈ rootsOf prog input g.proof := by
    rw [rootsOf_eq_of_walkChainLogged hsetup hl hwl]
    exact List.mem_cons_self
  have hlog := logWord_congr (l := g.logA) (l' := g.log) (root := w.root)
    (extractRows_determined g.logA g.logV (rootsOf prog input g.proof) w.root hroot hc
      (not_freshHit_roots hc hhit))
  have hpick := pick_of_walk Blake2sFlock.blake2sFlockSpec prog a.1.1 a.2.1 a.1.2 a.2.2
    (input, fun i ↦ i.elim0) tr hall (hfront.trans (hW0.trans (hlog _ _ _ _)))
  exact hX ((extracts_iff_isSome _ _ _ _ _).mpr (extract_isSome _ prog input g.proof g.logA a.2.1
    a.2.2 hsetup ((rootAt_eq_level0Root hst hobs).symm.trans h8) hpick))

/-- **The core on a possible run of the game**: on a run of the game whose joint log is
consistent and whose verdict accepts, if the extractor finds no stack with `M3Holds` from the
prover's log, the hash misbehaves. -/
theorem core_of_mem_support {prog : Program} {input : PublicInput} {A : Adversary} {g : Run}
    (hg : g ∈ support (loggedGame verifyWith prog input A)) (hc : QueryLog.Consistent g.log)
    (hok : g.ok = true)
    (hX : ¬ Extracts Blake2sFlock.blake2sFlockSpec prog input g.proof g.logA) :
    HashMisbehaves (rootsOf prog input) (leanVmReader prog input).Flip prog input g :=
  core hc (by rw [replay_of_mem_support_loggedGame hg hc, hok]) hX

/-! ## Knowledge soundness in the random-oracle model -/

/-- A run under the lazy random oracle is a possible run of the game, and its joint log is
consistent: every logged answer is the final cache's. -/
private theorem run_of_mem_support_runRandom {prog : Program} {input : PublicInput}
    {A : Adversary} {z : Run × hashSpec.QueryCache}
    (hz : z ∈ support (runRandom (loggedGame verifyWith prog input A))) :
    z.1 ∈ support (loggedGame verifyWith prog input A) ∧ QueryLog.Consistent z.1.log := by
  have hrun : runRandom (loggedGame verifyWith prog input A) =
      Prod.map id QueryHistory.freshLog.view <$>
        (simulateQ QueryHistory.freshLog.randomOracle (loggedGame verifyWith prog input A)).run
          ((∅ : hashSpec.QueryCache), []) := by
    unfold runRandom
    exact ((QueryHistory.freshLog (spec := hashSpec)).randomOracle_run_view
      (loggedGame verifyWith prog input A) ((∅ : hashSpec.QueryCache), [])).symm
  rw [hrun, support_map] at hz
  obtain ⟨z', hz', rfl⟩ := hz
  refine ⟨support_simulateQ_run'_subset QueryHistory.freshLog.randomOracle _
    ((∅ : hashSpec.QueryCache), []) ?_, ?_⟩
  · rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem _ hz'
  rw [show loggedGame verifyWith prog input A = A.withQueryLog >>= fun p ↦
    (verifyWith hashQuery prog input p.1).withQueryLog >>= fun q ↦
      pure ⟨p.1, p.2, q.2, q.1⟩ from rfl] at hz'
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz'
  obtain ⟨z₁, hz₁, z₂, hz₂, rfl⟩ := hz'
  obtain ⟨-, hf₁, -, hc₁⟩ :=
    QueryHistory.withQueryLog_freshLog_support _ QueryHistory.isFreshLog_empty hz₁
  obtain ⟨-, -, hle, hc₂⟩ := QueryHistory.withQueryLog_freshLog_support _ hf₁ hz₂
  have hcached : ∀ e ∈ z₁.1.2 ++ z₂.1.2, z₂.2.1 e.1 = some e.2 := fun e he ↦
    (List.mem_append.mp he).elim (fun he ↦ hle (hc₁ e he)) (hc₂ e)
  intro e₁ he₁ e₂ he₂ h
  have h₁ := hcached e₁ he₁
  rw [h] at h₁
  exact Option.some.inj (h₁.symm.trans (hcached e₂ he₂))

/-- **Knowledge soundness of the verifier in the random-oracle model.** With the hash a uniformly
random function and an adversary `A` of at most `Q` queries, the game's verifier accepts `A`'s
proof while the extractor finds no stack with `M3Holds` from `A`'s queries with probability at
most `(Q + 13697) / 2^128` (the challenges) plus `hashTerm 13697 Q` (collisions and hits).
Selective: the program and the public input are fixed before `A` runs. -/
theorem verify_knowledgeSound_rom (prog : Program) (input : PublicInput) (A : Adversary) {Q : ℕ}
    (hQ : IsTotalQueryBound A Q) :
    Pr{let z ← runRandom (loggedGame verifyWith prog input A)}[
      z.1.ok = true ∧ ¬ Extracts Blake2sFlock.blake2sFlockSpec prog input z.1.proof z.1.logA] ≤
      ((Q + 13697 : ℕ) / 2 ^ 128 + hashTerm 13697 Q : ℝ≥0) :=
  (OracleComp.prEvent_mono_of_support _ fun _ hz h ↦
    core_of_mem_support (run_of_mem_support_runRandom hz).1 (run_of_mem_support_runRandom hz).2
      h.1 h.2).trans (leanVm_misbehaves_rom_closed prog input A hQ)

end Core

end

end LeanerVM.Protocol
