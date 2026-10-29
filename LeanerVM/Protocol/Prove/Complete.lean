/-
  LeanerVM.Protocol.Prove.Complete

  The honest prover's completeness: a proof `proveWith` returns for a witness satisfying leanISA's
  constraint statement is accepted by `verifyWith`, whatever the hash, given that the executable
  verifier's algebra accepts every transcript the compiled oracle protocol's verifier accepts.
-/

module

public import LeanerVM.Protocol.Prove.Openings
public import LeanerVM.Protocol.LeanIsa.Complete

/-!
# The honest prover is complete

`baseProver_complete_of_agree`: for every byte hash `H`, a proof the honest prover returns for a
witness satisfying leanISA's constraint statement (`SatisfiedBy`) is accepted by the executable
verifier at `H`, given `PhasesAgree`: on the transcripts the compiled oracle protocol's verifier
accepts, the executable verifier's algebra accepts the transcript's wire (`wireOf`) and rows
(`rowsOf`). That hypothesis is the completeness half of the phase-by-phase agreement of the two
verifiers, proved as `Compile.phasesAgree` (`LeanerVM.Protocol.Compile.Agree`), where
`Prove.baseProver_complete` drops it.

The proof:

1. the prover's run against the wire of the compiled schedule steps through the wire on its
   transcript (`Prover.runWith_runsAs`), and that transcript is the run of the compiled protocol's
   honest prover on its own challenges (`Prover.runWith_eq_runWithChallenges`,
   `compiledProver_run`);
2. by the compiled protocol's perfect completeness, its verifier accepts that transcript
   (`Prover.accepts_of_run`), so `PhasesAgree` gives that the algebra accepts the transcript's wire
   and rows;
3. the chain walk reads the prover's stream back as the transcript's wire, but for the roots,
   the nonces and the positions' reduction (`walkChain_reads`), which the algebra does not read
   (`Verify.algebra_erase`); the openings are read back as the transcript's rows
   (`reads_openings`). The proof stores only the committed lanes of level 0's rows and the
   verifier fills the rest with zeros; the honest word's lanes past them vanish
   (`level0Word_honest`, `kwordOf_stackOf_high`: the stack is zero past its last block), so the
   rows read are the word's;
4. the announcement passes the setup, the ladder is the deployed chain's, the openings have their
   shapes and the stream and the openings are consumed.

`proveWith_eq_none`: the prover returns no proof only when the witness gives no sizes, its sizes
are not admissible, the rate is not valid, or a grind finds no nonce within its fuel at some chain
state. Every round of the wire runs when the grinds do (`Prover.runWith_total`), and the book
keeps as many commitments as positions (`book_compiled`), so the openings' size check never
fails. So the hypothesis that the prover returned a proof is met whenever the grinds succeed.

Both theorems hold from any start the prover and the verifier share
(`baseProver_complete_of_agree_from`, `proveFrom_eq_none`); the statements from the statement's
seed are their instances.

Transcripts are passed in explicit mode (`@t`, `@Prod.fst _ _ r`), which spares the elaborator
reducing their types (see `LeanerVM.Protocol.Prove.ReadBack`).

The grinding nonce shows where the oracle transcript and the proof differ: the oracle protocol's
honest prover sends zero, the proof carries the nonce the grind finds. The algebra reads neither,
so the agreement is applied at the honest transcript itself, and no lemma about the compiled
verifier's dependence on the nonce rounds is needed.
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Arithmetization Blake2sHash LeanIsa Whir
open OracleComp OracleSpec ProtocolSpec StepSchedule DecodeChain
open Air.Flat (EnsembleWitness)

@[expose] public section

namespace Prove

/-- The compiled protocol at leanVM's instance and WHIR's deployed chain, at an admissible
announcement and rate. -/
abbrev compiledDef (prog : Program) (s : Sizes) (hs : s.Admissible prog) (ρ : ℕ)
    (hρ : validRate ρ) :=
  listBindingDef (leanVmPhases (Verify.leanVm prog s)
      (leanIsa_conditions Blake2sFlock.blake2sFlockSpec prog s))
    (leanIsaChain_height Blake2sFlock.blake2sFlockSpec prog s hs ρ hρ)
    (leanIsaChain prog s hs ρ hρ).ladder

/-- **The phases agree, on the accepted transcripts** (the hypothesis of
`baseProver_complete_of_agree`):
on every full transcript of the compiled protocol at leanVM's instance and WHIR's deployed chain
that its verifier accepts on the public input, the executable verifier's algebra accepts the
transcript's wire and the rows its words have at its positions, at the chain's levels. -/
def PhasesAgree (prog : Program) (s : Sizes) (hs : s.Admissible prog) (ρ : ℕ) (hρ : validRate ρ)
    (input : PublicInput) : Prop :=
  ∀ (tr : (listBindingSpec (Verify.leanVm prog s) (leanIsaChain prog s hs ρ hρ).sh
      (leanIsaChain prog s hs ρ hρ).κ (leanIsaChain prog s hs ρ hρ).ladder).FullTranscript)
    (so : Unit × ∀ i, OneW (leanIsaChain prog s hs ρ hρ).ladder.finShape
      (leanIsaChain prog s hs ρ hρ).ladder.finN i),
    Id.run (runNoOracle ((compiledDef prog s hs ρ hρ).red.toReduction.verifier.run
      (input, fun i ↦ i.elim0) @tr).run) = some so →
    Verify.algebra prog s input (leanIsaChain prog s hs ρ hρ).ladder.shapes
      (wireOf (Verify.leanVm prog s) (leanIsaChain prog s hs ρ hρ).ladder @tr)
      (rowsOf (Verify.leanVm prog s) (leanIsaChain prog s hs ρ hρ).ladder @tr) = true

/-- An accepted wire carries one public value per sent line. -/
private theorem pubLength_of_algebra {prog : Program} {s : Sizes} {input : PublicInput}
    {shs : List Verify.LevelShape} {w : Verify.Wire} {rows : List (List (List K))}
    (h : Verify.algebra prog s input shs w rows = true) :
    w.pub.values.length =
      PublicInput.sentCount (Verify.leanVm prog s) ((Verify.leanVm prog s).publicLines input) := by
  unfold Verify.algebra at h
  rcases hb : Verify.leanVmBus prog s input w.bus with _ | b <;> simp only [hb] at h
  · cases h
  rcases ht : Verify.tableStep (Verify.leanVm prog s) b w.table with _ | t <;> simp only [ht] at h
  · cases h
  rcases hp : Verify.pubStep (Verify.leanVm prog s) t w.pub with _ | p <;> simp only [hp] at h
  · cases h
  simp only [Verify.leanVmBus, Option.bind_eq_bind, Option.bind_eq_some_iff] at hb
  obtain ⟨_, -, _, -, hb⟩ := hb
  cases hb
  simp only [Verify.tableStep, Option.bind_eq_bind, Option.bind_eq_some_iff] at ht
  obtain ⟨_, -, _, -, _, -, ht⟩ := ht
  split_ifs at ht
  cases ht
  simp only [Verify.pubStep] at hp
  split_ifs at hp with hacc
  simp only [PublicInput.accepts, Bool.and_eq_true, decide_eq_true_eq] at hacc
  exact hacc.1

/-- The run on given challenges of two components in sequence begins with the first's. -/
private theorem runWithChallenges_def_append_fst {StmtIn ι₁ ι₂ ι₃ : Type} {O₁ : ι₁ → Type}
    {O₂ : ι₂ → Type} {O₃ : ι₃ → Type} [∀ i, OracleInterface (O₁ i)]
    [∀ i, OracleInterface (O₂ i)] [∀ i, OracleInterface (O₃ i)] {W₁ S₂ W₂ S₃ W₃ : Type}
    {m n : ℕ} {p₁ : ProtocolSpec m} {p₂ : ProtocolSpec n}
    [∀ i, OracleInterface (p₁.Message i)] [∀ i, SampleableType (p₁.Challenge i)]
    [∀ i, OracleInterface (p₂.Message i)] [∀ i, SampleableType (p₂.Challenge i)]
    (D₁ : Component.Def StmtIn O₁ W₁ S₂ O₂ W₂ p₁) (D₂ : Component.Def S₂ O₂ W₂ S₃ O₃ W₃ p₂)
    (ch : (p₁ ++ₚ p₂).Challenges) (stmt : StmtIn × ∀ i, O₁ i) (wit : W₁) :
    (Prover.runWithChallenges (D₁.append D₂).red.prover ch stmt wit).1.fst =
      (Prover.runWithChallenges D₁.red.prover (challengesLeft ch) stmt wit).1 :=
  runWithChallenges_append_fst _ _ ch stmt wit

/-- **The honest level-0 word**: on any challenges, the compiled protocol's honest prover sends
the `K` word of its stack. -/
private theorem level0Word_honest (prog : Program) (s : Sizes) (hs : s.Admissible prog) (ρ : ℕ)
    (hρ : validRate ρ) (ch : (listBindingSpec (Verify.leanVm prog s)
      (leanIsaChain prog s hs ρ hρ).sh (leanIsaChain prog s hs ρ hρ).κ
      (leanIsaChain prog s hs ρ hρ).ladder).Challenges)
    (stmt : PublicInput × ∀ i, NoOracle i) (q : Column (Verify.leanVm prog s).μ) :
    level0Word (@Prod.fst _ _ (Prover.runWithChallenges (compiledDef prog s hs ρ hρ).red.prover @ch
      stmt q)) =
      kwordOf (leanIsaChain prog s hs ρ hρ).sh.ℓ (leanIsaChain prog s hs ρ hρ).κ
        (leanIsaChain prog s hs ρ hρ).sh.R (leanIsaChain prog s hs ρ hρ).sh.t
        ((leanIsaChain_height Blake2sFlock.blake2sFlockSpec prog s hs ρ hρ).symm ▸ q.values) := by
  simp only [level0Word, compiledDef, listBindingDef, runWithChallenges_def_append_fst]
  rfl

/-- A vector cast along an equality of lengths has the same entries. -/
private theorem getElem_cast_values {a b : ℕ} (h : b = a) (v : Vector K (2 ^ b)) (i : ℕ)
    (hi : i < 2 ^ a) : (h ▸ v)[i] = v[i]'(h ▸ hi) := by
  subst h
  rfl

/-- A lane of the `K` word of a table vanishes where the table's slice for that lane does. -/
private theorem kwordOf_row_eq_zero {ℓ κ R t : ℕ} (q : CompPoly.CMlPolynomialEval K (κ + ℓ))
    (y : Fin (2 ^ (κ + R))) (u : Fin (2 ^ ℓ)) (hz : ∀ x : Fin (2 ^ κ), q[cubeIndex x u] = 0) :
    ((kwordOf ℓ κ R t q).row y)[u] = 0 := by
  simp only [kwordOf, Fin.getElem_fin, Vector.getElem_ofFn, encode, Weight.pair]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  have h : (sliceLow (relayout q) u)[i] = 0 := by
    rw [sliceLow_getElem, relayout_getElem, hz]
  simp only [Fin.getElem_fin] at h
  simp [h]

/-- **The honest word's lanes past the committed ones vanish**: lane `u` of the word of a
witness's stack encodes the stack's cells from `u · 2 ^ κ` on, which lie past the last block when
`u` is past the committed lanes. -/
private theorem kwordOf_stackOf_high {prog : Program} {s : Sizes} (hs : s.Admissible prog) {ρ : ℕ}
    (hρ : validRate ρ) {κ : ℕ} (w : EnsembleWitness (leanIsaEnsemble prog κ))
    (y : Fin (2 ^ ((leanIsaChain prog s hs ρ hρ).κ + (leanIsaChain prog s hs ρ hρ).sh.R)))
    (u : Fin (2 ^ (leanIsaChain prog s hs ρ hρ).sh.ℓ)) (hu : Verify.nLanes prog s ≤ u.val) :
    ((kwordOf (leanIsaChain prog s hs ρ hρ).sh.ℓ (leanIsaChain prog s hs ρ hρ).κ
      (leanIsaChain prog s hs ρ hρ).sh.R (leanIsaChain prog s hs ρ hρ).sh.t
      ((leanIsaChain_height Blake2sFlock.blake2sFlockSpec prog s hs ρ hρ).symm ▸
        (stackOf Blake2sFlock.blake2sFlockSpec prog s w).values)).row y)[u] = 0 := by
  obtain ⟨-, -, -, -, hℓ⟩ := leanIsaChain_walk hs hρ
  have hheight := leanIsaChain_height Blake2sFlock.blake2sFlockSpec prog s hs ρ hρ
  have hμ : (leanIsaInstance Blake2sFlock.blake2sFlockSpec prog s).μ = leanIsaμ prog s := rfl
  have hκ : (leanIsaChain prog s hs ρ hρ).κ = Verify.stackMu prog s - Whir.initialFold := by
    simp only [Verify.stackMu, Whir.initialFold]
    omega
  have hlanes : (blocks prog s).total ≤
      2 ^ (leanIsaChain prog s hs ρ hρ).κ * Verify.nLanes prog s := by
    rw [hκ]
    unfold Verify.nLanes
    have hd := Nat.two_pow_pos (Verify.stackMu prog s - Whir.initialFold)
    generalize 2 ^ (Verify.stackMu prog s - Whir.initialFold) = d at hd ⊢
    have h₁ := Nat.div_add_mod ((blocks prog s).total + d - 1) d
    have h₂ := Nat.mod_lt ((blocks prog s).total + d - 1) hd
    have h₃ := Nat.mul_le_mul_left d (le_max_right 1 (((blocks prog s).total + d - 1) / d))
    generalize d * (((blocks prog s).total + d - 1) / d) = P at h₁ h₃
    generalize d * max 1 (((blocks prog s).total + d - 1) / d) = Q at h₃ ⊢
    omega
  refine kwordOf_row_eq_zero _ y u fun x ↦ ?_
  rw [Fin.getElem_fin, getElem_cast_values]
  simp only [stackOf, Blocks.stackColumn, Blocks.stackAt, Vector.getElem_ofFn, cubeIndex_val]
  rw [ite_eq_left]
  have h₁ := Nat.mul_le_mul_left (2 ^ (leanIsaChain prog s hs ρ hρ).κ) hu
  omega

/-- A stored level-0 row whose lanes past the committed ones vanish has the full row, lanes in
reverse, as its leaf image. -/
private theorem leafImage_level0Rows {ℓ b t n : ℕ} (hn : n ≤ 2 ^ ℓ) {x : KWord ℓ b t}
    {p : Fin (2 ^ b)} (hz : ∀ u : Fin (2 ^ ℓ), n ≤ u.val → (x.row p)[u] = 0) :
    leafImage (2 ^ ℓ) (level0Rows n x)[p] = (x.row p).toList.reverse := by
  have hdrop : (x.row p).toList.drop n = List.replicate (2 ^ ℓ - n) 0 := by
    refine List.eq_replicate_iff.mpr ⟨by simp, fun a ha ↦ ?_⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
    simp only [List.getElem_drop, Vector.getElem_toList]
    exact hz ⟨n + i, by simp at hi; omega⟩ (Nat.le_add_right n i)
  conv_rhs => rw [← List.take_append_drop n (x.row p).toList]
  simp [level0Rows, leafImage, hdrop, hn, List.reverse_append]

/-- A prover's proof is the proof of a run of its writer from the start's state and an empty
book. -/
private theorem runs_of_runProofFrom {seed : Id FsState} {wr : ProveM Id Unit}
    {proof : Proof PrunedMerklePaths} (h : runProofFrom (m := Id) seed wr = some proof) :
    ∃ s', proveSem.Runs wr (⟨#[], #[]⟩, ⟨Id.run seed, #[], #[]⟩) () s' ∧
      s'.2.proof = proof := by
  replace h : runProofFrom (m := Id) (pure (Id.run seed)) wr = some proof := h
  unfold runProofFrom runWrite at h
  simp only [pure_bind, StateT.run'_eq, StateT.run_map, OptionT.run_map] at h
  rcases hr : ((wr.run ⟨#[], #[]⟩).run ⟨Id.run seed, #[], #[]⟩).run with
    _ | ⟨⟨u, bk⟩, ws⟩
  · rw [hr] at h
    cases h
  · rw [hr] at h
    cases h
    exact ⟨(bk, ws), hr, rfl⟩

/-- The stored level-0 rows hold the committed lanes, at most a leaf's. -/
private theorem length_level0Rows {ℓ b t n : ℕ} (hn : n ≤ 2 ^ ℓ) (x : KWord ℓ b t) :
    ∀ row ∈ (level0Rows n x).toList, row.length = n := by
  intro row hrow
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hrow
  simp [level0Rows, hn]

/-- The verifier on a proof that passes the setup, whose ladder exists and whose openings have
their shapes, and on which the walk and the openings read a wire and rows and consume the proof
from the start's state: the algebra on them. -/
private theorem verifyFrom_of_run {H : List UInt8 → Digest} {seed : Id FsState} {prog : Program}
    {input : PublicInput} {proof : Proof PrunedMerklePaths} {s : Sizes} {ρ : ℕ}
    {levels : List Whir.Level} {w : Verify.Wire} {rows : List (List (List K))}
    (hsetup : Verify.setup? prog proof = some (s, ρ))
    (hl : Verify.ladderOf prog s ρ = some levels)
    (hok : Verify.openingsOk (Verify.nLanes prog s) true
      (Verify.levelShapes (Verify.stackMu prog s) levels) proof.merkle = true)
    (hrun : ((do
        let x ← Verify.walkProof (Verify.readerOps (m := Id) H) prog s input
          (Verify.levelShapes (Verify.stackMu prog s) levels)
        Reader.finish
        return x : Verify.Walk Id (Verify.Wire × List (List (List K)))).run'
          ⟨Id.run seed, proof.stream, proof.merkle⟩).run = Except.ok (w, rows)) :
    Verify.verifyFrom (m := Id) H seed prog input proof =
      Verify.algebra prog s input (Verify.levelShapes (Verify.stackMu prog s) levels) w rows := by
  change Verify.verifyFrom (m := Id) H (pure (Id.run seed)) prog input proof = _
  simp only [Verify.verifyFrom, hsetup, hl, hok, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    pure_bind]
  rw [hrun]
  rfl

/-- The rows the openings read of a level-0 word whose lanes past the committed ones vanish are
the rows of the transcript. -/
private theorem rowsOf_eq {I : M3Instance} {sh : Whir.Shape} {κ n : ℕ} {L : Ladder sh κ}
    {t : (listBindingSpec I sh κ L).FullTranscript} (hn : n ≤ 2 ^ sh.ℓ)
    (hz : ∀ p (u : Fin (2 ^ sh.ℓ)), n ≤ u.val → ((level0Word t).row p)[u] = 0) :
    ladderRows L (fun p ↦ leafImage (2 ^ sh.ℓ) (level0Rows n (level0Word t))[p]) (ladderPart t) =
      rowsOf I L t :=
  congrArg (ladderRows L · _) (funext fun p ↦ leafImage_level0Rows hn (hz p))

/-- **Completeness of the honest prover from a start**, modulo the phases' agreement: for every
byte hash `H`, start and fuel, a proof `proveFrom` returns for a witness satisfying leanISA's
constraint statement on the public input, at the deployed Flock specification, is accepted by the
executable verifier at `H` from the same start, if, at the announcement and rate the proof
carries, the executable verifier's algebra accepts every transcript the compiled oracle
protocol's verifier accepts (`PhasesAgree`). -/
theorem baseProver_complete_of_agree_from (H : List UInt8 → Digest) (seed : Id FsState)
    (fuel : ℕ) {prog : Program} {input : PublicInput}
    {κ : ℕ} {w : EnsembleWitness (leanIsaEnsemble prog κ)}
    {ρ : ℕ} {proof : Proof PrunedMerklePaths} (hsat : SatisfiedBy prog input w)
    (hagree : ∀ (s : Sizes) (hs : s.Admissible prog) (hρ : validRate ρ),
      PhasesAgree prog s hs ρ hρ input)
    (hp : proveFrom (m := Id) H seed fuel Blake2sFlock.blake2sFlockSpec prog input w ρ =
      some proof) :
    Verify.verifyFrom (m := Id) H seed prog input proof = true := by
  unfold proveFrom at hp
  rcases hws : Sizes.ofWitness w with _ | s
  · rw [hws] at hp
    cases hp
  rw [hws] at hp
  dsimp only at hp
  split_ifs at hp with hsρ
  obtain ⟨hs, hρ⟩ := hsρ
  replace hp : runProofFrom (m := Id) seed (writeProof (m := Id) H (proveOps H fuel)
      Blake2sFlock.blake2sFlockSpec prog s hs ρ hρ input
      (stackOf Blake2sFlock.blake2sFlockSpec prog s w)) = some proof := hp
  obtain ⟨s₃, hrun, rfl⟩ := runs_of_runProofFrom hp
  obtain ⟨u₁, s₁, hann, h₁⟩ := proveSem.bind_inv hrun
  obtain ⟨r, s₂, hrw, hho⟩ := proveSem.bind_inv h₁
  have hr := (proveSem.satisfies (Prover.runWith_eq_runWithChallenges _ _ _ _) hrw).trans
    (Prover.runWithChallenges_eq_of_run_eq _ (compiledProver_run (Verify.leanVm prog s)
      (leanIsa_conditions Blake2sFlock.blake2sFlockSpec prog s)
      (leanIsaChain_height Blake2sFlock.blake2sFlockSpec prog s hs ρ hρ)
      (leanIsaChain prog s hs ρ hρ).ladder
      ((leanIsaChain prog s hs ρ hρ).ladder.headPar (leanIsaChain prog s hs ρ hρ).pars).hb
      (input, fun i ↦ i.elim0) (stackOf Blake2sFlock.blake2sFlockSpec prog s w)) _)
  obtain ⟨so, hacc⟩ := Prover.accepts_of_run (pure ()) (fun t ↦ isEmptyElim t)
    (listBinding_deployed_perfectCompleteness Blake2sFlock.blake2sFlockSpec prog s hs ρ hρ (pure ())
      (fun t ↦ isEmptyElim t)) (R := (compiledDef prog s hs ρ hρ).red.toReduction)
    (stmt := (input, fun i ↦ i.elim0)) hr (m3Holds_stackOf hsat hws)
  have halg := hagree s hs hρ _ so hacc
  obtain ⟨levels, hl, hsh, hok, hℓ⟩ := leanIsaChain_walk hs hρ
  obtain ⟨wire, cs, pss, hR, herase, hroot, hcm, hpos, hmk, ⟨ys, hys⟩, hLR⟩ :=
    walkChain_reads H fuel input (leanIsaChain prog s hs ρ hρ).ladder (Verify.nLanes prog s)
      (fun x hx ↦ (hok x hx).2) hann (Prover.runWith_runsAs proveSem _ _ _ _ hrw)
      (by simpa only [wireOf, pubWireOf] using pubLength_of_algebra halg)
  obtain ⟨-, hfs₃, hst₃, hm₃⟩ := runs_hintOpenings hho
  have hn : Verify.nLanes prog s ≤ 2 ^ (leanIsaChain prog s hs ρ hρ).sh.ℓ := hℓ ▸ nLanes_le prog s
  have hw₀ := length_level0Rows hn (level0Word (@Prod.fst _ _ r))
  have hO := reads_openings H (Verify.nLanes prog s) (leanIsaChain prog s hs ρ hρ).ladder true _ hn
    hw₀ (fun x hx ↦ (hok x hx).1) hLR (w := s₂.2) (w' := s₃.2) hfs₃ hst₃
    (by rw [hm₃, hcm, hpos]; simp [Verify.leafWordsOf])
  rw [show ∀ sh, Verify.leafWordsOf true sh = 2 ^ sh.fold from fun _ ↦ rfl,
    rowsOf_eq (t := @Prod.fst _ _ r) hn fun p u hu ↦ by
      rw [hr, level0Word_honest]
      exact kwordOf_stackOf_high hs hρ w p u hu] at hO
  have hstream : s₃.2.proof.stream.take 8 = announcement s ρ := by
    obtain ⟨hs₁, -⟩ := stream_addScalars H _ (runs_lift.mp hann).2
    change s₃.2.stream.toList.take 8 = _
    rw [hst₃, hys, hs₁]
    simp [announcement]
  have hokm : Verify.openingsOk (Verify.nLanes prog s) true
      (Verify.levelShapes (Verify.stackMu prog s) levels) s₃.2.proof.merkle = true := by
    rw [hsh]
    change Verify.openingsOk _ true _ s₃.2.merkle.toList = true
    rw [hm₃, hmk, hcm, hpos]
    simpa [Verify.leafWordsOf] using openingsOk_openings H (Verify.nLanes prog s)
      (leanIsaChain prog s hs ρ hρ).ladder true _ hw₀ hLR
  rw [verifyFrom_of_run (setup?_of_announce (decide_eq_true ⟨hs, hρ⟩) hstream) hl hokm
    (by rw [hsh]; exact run_of_reads (hR.bind (Reads.bind_ret (by rw [hroot]; exact hO) rfl))),
    hsh, ← Verify.algebra_erase, herase, Verify.algebra_erase]
  exact halg

/-- **Completeness of the honest prover**, modulo the phases' agreement: for every byte hash `H`
and fuel, a proof `proveWith` returns for a witness satisfying leanISA's constraint statement on
the public input, at the deployed Flock specification, is accepted by the executable verifier at
`H`, if, at the announcement and rate the proof carries, the executable verifier's algebra accepts
every transcript the compiled oracle protocol's verifier accepts (`PhasesAgree`). -/
theorem baseProver_complete_of_agree (H : List UInt8 → Digest) (fuel : ℕ) {prog : Program}
    {input : PublicInput} {κ : ℕ} {w : EnsembleWitness (leanIsaEnsemble prog κ)} {ρ : ℕ}
    {proof : Proof PrunedMerklePaths} (hsat : SatisfiedBy prog input w)
    (hagree : ∀ (s : Sizes) (hs : s.Admissible prog) (hρ : validRate ρ),
      PhasesAgree prog s hs ρ hρ input)
    (hp : proveWith (m := Id) H fuel Blake2sFlock.blake2sFlockSpec prog input w ρ = some proof) :
    Verify.verifyWith (m := Id) H prog input proof = true :=
  baseProver_complete_of_agree_from H (FsState.seedWith (m := Id) H prog input) fuel hsat hagree
    hp

/-! ## When the prover returns a proof -/

section Total

variable (H : List UInt8 → Digest) (fuel : ℕ)

/-- A pure computation runs from every state. -/
private theorem total_pure {α : Type} (a : α) : proveSem.Total (pure a : ProveM Id α) :=
  fun s ↦ ⟨a, s, rfl⟩

/-- A bound computation runs from every state when its parts do. -/
private theorem total_bind {α β : Type} {x : ProveM Id α} {f : α → ProveM Id β}
    (hx : proveSem.Total x) (hf : ∀ a, proveSem.Total (f a)) : proveSem.Total (x >>= f) :=
  fun s ↦ let ⟨a, sm, h₁⟩ := hx s; let ⟨b, s', h₂⟩ := hf a sm; ⟨b, s', runs_bind h₁ h₂⟩

/-- A writer's step lifted to the prover runs from every state when it runs from every writer
state. -/
private theorem total_lift {α : Type} {y : WriteM Id PrunedMerklePaths α}
    (h : ∀ ws, ∃ a ws', (y.run ws).run = some (a, ws')) :
    proveSem.Total (StateT.lift y : ProveM Id α) :=
  fun s ↦ let ⟨a, ws', h⟩ := h s.2; ⟨a, (s.1, ws'), runs_lift.mpr ⟨rfl, h⟩⟩

/-- Sending scalars never fails. -/
private theorem addScalars_some : ∀ (xs : List E) (ws : WriterState PrunedMerklePaths),
    ∃ a ws', ((Writer.addScalars (m := Id) H xs).run ws).run = some (a, ws')
  | [], ws => ⟨(), ws, rfl⟩
  | x :: xs, ws => addScalars_some xs
      { ws with fs := Id.run (ws.fs.observe H x), stream := ws.stream.push x }

/-- The writer's primitives but the grind run from every state; the grind does when it never
runs out of fuel. -/
private theorem total_send (x : E) : proveSem.Total ((proveOps H fuel).send x) :=
  total_lift fun _ ↦ ⟨(), _, rfl⟩

private theorem total_sample : proveSem.Total (proveOps H fuel).sample :=
  total_lift fun _ ↦ ⟨_, _, rfl⟩

private theorem total_grind
    (hg : ∀ fs : FsState, Id.run (fs.grind H fuel queryGrindingBits) ≠ none) :
    proveSem.Total (proveOps H fuel).grind := by
  refine total_lift fun ws ↦ ?_
  rcases hq : Id.run (ws.fs.grind H fuel queryGrindingBits) with _ | ⟨nonce, fs'⟩
  · exact absurd hq (hg _)
  · refine ⟨(), { ws with fs := fs', stream := ws.stream.push nonce }, ?_⟩
    simp [Writer.grind, StateT.run_bind,
      show ws.fs.grind (m := Id) H fuel queryGrindingBits = Pure.pure (some (nonce, fs'))
        from hq]
    rfl

private theorem total_commit (depth leafWords : ℕ) (rows : Vector (List K) (2 ^ depth)) :
    proveSem.Total ((proveOps H fuel).commit depth leafWords rows) :=
  total_bind (fun s ↦ ⟨_, s, rfl⟩) fun _ ↦ total_bind (fun s ↦ ⟨(), (_, s.2), rfl⟩) fun _ ↦
    total_lift (addScalars_some H _)

private theorem total_record (ps : List ℕ) : proveSem.Total ((proveOps H fuel).record ps) :=
  fun s ↦ ⟨(), (_, s.2), rfl⟩

private theorem total_sendAll : ∀ l : List E, proveSem.Total (sendAll (proveOps H fuel) l)
  | [] => total_pure _
  | x :: xs => total_bind (total_send H fuel x) fun _ ↦ total_sendAll xs

private theorem total_samples : ∀ k, proveSem.Total (samples (proveOps H fuel) k)
  | 0 => total_pure _
  | k + 1 => total_bind (total_sample H fuel) fun _ ↦
      total_bind (total_samples k) fun _ ↦ total_pure _

private theorem total_positionsWith (depth : ℕ) : ∀ f need,
    proveSem.Total (Verify.positionsWith (proveOps H fuel).sample depth f need)
  | 0, _ => total_pure _
  | _ + 1, 0 => total_pure _
  | f + 1, _ + 1 => total_bind (total_sample H fuel) fun _ ↦
      total_bind (total_positionsWith depth f _) fun _ ↦ total_pure _

private theorem total_positions (depth t : ℕ) :
    proveSem.Total (positions (proveOps H fuel) depth t) :=
  total_bind (total_positionsWith H fuel depth t t) fun ps ↦
    total_bind (total_record H fuel ps) fun _ ↦ total_pure _

/-- Every round of a wire runs from every state. -/
private abbrev Every {n : ℕ} {pSpec : ProtocolSpec n} (c : RoundCodec (ProveM Id) pSpec) : Prop :=
  RoundCodec.Every (fun _ x ↦ proveSem.Total x) c

/-- Every round of each phase's wire runs from every state. -/
private theorem every_bus (I : M3Instance) : Every (busCodec (proveOps H fuel) I) :=
  (((RoundCodec.every_chal (total_bind (total_samples H fuel 4) fun _ ↦
      total_bind (total_sample H fuel) fun _ ↦ total_pure _)).append
    (RoundCodec.every_msg fun _ ↦ total_bind (total_send H fuel _) fun _ ↦
      total_send H fuel _)).append
    (RoundCodec.every_gkr I.μBus (fun _ ↦ total_sendAll H fuel _) (fun _ ↦ total_sendAll H fuel _)
      (fun _ ↦ total_sendAll H fuel _) (fun _ ↦ total_sendAll H fuel _)
      (total_sample H fuel))).append
    (RoundCodec.every_msg fun _ ↦ total_sendAll H fuel _)

private theorem every_table (I : M3Instance) : Every (tableCodec (proveOps H fuel) I) :=
  ((RoundCodec.every_chal (total_sample H fuel)).append
    (RoundCodec.every_rounds (fun _ ↦ total_sendAll H fuel _) (total_sample H fuel) _)).append
    (RoundCodec.every_msg fun _ ↦ total_sendAll H fuel _)

private theorem every_pub : Every (pubCodec (proveOps H fuel)) :=
  ⟨fun i h x ↦ (match i, h, x with
    | ⟨0, _⟩, h, _ => nomatch h
    | ⟨1, _⟩, _, xs => total_sendAll H fuel xs), fun i h ↦ match i, h with
    | ⟨0, _⟩, _ => total_sample H fuel
    | ⟨1, _⟩, h => nomatch h⟩

private theorem every_flockOf (k : ℕ) : Every (flockCodecOf (proveOps H fuel) k) :=
  (((((((((RoundCodec.every_chals (total_sample H fuel) (k + 1)).append
    (RoundCodec.every_msg fun _ ↦ total_sendAll H fuel _)).append
    (RoundCodec.every_chal (total_sample H fuel))).append
    (RoundCodec.every_rounds (fun _ ↦ total_sendAll H fuel _) (total_sample H fuel) 8)).append
    (RoundCodec.every_rounds (fun _ ↦ total_sendAll H fuel _) (total_sample H fuel) k)).append
    (RoundCodec.every_msg fun _ ↦ total_sendAll H fuel _)).append
    (RoundCodec.every_chal (total_sample H fuel))).append
    (RoundCodec.every_rounds (fun _ ↦ total_sendAll H fuel _) (total_sample H fuel) 8)).append
    (RoundCodec.every_msg fun _ ↦ total_sendAll H fuel _)).append
    (RoundCodec.every_chals (total_sample H fuel) 6)

private theorem every_flockOpt (I : M3Instance) :
    ∀ o, Every (flockCodecOpt (proveOps H fuel) I o)
  | none => RoundCodec.every_empty
  | some r => every_flockOf H fuel r.kBatch

/-- The openings' loop runs from every state. -/
private theorem total_forIn_openings : ∀ l : List ((Σ k, MerkleCommitment k) × List ℕ),
    proveSem.Total (forIn l PUnit.unit fun x _ ↦ match x with
        | (c, ps) => do
          StateT.lift (Writer.hintOpening (m := Id) (merkleOpen c.2 ps))
          return ForInStep.yield PUnit.unit)
  | [] => total_pure _
  | (c, ps) :: l => by
    rw [List.forIn_cons]
    exact total_bind (total_bind (total_lift fun _ ↦ ⟨(), _, rfl⟩) fun _ ↦ total_pure _)
      fun r ↦ match r with
        | .done _ => total_pure _
        | .yield _ => total_forIn_openings l

/-- The openings run when the commitments and the positions kept are as many. -/
private theorem runs_hintOpenings_of_size {s : PState}
    (h : s.1.commits.size = s.1.positions.size) :
    ∃ s', proveSem.Runs (hintOpenings (m := Id)) s () s' := by
  obtain ⟨u, s', h'⟩ := total_forIn_openings (s.1.commits.toList.zip s.1.positions.toList) s
  refine ⟨s', ?_⟩
  unfold hintOpenings
  refine runs_bind (a := s.1) (sm := s) rfl ?_
  simp only [h, ne_eq, not_true_eq_false, ↓reduceIte]
  exact runs_bind h' rfl

/-- The proof of a writer run from the start's state with an empty book. -/
private theorem runProofFrom_of_runs {seed : Id FsState} {wr : ProveM Id Unit} {s' : PState}
    (h : proveSem.Runs wr (⟨#[], #[]⟩, ⟨Id.run seed, #[], #[]⟩) () s') :
    runProofFrom (m := Id) seed wr = some s'.2.proof := by
  change runProofFrom (m := Id) (pure (Id.run seed)) wr = _
  unfold runProofFrom runWrite
  simp only [pure_bind, StateT.run'_eq, StateT.run_map, OptionT.run_map]
  rw [show ((wr.run ⟨#[], #[]⟩).run ⟨Id.run seed, #[], #[]⟩).run =
    some (((), s'.1), s'.2) from h]
  rfl

variable (hg : ∀ fs : FsState, Id.run (fs.grind H fuel queryGrindingBits) ≠ none)
include hg

/-- WHIR's levels run from every state when no grind runs out of fuel. -/
private theorem every_ladder : ∀ {sh : Whir.Shape} {κ : ℕ} (L : Ladder sh κ),
    Every (ladderCodec (proveOps H fuel) L)
  | _, _, .last sh nf =>
    (RoundCodec.every_chal (total_sample H fuel)).append <|
    (RoundCodec.every_rounds (fun _ ↦ total_sendAll H fuel _) (total_sample H fuel) _).append <|
    (RoundCodec.every_msg fun _ ↦ total_sendAll H fuel _).append <|
    (RoundCodec.every_msg fun _ ↦ total_sendAll H fuel _).append <|
    (RoundCodec.every_msg fun _ ↦ total_grind H fuel hg).append <|
    (RoundCodec.every_chal (total_positions H fuel _ _)).append <|
    (RoundCodec.every_chal (total_sample H fuel)).append <|
    RoundCodec.every_empty.append <|
    (RoundCodec.every_msg fun _ ↦ total_sendAll H fuel _).append <|
    RoundCodec.every_empty.append <|
    (RoundCodec.every_chal (total_sample H fuel)).append <|
    (RoundCodec.every_rounds (fun _ ↦ total_sendAll H fuel _) (total_sample H fuel) _).append
      RoundCodec.every_empty
  | _, _, @Ladder.cons sh sh' κ' L =>
    (RoundCodec.every_chal (total_sample H fuel)).append <|
    (RoundCodec.every_rounds (fun _ ↦ total_sendAll H fuel _) (total_sample H fuel) _).append <|
    (RoundCodec.every_msg fun _ ↦ total_sendAll H fuel _).append <|
    (RoundCodec.every_msg fun _ ↦ total_commit H fuel _ _ _).append <|
    (RoundCodec.every_chals (total_sample H fuel) _).append <|
    (RoundCodec.every_msg (total_send H fuel)).append <|
    (RoundCodec.every_msg fun _ ↦ total_sendAll H fuel _).append <|
    (RoundCodec.every_msg fun _ ↦ total_grind H fuel hg).append <|
    (RoundCodec.every_chal (total_positions H fuel _ _)).append <|
    (RoundCodec.every_chal (total_sample H fuel)).append <|
    RoundCodec.every_empty.append <|
    (RoundCodec.every_msg fun _ ↦ total_sendAll H fuel _).append <|
    RoundCodec.every_empty.append (every_ladder L)

/-- Every round of the wire of the compiled schedule runs from every state when no grind runs out
of fuel. -/
private theorem every_compiled (I : M3Instance) (n : ℕ) {sh : Whir.Shape} {κ : ℕ}
    (L : Ladder sh κ) : Every (compiledCodec (proveOps H fuel) I n L) :=
  (((((((RoundCodec.every_sendOne fun _ ↦ total_commit H fuel _ _ _).append
    (every_bus H fuel I)).append (every_table H fuel I)).append (every_pub H fuel)).append
    (every_flockOpt H fuel I I.flock)).append
    (RoundCodec.every_chal (total_sample H fuel))).append RoundCodec.every_empty).append
    (RoundCodec.every_empty.append ((RoundCodec.every_msg fun _ ↦ total_sendAll H fuel _).append
      (every_ladder H fuel hg L)))

end Total

/-- **The honest prover returns a proof** from every start when the witness gives sizes
admissible with the rate and no grind runs out of fuel, whatever the hash and the Flock
specification. -/
theorem proveFrom_ne_none (H : List UInt8 → Digest) (seed : Id FsState) (fuel : ℕ) (F : FlockSpec)
    {prog : Program} {input : PublicInput}
    {κ : ℕ} {w : EnsembleWitness (leanIsaEnsemble prog κ)} {ρ : ℕ}
    {s : Sizes} (hws : Sizes.ofWitness w = some s) (hs : s.Admissible prog) (hρ : validRate ρ)
    (hg : ∀ fs : FsState, Id.run (fs.grind H fuel queryGrindingBits) ≠ none) :
    proveFrom (m := Id) H seed fuel F prog input w ρ ≠ none := by
  unfold proveFrom
  rw [hws]
  dsimp only
  split_ifs with hsρ
  swap
  · exact absurd ⟨hs, hρ⟩ hsρ
  obtain ⟨u₁, s₁, h₁⟩ := total_lift (fun ws ↦ addScalars_some H (announcement s ρ) ws)
    ((⟨#[], #[]⟩, ⟨Id.run seed, #[], #[]⟩) : PState)
  obtain ⟨r, s₂, h₂⟩ := Prover.runWith_total proveSem _
    (compiledProver (leanIsaInstance F prog s) (leanIsa_conditions F prog s)
      (leanIsaChain_height F prog s hs ρ hρ) (leanIsaChain prog s hs ρ hρ).ladder
      ((leanIsaChain prog s hs ρ hρ).ladder.headPar (leanIsaChain prog s hs ρ hρ).pars).hb)
    (fun _ _ ↦ rfl) (fun h₁ h₂ ↦ runs_bind h₁ h₂)
    (every_compiled H fuel hg _ (Verify.nLanes prog s) (leanIsaChain prog s hs ρ hρ).ladder)
    (input, fun i ↦ i.elim0) (stackOf F prog s w) s₁
  obtain ⟨-, -, -, hok, -⟩ := leanIsaChain_walk hs hρ
  have hsz := book_compiled H fuel _ _ _ (fun x hx ↦ (hok x hx).2)
    (Prover.runWith_runsAs proveSem _ _ _ _ h₂) (by rw [(runs_lift.mp h₁).1]; rfl)
  obtain ⟨s₃, h₃⟩ := runs_hintOpenings_of_size hsz
  have hrun : proveSem.Runs (writeProof (m := Id) H (proveOps H fuel) F prog s hs ρ hρ input
      (stackOf F prog s w)) _ () s₃ := runs_bind h₁ (runs_bind h₂ h₃)
  rw [runProofFrom_of_runs hrun]
  exact Option.some_ne_none _

/-- **The honest prover returns a proof** when the witness gives sizes admissible with the rate
and no grind runs out of fuel, whatever the hash and the Flock specification. -/
theorem proveWith_ne_none (H : List UInt8 → Digest) (fuel : ℕ) (F : FlockSpec) {prog : Program}
    {input : PublicInput} {κ : ℕ} {w : EnsembleWitness (leanIsaEnsemble prog κ)} {ρ : ℕ}
    {s : Sizes} (hws : Sizes.ofWitness w = some s) (hs : s.Admissible prog) (hρ : validRate ρ)
    (hg : ∀ fs : FsState, Id.run (fs.grind H fuel queryGrindingBits) ≠ none) :
    proveWith (m := Id) H fuel F prog input w ρ ≠ none :=
  proveFrom_ne_none H (FsState.seedWith (m := Id) H prog input) fuel F hws hs hρ hg

/-- **When the honest prover returns no proof** from a start: the witness gives no sizes, or its
sizes are not admissible, or the rate is not valid, or the grind runs out of fuel at some chain
state. The openings' check that the commitments and the positions kept are as many never
fails. -/
theorem proveFrom_eq_none (H : List UInt8 → Digest) (seed : Id FsState) (fuel : ℕ) (F : FlockSpec)
    {prog : Program} {input : PublicInput}
    {κ : ℕ} {w : EnsembleWitness (leanIsaEnsemble prog κ)} {ρ : ℕ}
    (h : proveFrom (m := Id) H seed fuel F prog input w ρ = none) :
    Sizes.ofWitness w = none ∨ ∃ s, Sizes.ofWitness w = some s ∧
      (¬ s.Admissible prog ∨ ¬ validRate ρ ∨
        ∃ fs : FsState, Id.run (fs.grind H fuel queryGrindingBits) = none) := by
  rcases hws : Sizes.ofWitness w with _ | s
  · exact Or.inl rfl
  refine Or.inr ⟨s, rfl, ?_⟩
  by_contra hc
  simp only [not_or, not_not, not_exists] at hc
  obtain ⟨hs, hρ, hg⟩ := hc
  exact proveFrom_ne_none H seed fuel F hws hs hρ hg h

/-- **When the honest prover returns no proof**: the witness gives no sizes, or its sizes are
not admissible, or the rate is not valid, or the grind runs out of fuel at some chain state. The
openings' check that the commitments and the positions kept are as many never fails. -/
theorem proveWith_eq_none (H : List UInt8 → Digest) (fuel : ℕ) (F : FlockSpec) {prog : Program}
    {input : PublicInput} {κ : ℕ} {w : EnsembleWitness (leanIsaEnsemble prog κ)} {ρ : ℕ}
    (h : proveWith (m := Id) H fuel F prog input w ρ = none) :
    Sizes.ofWitness w = none ∨ ∃ s, Sizes.ofWitness w = some s ∧
      (¬ s.Admissible prog ∨ ¬ validRate ρ ∨
        ∃ fs : FsState, Id.run (fs.grind H fuel queryGrindingBits) = none) :=
  proveFrom_eq_none H (FsState.seedWith (m := Id) H prog input) fuel F h

end Prove

end
end LeanerVM.Protocol
