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

`baseProver_complete`: for every byte hash `H`, a proof the honest prover returns for a witness
satisfying leanISA's constraint statement (`SatisfiedBy`) is accepted by the executable verifier
at `H`, modulo one hypothesis, `PhasesAgree`: on the transcripts the compiled oracle protocol's
verifier accepts, the executable verifier's algebra accepts the transcript's wire (`wireOf`) and
rows (`rowsOf`). That hypothesis is the completeness half of the phase-by-phase agreement of the
two verifiers, which the soundness direction needs too.

The proof:

1. the prover's run against the wire of the compiled schedule steps through the wire on its
   transcript (`Prover.runWith_runsAs`), and that transcript is the run of the compiled protocol's
   honest prover on its own challenges (`Prover.runWith_eq_runWithChallenges`,
   `compiledProver_run`);
2. by the compiled protocol's perfect completeness, its verifier accepts that transcript on every
   challenge vector (`Prover.accepts_of_perfectCompleteness`), so `PhasesAgree` gives that the
   algebra accepts the transcript's wire and rows;
3. the chain walk reads the prover's stream back as the transcript's wire, but for the roots,
   the nonces and the positions' reduction (`walkChain_reads`), which the algebra does not read
   (`Verify.algebra_erase`); the openings are read back as the transcript's rows
   (`reads_openings`). The proof stores only the committed lanes of level 0's rows and the
   verifier fills the rest with zeros; the honest word's lanes past them vanish
   (`level0Word_honest`, `kwordOf_stackOf_high`: the stack is zero past its last block), so the
   rows read are the word's;
4. the announcement passes the setup, the ladder is the deployed chain's, the openings have their
   shapes and the stream and the openings are consumed.

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

/-- **The phases agree, on the accepted transcripts** (the hypothesis of `baseProver_complete`):
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
      (input, fun i ↦ i.elim0) tr).run) = some so →
    Verify.algebra prog s input (leanIsaChain prog s hs ρ hρ).ladder.shapes
      (wireOf (Verify.leanVm prog s) (leanIsaChain prog s hs ρ hρ).ladder tr)
      (rowsOf (Verify.leanVm prog s) (leanIsaChain prog s hs ρ hρ).ladder tr) = true

/-- An accepted wire carries one public value per sent line. -/
theorem pubLength_of_algebra {prog : Program} {s : Sizes} {input : PublicInput}
    {shs : List Verify.LevelShape} {w : Verify.Wire} {rows : List (List (List K))}
    (h : Verify.algebra prog s input shs w rows = true) :
    w.pub.values.length =
      PublicInput.sentCount (Verify.leanVm prog s) ((Verify.leanVm prog s).publicLines input) := by
  unfold Verify.algebra at h
  dsimp only at h
  rcases hb : Verify.leanVmBus prog s input w.bus with _ | b
  · rw [hb] at h
    cases h
  rw [hb] at h
  dsimp only at h
  rcases ht : Verify.tableStep (Verify.leanVm prog s) b w.table with _ | t
  · rw [ht] at h
    cases h
  rw [ht] at h
  dsimp only at h
  rcases hp : Verify.pubStep (Verify.leanVm prog s) t w.pub with _ | p
  · rw [hp] at h
    cases h
  have hb₁ : b.1 = input := by
    simp only [Verify.leanVmBus, Option.bind_eq_bind, Option.bind_eq_some_iff] at hb
    obtain ⟨_, -, _, -, hb⟩ := hb
    cases hb
    rfl
  have ht₁ : t.1 = b.1 := by
    simp only [Verify.tableStep, Option.bind_eq_bind, Option.bind_eq_some_iff] at ht
    obtain ⟨_, -, _, -, _, -, ht⟩ := ht
    split_ifs at ht
    cases ht
    rfl
  simp only [Verify.pubStep] at hp
  split_ifs at hp with hacc
  simp only [PublicInput.accepts, Bool.and_eq_true, decide_eq_true_eq] at hacc
  rw [hacc.1, ht₁, hb₁]

/-- The public values a transcript's wire carries are its public-input message. -/
theorem wireOf_pub_values (I : M3Instance) {sh : Whir.Shape} {κ : ℕ} (L : Ladder sh κ)
    (t : (listBindingSpec I sh κ L).FullTranscript) :
    (wireOf I L t).pub.values = pubMessage t := rfl

/-- The run on given challenges of two components in sequence begins with the first's. -/
theorem runWithChallenges_def_append_fst {StmtIn ι₁ ι₂ ι₃ : Type} {O₁ : ι₁ → Type}
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
theorem level0Word_honest (prog : Program) (s : Sizes) (hs : s.Admissible prog) (ρ : ℕ)
    (hρ : validRate ρ) (ch : (listBindingSpec (Verify.leanVm prog s)
      (leanIsaChain prog s hs ρ hρ).sh (leanIsaChain prog s hs ρ hρ).κ
      (leanIsaChain prog s hs ρ hρ).ladder).Challenges)
    (stmt : PublicInput × ∀ i, NoOracle i) (q : Column (Verify.leanVm prog s).μ) :
    level0Word (Prover.runWithChallenges (compiledDef prog s hs ρ hρ).red.prover ch stmt q).1 =
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
theorem kwordOf_row_eq_zero {ℓ κ R t : ℕ} (q : CompPoly.CMlPolynomialEval K (κ + ℓ))
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
theorem kwordOf_stackOf_high {prog : Program} {s : Sizes} (hs : s.Admissible prog) {ρ : ℕ}
    (hρ : validRate ρ) (w : EnsembleWitness (leanIsaEnsemble prog))
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
theorem leafImage_level0Rows {ℓ b t n : ℕ} (hn : n ≤ 2 ^ ℓ) {x : KWord ℓ b t} {p : Fin (2 ^ b)}
    (hz : ∀ u : Fin (2 ^ ℓ), n ≤ u.val → (x.row p)[u] = 0) :
    leafImage (2 ^ ℓ) (level0Rows n x)[p] = (x.row p).toList.reverse := by
  have hdrop : (x.row p).toList.drop n = List.replicate (2 ^ ℓ - n) 0 := by
    refine List.eq_replicate_iff.mpr ⟨by simp, fun a ha ↦ ?_⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
    simp only [List.getElem_drop, Vector.getElem_toList]
    exact hz ⟨n + i, by simp at hi; omega⟩ (Nat.le_add_right n i)
  conv_rhs => rw [← List.take_append_drop n (x.row p).toList]
  simp [level0Rows, leafImage, hdrop, hn, List.reverse_append]

/-- A prover's proof is the proof of a run of its writer from the statement's seed and an empty
book. -/
theorem runs_of_runProof {prog : Program} {input : PublicInput} {wr : ProveM Id Unit}
    {proof : Proof PrunedMerklePaths} (h : runProof (m := Id) prog input wr = some proof) :
    ∃ s', proveSem.Runs wr (⟨#[], #[]⟩, ⟨FsState.seed prog input, #[], #[]⟩) () s' ∧
      s'.2.proof = proof := by
  unfold runProof runWrite at h
  simp only [StateT.run'_eq, StateT.run_map, OptionT.run_map] at h
  rcases hr : ((wr.run ⟨#[], #[]⟩).run ⟨FsState.seed prog input, #[], #[]⟩).run with
    _ | ⟨⟨u, bk⟩, ws⟩
  · rw [hr] at h
    cases h
  · rw [hr] at h
    cases h
    exact ⟨(bk, ws), hr, rfl⟩

/-- The stored level-0 rows hold the committed lanes, at most a leaf's. -/
theorem length_level0Rows {ℓ b t n : ℕ} (hn : n ≤ 2 ^ ℓ) (x : KWord ℓ b t) :
    ∀ row ∈ (level0Rows n x).toList, row.length = n := by
  intro row hrow
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hrow
  simp [level0Rows, hn]

/-- The verifier on a proof that passes the setup, whose ladder exists and whose openings have
their shapes, and on which the walk and the openings read a wire and rows and consume the proof:
the algebra on them. -/
theorem verifyWith_of_run {H : List UInt8 → Digest} {prog : Program} {input : PublicInput}
    {proof : Proof PrunedMerklePaths} {s : Sizes} {ρ : ℕ} {levels : List Whir.Level}
    {w : Verify.Wire} {rows : List (List (List K))}
    (hsetup : Verify.setup? prog proof = some (s, ρ))
    (hl : Verify.ladderOf prog s ρ = some levels)
    (hok : Verify.openingsOk (Verify.nLanes prog s) true
      (Verify.levelShapes (Verify.stackMu prog s) levels) proof.merkle = true)
    (hrun : ((do
        let x ← Verify.walkProof (Verify.readerOps (m := Id) H) prog s input
          (Verify.levelShapes (Verify.stackMu prog s) levels)
        Reader.finish
        return x : Verify.Walk Id (Verify.Wire × List (List (List K)))).run'
          ⟨FsState.seed prog input, proof.stream, proof.merkle⟩).run = Except.ok (w, rows)) :
    Verify.verifyWith (m := Id) H prog input proof =
      Verify.algebra prog s input (Verify.levelShapes (Verify.stackMu prog s) levels) w rows := by
  simp only [Verify.verifyWith, hsetup, hl, hok, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [hrun]
  rfl

/-- **Completeness of the honest prover**, modulo the phases' agreement: for every byte hash `H`
and fuel, a proof `proveWith` returns for a witness satisfying leanISA's constraint statement on
the public input, at the deployed Flock specification, is accepted by the executable verifier at
`H`, if, at the announcement and rate the proof carries, the executable verifier's algebra accepts
every transcript the compiled oracle protocol's verifier accepts (`PhasesAgree`). -/
theorem baseProver_complete (H : List UInt8 → Digest) (fuel : ℕ) {prog : Program}
    {input : PublicInput} {w : EnsembleWitness (leanIsaEnsemble prog)} {ρ : ℕ}
    {proof : Proof PrunedMerklePaths} (hsat : SatisfiedBy prog input w)
    (hagree : ∀ (s : Sizes) (hs : s.Admissible prog) (hρ : validRate ρ),
      PhasesAgree prog s hs ρ hρ input)
    (hp : proveWith (m := Id) H fuel Blake2sFlock.blake2sFlockSpec prog input w ρ = some proof) :
    Verify.verifyWith (m := Id) H prog input proof = true := by
  unfold proveWith at hp
  rcases hws : Sizes.ofWitness w with _ | s
  · rw [hws] at hp
    cases hp
  rw [hws] at hp
  dsimp only at hp
  split_ifs at hp with hsρ
  obtain ⟨hs, hρ⟩ := hsρ
  replace hp : runProof (m := Id) prog input (writeProof (m := Id) H (proveOps H fuel)
      Blake2sFlock.blake2sFlockSpec prog s hs ρ hρ input
      (stackOf Blake2sFlock.blake2sFlockSpec prog s w)) = some proof := hp
  obtain ⟨s₃, hrun, rfl⟩ := runs_of_runProof hp
  obtain ⟨u₁, s₁, hann, h₁⟩ := proveSem.bind_inv hrun
  obtain ⟨r, s₂, hrw, hho⟩ := proveSem.bind_inv h₁
  have hras := Prover.runWith_runsAs proveSem _ _ _ _ hrw
  have hrr := proveSem.satisfies (Prover.runWith_eq_runWithChallenges _ _ _ _) hrw
  have hhon := Prover.runWithChallenges_eq_of_run_eq _
    (P' := (compiledDef prog s hs ρ hρ).red.prover)
    (compiledProver_run (Verify.leanVm prog s)
      (leanIsa_conditions Blake2sFlock.blake2sFlockSpec prog s)
      (leanIsaChain_height Blake2sFlock.blake2sFlockSpec prog s hs ρ hρ)
      (leanIsaChain prog s hs ρ hρ).ladder
      ((leanIsaChain prog s hs ρ hρ).ladder.headPar (leanIsaChain prog s hs ρ hρ).pars).hb
      (input, fun i ↦ i.elim0) (stackOf Blake2sFlock.blake2sFlockSpec prog s w)) r.1.challenges
  have hin : ((input, fun i ↦ i.elim0), stackOf Blake2sFlock.blake2sFlockSpec prog s w) ∈
      M3Rel (Verify.leanVm prog s) := m3Holds_stackOf hsat hws
  obtain ⟨so, hacc, -, -⟩ := Prover.accepts_of_perfectCompleteness (pure ())
    (fun t ↦ isEmptyElim t) _ (listBinding_deployed_perfectCompleteness
      Blake2sFlock.blake2sFlockSpec prog s hs ρ hρ (pure ()) (fun t ↦ isEmptyElim t)) hin
    r.1.challenges
  have hr1 : (Prover.runWithChallenges (compiledDef prog s hs ρ hρ).red.toReduction.prover
      r.1.challenges (input, fun i ↦ i.elim0)
      (stackOf Blake2sFlock.blake2sFlockSpec prog s w)).1 = r.1 := by
    change (Prover.runWithChallenges (compiledDef prog s hs ρ hρ).red.prover
      r.1.challenges (input, fun i ↦ i.elim0)
      (stackOf Blake2sFlock.blake2sFlockSpec prog s w)).1 = r.1
    rw [← hhon, ← hrr]
  have halg := hagree s hs hρ r.1 so (by rw [← hr1]; exact hacc)
  obtain ⟨levels, hl, hsh, hok, hℓ⟩ := leanIsaChain_walk hs hρ
  obtain ⟨wire, cs, pss, hR, herase, hroot, hcm, hpos, hmk, ⟨ys, hys⟩, hLR⟩ :=
    walkChain_reads H fuel input (leanIsaChain prog s hs ρ hρ).ladder (Verify.nLanes prog s)
      (fun x hx ↦ (hok x hx).2) hann hras (wireOf_pub_values _ _ r.1 ▸ pubLength_of_algebra halg)
  obtain ⟨-, hfs₃, hst₃, hm₃⟩ := runs_hintOpenings hho
  have hn : Verify.nLanes prog s ≤ 2 ^ (leanIsaChain prog s hs ρ hρ).sh.ℓ :=
    hℓ ▸ nLanes_le prog s
  have hw₀ := length_level0Rows hn (level0Word r.1)
  have hx : level0Word r.1 = kwordOf (leanIsaChain prog s hs ρ hρ).sh.ℓ
      (leanIsaChain prog s hs ρ hρ).κ (leanIsaChain prog s hs ρ hρ).sh.R
      (leanIsaChain prog s hs ρ hρ).sh.t
      ((leanIsaChain_height Blake2sFlock.blake2sFlockSpec prog s hs ρ hρ).symm ▸
        (stackOf Blake2sFlock.blake2sFlockSpec prog s w).values) := by
    rw [← hr1]
    exact level0Word_honest prog s hs ρ hρ _ _ _
  have hO := reads_openings H (Verify.nLanes prog s) (leanIsaChain prog s hs ρ hρ).ladder true
    (level0Rows (Verify.nLanes prog s) (level0Word r.1)) hn hw₀ (fun x hx ↦ (hok x hx).1) hLR
    (w := s₂.2) (w' := s₃.2) hfs₃ hst₃ (by rw [hm₃, hcm, hpos]; simp [Verify.leafWordsOf])
  have hlw : Verify.leafWordsOf true ⟨(leanIsaChain prog s hs ρ hρ).sh.ℓ,
      (leanIsaChain prog s hs ρ hρ).κ, (leanIsaChain prog s hs ρ hρ).sh.R,
      (leanIsaChain prog s hs ρ hρ).sh.t, false⟩ = 2 ^ (leanIsaChain prog s hs ρ hρ).sh.ℓ := by
    simp only [Verify.leafWordsOf, ite_true]
  rw [hlw] at hO
  have hleaf : (fun p ↦ leafImage (2 ^ (leanIsaChain prog s hs ρ hρ).sh.ℓ)
      (level0Rows (Verify.nLanes prog s) (level0Word r.1))[p]) =
      fun p ↦ ((level0Word r.1).row p).toList.reverse := by
    funext p
    exact leafImage_level0Rows (ℓ := (leanIsaChain prog s hs ρ hρ).sh.ℓ) (x := level0Word r.1)
      (p := p) hn fun u hu ↦ by
        rw [hx]
        exact kwordOf_stackOf_high hs hρ w p u hu
  rw [hleaf] at hO
  have hW : Reads (Verify.walkProof (Verify.readerOps (m := Id) H) prog s input
      (leanIsaChain prog s hs ρ hρ).ladder.shapes) ⟨FsState.seed prog input, #[], #[]⟩ s₃.2
      (wire, rowsOf (Verify.leanVm prog s) (leanIsaChain prog s hs ρ hρ).ladder r.1) := by
    unfold Verify.walkProof
    refine hR.bind (Reads.bind_ret ?_ rfl)
    rw [hroot]
    exact hO
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
  rw [verifyWith_of_run (setup?_of_announce (decide_eq_true ⟨hs, hρ⟩) hstream) hl hokm
    (by rw [hsh]; exact run_of_reads hW), hsh, ← Verify.algebra_erase, herase,
    Verify.algebra_erase]
  exact halg

end Prove

end
end LeanerVM.Protocol
