import Sphincs.Layered
import Statement.LeanSphincs

/-!
# The statement's leanSPHINCS is the layered presentation

`Statement/LeanSphincs.lean` writes leanSPHINCS with its one tree: a signature carries the WOTS+C
counter, chain values and path directly, and no hash function takes a layer or a tree. The proofs
of this project are about `SphincsLayered` (`Sphincs/Layered.lean`), the same scheme written as a
hypertree of one layer, as the statement wrote it until `1e8e4463`. This file proves the two the
same scheme and moves the end theorem across.

* **The bijection.** `signatureEquiv : SphincsLayered.Signature ≃ Sphincs.Signature` takes the one
  layer's fields out of `layers` (and the forest's openings through `coordOpeningEquiv`, the same
  fields), and `forgeryEquiv` the forgeries with it.
* **The algorithms.** Key generation is the same computation (`keygenFromSeed_eq`), the signer's
  signature is the layered signer's through the bijection (`sign_eq`), and the verifier accepts
  exactly what the layered verifier accepts through it (`verify_eq`). Every hash input is the same
  bytes: neither the layer nor the tree is addressed (`hashDomainFields`, `tweak.rs`), and the
  layered leaf index `leafIndexAt index lay` is `index` (`leafIndexAt_eq`). The two presentations'
  definitions are distinct constants over types equal by unfolding, so the proofs first write the
  layered algorithms as the statement's (`verify_layered`, `sign_layered`, in the layered types),
  align the recursions (`signDigestLoop_eq`, `otsSignFrom_eq`, `spineNode_eq`: no unfolding meets
  their `2^32` attempts) and then compare by unfolding.
* **The games.** A scheme whose signer and verifier are another's through maps of the answers and
  of the forgeries has the same SUF-CMA game in the random-permutation model, adversary by
  adversary (`rpmGame_eq`: the adversary against the second, its signing answers read through the
  map, is one against the first), so `RpmSecure` passes from the first to the second
  (`rpmSecure_of_map`) at the same bound and the same budget. Both ways round,
  `requestedSecurityRpm_iff`: the statement's end statement is the layered one.
-/

open OracleComp OracleSpec ENNReal Common Common.SufCma

namespace Sphincs.OneLayer

/-! ## A SUF-CMA game through maps of the answers and the forgeries -/

section Transport

variable {D Seed PK SK Req Resp₁ Resp₂ F₁ F₂ : Type} [SampleableType D] (e : KDigest ≃ D)

/-- A signing log, every answer read through `φ`. -/
def mapLog (φ : Resp₁ → Resp₂) (log : QueryLog (Req →ₒ Resp₁)) : QueryLog (Req →ₒ Resp₂) :=
  log.map fun entry ↦ ⟨entry.1, φ entry.2⟩

/-- An adversary's oracles against a scheme answering `Resp₂`, from those of one answering `Resp₁`:
the permutation's queries forwarded, the signing oracle's answers read through `φ`. -/
def mapAnswers (φ : Resp₁ → Resp₂) :
    QueryImpl (KSpec + (Req →ₒ Resp₂)) (OracleComp (KSpec + (Req →ₒ Resp₁)))
  | .inl t => liftM ((KSpec + (Req →ₒ Resp₁)).query (.inl t))
  | .inr r => φ <$> liftM ((KSpec + (Req →ₒ Resp₁)).query (.inr r))

/-- The game's oracles: the permutation's queries lifted, the signing oracle logging. -/
abbrev gameImpl {Resp F : Type} (S : Scheme D Seed PK SK Req Resp F) (sk : SK) :=
  QueryImpl.ofLift KSpec (WriterT (QueryLog (Req →ₒ Resp)) (OracleComp KSpec)) +
    signingOracleK e S sk

omit [SampleableType D] in
/-- **The adversary's run, through the map**: run against the second scheme's oracles, an
adversary's run is its run against the first's with the signing answers read through `φ`, the
log read through `φ`. -/
theorem run_gameImpl (S₁ : Scheme D Seed PK SK Req Resp₁ F₁) (S₂ : Scheme D Seed PK SK Req Resp₂ F₂)
    (φ : Resp₁ → Resp₂) (hsign : ∀ sk r, S₂.sign sk r = φ <$> S₁.sign sk r) (sk : SK) {α : Type}
    (oa : OracleComp (KSpec + (Req →ₒ Resp₂)) α) :
    (simulateQ (gameImpl e S₂ sk) oa).run =
      (fun z ↦ (z.1, mapLog φ z.2)) <$>
        (simulateQ (gameImpl e S₁ sk) (simulateQ (mapAnswers φ) oa)).run := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp [mapLog]
  | query_bind t k ih =>
    rcases t with t | r
    · have h₂ : (gameImpl e S₂ sk (.inl t)).run =
          (·, ∅) <$> (liftM (KSpec.query t) : OracleComp KSpec _) := rfl
      have h₁ : (simulateQ (gameImpl e S₁ sk) (mapAnswers φ (.inl t))).run =
          (·, ∅) <$> (liftM (KSpec.query t) : OracleComp KSpec _) := by
        simp only [mapAnswers, simulateQ_spec_query]
        rfl
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, WriterT.run_bind', h₂, h₁, ih, bind_map_left, map_bind,
        Functor.map_map]
      refine bind_congr fun u ↦ ?_
      congr 1
    · have h₂ : (gameImpl e S₂ sk (.inr r)).run = (fun u ↦ (u, [⟨r, u⟩])) <$>
          simulateQ (hashK e) (S₂.sign sk r) := by
        simp [gameImpl, signingOracleK]
      have h₁ : (simulateQ (gameImpl e S₁ sk) (mapAnswers φ (.inr r))).run =
          (fun u ↦ (φ u, [⟨r, u⟩])) <$> simulateQ (hashK e) (S₁.sign sk r) := by
        have hs : (gameImpl e S₁ sk (.inr r)).run =
            (fun u ↦ (u, [⟨r, u⟩])) <$> simulateQ (hashK e) (S₁.sign sk r) := by
          simp [gameImpl, signingOracleK]
        simp only [mapAnswers, simulateQ_map, simulateQ_spec_query, WriterT.run_map']
        rw [hs, Functor.map_map]
        rfl
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, WriterT.run_bind', h₂, h₁, hsign, simulateQ_map, ih,
        bind_map_left, map_bind, Functor.map_map]
      refine bind_congr fun u ↦ ?_
      congr 1

/-- The adversary against the first scheme that runs `main` against the second: its signing
answers read through `φ`, its forgery through `ψ`. -/
def mapAdversary (φ : Resp₁ → Resp₂) (ψ : F₂ → F₁) (main : PK → OracleComp (KSpec + (Req →ₒ Resp₂)) F₂)
    (pk : PK) : OracleComp (KSpec + (Req →ₒ Resp₁)) F₁ :=
  ψ <$> simulateQ (mapAnswers φ) (main pk)

omit [SampleableType D] in
/-- **The same game**: when the second scheme samples and generates keys as the first, signs as the
first through `φ`, verifies a forgery as the first verifies it through `ψ`, and wins on a log read
through `φ` as the first wins on the log with the forgery through `ψ`, the second scheme's game
against `main` is the first's against `mapAdversary φ ψ main`. -/
theorem rpmGame_eq (S₁ : Scheme D Seed PK SK Req Resp₁ F₁) (S₂ : Scheme D Seed PK SK Req Resp₂ F₂)
    (φ : Resp₁ → Resp₂) (ψ : F₂ → F₁) (hsample : S₂.sample = S₁.sample)
    (hkeygen : S₂.keygen = S₁.keygen) (hsign : ∀ sk r, S₂.sign sk r = φ <$> S₁.sign sk r)
    (hverify : ∀ pk f, S₂.verify pk f = S₁.verify pk (ψ f))
    (hwin : ∀ log f, S₂.win (mapLog φ log) f = S₁.win log (ψ f))
    (main : PK → OracleComp (KSpec + (Req →ₒ Resp₂)) F₂) :
    rpmGame e S₂ main = rpmGame e S₁ (mapAdversary φ ψ main) := by
  unfold rpmGame mapAdversary
  rw [hsample, hkeygen]
  refine bind_congr fun seed ↦ bind_congr fun keys ↦ ?_
  rcases keys with ⟨pk, sk⟩
  dsimp only
  have h := run_gameImpl e S₁ S₂ φ hsign sk (main pk)
  simp only [gameImpl] at h
  rw [h, simulateQ_map, WriterT.run_map', bind_map_left, bind_map_left]
  refine bind_congr fun z ↦ ?_
  simp only [Prod.map, id, hverify, hwin]

omit [SampleableType D] in
/-- **`RpmSecure` through the maps**: under the hypotheses of `rpmGame_eq`, the second scheme has
the first's bits of security. -/
theorem rpmSecure_of_map (S₁ : Scheme D Seed PK SK Req Resp₁ F₁)
    (S₂ : Scheme D Seed PK SK Req Resp₂ F₂) (φ : Resp₁ → Resp₂) (ψ : F₂ → F₁)
    (hsample : S₂.sample = S₁.sample) (hkeygen : S₂.keygen = S₁.keygen)
    (hsign : ∀ sk r, S₂.sign sk r = φ <$> S₁.sign sk r)
    (hverify : ∀ pk f, S₂.verify pk f = S₁.verify pk (ψ f))
    (hwin : ∀ log f, S₂.win (mapLog φ log) f = S₁.win log (ψ f)) {bits : ℕ}
    (h : RpmSecure e S₁ bits) : RpmSecure e S₂ bits := by
  intro Q hQ hcap main hbound
  have hgame := rpmGame_eq e S₁ S₂ φ ψ hsample hkeygen hsign hverify hwin main
  rw [hgame] at hbound
  unfold rpmExperiment
  rw [hgame]
  exact h Q hQ hcap _ hbound

theorem mapLog_mapLog {Resp₃ : Type} (φ : Resp₁ → Resp₂) (φ' : Resp₂ → Resp₃)
    (log : QueryLog (Req →ₒ Resp₁)) :
    mapLog φ' (mapLog φ log) = mapLog (φ' ∘ φ) log := by
  simp [mapLog, Function.comp_def]

theorem mapLog_id (log : QueryLog (Req →ₒ Resp₁)) : mapLog id log = log := by
  simp [mapLog]

omit [SampleableType D] in
/-- **`RpmSecure` through bijections, both ways**: under the hypotheses of `rpmGame_eq` with `φ`
and `ψ` bijections, the two schemes have the same bits of security. -/
theorem rpmSecure_iff_of_equiv (S₁ : Scheme D Seed PK SK Req Resp₁ F₁)
    (S₂ : Scheme D Seed PK SK Req Resp₂ F₂) (φ : Resp₁ ≃ Resp₂) (ψ : F₂ ≃ F₁)
    (hsample : S₂.sample = S₁.sample) (hkeygen : S₂.keygen = S₁.keygen)
    (hsign : ∀ sk r, S₂.sign sk r = φ <$> S₁.sign sk r)
    (hverify : ∀ pk f, S₂.verify pk f = S₁.verify pk (ψ f))
    (hwin : ∀ log f, S₂.win (mapLog φ log) f = S₁.win log (ψ f)) (bits : ℕ) :
    RpmSecure e S₂ bits ↔ RpmSecure e S₁ bits := by
  refine ⟨rpmSecure_of_map e S₂ S₁ φ.symm ψ.symm hsample.symm hkeygen.symm ?_ ?_ ?_,
    rpmSecure_of_map e S₁ S₂ φ ψ hsample hkeygen hsign hverify hwin⟩
  · intro sk r
    rw [hsign, Functor.map_map]
    simp
  · intro pk f
    rw [hverify, Equiv.apply_symm_apply]
  · intro log f
    have h := hwin (mapLog φ.symm log) (ψ.symm f)
    rw [mapLog_mapLog, Equiv.apply_symm_apply, Equiv.self_comp_symm, mapLog_id] at h
    exact h.symm

end Transport

/-! ## The bijection of the signatures -/

/-- A sub-tree's opening, in the layered presentation. -/
def subOpeningEquiv : SphincsLayered.SubOpening ≃ SubOpening where
  toFun o := ⟨o.values, o.path⟩
  invFun o := ⟨o.values, o.path⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- A coordinate's opening, in the layered presentation. -/
def coordOpeningEquiv : SphincsLayered.CoordOpening ≃ CoordOpening where
  toFun o := ⟨fun j ↦ subOpeningEquiv (o.sub j), o.top⟩
  invFun o := ⟨fun j ↦ subOpeningEquiv.symm (o.sub j), o.top⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The bijection**: a layered signature is the randomizer, the forest opening and its one
layer's counter, chain values and path. -/
def signatureEquiv : SphincsLayered.Signature ≃ Signature where
  toFun σ := ⟨σ.randomness, fun c ↦ coordOpeningEquiv (σ.forest c),
    (σ.layers SphincsLayered.topLayer).counter, (σ.layers SphincsLayered.topLayer).chainValues,
    (σ.layers SphincsLayered.topLayer).path⟩
  invFun σ := ⟨σ.randomness, fun c ↦ coordOpeningEquiv.symm (σ.forest c),
    fun _ ↦ ⟨σ.counter, σ.chainValues, σ.path⟩⟩
  left_inv σ := by
    rcases σ with ⟨randomness, forest, layers⟩
    have hl : (fun lay : SphincsLayered.Layer ↦ (⟨(layers SphincsLayered.topLayer).counter,
        (layers SphincsLayered.topLayer).chainValues, (layers SphincsLayered.topLayer).path⟩ :
          SphincsLayered.LayerSignature lay)) = layers := by
      funext lay
      obtain rfl : lay = SphincsLayered.topLayer := Fin.ext (Nat.lt_one_iff.mp lay.isLt)
      rfl
    exact congrArg (SphincsLayered.Signature.mk randomness forest) hl
  right_inv _ := rfl

/-- The forgeries, with the signatures. -/
def forgeryEquiv : SphincsLayered.Forgery ≃ Forgery where
  toFun f := ⟨f.message, signatureEquiv f.signature⟩
  invFun f := ⟨f.message, signatureEquiv.symm f.signature⟩
  left_inv f := by cases f; simp
  right_inv f := by cases f; simp

/-- The parameters in the layered presentation. -/
abbrev layeredParams [P : Params] : SphincsLayered.Params :=
  ⟨P.subtreeHeight, P.signatureLimit, P.subtreeHeight_le⟩

attribute [local instance] layeredParams

/-! ## The algorithms, the same hashes -/

section Algorithms

variable {m : Type → Type} [Monad m] [LawfulMonad m] [HasQuery HashSpec m]

omit [HasQuery HashSpec m] in
/-- `sequenceFin` through a map of its entries. -/
theorem sequenceFin_map {α β : Type} (g : α → β) :
    ∀ (n : Nat) (f : Fin n → m α),
      Concrete.sequenceFin (fun i ↦ g <$> f i) = (fun v ↦ g ∘ v) <$> Concrete.sequenceFin f
  | 0, f => by
    simp only [Concrete.sequenceFin, map_pure]
    congr 1
    funext i
    exact i.elim0
  | n + 1, f => by
    simp only [Concrete.sequenceFin, map_bind, bind_map_left, map_pure]
    refine bind_congr fun head ↦ ?_
    rw [sequenceFin_map g n (fun i : Fin n ↦ f i.succ), bind_map_left]
    refine bind_congr fun tail ↦ ?_
    congr 1
    funext i
    refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp

omit [HasQuery HashSpec m] in
/-- A `sequenceFin` whose entries are another's through `g`, then a continuation. -/
theorem bind_sequenceFin_map {α β γ : Type} (g : α → β) {n : Nat} (f : Fin n → m α)
    (f' : Fin n → m β) (k : (Fin n → β) → m γ) (k' : (Fin n → α) → m γ)
    (hf : ∀ i, f' i = g <$> f i) (hk : ∀ v, k (g ∘ v) = k' v) :
    Concrete.sequenceFin f' >>= k = Concrete.sequenceFin f >>= k' := by
  rw [show f' = fun i ↦ g <$> f i from funext hf, sequenceFin_map, bind_map_left]
  exact bind_congr hk

omit [HasQuery HashSpec m] in
/-- A computation that is another's through `g`, then a continuation. -/
theorem bind_map_congr {α β γ : Type} (g : α → β) (x : m α) (y : m β) (hy : y = g <$> x)
    (k : β → m γ) (k' : α → m γ) (hk : ∀ a, k (g a) = k' a) : y >>= k = x >>= k' := by
  rw [hy, bind_map_left]
  exact bind_congr hk

/-- The opening of a coordinate, through the bijection. -/
theorem coordOpen_eq (parameter : PublicParameter) (index : Index) (c : Coord)
    (digest : MessageDigest) (seed : MasterSeed) :
    Seeded.coordOpen (m := m) parameter index c (Concrete.digestMarks digest c) seed =
      coordOpeningEquiv <$> SphincsLayered.Seeded.coordOpen parameter index c
        (SphincsLayered.Concrete.digestMarks digest c) seed := by
  refine Eq.trans ?_ (map_bind _ _ _).symm
  refine bind_sequenceFin_map subOpeningEquiv _ _ _ _ (fun j ↦ ?_) (fun v ↦ ?_)
  · simp only [map_bind, map_pure]
    rfl
  · simp only [map_bind, map_pure]
    rfl

/-- The forest opening, through the bijection. -/
theorem forestOpen_eq (parameter : PublicParameter) (index : Index) (digest : MessageDigest)
    (seed : MasterSeed) :
    Seeded.forestOpen (m := m) parameter index (Concrete.digestMarks digest) seed =
      (fun opening ↦ coordOpeningEquiv ∘ opening) <$> SphincsLayered.Seeded.forestOpen parameter
        index (SphincsLayered.Concrete.digestMarks digest) seed :=
  (congrArg Concrete.sequenceFin
    (funext fun c ↦ coordOpen_eq parameter index c digest seed)).trans (sequenceFin_map _ _ _)

/-- An index as a layered leaf. -/
def toLeaf (index : SphincsLayered.Index) : SphincsLayered.LeafIndex := ⟨index.val, index.isLt⟩

/-- A layered leaf as an index. -/
def ofLeaf (leaf : SphincsLayered.LeafIndex) : Index := ⟨leaf.val, leaf.isLt⟩

/-- A layered forest key as a forest key. -/
def ofKey (key : SphincsLayered.ForestKey) : ForestKey := key

/-- The layered leaf of an index, at the one layer: the index (`h = 26`, no index bits below). -/
theorem leafIndexAt_eq (index : SphincsLayered.Index) (lay : SphincsLayered.Layer) :
    SphincsLayered.Concrete.leafIndexAt index lay = toLeaf index := by
  obtain rfl : lay = SphincsLayered.topLayer := Fin.ext (Nat.lt_one_iff.mp lay.isLt)
  have hbelow : SphincsLayered.heightBelow SphincsLayered.topLayer = 0 := by decide
  ext
  simp only [SphincsLayered.Concrete.leafIndexAt, toLeaf, hbelow, pow_zero, Nat.div_one]
  exact Nat.mod_eq_of_lt index.isLt

omit [LawfulMonad m] in
/-- The one-time signer at a layered leaf. -/
theorem otsSignFrom_eq (parameter : PublicParameter) (lay : SphincsLayered.Layer)
    (tree : SphincsLayered.TreeIndex) (leaf : SphincsLayered.LeafIndex) (seed : MasterSeed)
    (message : SphincsLayered.ForestKey) :
    ∀ attempts counter,
      SphincsLayered.Seeded.otsSignFrom (m := m) parameter lay tree leaf seed message attempts
          counter =
        Seeded.otsSignFrom parameter (ofLeaf leaf) seed (ofKey message) attempts counter := by
  intro attempts
  induction attempts with
  | zero => intro counter; rfl
  | succ attempts ih =>
    intro counter
    rw [SphincsLayered.Seeded.otsSignFrom.eq_2, Seeded.otsSignFrom.eq_2]
    refine bind_congr fun encoding ↦ ?_
    rcases encoding with _ | encoding
    · exact ih (counter + 1)
    · rfl

omit [LawfulMonad m] in
/-- A node of the spine, the same hashes. -/
theorem spineNode_eq [Params] (parameter : PublicParameter) (lay : SphincsLayered.Layer)
    (tree : SphincsLayered.TreeIndex) (seed : MasterSeed) :
    ∀ steps, SphincsLayered.Seeded.spineNode (m := m) parameter lay tree seed steps =
      Seeded.spineNode parameter seed steps
  | 0 => rfl
  | steps + 1 => by
    rw [SphincsLayered.Seeded.spineNode, Seeded.spineNode, spineNode_eq parameter lay tree seed steps]
    rfl

omit [LawfulMonad m] in
/-- The layered verifier's loop over its one layer. -/
theorem verifyLayers_one (parameter : PublicParameter) (index : SphincsLayered.Index)
    (signature : SphincsLayered.Signature) (key : SphincsLayered.ForestKey) :
    SphincsLayered.Concrete.verifyLayers (m := m) parameter index signature
        SphincsLayered.numLayers key = (do
      let some value ← SphincsLayered.Concrete.otsLeaf parameter SphincsLayered.topLayer 0
          (SphincsLayered.Concrete.leafIndexAt index SphincsLayered.topLayer) key
          (signature.layers SphincsLayered.topLayer).counter
          (signature.layers SphincsLayered.topLayer).chainValues | return none
      let root ← SphincsLayered.Concrete.treeFold parameter SphincsLayered.topLayer 0
        (SphincsLayered.Concrete.leafIndexAt index SphincsLayered.topLayer)
        (SphincsLayered.Concrete.signaturePath signature SphincsLayered.topLayer)
        (SphincsLayered.layerHeight SphincsLayered.topLayer) value
      return some root) :=
  rfl

/-- The layered verifier, written as the statement's: no loop over the layers. -/
theorem verify_layered (publicKey : PublicKey) (message : Message)
    (signature : SphincsLayered.Signature) :
    SphincsLayered.Concrete.verify (m := m) publicKey message signature = (do
      let digest ← SphincsLayered.Concrete.messageDigest publicKey.parameter publicKey.root message
        signature.randomness
      let index := SphincsLayered.Concrete.digestIndex digest
      let key ← SphincsLayered.Concrete.forestRecover publicKey.parameter index
        (SphincsLayered.Concrete.digestMarks digest) signature.forest
      let some leaf ← SphincsLayered.Concrete.otsLeaf publicKey.parameter SphincsLayered.topLayer 0
          (toLeaf index) key (signature.layers SphincsLayered.topLayer).counter
          (signature.layers SphincsLayered.topLayer).chainValues | return false
      let root ← SphincsLayered.Concrete.treeFold publicKey.parameter SphincsLayered.topLayer 0
        (toLeaf index) (SphincsLayered.Concrete.signaturePath signature SphincsLayered.topLayer)
        (SphincsLayered.layerHeight SphincsLayered.topLayer) leaf
      return decide (root = publicKey.root)) := by
  rw [SphincsLayered.Concrete.verify.eq_def]
  simp only [verifyLayers_one, leafIndexAt_eq, bind_assoc]
  refine bind_congr fun digest ↦ bind_congr fun key ↦ bind_congr fun leaf ↦ ?_
  rcases leaf with _ | leaf <;> simp

/-- **The verifier, through the bijection.** -/
theorem verify_eq (publicKey : PublicKey) (message : Message) (signature : Signature) :
    Concrete.verify (m := m) publicKey message signature =
      SphincsLayered.Concrete.verify publicKey message (signatureEquiv.symm signature) := by
  rw [verify_layered, Concrete.verify.eq_def]
  rfl

variable [Params]

omit [LawfulMonad m] in
/-- The grinding loop, the same hashes. -/
theorem signDigestLoop_eq (secretKey : LeanXmss.Seeded.SecretKey) (message : Message) :
    ∀ attempts randomness,
      Seeded.signDigestLoop (m := m) secretKey message attempts randomness =
        SphincsLayered.Seeded.signDigestLoop secretKey message attempts randomness
  | 0, _ => rfl
  | attempts + 1, randomness => by
    rw [Seeded.signDigestLoop, SphincsLayered.Seeded.signDigestLoop]
    refine bind_congr fun found ↦ ?_
    rcases found with _ | index
    · exact signDigestLoop_eq secretKey message attempts (randomness + 1)
    · rfl

/-- The layered signer, written as the statement's: no loop over the layers, the encoding
counter's search the statement's. -/
theorem sign_layered (secretKey : LeanXmss.Seeded.SecretKey) (message : Message) :
    SphincsLayered.Seeded.sign (m := m) secretKey message = (do
      let base ← SphincsLayered.deriveRandomizer secretKey.parameter secretKey.seed message
      let some (randomness, _) ← SphincsLayered.Seeded.signDigestLoop secretKey message
          SphincsLayered.digestAttemptLimit base | return none
      let digest ← SphincsLayered.Concrete.messageDigest secretKey.parameter secretKey.root message
        randomness
      let index := SphincsLayered.Concrete.digestIndex digest
      let opening ← SphincsLayered.Seeded.forestOpen secretKey.parameter index
        (SphincsLayered.Concrete.digestMarks digest) secretKey.seed
      let key ← SphincsLayered.Seeded.forestKey secretKey.parameter index secretKey.seed
      let some (counter, values) ← Seeded.otsSignFrom secretKey.parameter (ofLeaf (toLeaf index))
          secretKey.seed (ofKey key) SphincsLayered.encodingAttemptLimit 0 | return none
      let path ← SphincsLayered.Seeded.treePath secretKey.parameter SphincsLayered.topLayer 0
        secretKey.seed (toLeaf index)
      return some ⟨randomness, opening,
        Fin.cases (⟨counter, values, path⟩ : SphincsLayered.LayerSignature SphincsLayered.topLayer)
          (fun i ↦ Fin.elim0 i)⟩) := by
  rw [SphincsLayered.Seeded.sign]
  simp only [SphincsLayered.Concrete.sequenceLayers, SphincsLayered.Seeded.signLayer,
    SphincsLayered.Seeded.layerMessage, SphincsLayered.Seeded.otsSign, leafIndexAt_eq,
    otsSignFrom_eq, bind_assoc]
  refine bind_congr fun base ↦ bind_congr fun found ↦ ?_
  rcases found with _ | ⟨randomness, _⟩
  · rfl
  · refine bind_congr fun digest ↦ bind_congr fun opening ↦ bind_congr fun key ↦ ?_
    refine (bind_assoc _ _ _).trans (bind_congr fun signed ↦ ?_)
    rcases signed with _ | ⟨counter, values⟩
    · simp
    · simp
      rfl

/-- **The signer, through the bijection.** -/
theorem sign_eq (secretKey : LeanXmss.Seeded.SecretKey) (message : Message) :
    Seeded.sign (m := m) secretKey message =
      Option.map signatureEquiv <$> SphincsLayered.Seeded.sign secretKey message := by
  rw [sign_layered, Seeded.sign]
  simp only [signDigestLoop_eq, Seeded.otsSign, map_bind]
  refine bind_congr fun base ↦ bind_congr fun found ↦ ?_
  rcases found with _ | ⟨randomness, _⟩
  · simp
  · simp only [map_bind]
    refine bind_congr fun digest ↦ ?_
    refine bind_map_congr (fun opening ↦ coordOpeningEquiv ∘ opening) _ _
      (forestOpen_eq _ _ _ _) _ _ fun opening ↦ ?_
    refine bind_congr fun key ↦ bind_congr fun signed ↦ ?_
    rcases signed with _ | ⟨counter, values⟩
    · simp
    · simp only [map_bind, map_pure]
      refine bind_congr fun path ↦ ?_
      rfl

/-- **Key generation, the same computation.** -/
theorem keygenFromSeed_eq (seed : MasterSeed) :
    Seeded.keygenFromSeed seed = SphincsLayered.Seeded.keygenFromSeed seed := by
  simp only [Seeded.keygenFromSeed, SphincsLayered.Seeded.keygenFromSeed,
    Seeded.keygenFromMaster, SphincsLayered.Seeded.keygenFromMaster, Seeded.treeRoot,
    SphincsLayered.Seeded.treeRoot]
  refine bind_congr fun master ↦ bind_congr fun parameter ↦ ?_
  have h := spineNode_eq (m := OracleComp HashSpec) parameter SphincsLayered.topLayer
    SphincsLayered.Concrete.rootTree master
    (SphincsLayered.totalHeight - SphincsLayered.subtreeHeight)
  simp only [h]
  rfl

/-- The winning condition, through the bijection. -/
theorem win_eq (log : QueryLog SphincsLayered.SigningSpec) (forgery : Forgery) :
    Rpm.scheme.win (mapLog (Option.map signatureEquiv) log) forgery =
      SphincsLayered.Rpm.scheme.win log (forgeryEquiv.symm forgery) := by
  simp only [Rpm.scheme, SphincsLayered.Rpm.scheme, decide_eq_decide]
  refine and_congr ?_ (not_congr ?_)
  · exact Iff.of_eq (congrArg (· ≤ signatureLimit)
      (by simp [mapLog] : (mapLog (Option.map signatureEquiv) log).length = log.length))
  · unfold SigningTranscript.Contains SphincsLayered.SigningTranscript.Contains mapLog
    constructor
    · rintro ⟨entry', hmem, hmsg, hsig⟩
      obtain ⟨entry, hentry, rfl⟩ := List.mem_map.mp hmem
      refine ⟨entry, hentry, hmsg, ?_⟩
      obtain ⟨s, hs, hseq⟩ := Option.map_eq_some_iff.mp hsig
      rw [hs]
      show some s = some (signatureEquiv.symm forgery.signature)
      rw [← hseq, Equiv.symm_apply_apply]
    · rintro ⟨entry, hentry, hmsg, hsig⟩
      refine ⟨⟨entry.1, Option.map signatureEquiv entry.2⟩,
        List.mem_map.mpr ⟨entry, hentry, rfl⟩, hmsg, ?_⟩
      show Option.map signatureEquiv entry.2 = some forgery.signature
      rw [hsig]
      simp [forgeryEquiv]

/-- **The same game**: the statement's scheme has the layered scheme's bits of security, and
conversely, through the bijection. -/
theorem rpmSecure_iff (bits : ℕ) :
    RpmSecure digestBitVec Rpm.scheme bits ↔
      RpmSecure digestBitVec SphincsLayered.Rpm.scheme bits :=
  rpmSecure_iff_of_equiv _ SphincsLayered.Rpm.scheme Rpm.scheme
    (Equiv.optionCongr signatureEquiv) forgeryEquiv.symm rfl
    (funext keygenFromSeed_eq) (fun sk message ↦ sign_eq sk message)
    (fun pk forgery ↦ verify_eq pk forgery.message forgery.signature) win_eq bits

end Algorithms

/-- **The end statement is the layered one**: at every lifetime, the statement's leanSPHINCS has
`RpmSecure` at 127 bits exactly when the layered presentation has. -/
theorem requestedSecurityRpm_iff :
    Lifetimes.RequestedSecurityRpm ↔ SphincsLayered.Lifetimes.RequestedSecurityRpm := by
  simp only [Lifetimes.RequestedSecurityRpm, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  exact and_congr (@rpmSecure_iff Lifetimes.full 127) <| and_congr (@rpmSecure_iff Lifetimes.pruned20 127) <|
    and_congr (@rpmSecure_iff Lifetimes.pruned14 127) <|
    and_congr (@rpmSecure_iff Lifetimes.pruned13 127) <|
    and_congr (@rpmSecure_iff Lifetimes.pruned12 127) <|
    and_congr (@rpmSecure_iff Lifetimes.pruned10 127) (@rpmSecure_iff Lifetimes.pruned8 127)

end Sphincs.OneLayer
