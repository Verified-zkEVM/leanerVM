/-
  LeanVM.E2E.Reduction.XmssBound

  The hash queries of leanXMSS's honest key generation and signer: the tree nodes, the one-time
  signatures' randomizer search and the authentication paths.
-/

module

public import LeanVM.E2E.Reduction.VerifyBound

/-!
# leanXMSS's key generation and signer are query-bounded

A node at level `l` of a leanXMSS tree makes `xmssNodeBound l = 205 · 2^l - 1` hash queries: each
of its `2^l` one-time keys `29` seed derivations, `58 · 3` chain steps and a leaf hash, and
`2^l - 1` inner nodes (`treeNode_isTotalQueryBound`). So

* key generation (`Seeded.keygenFromSeed`: the seed hash, the parameter, the top tree) makes at
  most `xmssKeygenBound = 2 + xmssNodeBound 16 = 13,434,881` (lean_xmss's exact count
  `XmssSecurity.Bridge.keygenQueries`, `keygenFromSeed_isTotalQueryBound`);
* a signature (`Seeded.sign`: per layer the randomizer, at most `2^32` digest trials, one
  opening and the path, and the bottom tree's root in between) makes at most
  `xmssSignBound = 2^33 + 40,304,605` (`sign_isTotalQueryBound`).

These are the `cxk` and `cxs` of `aggregate_no_forgery`.
-/

namespace LeanVM.E2E

open OracleSpec OracleComp LeanXmss LeanXmss.Concrete

@[expose] public section

/-- One oracle call is one query. -/
theorem xOracleHash_isTotalQueryBound (x : HashInput) :
    IsTotalQueryBound (oracleHash x : OracleComp LeanXmss.HashSpec HashOutput) 1 := by
  change IsTotalQueryBound ((liftM (LeanXmss.HashSpec.query x) : OracleComp LeanXmss.HashSpec _) >>=
    fun o ↦ pure o) 1
  exact isTotalQueryBound_query_bind_iff.mpr ⟨Nat.one_pos, fun _ ↦ trivial⟩

/-- **A sequence of computations, the `i`-th with at most `b i` queries,** makes at most their
sum. -/
theorem xSequenceFin_isTotalQueryBound_sum {α : Type} :
    ∀ {n : ℕ} (c : Fin n → OracleComp LeanXmss.HashSpec α) (b : Fin n → ℕ),
      (∀ i, IsTotalQueryBound (c i) (b i)) →
      IsTotalQueryBound (LeanXmss.Concrete.sequenceFin c) (∑ i, b i)
  | 0, _, _, _ => trivial
  | n + 1, c, b, h => by
    simp only [LeanXmss.Concrete.sequenceFin]
    have := isTotalQueryBound_bind (n₁ := b 0) (n₂ := (∑ i : Fin n, b i.succ) + 0) (h 0) fun hd ↦
      isTotalQueryBound_bind (ob := fun tl ↦ (pure (fun i ↦ Fin.cases hd tl i) :
        OracleComp LeanXmss.HashSpec (Fin (n + 1) → α)))
        (xSequenceFin_isTotalQueryBound_sum (fun i ↦ c i.succ) (fun i ↦ b i.succ)
          fun i ↦ h i.succ) fun _ ↦ trivial
    rwa [Fin.sum_univ_succ, ← Nat.add_zero (b 0 + _), Nat.add_assoc]

/-- A one-time key's seed derivations: `29` queries. -/
theorem otsSecrets_isTotalQueryBound (p : PublicParameter) (lay : Layer) (key : KeyIndex)
    (seed : MasterSeed) :
    IsTotalQueryBound (Seeded.otsSecrets p lay key seed :
      OracleComp LeanXmss.HashSpec (ChainIndex → Digest)) 29 := by
  unfold Seeded.otsSecrets
  have h := isTotalQueryBound_sequenceFin 1 (fun pair : ChainPair ↦
    (deriveOutput p (.ots lay key pair) seed : OracleComp LeanXmss.HashSpec HashOutput))
    fun _ ↦ xOracleHash_isTotalQueryBound _
  exact isTotalQueryBound_bind (n₂ := 0) h fun _ ↦ trivial

/-- The chain walks of a one-time key, each at most `3` steps: `58 · 3` queries. -/
theorem chainWalks_isTotalQueryBound (p : PublicParameter) (lay : Layer) (key : KeyIndex)
    (steps : ChainIndex → ℕ) (hsteps : ∀ i, steps i ≤ chainLength - 1)
    (secrets : ChainIndex → Digest) :
    IsTotalQueryBound (sequenceFin fun chainIdx ↦ chainWalk p lay key chainIdx 0 (steps chainIdx)
      (secrets chainIdx) : OracleComp LeanXmss.HashSpec (ChainIndex → Digest)) (numChains * 3) :=
  isTotalQueryBound_sequenceFin 3 _ fun i ↦
    (chainWalk_isTotalQueryBound _ _ _ _ _ _ _).mono (hsteps i)

/-- The hash queries of a leanXMSS tree node at `level`. -/
def xmssNodeBound (level : ℕ) : ℕ := 205 * 2 ^ level - 1

/-- **A tree node at `level` makes at most `xmssNodeBound level` queries.** -/
theorem treeNode_isTotalQueryBound (p : PublicParameter) (lay : Layer) (seed : MasterSeed) :
    ∀ (level node : ℕ), IsTotalQueryBound (Seeded.treeNode p lay seed level node :
      OracleComp LeanXmss.HashSpec Digest) (xmssNodeBound level)
  | 0, node => by
    simp only [Seeded.treeNode, Seeded.oneTimePublicKey, bind_assoc]
    refine (isTotalQueryBound_bind (otsSecrets_isTotalQueryBound p lay _ seed) fun secrets ↦
      isTotalQueryBound_bind (chainWalks_isTotalQueryBound p lay _ (fun _ ↦ chainLength - 1)
        (fun _ ↦ le_rfl) secrets) fun _ ↦ tweakableHash_isTotalQueryBound _ _ _).mono ?_
    simp [xmssNodeBound, numChains]
  | level + 1, node => by
    simp only [Seeded.treeNode]
    refine (isTotalQueryBound_bind (treeNode_isTotalQueryBound p lay seed level (2 * node))
      fun _ ↦ isTotalQueryBound_bind (treeNode_isTotalQueryBound p lay seed level (2 * node + 1))
        fun _ ↦ tweakableHash_isTotalQueryBound _ _ _).mono ?_
    simp only [xmssNodeBound, pow_succ]
    have : 1 ≤ 2 ^ level := Nat.one_le_two_pow
    omega

/-- **leanXMSS's key generation makes at most `xmssKeygenBound` hash queries.** -/
def xmssKeygenBound : ℕ := 2 + xmssNodeBound layerHeight

theorem xmssKeygenBound_eq : xmssKeygenBound = 13434881 := by decide

theorem keygenFromSeed_isTotalQueryBound (seed : MasterSeed) :
    IsTotalQueryBound (Seeded.keygenFromSeed seed) xmssKeygenBound := by
  have hd : ∀ s, IsTotalQueryBound (deriveKey 0 .parameter s : OracleComp LeanXmss.HashSpec Digest)
      1 := fun s ↦ by
    unfold deriveKey
    exact isTotalQueryBound_bind (n₂ := 0) (xOracleHash_isTotalQueryBound _) fun _ ↦
      isQueryBound_pure _ _ _ _
  unfold Seeded.keygenFromSeed
  refine (isTotalQueryBound_bind (xOracleHash_isTotalQueryBound _) fun s ↦
    isTotalQueryBound_bind (hd s) fun _ ↦
      isTotalQueryBound_bind (n₂ := 0) (treeNode_isTotalQueryBound _ _ _ _ _)
        fun _ ↦ isQueryBound_pure _ _ _ _).mono ?_
  unfold xmssKeygenBound
  omega

/-- The randomizer trials: one digest per trial, then one opening of `29 + 58 · 3` queries. -/
theorem otsSignFrom_isTotalQueryBound (p : PublicParameter) (lay : Layer) (key : KeyIndex)
    (seed : MasterSeed) (msg : HashInput) (base : Randomness) :
    ∀ (attempts trial : ℕ), IsTotalQueryBound (Seeded.otsSignFrom p lay key seed msg base attempts
      trial : OracleComp LeanXmss.HashSpec _) (attempts + 203)
  | 0, _ => trivial
  | attempts + 1, trial => by
    simp only [Seeded.otsSignFrom]
    refine (isTotalQueryBound_bind (n₂ := attempts + 203) (tweakableHash_isTotalQueryBound _ _ _)
      fun d ↦ ?_).mono (by omega)
    split
    · refine (isTotalQueryBound_bind (otsSecrets_isTotalQueryBound _ _ _ _) fun secrets ↦
        isTotalQueryBound_bind (n₂ := 0) (chainWalks_isTotalQueryBound _ _ _ _
          (fun i ↦ Nat.le_sub_one_of_lt (Fin.isLt _)) secrets) fun _ ↦
            isQueryBound_pure _ _ _ _).mono ?_
      simp only [numChains]
      omega
    · exact otsSignFrom_isTotalQueryBound p lay key seed msg base attempts (trial + 1)

/-- An authentication path: the sibling node at every level below the layer's height. -/
theorem treePath_isTotalQueryBound (p : PublicParameter) (lay : Layer) (seed : MasterSeed)
    (key : KeyIndex) :
    IsTotalQueryBound (Seeded.treePath p lay seed key : OracleComp LeanXmss.HashSpec _)
      (∑ level : Fin layerHeight, xmssNodeBound level) :=
  xSequenceFin_isTotalQueryBound_sum _ _ fun _ ↦ treeNode_isTotalQueryBound _ _ _ _ _

/-- The hash queries of one layer's signature: the randomizer, `2^32` trials, the opening and the
path. -/
def xmssLayerBound : ℕ :=
  1 + ((randomizerAttemptLimit + 203) + ((∑ level : Fin layerHeight, xmssNodeBound level) + 0))

theorem signLayer_isTotalQueryBound (sk : Seeded.SecretKey) (lay : Layer) (key : KeyIndex)
    (msg : HashInput) :
    IsTotalQueryBound (Seeded.signLayer sk lay key msg : OracleComp LeanXmss.HashSpec _)
      xmssLayerBound := by
  simp only [Seeded.signLayer, Seeded.otsSign, deriveRandomizer, bind_assoc, pure_bind]
  refine isTotalQueryBound_bind (xOracleHash_isTotalQueryBound _) fun _ ↦
    isTotalQueryBound_bind (otsSignFrom_isTotalQueryBound _ _ _ _ _ _ _ _) fun o ↦ ?_
  rcases o with _ | ⟨r, v⟩
  · exact isQueryBound_pure _ _ _ _
  · exact isTotalQueryBound_bind (treePath_isTotalQueryBound _ _ _ _) fun _ ↦
      isQueryBound_pure _ _ _ _

/-- **leanXMSS's signer makes at most `xmssSignBound` hash queries**: two layers' signatures and
the bottom tree's root. -/
def xmssSignBound : ℕ := xmssLayerBound + (xmssNodeBound layerHeight + xmssLayerBound)

theorem xmssSignBound_eq : xmssSignBound = 2 ^ 33 + 40304605 := by decide

theorem sign_isTotalQueryBound (sk : Seeded.SecretKey) (i : LeafIndex) (msg : Message) :
    IsTotalQueryBound (Seeded.sign sk i msg : OracleComp LeanXmss.HashSpec _) xmssSignBound := by
  unfold xmssSignBound
  simp only [Seeded.sign]
  -- the bottom tree's height as a variable: a goal with a concrete tree node would be reduced
  generalize layerHeight = L
  refine isTotalQueryBound_bind (signLayer_isTotalQueryBound _ _ _ _) fun o ↦ ?_
  rcases o with _ | bottom
  · exact isQueryBound_pure _ _ _ _
  · refine (isTotalQueryBound_bind (treeNode_isTotalQueryBound _ _ _ _ _) fun _ ↦
      isTotalQueryBound_bind (n₂ := 0) (signLayer_isTotalQueryBound _ _ _ _) fun o' ↦ ?_).mono
        (by omega)
    rcases o' with _ | top <;> exact isQueryBound_pure _ _ _ _

end
end LeanVM.E2E
