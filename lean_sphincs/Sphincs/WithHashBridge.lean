import Sphincs.WithHash
import Common.WithHashBridge

/-!
# The statement's leanSPHINCS is the hash-query form, the hash over `π`

The statement's leanSPHINCS hashes with Keccak-256 over the permutation it is given; the proofs'
form queries a hash (`Sphincs.WithHash`). With the model's permutation `π`, each algorithm is the
hash-query one with every query answered by Keccak-256 over `π`
(`Common.SufCma.schemeHashOverPermutation`), one simulation lemma per algorithm; so the statement's
scheme is `Rpm.schemeWithHash` so answered (`Sphincs.Rpm.scheme_eq`), and its end statement
follows from the hash-query one (`Sphincs.Lifetimes.leanSphincsStronglyUnforgeable_of_withHash`).
-/

open OracleComp OracleSpec
open Common Common.SufCma
open LeanXmss (simulateQ_sequenceFin simulateQ_walkChain simulateQ_foldPath simulateQ_buildTree)
open LeanXmss.Concrete (simulateQ_thWithHash simulateQ_thPairWithHash simulateQ_taggedSeedWithHash)

local notation "σ" => schemeHashOverPermutation

namespace Sphincs

namespace Concrete

variable (parameter : PublicParameter) (leaf index : Index) (chainIdx : ChainIndex) (digit : Digit)
  (value : Digest) (start steps : ℕ) (endpoints : ChainIndex → Digest) (message : ForestKey)
  (counter : Counter) (values : ChainIndex → Digest) (path : ℕ → Digest) (c : Coord) (s : SuperIdx)
  (j : SubIdx) (a : ChildIdx) (i : FChain) (deficit : FPos) (ends : FChain → Digest)
  (word : Codeword) (fvalues : FChain → Digest) (level node : ℕ) (payload : HashInput)
  (subPath : Fin subHeight → Digest) (tops : SubIdx → Digest × Digest)
  (topPath : Fin topHeight → Digest) (mark : CoordMark) (opening : CoordOpening)
  (marks : Coord → CoordMark) (openings : Coord → CoordOpening) (msg : Message)
  (randomness : Randomness) (domain : HashDomain)

theorem simulateQ_tweakableHashWithHash :
    simulateQ σ (tweakableHashWithHash (m := OracleComp HashSpec) parameter domain payload) =
      tweakableHash queryPermutation parameter domain payload :=
  simulateQ_thWithHash _ _ _

theorem simulateQ_chainWalkWithHash :
    simulateQ σ (chainWalkWithHash (m := OracleComp HashSpec) parameter leaf chainIdx start steps
      value) = chainWalk queryPermutation parameter leaf chainIdx start steps value := by
  simp only [chainWalkWithHash, chainWalk, simulateQ_walkChain, simulateQ_tweakableHashWithHash]

theorem simulateQ_recoverChainWithHash :
    simulateQ σ (recoverChainWithHash (m := OracleComp HashSpec) parameter leaf chainIdx digit
      value) = recoverChain queryPermutation parameter leaf chainIdx digit value :=
  simulateQ_chainWalkWithHash _ _ _ _ _ _

theorem simulateQ_leafHashWithHash :
    simulateQ σ (leafHashWithHash (m := OracleComp HashSpec) parameter leaf endpoints) =
      leafHash queryPermutation parameter leaf endpoints :=
  simulateQ_tweakableHashWithHash _ _ _

theorem simulateQ_encodeWithHash :
    simulateQ σ (encodeWithHash (m := OracleComp HashSpec) parameter leaf message counter) =
      encode queryPermutation parameter leaf message counter := by
  simp only [encodeWithHash, encode, simulateQ_bind, simulateQ_pure,
    simulateQ_tweakableHashWithHash]

theorem simulateQ_otsLeafWithHash :
    simulateQ σ (otsLeafWithHash (m := OracleComp HashSpec) parameter leaf message counter
      values) = otsLeaf queryPermutation parameter leaf message counter values := by
  simp only [otsLeafWithHash, otsLeaf, simulateQ_bind, simulateQ_encodeWithHash]
  congr 1; funext encoding
  rcases encoding with _ | encoding
  · simp
  · simp only [simulateQ_bind, simulateQ_pure, simulateQ_sequenceFin,
      simulateQ_recoverChainWithHash, simulateQ_leafHashWithHash]

theorem simulateQ_treeFoldWithHash :
    simulateQ σ (treeFoldWithHash (m := OracleComp HashSpec) parameter leaf path steps value) =
      treeFold queryPermutation parameter leaf path steps value := by
  simp only [treeFoldWithHash, treeFold, simulateQ_foldPath, simulateQ_tweakableHashWithHash]

theorem simulateQ_forestWalkWithHash :
    simulateQ σ (forestWalkWithHash (m := OracleComp HashSpec) parameter index c s j a i start steps
      value) = forestWalk queryPermutation parameter index c s j a i start steps value := by
  simp only [forestWalkWithHash, forestWalk, simulateQ_walkChain, simulateQ_tweakableHashWithHash]

theorem simulateQ_forestRecoverChainWithHash :
    simulateQ σ (forestRecoverChainWithHash (m := OracleComp HashSpec) parameter index c s j a i
      deficit value) =
      forestRecoverChain queryPermutation parameter index c s j a i deficit value :=
  simulateQ_forestWalkWithHash _ _ _ _ _ _ _ _ _ _

theorem simulateQ_childLeafHashWithHash :
    simulateQ σ (childLeafHashWithHash (m := OracleComp HashSpec) parameter index c s j a ends) =
      childLeafHash queryPermutation parameter index c s j a ends :=
  simulateQ_tweakableHashWithHash _ _ _

theorem simulateQ_childRecoverWithHash :
    simulateQ σ (childRecoverWithHash (m := OracleComp HashSpec) parameter index c s j a word
      fvalues) = childRecover queryPermutation parameter index c s j a word fvalues := by
  simp only [childRecoverWithHash, childRecover, simulateQ_bind, simulateQ_sequenceFin,
    simulateQ_forestRecoverChainWithHash, simulateQ_childLeafHashWithHash]

theorem simulateQ_subNodeHashWithHash :
    simulateQ σ (subNodeHashWithHash (m := OracleComp HashSpec) parameter index c s j level node
      payload) = subNodeHash queryPermutation parameter index c s j level node payload := by
  simp only [subNodeHashWithHash, subNodeHash]
  split <;> simp only [simulateQ_pure, simulateQ_tweakableHashWithHash]

theorem simulateQ_subFoldWithHash :
    simulateQ σ (subFoldWithHash (m := OracleComp HashSpec) parameter index c s j a subPath steps
      value) = subFold queryPermutation parameter index c s j a subPath steps value := by
  simp only [subFoldWithHash, subFold, simulateQ_foldPath, simulateQ_subNodeHashWithHash]

theorem simulateQ_superHashWithHash :
    simulateQ σ (superHashWithHash (m := OracleComp HashSpec) parameter index c s tops) =
      superHash queryPermutation parameter index c s tops :=
  simulateQ_tweakableHashWithHash _ _ _

theorem simulateQ_topNodeHashWithHash :
    simulateQ σ (topNodeHashWithHash (m := OracleComp HashSpec) parameter index c level node
      payload) = topNodeHash queryPermutation parameter index c level node payload := by
  simp only [topNodeHashWithHash, topNodeHash]
  split <;> simp only [simulateQ_pure, simulateQ_tweakableHashWithHash]

theorem simulateQ_topFoldWithHash :
    simulateQ σ (topFoldWithHash (m := OracleComp HashSpec) parameter index c s topPath steps
      value) = topFold queryPermutation parameter index c s topPath steps value := by
  simp only [topFoldWithHash, topFold, simulateQ_foldPath, simulateQ_topNodeHashWithHash]

theorem simulateQ_coordRecoverWithHash :
    simulateQ σ (coordRecoverWithHash (m := OracleComp HashSpec) parameter index c mark opening) =
      coordRecover queryPermutation parameter index c mark opening := by
  simp only [coordRecoverWithHash, coordRecover, simulateQ_bind, simulateQ_pure,
    simulateQ_sequenceFin, simulateQ_childRecoverWithHash, simulateQ_subFoldWithHash,
    simulateQ_superHashWithHash, simulateQ_topFoldWithHash]

theorem simulateQ_forestRecoverWithHash :
    simulateQ σ (forestRecoverWithHash (m := OracleComp HashSpec) parameter index marks openings) =
      forestRecover queryPermutation parameter index marks openings := by
  simp only [forestRecoverWithHash, forestRecover, simulateQ_sequenceFin,
    simulateQ_coordRecoverWithHash]

theorem simulateQ_messageDigestCallWithHash :
    simulateQ σ (messageDigestCallWithHash (m := OracleComp HashSpec) parameter msg randomness) =
      messageDigestCall queryPermutation parameter msg randomness :=
  simulateQ_thPairWithHash _ _ _

theorem simulateQ_messageDigestWithHash :
    simulateQ σ (messageDigestWithHash (m := OracleComp HashSpec) parameter msg randomness) =
      messageDigest queryPermutation parameter msg randomness := by
  simp only [messageDigestWithHash, messageDigest, simulateQ_bind, simulateQ_pure,
    simulateQ_messageDigestCallWithHash]

theorem simulateQ_verifyWithHash (publicKey : PublicKey) (signature : Signature) :
    simulateQ σ (verifyWithHash (m := OracleComp HashSpec) publicKey msg signature) =
      verify queryPermutation publicKey msg signature := by
  simp only [verifyWithHash, verify, simulateQ_bind, simulateQ_messageDigestWithHash]
  congr 1; funext digest
  simp only [simulateQ_forestRecoverWithHash]
  congr 1; funext forestKey
  simp only [simulateQ_otsLeafWithHash]
  congr 1; funext leaf
  rcases leaf with _ | leaf
  · simp
  · simp only [simulateQ_bind, simulateQ_pure, simulateQ_treeFoldWithHash]

end Concrete

namespace Seeded

open Concrete

variable (parameter : PublicParameter) (leaf index : Index) (seed : MasterSeed)
  (message : ForestKey)
  (c : Coord) (s : SuperIdx) (j : SubIdx) (a : ChildIdx) (mark : CoordMark)
  (marks : Coord → CoordMark) (level node : ℕ)

theorem simulateQ_otsSecretsWithHash :
    simulateQ σ (otsSecretsWithHash (m := OracleComp HashSpec) parameter leaf seed) =
      otsSecrets queryPermutation parameter leaf seed := by
  simp only [otsSecretsWithHash, otsSecrets, simulateQ_bind, simulateQ_pure, simulateQ_sequenceFin,
    simulateQ_thPairWithHash]

theorem simulateQ_oneTimePublicKeyWithHash :
    simulateQ σ (oneTimePublicKeyWithHash (m := OracleComp HashSpec) parameter leaf seed) =
      oneTimePublicKey queryPermutation parameter leaf seed := by
  simp only [oneTimePublicKeyWithHash, oneTimePublicKey, simulateQ_bind, simulateQ_sequenceFin,
    simulateQ_otsSecretsWithHash, simulateQ_chainWalkWithHash]

theorem simulateQ_otsSignFromWithHash :
    ∀ attempts counter : ℕ,
      simulateQ σ (otsSignFromWithHash (m := OracleComp HashSpec) parameter leaf seed message
        attempts counter) = otsSignFrom queryPermutation parameter leaf seed message attempts
          counter
  | 0, _ => by simp [otsSignFromWithHash, otsSignFrom]
  | attempts + 1, counter => by
    simp only [otsSignFromWithHash, otsSignFrom, simulateQ_bind, simulateQ_encodeWithHash]
    congr 1; funext encoding
    rcases encoding with _ | encoding
    · exact simulateQ_otsSignFromWithHash attempts _
    · simp only [simulateQ_bind, simulateQ_pure, simulateQ_otsSecretsWithHash,
        simulateQ_sequenceFin, simulateQ_chainWalkWithHash]

theorem simulateQ_otsSignWithHash :
    simulateQ σ (otsSignWithHash (m := OracleComp HashSpec) parameter leaf seed message) =
      otsSign queryPermutation parameter leaf seed message :=
  simulateQ_otsSignFromWithHash _ _ _ _ _ _

theorem simulateQ_treeNodeWithHash :
    simulateQ σ (treeNodeWithHash (m := OracleComp HashSpec) parameter seed level node) =
      treeNode queryPermutation parameter seed level node := by
  simp only [treeNodeWithHash, treeNode, simulateQ_buildTree, simulateQ_bind,
    simulateQ_oneTimePublicKeyWithHash, simulateQ_leafHashWithHash,
    simulateQ_tweakableHashWithHash]

theorem simulateQ_forestSecretsWithHash :
    simulateQ σ (forestSecretsWithHash (m := OracleComp HashSpec) parameter index c s j a seed) =
      forestSecrets queryPermutation parameter index c s j a seed := by
  simp only [forestSecretsWithHash, forestSecrets, simulateQ_bind, simulateQ_pure,
    simulateQ_sequenceFin, simulateQ_thPairWithHash]

theorem simulateQ_childLeafWithHash :
    simulateQ σ (childLeafWithHash (m := OracleComp HashSpec) parameter index c s j a seed) =
      childLeaf queryPermutation parameter index c s j a seed := by
  simp only [childLeafWithHash, childLeaf, simulateQ_bind, simulateQ_forestSecretsWithHash,
    simulateQ_sequenceFin, simulateQ_forestWalkWithHash, simulateQ_childLeafHashWithHash]

theorem simulateQ_subNodeWithHash :
    simulateQ σ (subNodeWithHash (m := OracleComp HashSpec) parameter index c s j seed level node) =
      subNode queryPermutation parameter index c s j seed level node := by
  simp only [subNodeWithHash, subNode, simulateQ_buildTree, simulateQ_childLeafWithHash,
    simulateQ_subNodeHashWithHash]

theorem simulateQ_superNodeWithHash :
    simulateQ σ (superNodeWithHash (m := OracleComp HashSpec) parameter index c s seed) =
      superNode queryPermutation parameter index c s seed := by
  simp only [superNodeWithHash, superNode, simulateQ_bind, simulateQ_pure, simulateQ_sequenceFin,
    simulateQ_subNodeWithHash, simulateQ_superHashWithHash]

theorem simulateQ_topNodeWithHash :
    simulateQ σ (topNodeWithHash (m := OracleComp HashSpec) parameter index c seed level node) =
      topNode queryPermutation parameter index c seed level node := by
  simp only [topNodeWithHash, topNode, simulateQ_buildTree, simulateQ_superNodeWithHash,
    simulateQ_topNodeHashWithHash]

theorem simulateQ_forestKeyWithHash :
    simulateQ σ (forestKeyWithHash (m := OracleComp HashSpec) parameter index seed) =
      forestKey queryPermutation parameter index seed := by
  simp only [forestKeyWithHash, forestKey, simulateQ_bind, simulateQ_pure, simulateQ_sequenceFin,
    simulateQ_topNodeWithHash]

theorem simulateQ_coordOpenWithHash :
    simulateQ σ (coordOpenWithHash (m := OracleComp HashSpec) parameter index c mark seed) =
      coordOpen queryPermutation parameter index c mark seed := by
  simp only [coordOpenWithHash, coordOpen, simulateQ_bind, simulateQ_pure, simulateQ_sequenceFin,
    simulateQ_forestSecretsWithHash, simulateQ_forestWalkWithHash, simulateQ_subNodeWithHash,
    simulateQ_topNodeWithHash]

theorem simulateQ_forestOpenWithHash :
    simulateQ σ (forestOpenWithHash (m := OracleComp HashSpec) parameter index marks seed) =
      forestOpen queryPermutation parameter index marks seed := by
  simp only [forestOpenWithHash, forestOpen, simulateQ_sequenceFin, simulateQ_coordOpenWithHash]

theorem simulateQ_surrogateWithHash :
    simulateQ σ (surrogateWithHash (m := OracleComp HashSpec) parameter seed level) =
      surrogate queryPermutation parameter seed level := by
  simp only [surrogateWithHash, surrogate]
  split <;> simp only [simulateQ_pure, simulateQ_thWithHash]

variable [Params]

theorem simulateQ_spineNodeWithHash :
    ∀ steps : ℕ, simulateQ σ (spineNodeWithHash (m := OracleComp HashSpec) parameter seed steps) =
      spineNode queryPermutation parameter seed steps
  | 0 => by simp only [spineNodeWithHash, spineNode, simulateQ_treeNodeWithHash]
  | steps + 1 => by
    simp only [spineNodeWithHash, spineNode, simulateQ_bind, simulateQ_spineNodeWithHash,
      simulateQ_surrogateWithHash]
    congr 1; funext below; congr 1; funext sibling
    split <;> simp only [simulateQ_tweakableHashWithHash]

theorem simulateQ_treeRootWithHash :
    simulateQ σ (treeRootWithHash (m := OracleComp HashSpec) parameter seed) =
      treeRoot queryPermutation parameter seed :=
  simulateQ_spineNodeWithHash _ _ _

theorem simulateQ_treePathWithHash :
    simulateQ σ (treePathWithHash (m := OracleComp HashSpec) parameter seed leaf) =
      treePath queryPermutation parameter seed leaf := by
  simp only [treePathWithHash, treePath, simulateQ_sequenceFin]
  congr 1; funext l
  split <;> simp only [simulateQ_treeNodeWithHash, simulateQ_surrogateWithHash]

theorem simulateQ_keygenFromMasterWithHash :
    simulateQ σ (keygenFromMasterWithHash seed) = keygenFromMaster queryPermutation seed := by
  simp only [keygenFromMasterWithHash, keygenFromMaster, simulateQ_bind, simulateQ_pure,
    simulateQ_thWithHash]
  refine congrArg _ (funext fun parameter ↦ ?_)
  -- `parameter` is a `Digest`, the public parameter's type up to `digestBits = 128`
  rw [simulateQ_treeRootWithHash parameter]

theorem simulateQ_keygenFromSeedWithHash :
    simulateQ σ (keygenFromSeedWithHash seed) = keygenFromSeed queryPermutation seed := by
  simp only [keygenFromSeedWithHash, keygenFromSeed, simulateQ_bind,
    simulateQ_taggedSeedWithHash, simulateQ_keygenFromMasterWithHash]

theorem simulateQ_signAttemptWithHash (secretKey : SecretKey) (msg : Message)
    (randomness : Randomness) :
    simulateQ σ (signAttemptWithHash (m := OracleComp HashSpec) secretKey msg randomness) =
      signAttempt queryPermutation secretKey msg randomness := by
  simp only [signAttemptWithHash, signAttempt, simulateQ_bind, simulateQ_messageDigestCallWithHash]
  congr 1; funext first
  split <;> simp

theorem simulateQ_signDigestLoopWithHash (secretKey : SecretKey) (msg : Message) :
    ∀ (attempts : ℕ) (randomness : Randomness),
      simulateQ σ (signDigestLoopWithHash (m := OracleComp HashSpec) secretKey msg attempts
        randomness) = signDigestLoop queryPermutation secretKey msg attempts randomness
  | 0, _ => by simp [signDigestLoopWithHash, signDigestLoop]
  | attempts + 1, randomness => by
    simp only [signDigestLoopWithHash, signDigestLoop, simulateQ_bind,
      simulateQ_signAttemptWithHash]
    congr 1; funext attempt
    rcases attempt with _ | index
    · exact simulateQ_signDigestLoopWithHash secretKey msg attempts _
    · simp

theorem simulateQ_signWithHash (secretKey : SecretKey) (msg : Message) :
    simulateQ σ (signWithHash (m := OracleComp HashSpec) secretKey msg) =
      sign queryPermutation secretKey msg := by
  simp only [signWithHash, sign, simulateQ_bind, simulateQ_thWithHash]
  refine congrArg _ (funext fun base ↦ ?_)
  simp only [simulateQ_signDigestLoopWithHash]
  refine congrArg _ (funext fun found ↦ ?_)
  rcases found with _ | ⟨randomness, _⟩
  · simp
  · simp only [simulateQ_bind, simulateQ_messageDigestWithHash, simulateQ_forestOpenWithHash,
      simulateQ_forestKeyWithHash, simulateQ_otsSignWithHash]
    refine congrArg _ (funext fun digest ↦ congrArg _ (funext fun opening ↦
      congrArg _ (funext fun key ↦ congrArg _ (funext fun signed ↦ ?_))))
    rcases signed with _ | ⟨counter, values⟩
    · simp
    · simp only [simulateQ_bind, simulateQ_pure, simulateQ_treePathWithHash]

end Seeded

namespace Rpm

variable [Params]

/-- **The statement's leanSPHINCS is the hash-query scheme over `π`.** -/
theorem scheme_eq : scheme = schemeWithHash.overPermutation := by
  simp only [scheme, schemeWithHash, SchemeWithHash.overPermutation,
    Seeded.simulateQ_keygenFromSeedWithHash, Seeded.simulateQ_signWithHash,
    Concrete.simulateQ_verifyWithHash]

end Rpm

namespace Lifetimes

/-- **leanSPHINCS in the random-permutation model, from its hash-query form.** -/
theorem leanSphincsStronglyUnforgeable_of_withHash (h : LeanSphincsStronglyUnforgeableWithHash) :
    LeanSphincsStronglyUnforgeable := by
  intro P hP
  rw [@Rpm.scheme_eq P]
  exact stronglyUnforgeable_overPermutation (h P hP)

end Lifetimes

end Sphincs
