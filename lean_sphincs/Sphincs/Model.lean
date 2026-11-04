import FORS.Statement
import Statement.LeanSphincs
import Common.WithHashBridge

/-!
# The statement's leanSPHINCS is upstream's model at the deployed configuration

The proof of this project (`FORS`, leanVM's `formal/lean_sphincs` at `542b0353`) is about
`FORS.Scheme`, a model of leanSPHINCS generic in its shape (`FORS.Params`), with the hash a random
oracle (`FORS.HashSpec`). At the deployed configuration, `.layered 26 3 8 24 10 1182000000`
(`Sphincs.Model.params`), it is the statement's scheme (`Statement/LeanSphincs.lean`) with the hash
a query: this file and `Sphincs/ModelSigner.lean` prove each algorithm of the model, its queries
answered by Keccak-256 over `π` (`schemeHashOverPermutation`), the statement's over `π`.

The two differ in presentation only:

* the model numbers the layers from the top (`lay = 0` the top layer, the address's layer byte
  `d - 1 - lay`), the statement from the bottom as the crate does (`toLayer`);
* the model's signature holds each layer's path in its layer's signature, its path's length the
  model's `layerHeight`, the statement's likewise with the statement's `layerHeight`
  (`signatureEquiv`);
* every hash input is the same bytes (`fieldBytes_hashDomainFields`): the model's own copies of the
  types, the address and the byte encodings are the statement's at this configuration.
-/

open OracleComp OracleSpec

namespace Sphincs.Model

open HashSig HashSig.OverPermutation Common Common.SufCma

/-- The deployed configuration: height 26, three layers of 10 + 8 + 8 from the top, FORS of 24
trees of height 10, `N = 1,182,000,000`. -/
abbrev params : FORS.Params := .layered 26 3 8 24 10 1182000000

attribute [local instance] params

local notation "σ" => schemeHashOverPermutation

/-! ## The maps -/

/-- A model layer (`0` the top) as the statement's layer (`0` the bottom). -/
def toLayer (lay : FORS.Layer) : Layer := ⟨2 - lay.val, by have := lay.isLt; unfold layerCount; omega⟩

/-- A statement layer as the model's. -/
def ofLayer (layer : Layer) : FORS.Layer :=
  ⟨2 - layer.val, by have := layer.isLt; unfold layerCount at this; show _ < 3; omega⟩

theorem toLayer_ofLayer (layer : Layer) : toLayer (ofLayer layer) = layer := by
  have := layer.isLt; unfold layerCount at this
  apply Fin.ext; simp only [toLayer, ofLayer]; omega

theorem ofLayer_toLayer (lay : FORS.Layer) : ofLayer (toLayer lay) = lay := by
  have := lay.isLt; change _ < 3 at this
  apply Fin.ext; simp only [toLayer, ofLayer]; omega

/-- The layers, through the reversal. -/
def layerEquiv : FORS.Layer ≃ Layer := ⟨toLayer, ofLayer, ofLayer_toLayer, toLayer_ofLayer⟩

theorem layerHeight_toLayer (lay : FORS.Layer) : layerHeight (toLayer lay) = FORS.layerHeight lay := by
  have := lay.isLt; change _ < 3 at this
  unfold layerHeight toLayer FORS.layerHeight
  rcases lay with ⟨_ | _ | _ | n, h⟩ <;> first | rfl | (change _ < 3 at h; omega)

/-- A model hash domain as the statement's: the layer reversed, every other field as it is. -/
def toDomain : FORS.HashDomain → HashDomain
  | .chain lay tree leaf chainIndex step => .chain (toLayer lay) tree leaf chainIndex step
  | .leaf lay tree leaf => .leaf (toLayer lay) tree leaf
  | .node lay tree level nodeIndex => .node (toLayer lay) tree level nodeIndex
  | .encoding lay tree leaf => .encoding (toLayer lay) tree leaf
  | .forsLeaf index forsTree leaf => .forsLeaf index forsTree leaf
  | .forsNode index forsTree level node => .forsNode index forsTree level node
  | .message call => .message call

/-- **The same address bytes.** -/
theorem fieldBytes_hashDomainFields (domain : FORS.HashDomain) :
    FORS.fieldBytes (FORS.hashDomainFields domain) = addressBytes (hashDomainFields (toDomain domain)) := by
  cases domain <;> rfl

/-- **The same hash input.** -/
theorem tweakableHashInput_eq (parameter : FORS.PublicParameter) (domain : FORS.HashDomain)
    (payload : FORS.HashInput) :
    FORS.tweakableHashInput parameter domain payload =
      thInput parameter (hashDomainFields (toDomain domain)) payload := by
  simp only [FORS.tweakableHashInput, FORS.tweakBytes, fieldBytes_hashDomainFields, thInput]
  rfl

/-! ## The hash

The model's computations are in `OracleComp FORS.HashSpec`, the statement's hash spec up to
unfolding: the simulation lemmas of its binds, stated in that monad, so that `simp` sees them. -/

theorem sim_bind {α β : Type} (x : OracleComp FORS.HashSpec α) (f : α → OracleComp FORS.HashSpec β) :
    simulateQ σ (@Bind.bind (OracleComp FORS.HashSpec) _ α β x f) =
      simulateQ σ x >>= fun a ↦ simulateQ σ (f a) :=
  simulateQ_bind _ _ _

theorem sim_pure {α : Type} (a : α) :
    simulateQ σ (@Pure.pure (OracleComp FORS.HashSpec) _ α a) = pure a :=
  simulateQ_pure _ _

theorem sim_map {α β : Type} (f : α → β) (x : OracleComp FORS.HashSpec α) :
    simulateQ σ (@Functor.map (OracleComp FORS.HashSpec) _ α β f x) = f <$> simulateQ σ x :=
  simulateQ_map _ _ _

theorem simulateQ_oracleHash (input : FORS.HashInput) :
    simulateQ σ (FORS.Concrete.oracleHash (m := OracleComp FORS.HashSpec) input) =
      keccakHash queryPermutation input :=
  LeanXmss.Verification.simulateQ_oracleHashWithHash input

theorem simulateQ_tweakableHash (parameter : FORS.PublicParameter) (domain : FORS.HashDomain)
    (payload : FORS.HashInput) :
    simulateQ σ (FORS.Concrete.tweakableHash (m := OracleComp FORS.HashSpec) parameter domain
      payload) = Verification.tweakableHash queryPermutation parameter (toDomain domain) payload := by
  simp only [FORS.Concrete.tweakableHash, sim_bind, sim_pure, simulateQ_oracleHash,
    tweakableHashInput_eq, Verification.tweakableHash, th]
  rfl

theorem simulateQ_sequenceFin {α : Type} {n : ℕ} (c : Fin n → OracleComp FORS.HashSpec α) :
    simulateQ σ (FORS.Concrete.sequenceFin (m := OracleComp FORS.HashSpec) c) =
      sequenceFin fun i ↦ simulateQ σ (c i) := by
  induction n with
  | zero => simp only [FORS.Concrete.sequenceFin, sequenceFin, sim_pure]
  | succ n ih =>
    simp only [FORS.Concrete.sequenceFin, sequenceFin, sim_bind, sim_pure, ih]

/-- `sequenceFin` through a map of its entries. -/
theorem sequenceFin_map {m : Type → Type} [Monad m] [LawfulMonad m] {α β : Type} (g : α → β) :
    ∀ (n : Nat) (f : Fin n → m α),
      sequenceFin (fun i ↦ g <$> f i) = (fun v ↦ g ∘ v) <$> sequenceFin f
  | 0, f => by
    simp only [sequenceFin, map_pure]
    congr 1
    funext i
    exact i.elim0
  | n + 1, f => by
    simp only [sequenceFin, map_bind, bind_map_left, map_pure]
    refine bind_congr fun head ↦ ?_
    rw [sequenceFin_map g n (fun i : Fin n ↦ f i.succ), bind_map_left]
    refine bind_congr fun tail ↦ ?_
    congr 1
    funext i
    refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp

/-! ## The model's copies of the statement's definitions -/

theorem bytesLE_eq : @FORS.bytesLE = @littleEndianBytes := rfl

theorem nodePayload_eq (left right : Digest) :
    FORS.Concrete.nodePayload left right = nodePayload left right := rfl

theorem chainLength_eq : FORS.chainLength = HashSig.chainLength := rfl

theorem orderTops_eq : @FORS.Concrete.orderTops = @Verification.orderTops := rfl

/-- Two binds agree when their computations and their continuations do. -/
theorem bind_eq_of {m : Type → Type} [Monad m] {α β : Type} {x y : m α} {f g : α → m β}
    (hx : x = y) (hfg : ∀ a, f a = g a) : x >>= f = y >>= g := by
  rw [hx, funext hfg]

theorem decodeDigest_eq (digest : Digest) :
    FORS.TargetSum.decodeDigest digest = TargetSum.decodeDigest digest := by
  unfold FORS.TargetSum.decodeDigest TargetSum.decodeDigest
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd h1 h2
  · exact absurd h2 h1
  · rfl

/-! ## The maps of keys and signatures -/

/-- A statement public key as the model's. -/
def toModelPublicKey (publicKey : PublicKey) : FORS.PublicKey :=
  ⟨publicKey.root, publicKey.parameter⟩

/-- A model public key as the statement's. -/
def ofModelPublicKey (publicKey : FORS.PublicKey) : PublicKey :=
  ⟨publicKey.root, publicKey.parameter⟩

/-- The public keys correspond. -/
def publicKeyEquiv : FORS.PublicKey ≃ PublicKey where
  toFun := ofModelPublicKey
  invFun := toModelPublicKey
  left_inv _ := rfl
  right_inv _ := rfl

/-- A FORS tree's opening, the model's from the statement's. -/
def toModelTreeOpening (opening : ForsTreeOpening) : FORS.TreeOpening :=
  ⟨opening.secret, opening.path⟩

/-- A FORS tree's opening, the statement's from the model's. -/
def ofModelTreeOpening (opening : FORS.TreeOpening) : ForsTreeOpening :=
  ⟨opening.secret, opening.path⟩

/-- A statement signature as the model's: the layers reversed, each path read through its length's
equality. -/
def toModelSignature (signature : Signature) : FORS.Signature where
  randomness := signature.randomizer
  fors forsTree := toModelTreeOpening (signature.forsOpening forsTree)
  layers lay :=
    ⟨(signature.layers (toLayer lay)).counter, (signature.layers (toLayer lay)).chainValues,
      fun level ↦ (signature.layers (toLayer lay)).authenticationPath
        (Fin.cast (layerHeight_toLayer lay).symm level)⟩

theorem layerHeight_ofLayer (layer : Layer) : FORS.layerHeight (ofLayer layer) = layerHeight layer := by
  rw [← layerHeight_toLayer, toLayer_ofLayer]

/-- A model signature as the statement's. -/
def ofModelSignature (signature : FORS.Signature) : Signature where
  randomizer := signature.randomness
  forsOpening forsTree := ofModelTreeOpening (signature.fors forsTree)
  layers layer :=
    ⟨(signature.layers (ofLayer layer)).counter, (signature.layers (ofLayer layer)).chainValues,
      fun level ↦ (signature.layers (ofLayer layer)).path
        (Fin.cast (layerHeight_ofLayer layer).symm level)⟩

/-- **The signatures correspond.** -/
def signatureEquiv : FORS.Signature ≃ Signature where
  toFun := ofModelSignature
  invFun := toModelSignature
  left_inv signature := by
    rcases signature with ⟨randomness, fors, layers⟩
    simp only [toModelSignature, ofModelSignature, toModelTreeOpening, ofModelTreeOpening]
    congr 1
    funext lay
    fin_cases lay <;> rfl
  right_inv signature := by
    rcases signature with ⟨randomizer, forsOpening, layers⟩
    simp only [toModelSignature, ofModelSignature, toModelTreeOpening, ofModelTreeOpening]
    congr 1
    funext layer
    fin_cases layer <;> rfl

/-! ## The index -/

theorem treeIndexAt_eq (index : FORS.Index) (lay : FORS.Layer) :
    FORS.Concrete.treeIndexAt index lay = treeOfIndex (toLayer lay) index := by
  apply Fin.ext
  fin_cases lay <;> rfl

theorem leafIndexAt_eq (index : FORS.Index) (lay : FORS.Layer) :
    FORS.Concrete.leafIndexAt index lay = leafOfIndex (toLayer lay) index := by
  apply Fin.ext
  fin_cases lay <;> rfl

/-! ## Verification -/

section Verification

open Verification

variable (parameter : FORS.PublicParameter)

theorem simulateQ_chainWalk (lay : FORS.Layer) (tree : FORS.TreeIndex) (leaf : FORS.LeafIndex)
    (chainIndex : FORS.ChainIndex) (start : ℕ) :
    ∀ (steps : ℕ) (value : FORS.Digest),
      simulateQ σ (FORS.Concrete.chainWalk (m := OracleComp FORS.HashSpec) parameter lay tree leaf
        chainIndex start steps value) =
        chainWalk queryPermutation parameter (toLayer lay) tree leaf chainIndex start steps value
  | 0, value => by
    simp only [FORS.Concrete.chainWalk, chainWalk, walkChain]
    exact sim_pure _
  | steps + 1, value => by
    simp only [FORS.Concrete.chainWalk, sim_bind, simulateQ_chainWalk lay tree leaf chainIndex start steps]
    simp only [chainWalk, walkChain]
    congr 1
    funext previous
    by_cases h : start + steps < 3
    · rw [dite_eq_left (show start + steps < FORS.chainLength - 1 from h),
        dite_eq_left (show start + steps < HashSig.chainLength - 1 from h),
        simulateQ_tweakableHash]
      rfl
    · rw [dite_eq_right (show ¬start + steps < FORS.chainLength - 1 from h),
        dite_eq_right (show ¬start + steps < HashSig.chainLength - 1 from h), sim_pure]
      rfl

theorem simulateQ_recoverChain (lay : FORS.Layer) (tree : FORS.TreeIndex) (leaf : FORS.LeafIndex)
    (chainIndex : FORS.ChainIndex) (digit : FORS.Digit) (value : FORS.Digest) :
    simulateQ σ (FORS.Concrete.recoverChain (m := OracleComp FORS.HashSpec) parameter lay tree leaf
      chainIndex digit value) =
      recoverChain queryPermutation parameter (toLayer lay) tree leaf chainIndex digit value :=
  simulateQ_chainWalk parameter lay tree leaf chainIndex _ _ _

theorem simulateQ_leafHash (lay : FORS.Layer) (tree : FORS.TreeIndex) (leaf : FORS.LeafIndex)
    (endpoints : FORS.ChainIndex → FORS.Digest) :
    simulateQ σ (FORS.Concrete.leafHash (m := OracleComp FORS.HashSpec) parameter lay tree leaf
      endpoints) = leafHash queryPermutation parameter (toLayer lay) tree leaf endpoints :=
  simulateQ_tweakableHash _ _ _

theorem simulateQ_encode (lay : FORS.Layer) (tree : FORS.TreeIndex) (leaf : FORS.LeafIndex)
    (message : FORS.HashInput) (counter : FORS.Counter) :
    simulateQ σ (FORS.Concrete.encode (m := OracleComp FORS.HashSpec) parameter lay tree leaf
      message counter) = encode queryPermutation parameter (toLayer lay) tree leaf message counter := by
  simp only [FORS.Concrete.encode, encode, sim_bind, sim_pure, simulateQ_tweakableHash]
  congr 1

theorem simulateQ_otsLeaf (lay : FORS.Layer) (tree : FORS.TreeIndex) (leaf : FORS.LeafIndex)
    (message : FORS.HashInput) (counter : FORS.Counter) (values : FORS.ChainIndex → FORS.Digest) :
    simulateQ σ (FORS.Concrete.otsLeaf (m := OracleComp FORS.HashSpec) parameter lay tree leaf
      message counter values) =
      otsLeaf queryPermutation parameter (toLayer lay) tree leaf message counter values := by
  simp only [FORS.Concrete.otsLeaf, otsLeaf, sim_bind, simulateQ_encode]
  congr 1
  funext encoding
  rcases encoding with _ | encoding
  · exact sim_pure _
  · simp only [sim_bind, sim_pure, simulateQ_sequenceFin, simulateQ_recoverChain, simulateQ_leafHash]
    rfl

theorem simulateQ_treeFold (lay : FORS.Layer) (tree : FORS.TreeIndex) (leaf : FORS.LeafIndex)
    (path : ℕ → FORS.Digest) :
    ∀ (levels : ℕ) (value : FORS.Digest),
      simulateQ σ (FORS.Concrete.treeFold (m := OracleComp FORS.HashSpec) parameter lay tree leaf
        path levels value) =
        treeFold queryPermutation parameter (toLayer lay) tree leaf path levels value
  | 0, value => by
    simp only [FORS.Concrete.treeFold, treeFold, foldPath]
    exact sim_pure _
  | levels + 1, value => by
    simp only [FORS.Concrete.treeFold, sim_bind, simulateQ_treeFold lay tree leaf path levels]
    simp only [treeFold, foldPath]
    congr 1
    funext current
    split <;> rw [simulateQ_tweakableHash] <;> rfl

/-- The statement's FORS node hash at a node in range. -/
theorem forsNodeHash_of_lt {m : Type → Type} [Monad m] (π : LeanVM.Semantics.KeccakState → m
    LeanVM.Semantics.KeccakState) (parameter : PublicParameter) (index : Index)
    (forsTree : ForsTreeIndex) (level node : ℕ) (hnode : node < 2 ^ forsTreeHeight)
    (payload : HashInput) :
    forsNodeHash π parameter index forsTree level node payload =
      if h : level < forsTreeHeight then
        Verification.tweakableHash π parameter (.forsNode index forsTree ⟨level, h⟩ ⟨node, hnode⟩)
          payload
      else pure 0 := by
  unfold forsNodeHash
  simp only [Nat.mod_eq_of_lt hnode]

theorem simulateQ_forsFold (index : FORS.Index) (forsTree : FORS.FTree) (leaf : FORS.FLeaf)
    (path : Fin FORS.forsHeight → FORS.Digest) :
    ∀ (levels : ℕ) (value : FORS.Digest),
      simulateQ σ (FORS.Concrete.forsFold (m := OracleComp FORS.HashSpec) parameter index forsTree
        leaf path levels value) =
        forsFold queryPermutation parameter index forsTree leaf path levels value
  | 0, value => by
    simp only [FORS.Concrete.forsFold, forsFold, foldPath]
    exact sim_pure _
  | levels + 1, value => by
    simp only [FORS.Concrete.forsFold, sim_bind, simulateQ_forsFold index forsTree leaf path levels]
    simp only [forsFold, foldPath]
    congr 1
    funext current
    rw [forsNodeHash_of_lt queryPermutation parameter index forsTree levels (leaf.val / 2 ^ (levels + 1))
      (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) leaf.isLt)]
    by_cases hlevel : levels < 10
    · have hlt : levels < forsTreeHeight := hlevel
      rw [dite_eq_left (show levels < FORS.forsHeight from hlevel), dite_eq_left hlt]
      by_cases hbit : leaf.val.testBit levels = true
      · simp only [hbit, ↓reduceIte, hlt, ↓reduceDIte]
        rw [simulateQ_tweakableHash]
        rfl
      · simp only [hbit, Bool.false_eq_true, ↓reduceIte, hlt, ↓reduceDIte]
        rw [simulateQ_tweakableHash]
        rfl
    · rw [dite_eq_right (show ¬levels < FORS.forsHeight from hlevel),
        dite_eq_right (show ¬levels < forsTreeHeight from hlevel), sim_pure]
      rfl

theorem simulateQ_forsTreeRecover (index : FORS.Index) (forsTree : FORS.FTree)
    (leaf : FORS.FLeaf) (opening : FORS.TreeOpening) :
    simulateQ σ (FORS.Concrete.treeRecover (m := OracleComp FORS.HashSpec) parameter index forsTree
      leaf opening) =
      forsTreeRecover queryPermutation parameter index forsTree leaf (ofModelTreeOpening opening) := by
  simp only [FORS.Concrete.treeRecover, forsTreeRecover, sim_bind, sim_pure,
    FORS.Concrete.forsLeafHash, simulateQ_tweakableHash, simulateQ_forsFold]
  rfl

theorem simulateQ_forsRecover (index : FORS.Index) (leaves : FORS.FTree → FORS.FLeaf)
    (opening : FORS.FTree → FORS.TreeOpening) :
    simulateQ σ (FORS.Concrete.forsRecover (m := OracleComp FORS.HashSpec) parameter index leaves
      opening) =
      forsRecover queryPermutation parameter index leaves
        (fun forsTree ↦ ofModelTreeOpening (opening forsTree)) := by
  simp only [FORS.Concrete.forsRecover, forsRecover, simulateQ_sequenceFin, simulateQ_forsTreeRecover]
  rfl

theorem simulateQ_messageDigestCall (root : FORS.Digest) (message : FORS.Message)
    (randomizer : FORS.Randomness) (call : FORS.DigestCall) :
    simulateQ σ (FORS.Concrete.messageDigestCall (m := OracleComp FORS.HashSpec) parameter root
      message randomizer call) =
      messageDigestCall queryPermutation parameter message randomizer call := by
  simp only [FORS.Concrete.messageDigestCall, simulateQ_oracleHash, tweakableHashInput_eq,
    messageDigestCall, thPair]
  rfl

theorem simulateQ_messageDigest (root : FORS.Digest) (message : FORS.Message)
    (randomizer : FORS.Randomness) :
    simulateQ σ (FORS.Concrete.messageDigest (m := OracleComp FORS.HashSpec) parameter root
      message randomizer) = messageDigest queryPermutation parameter message randomizer := by
  simp only [FORS.Concrete.messageDigest, messageDigest, sim_bind, sim_pure, simulateQ_sequenceFin,
    simulateQ_messageDigestCall]
  rfl

theorem signaturePath_eq (signature : Signature) (lay : FORS.Layer) :
    FORS.Concrete.signaturePath (toModelSignature signature) lay =
      layerPath signature (toLayer lay) := by
  funext level
  fin_cases lay <;> rfl

theorem simulateQ_verifyLayers (index : FORS.Index) (signature : Signature) :
    ∀ (layersLeft : ℕ) (message : FORS.HashInput),
      simulateQ σ (FORS.Concrete.verifyLayers (m := OracleComp FORS.HashSpec) parameter index
        (toModelSignature signature) layersLeft message) =
        verifyLayers queryPermutation parameter index signature layersLeft message
  | 0, _ => by
    simp only [FORS.Concrete.verifyLayers, verifyLayers]
    exact sim_pure _
  | layersLeft + 1, message => by
    have ih := simulateQ_verifyLayers index signature layersLeft
    rw [FORS.Concrete.verifyLayers]
    simp only [verifyLayers]
    by_cases hlayer : layersLeft < 3
    · rw [dite_eq_left (show layersLeft < FORS.numLayers from hlayer),
        dite_eq_left (show layersLeft < layerCount from hlayer)]
      interval_cases layersLeft <;>
      · simp only [sim_bind, simulateQ_otsLeaf]
        refine bind_eq_of rfl fun found ↦ ?_
        rcases found with _ | value
        · exact sim_pure _
        · simp only [sim_bind, simulateQ_treeFold]
          refine bind_eq_of (by rw [signaturePath_eq]; rfl) fun root ↦ ?_
          simp only [↓reduceIte, Nat.succ_ne_zero, sim_pure, ih]
          rfl
    · rw [dite_eq_right (show ¬layersLeft < FORS.numLayers from hlayer),
        dite_eq_right (show ¬layersLeft < layerCount from hlayer), sim_pure]
      rfl

theorem toModelSignature_fors (signature : Signature) :
    (toModelSignature signature).fors =
      fun forsTree ↦ toModelTreeOpening (signature.forsOpening forsTree) := rfl

theorem toModelSignature_randomness (signature : Signature) :
    (toModelSignature signature).randomness = signature.randomizer := rfl

theorem toModelPublicKey_parameter (publicKey : PublicKey) :
    (toModelPublicKey publicKey).parameter = publicKey.parameter := rfl

theorem toModelPublicKey_root (publicKey : PublicKey) :
    (toModelPublicKey publicKey).root = publicKey.root := rfl

theorem simulateQ_verify (publicKey : PublicKey) (message : FORS.Message) (signature : Signature) :
    simulateQ σ (FORS.Concrete.verify (m := OracleComp FORS.HashSpec) (toModelPublicKey publicKey)
      message (toModelSignature signature)) = verify queryPermutation publicKey message signature := by
  rw [FORS.Concrete.verify]
  simp only [verify, sim_bind, simulateQ_messageDigest, simulateQ_forsRecover,
    simulateQ_verifyLayers]
  refine bind_eq_of rfl fun digest ↦ bind_eq_of rfl fun forsKey ↦ bind_eq_of rfl fun found ↦ ?_
  rcases found with _ | root
  · exact sim_pure _
  · exact sim_pure _

end Verification

end Sphincs.Model
