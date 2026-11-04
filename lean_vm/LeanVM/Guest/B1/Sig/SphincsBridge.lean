/-
  LeanVM.Guest.B1.Sig.SphincsBridge

  The statement's leanSPHINCS verification (`Sphincs.verifyWithKeccak`, `Statement/LeanSphincs.lean`
  at leanVM `ed7d2b9c`) over cells: its message digest, its FORS key, and its walk up the layers,
  stage by stage.
-/

module

public import LeanVM.Guest.B1.Sig.SphincsHash
public import LeanVM.Guest.B1.Sig.SphincsForsComplete

/-!
# leanSPHINCS's verification over cells

The guest computes `Sphincs.verifyWithKeccak` in stages; these lemmas restate each stage over the
cells it reads (`Id` over `keccakF1600`), for soundness and completeness alike:

* `sphincsDigest_cells`: the message digest of a message of two cells and a randomizer cell is the
  low `266` bits of `digestD` of the two calls' `hcell`s at the addresses `digestAdr c`;
* `forsTreeRecover_cells`, `forsRecover_cells`: a FORS tree's two top nodes are `fTops` of its
  opening's cells at the index's cell `eOfNat idx`;
* `sDigestOf`, `sForsKeyOf`, `LayerReaches`, `verifyWithKeccak_iff_stages`: verification holds
  exactly when, from the FORS key's bytes, each layer's one-time key recovers a leaf whose path
  reaches a root, the next layer signing that root's bytes, the top one reaching the key's root.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier LeanVM.Guest LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open HashSig HashSig.OverPermutation
open Sphincs Sphincs.Verification

@[expose] public section

/-! ## Addresses of fields that are numbers -/

/-- Two numbers whose bits do not overlap add as words. -/
theorem eOfNat_add_low {k a b : Nat} (hb : b < 2 ^ k) :
    eOfNat (2 ^ k * a + b) = eOfNat (2 ^ k * a) + eOfNat b := by
  rw [← two_pow_mul_xor hb, eOfNat_xor]

/-- **The address of type `tag`, field `hi` and `lo`, layer and tree zero, is the word of its
packed number.** -/
theorem addressBytes_tweakFields {tag hi lo : Nat} (htag : tag < 32) (hhi : hi < 2 ^ 24)
    (hlo : lo < 2 ^ 32) :
    addressBytes (tweakFields tag 0 hi lo) = cellBytes (eOfNat (2 ^ 56 * tag + (2 ^ 32 * hi + lo))) := by
  rw [addressBytes_eq_cell, tweakNat_tweakFields, addrNat, Nat.mod_eq_of_lt hlo, Nat.mod_eq_of_lt hhi,
    Nat.mod_eq_of_lt htag, Nat.zero_mod, ← eOfNat192_of_lt (by omega)]
  congr 2
  ring

/-- The address of digest call `c`. -/
theorem digestAdr_bytes (c : DigestCall) :
    addressBytes (hashDomainFields (.message c)) = cellBytes (digestAdr c.val) := by
  have hc := c.isLt
  simp only [digestCallCount] at hc
  rw [hashDomainFields, addressBytes_tweakFields (by norm_num) (by omega) (by norm_num), digestAdr,
    word_eq_eOfNat]
  congr 2
  simp [tw, hiMul]
  ring

/-- The address of FORS tree `c`'s leaf `s` at the index `idx`. -/
theorem fLeafAdr_bytes (idx : Index) (c : ForsTreeIndex) (s : ForsLeafIndex) :
    addressBytes (hashDomainFields (.forsLeaf idx c s)) = cellBytes (fLeafAdr (eOfNat idx.val) c.val s.val) := by
  have hi : idx.val < 2 ^ 26 := idx.isLt
  have hc : c.val < 24 := c.isLt
  have hs : s.val < 2 ^ 10 := s.isLt
  rw [hashDomainFields, forsHi, addressBytes_tweakFields (by norm_num) (by omega) (by omega), fLeafAdr,
    word_eq_eOfNat]
  congr 1
  rw [show 2 ^ 56 * 15 + (2 ^ 32 * (c.val + 64 * s.val) + idx.val) =
      2 ^ 56 * 15 + (2 ^ 38 * s.val + (2 ^ 32 * c.val + idx.val)) by ring,
    eOfNat_add_low (by omega), eOfNat_add_low (by omega), eOfNat_add_low (by omega),
    show tw 15 + c.val * hiMul = 2 ^ 56 * 15 + 2 ^ 32 * c.val by simp [tw, hiMul]; ring,
    eOfNat_add_low (by omega)]
  ring

/-- The address of FORS tree `c`'s node above level `l` on the path of leaf `s`. -/
theorem fNodeAdr_bytes (idx : Index) (c : ForsTreeIndex) (l : ForsLevel) (s : Nat) (hs : s < 2 ^ 10) :
    addressBytes (hashDomainFields (.forsNode idx c l ⟨s / 2 ^ (l.val + 1) % 2 ^ forsTreeHeight,
      Nat.mod_lt _ (Nat.two_pow_pos _)⟩)) =
      cellBytes (fNodeAdr (eOfNat idx.val) c.val l.val s) := by
  have hi : idx.val < 2 ^ 26 := idx.isLt
  have hc : c.val < 24 := c.isLt
  have hl : l.val < 10 := l.isLt
  have hd : s / 2 ^ (l.val + 1) < 2 ^ 9 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
    calc s < 2 ^ 10 := hs
      _ ≤ 2 ^ 9 * 2 ^ (l.val + 1) := by rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hmod : s / 2 ^ (l.val + 1) % 2 ^ forsTreeHeight = s >>> (l.val + 1) := by
    rw [Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by simp [forsTreeHeight]; omega)]
  simp only [hashDomainFields, forsHi, hmod]
  rw [Nat.shiftRight_eq_div_pow] at *
  rw [addressBytes_tweakFields (by norm_num) (by omega) (by omega), fNodeAdr, word_eq_eOfNat,
    word_eq_eOfNat, Nat.shiftRight_eq_div_pow]
  congr 1
  set d := s / 2 ^ (l.val + 1)
  rw [show 2 ^ 56 * 17 + (2 ^ 32 * (c.val + 64 * (l.val + 1 + 16 * d)) + idx.val) =
      2 ^ 56 * 17 + (2 ^ 42 * d + (2 ^ 38 * (l.val + 1) + (2 ^ 32 * c.val + idx.val))) by ring,
    eOfNat_add_low (by omega), eOfNat_add_low (by omega), eOfNat_add_low (by omega),
    eOfNat_add_low (by omega),
    show tw 17 + c.val * hiMul = 2 ^ 56 * 17 + 2 ^ 32 * c.val by simp [tw, hiMul]; ring,
    eOfNat_add_low (by omega), show 64 * (l.val + 1) * hiMul = 2 ^ 38 * (l.val + 1) by simp [hiMul]; ring]
  ring

/-! ## The message digest -/

/-- A message's number from its two cells, the first low. -/
theorem toNat_cellPairVal (c d : E) : (cellPairVal c d).toNat = cellNat c + 2 ^ 128 * cellNat d := by
  have h0 := cellNat_lt c
  unfold cellPairVal
  rw [BitVec.toNat_append, toNat_cellVal, toNat_cellVal, Nat.shiftLeft_eq, mul_comm, two_pow_mul_or h0]
  ring

/-- A message's bytes are its two cells', the first low. -/
theorem bytesLE_cellPairVal' (c d : E) :
    littleEndianBytes 32 (cellPairVal c d) = cellBytes c ++ cellBytes d := by
  have h1 := cellNat_lt c
  rw [bytesLE_eq, toNat_cellPairVal, cellBytes_eq_leBytes, cellBytes_eq_leBytes,
    show (2 : Nat) ^ 128 = 256 ^ 16 by norm_num, show 32 = 16 + 16 from rfl,
    leBytes_add_mul _ _ _ _ (by norm_num; omega)]

/-- The payload of a digest call over cells. -/
theorem messageDigestPayload_cells (m0 m1 ρ : E) :
    messageDigestPayload (cellPairVal m0 m1) (cellVal ρ) = [m0, m1, ρ].flatMap cellBytes := by
  show littleEndianBytes 32 (cellPairVal m0 m1) ++ littleEndianBytes 16 (cellVal ρ) = _
  rw [bytesLE_cellPairVal', bytesLE_cellVal]
  simp

/-- Digest call `c` over cells. -/
theorem messageDigestCall_cells (pp m0 m1 ρ : E) (c : DigestCall) :
    messageDigestCall (m := Id) keccakF1600 (cellVal pp) (cellPairVal m0 m1) (cellVal ρ) c =
      cellPairVal (hcell [pp, digestAdr c.val, m0, m1, ρ]).1 (hcell [pp, digestAdr c.val, m0, m1, ρ]).2 := by
  unfold messageDigestCall
  rw [messageDigestPayload_cells]
  exact thPair_cells (thInput_cells (digestAdr_bytes c) _)

/-- The two calls' outputs as one number. -/
theorem digestValue_eq (o : DigestCall → HashOutput) :
    digestValue o = (o 0).toNat + 2 ^ 256 * (o 1).toNat := by
  unfold digestValue
  refine (Fin.sum_univ_two (fun call : Fin 2 => (o call).toNat * 2 ^ (256 * call.val))).trans ?_
  simp only [Fin.val_zero, Fin.val_one, mul_zero, pow_zero, mul_one]
  rw [Nat.mul_comm]
  rfl

/-- **The message digest over cells**: the low `266` bits of the first call's two cells and the
second's first. -/
theorem sphincsDigest_cells (pp m0 m1 ρ : E) :
    Id.run (messageDigest (m := Id) keccakF1600 (cellVal pp) (cellPairVal m0 m1) (cellVal ρ)) =
      BitVec.ofNat messageDigestBits (digestD (hcell [pp, digestAdr 0, m0, m1, ρ]).1
        (hcell [pp, digestAdr 0, m0, m1, ρ]).2 (hcell [pp, digestAdr 1, m0, m1, ρ]).1) := by
  have e : Id.run (messageDigest (m := Id) keccakF1600 (cellVal pp) (cellPairVal m0 m1) (cellVal ρ)) =
      truncateMessageDigest fun c => messageDigestCall (m := Id) keccakF1600 (cellVal pp)
        (cellPairVal m0 m1) (cellVal ρ) c := by
    simp only [messageDigest, sequenceFin_id]
    rfl
  rw [e, truncateMessageDigest, digestValue_eq, messageDigestCall_cells, messageDigestCall_cells,
    show ((1 : DigestCall) : Nat) = 1 from rfl, show ((0 : DigestCall) : Nat) = 0 from rfl]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, messageDigestBits, indexBits, forsTreeCount, forsTreeHeight,
    toNat_cellPairVal, digestD]
  have h1 := cellNat_lt (hcell [pp, digestAdr 1, m0, m1, ρ]).1
  omega

/-! ## FORS -/

/-- A pair of digests that are cells' values, as the bytes of the cells. -/
theorem nodePayload_cells2 (a b : E) : nodePayload (cellVal a) (cellVal b) = [a, b].flatMap cellBytes := by
  show littleEndianBytes 16 (cellVal a) ++ littleEndianBytes 16 (cellVal b) = _
  rw [bytesLE_cellVal, bytesLE_cellVal]
  simp

/-- **A FORS tree's levels over cells.** -/
theorem forsFold_cells (pp : E) (idx : Index) (c : ForsTreeIndex) (leaf : ForsLeafIndex)
    (path : Fin forsTreeHeight → HashSig.Digest) {sib : Nat → E} (hsib : ∀ l (h : l < 10), cellVal (sib l) = path ⟨l, h⟩) :
    ∀ n ≤ 10, ∀ v : E, Id.run (forsFold (m := Id) keccakF1600 (cellVal pp) idx c leaf path n (cellVal v)) =
      cellVal (pFold (fNode pp (eOfNat idx.val) c.val leaf.val sib) n v)
  | 0, _, v => rfl
  | n + 1, hn, v => by
      have ih := forsFold_cells pp idx c leaf path hsib n (by omega) v
      have hs : leaf.val < 2 ^ 10 := leaf.isLt
      have e : Id.run (forsFold (m := Id) keccakF1600 (cellVal pp) idx c leaf path (n + 1) (cellVal v)) =
          forsNodeHash (m := Id) keccakF1600 (cellVal pp) idx c n (leaf.val / 2 ^ (n + 1))
            (if leaf.val.testBit n then
              nodePayload (if h : n < forsTreeHeight then path ⟨n, h⟩ else 0)
                (Id.run (forsFold (m := Id) keccakF1600 (cellVal pp) idx c leaf path n (cellVal v)))
            else nodePayload (Id.run (forsFold (m := Id) keccakF1600 (cellVal pp) idx c leaf path n
                (cellVal v))) (if h : n < forsTreeHeight then path ⟨n, h⟩ else 0)) := rfl
      have hn10 : n < forsTreeHeight := by simp [forsTreeHeight]; omega
      rw [e, ih]
      simp only [hn10, ↓reduceDIte, forsNodeHash]
      rw [← hsib n (by omega)]
      show _ = cellVal (hcell _).1
      have ha := fNodeAdr_bytes idx c ⟨n, hn10⟩ leaf.val hs
      cases hb : leaf.val.testBit n
      · simp only [Bool.false_eq_true, ↓reduceIte, mPair]
        rw [nodePayload_cells2]
        exact th_cells (thInput_cells ha _)
      · simp only [↓reduceIte, mPair]
        rw [nodePayload_cells2]
        exact th_cells (thInput_cells ha _)

/-- **A FORS tree's two top nodes over cells**: the opening's secret and path at cells `secret`,
`sib`, recovered at the index `idx`, are `fTops` at the index's cell. -/
theorem forsTreeRecover_cells (pp : E) (idx : Index) (c : ForsTreeIndex) (leaf : ForsLeafIndex)
    (op : ForsTreeOpening) {secret : E} {sib : Nat → E} (hs : cellVal secret = op.secret)
    (hsib : ∀ l (h : l < 10), cellVal (sib l) = op.path ⟨l, h⟩) :
    Id.run (forsTreeRecover (m := Id) keccakF1600 (cellVal pp) idx c leaf op) =
      (cellVal (fTops pp (eOfNat idx.val) c.val leaf.val secret sib).1,
        cellVal (fTops pp (eOfNat idx.val) c.val leaf.val secret sib).2) := by
  have hl : forsLeafHash (m := Id) keccakF1600 (cellVal pp) idx c leaf op.secret =
      cellVal (fLeaf pp (eOfNat idx.val) c.val leaf.val secret) := by
    rw [forsLeafHash, ← hs, bytesLE_cellVal, show cellBytes secret = [secret].flatMap cellBytes by simp]
    exact th_cells (thInput_cells (fLeafAdr_bytes idx c leaf) _)
  have e : Id.run (forsTreeRecover (m := Id) keccakF1600 (cellVal pp) idx c leaf op) =
      orderTops (leaf.val.testBit (forsTreeHeight - 1))
        (Id.run (forsFold (m := Id) keccakF1600 (cellVal pp) idx c leaf op.path (forsTreeHeight - 1)
          (forsLeafHash (m := Id) keccakF1600 (cellVal pp) idx c leaf op.secret)))
        (op.path forsTopLevel) := rfl
  rw [e, hl, show forsTreeHeight - 1 = 9 from rfl, forsFold_cells pp idx c leaf op.path hsib 9 (by norm_num), fTops,
    show op.path forsTopLevel = cellVal (sib 9) from (hsib 9 (by norm_num)).symm]
  simp only [orderTops, mPair, forsTreeHeight]
  split <;> rfl

/-- **The FORS key over cells**: tree `c`'s opening at the cells `secretOf c`, `sibOf c`. -/
theorem forsRecover_cells (pp : E) (idx : Index) (leaves : ForsTreeIndex → ForsLeafIndex)
    (op : ForsTreeIndex → ForsTreeOpening) {secretOf : Nat → E} {sibOf : Nat → Nat → E}
    (hs : ∀ c : ForsTreeIndex, cellVal (secretOf c.val) = (op c).secret)
    (hsib : ∀ (c : ForsTreeIndex) l (h : l < 10), cellVal (sibOf c.val l) = (op c).path ⟨l, h⟩) :
    Id.run (forsRecover (m := Id) keccakF1600 (cellVal pp) idx leaves op) = fun c =>
      (cellVal (fTops pp (eOfNat idx.val) c.val (leaves c).val (secretOf c.val) (sibOf c.val)).1,
        cellVal (fTops pp (eOfNat idx.val) c.val (leaves c).val (secretOf c.val) (sibOf c.val)).2) := by
  unfold forsRecover
  rw [sequenceFin_id]
  funext c
  exact forsTreeRecover_cells pp idx c (leaves c) (op c) (hs c) (hsib c)

/-! ## Verification by stages -/

/-- The message digest a signature's randomizer gives. -/
def sDigestOf (pk : PublicKey) (m : Message) (sig : Sphincs.Signature) : MessageDigest :=
  Id.run (messageDigest (m := Id) keccakF1600 pk.parameter m sig.randomizer)

/-- The FORS key a signature's openings recover at its digest. -/
def sForsKeyOf (pk : PublicKey) (m : Message) (sig : Sphincs.Signature) : ForsKey :=
  Id.run (forsRecover (m := Id) keccakF1600 pk.parameter (digestIndex (sDigestOf pk m sig))
    (digestForsLeaves (sDigestOf pk m sig)) sig.forsOpening)

/-- **The root layer `l` reaches from `msg`**: its one-time key `K_l(idx)` recovers a leaf from the
message `msg` and the layer's counter and chain values, and the layer's path folds it to the root;
nothing when the counter does not encode `msg`. -/
def layerRoot (P : PublicParameter) (idx : Index) (sig : Sphincs.Signature) (l : Layer)
    (msg : HashInput) : Option HashSig.Digest :=
  match Id.run (otsLeaf (m := Id) keccakF1600 P l (treeOfIndex l idx) (leafOfIndex l idx) msg
      (sig.layers l).counter (sig.layers l).chainValues) with
  | none => none
  | some v => some (Id.run (treeFold (m := Id) keccakF1600 P l (treeOfIndex l idx) (leafOfIndex l idx)
      (layerPath sig l) (layerHeight l) v))

/-- **Layer `l` of the signature reaches `root` from `msg`.** -/
def LayerReaches (P : PublicParameter) (idx : Index) (sig : Sphincs.Signature) (l : Layer)
    (msg : HashInput) (root : HashSig.Digest) : Prop :=
  layerRoot P idx sig l msg = some root

/-- A layer reaches `root`: its one-time leaf is recovered, and its path folds the leaf to `root`. -/
theorem layerReaches_iff (P : PublicParameter) (idx : Index) (sig : Sphincs.Signature) (l : Layer)
    (msg : HashInput) (root : HashSig.Digest) :
    LayerReaches P idx sig l msg root ↔
      ∃ v, Id.run (otsLeaf (m := Id) keccakF1600 P l (treeOfIndex l idx) (leafOfIndex l idx) msg
          (sig.layers l).counter (sig.layers l).chainValues) = some v ∧
        Id.run (treeFold (m := Id) keccakF1600 P l (treeOfIndex l idx) (leafOfIndex l idx)
          (layerPath sig l) (layerHeight l) v) = root := by
  unfold LayerReaches layerRoot
  split <;> simp_all

/-- One layer of the walk up, in `Id`. -/
theorem verifyLayers_succ_eq (P : PublicParameter) (idx : Index) (sig : Sphincs.Signature) (n : Nat)
    (hn : n < layerCount) (msg : HashInput) :
    Id.run (verifyLayers (m := Id) keccakF1600 P idx sig (n + 1) msg) =
      (layerRoot P idx sig ⟨layerCount - 1 - n, by omega⟩ msg).bind fun r =>
        if n = 0 then some r else Id.run (verifyLayers (m := Id) keccakF1600 P idx sig n (littleEndianBytes 16 r)) := by
  rw [verifyLayers.eq_2]
  simp only [hn, ↓reduceDIte, Id.run_bind, layerRoot]
  generalize Id.run (otsLeaf (m := Id) keccakF1600 P ⟨layerCount - 1 - n, by omega⟩
    (treeOfIndex ⟨layerCount - 1 - n, by omega⟩ idx) (leafOfIndex ⟨layerCount - 1 - n, by omega⟩ idx) msg
    (sig.layers ⟨layerCount - 1 - n, by omega⟩).counter (sig.layers ⟨layerCount - 1 - n, by omega⟩).chainValues) = o
  rcases o with _ | v
  · rfl
  · simp only [Option.bind_some, Id.run_bind]
    split <;> rfl

/-- The walk up the three layers, in `Id`. -/
theorem verifyLayers_three (P : PublicParameter) (idx : Index) (sig : Sphincs.Signature)
    (msg : HashInput) :
    Id.run (verifyLayers (m := Id) keccakF1600 P idx sig layerCount msg) =
      (layerRoot P idx sig 0 msg).bind fun r0 => (layerRoot P idx sig 1 (littleEndianBytes 16 r0)).bind
        fun r1 => layerRoot P idx sig 2 (littleEndianBytes 16 r1) := by
  conv_lhs => rw [show layerCount = 2 + 1 from rfl]
  rw [verifyLayers_succ_eq P idx sig 2 (by decide)]
  simp only [show (2 : Nat) ≠ 0 by decide, ↓reduceIte,
    verifyLayers_succ_eq P idx sig 1 (by decide), show (1 : Nat) ≠ 0 by decide,
    verifyLayers_succ_eq P idx sig 0 (by decide), show (⟨layerCount - 1 - 2, by decide⟩ : Layer) = 0 from rfl,
    show (⟨layerCount - 1 - 1, by decide⟩ : Layer) = 1 from rfl,
    show (⟨layerCount - 1 - 0, by decide⟩ : Layer) = 2 from rfl]
  simp only [Option.bind_fun_some]

/-- The walk reaches `root` exactly when each layer reaches the next one's message. -/
theorem verifyLayers_some (P : PublicParameter) (idx : Index) (sig : Sphincs.Signature)
    (msg : HashInput) (root : HashSig.Digest) :
    Id.run (verifyLayers (m := Id) keccakF1600 P idx sig layerCount msg) = some root ↔
      ∃ r0 r1, LayerReaches P idx sig 0 msg r0 ∧ LayerReaches P idx sig 1 (littleEndianBytes 16 r0) r1 ∧
        LayerReaches P idx sig 2 (littleEndianBytes 16 r1) root := by
  rw [verifyLayers_three]
  simp only [LayerReaches, Option.bind_eq_some_iff]
  constructor
  · rintro ⟨a, h0, b, h1, h2⟩
    exact ⟨a, b, h0, h1, h2⟩
  · rintro ⟨a, b, h0, h1, h2⟩
    exact ⟨a, h0, b, h1, h2⟩

/-- **leanSPHINCS verification by stages**: a signature verifies exactly when, from the bytes of
the FORS key its openings recover at its digest, the bottom layer reaches a root `r0`, the middle
one from `r0`'s bytes a root `r1`, and the top one from `r1`'s bytes the key's root. -/
theorem verifyWithKeccak_iff_stages (pk : PublicKey) (m : Message) (sig : Sphincs.Signature) :
    Sphincs.verifyWithKeccak pk m sig = true ↔
      ∃ r0 r1, LayerReaches pk.parameter (digestIndex (sDigestOf pk m sig)) sig 0
          (forsKeyPayload (sForsKeyOf pk m sig)) r0 ∧
        LayerReaches pk.parameter (digestIndex (sDigestOf pk m sig)) sig 1 (littleEndianBytes 16 r0) r1 ∧
        LayerReaches pk.parameter (digestIndex (sDigestOf pk m sig)) sig 2 (littleEndianBytes 16 r1)
          pk.root := by
  rw [← verifyLayers_some]
  simp only [sDigestOf, sForsKeyOf, Sphincs.verifyWithKeccak, Verification.verify, Id.run_bind]
  split <;> simp_all

end
end LeanVM.Guest.B1.Sig
