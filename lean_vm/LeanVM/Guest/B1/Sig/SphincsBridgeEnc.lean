/-
  LeanVM.Guest.B1.Sig.SphincsBridgeEnc

  The statement's leanSPHINCS encoding (`Sphincs.Verification.encode`, `otsLeaf`, over
  Keccak-f[1600] in `Id`) over the guest's cells: the encoding digest of a message of cells and a
  counter is the first cell of the Keccak message the guest hashes, and a one-time leaf that
  exists is `wotsLeafOf` at a digest of valid digits.
-/

module

public import LeanVM.Guest.B1.Sig.SphincsBridgePath

/-!
# The encoding over cells

* `th_bytes`: a tweakable hash is the first cell of the digest of its input;
* `encTh_cells`: the encoding's hash of the cells `cs` and the counter `ctr` is the first cell of the
  digest of `P`, the key's address plus `TW_ENC`, the cells and the counter's word, cut after the
  counter's four bytes (the guest's `kMsg` of `len = 16 (|cs| + 2) + 4`);
* `otsLeaf_some`: a one-time leaf that exists is `wotsLeafOf` at the encoding's digest, whose digits
  reach the target sum;
* `forsKeyPayload_cells`, `bytes16_cell`: the bottom key's message (the FORS key) and an upper one's
  (the root below) as bytes of cells.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier (eOfNat kToNat)
open HashSig HashSig.OverPermutation

@[expose] public section

/-- A tweakable hash is the first cell of the digest of its input. -/
theorem th_bytes (P : PublicParameter) (fields : TweakFields) (payload : HashInput) :
    th (m := Id) keccakF1600 P fields payload = cellVal (digestHalves (keccak256 (thInput P fields payload))).1 := by
  show truncateHash (keccakHash (m := Id) keccakF1600 (thInput P fields payload)) = _
  rw [keccakHash_keccakF1600, truncateHash_keccakBits]

theorem take_flatMap_cellBytes (cs : List E) (x : E) (k : Nat) (hk : k ≤ 16) :
    (cellsBytes (cs ++ [x])).take (16 * cs.length + k) = cs.flatMap cellBytes ++ (cellBytes x).take k := by
  rw [cellsBytes_eq_flatMap, List.flatMap_append, List.take_append]
  have hl : (cs.flatMap cellBytes).length = 16 * cs.length := by
    induction cs with
    | nil => rfl
    | cons c cs ih => simp only [List.flatMap_cons, List.length_append, length_cellBytes, ih, List.length_cons]; ring
  rw [hl, List.take_of_length_le (by omega), show 16 * cs.length + k - 16 * cs.length = k by omega]
  simp

theorem counter_bytes (ctr : Sphincs.EncodingCounter) :
    littleEndianBytes 4 ctr = (cellBytes (eOfNat ctr.toNat)).take 4 := by
  have h : ctr.toNat < 2 ^ 64 := lt_of_lt_of_le ctr.isLt (by decide)
  rw [cellBytes_eOfNat h, sphincs_bytesLE_eq 4 ctr, ← leBytes_append ctr.toNat 4 12]
  exact (List.take_left' (by simp [leBytes])).symm

/-- **The encoding's hash over cells.** -/
theorem encTh_cells (pp : E) (layer : Sphincs.Layer) (tree : Sphincs.TreeIndex) (leaf : Sphincs.TreeLeafIndex)
    (cs : List E) (ctr : Sphincs.EncodingCounter) :
    th (m := Id) keccakF1600 (cellVal pp) (Sphincs.hashDomainFields (.encoding layer tree leaf))
        (cs.flatMap cellBytes ++ littleEndianBytes 4 ctr) =
      cellVal (digestHalves (keccak256 ((cellsBytes ([pp, keyAddressCell layer tree leaf + word (tw 4) 0 0] ++ cs ++
        [eOfNat ctr.toNat])).take (16 * (cs.length + 2) + 4)))).1 := by
  rw [th_bytes]
  congr 4
  have ha : addressBytes (Sphincs.hashDomainFields (.encoding layer tree leaf)) =
      cellBytes (keyAddressCell layer tree leaf + word (tw 4) 0 0) := by
    simp only [Sphincs.hashDomainFields]
    rw [encConst_eq]
    exact keyAddress_bytes (by norm_num) (by norm_num) (by norm_num)
  rw [show 16 * (cs.length + 2) + 4 = 16 * ([pp, keyAddressCell layer tree leaf + word (tw 4) 0 0] ++ cs).length + 4 by
    simp only [List.length_append, List.length_cons, List.length_nil]; ring,
    take_flatMap_cellBytes _ _ 4 (by norm_num), thInput, bytesLE_cellVal, ha, counter_bytes]
  simp [List.append_assoc]

/-- `otsLeaf` in `Id`: the leaf of the chains recovered at the encoding, if it exists. -/
theorem sOtsLeaf_id (P : PublicParameter) (layer : Sphincs.Layer) (tree : Sphincs.TreeIndex)
    (leaf : Sphincs.TreeLeafIndex) (msg : HashInput) (ctr : Sphincs.EncodingCounter)
    (values : Sphincs.ChainIndex → Digest) :
    Id.run (Sphincs.Verification.otsLeaf keccakF1600 P layer tree leaf msg ctr values) =
      (Sphincs.TargetSum.decodeDigest (th (m := Id) keccakF1600 P
        (Sphincs.hashDomainFields (.encoding layer tree leaf)) (msg ++ littleEndianBytes 4 ctr))).map fun enc =>
        Sphincs.Verification.leafHash (m := Id) keccakF1600 P layer tree leaf fun i =>
          Sphincs.Verification.recoverChain (m := Id) keccakF1600 P layer tree leaf i (enc i) (values i) := by
  rw [Sphincs.Verification.otsLeaf.eq_def]
  simp only [bind, pure]
  split
  next enc h =>
    have h' : Sphincs.TargetSum.decodeDigest (th (m := Id) keccakF1600 P
        (Sphincs.hashDomainFields (.encoding layer tree leaf)) (msg ++ littleEndianBytes 4 ctr)) = some enc := h
    rw [h', sequenceFin_id]; rfl
  next h =>
    cases h' : Sphincs.TargetSum.decodeDigest (th (m := Id) keccakF1600 P
        (Sphincs.hashDomainFields (.encoding layer tree leaf)) (msg ++ littleEndianBytes 4 ctr)) with
    | none => rfl
    | some enc => exact absurd h' (h enc)

/-- **A one-time leaf that exists** is `wotsLeafOf` at the encoding's digest, whose digits reach the
target sum. -/
theorem otsLeaf_some {P : PublicParameter} {layer : Sphincs.Layer} {tree : Sphincs.TreeIndex}
    {leaf : Sphincs.TreeLeafIndex} {msg : HashInput} {ctr : Sphincs.EncodingCounter}
    {values : Sphincs.ChainIndex → Digest} {v : Digest}
    (h : Id.run (Sphincs.Verification.otsLeaf keccakF1600 P layer tree leaf msg ctr values) = some v) :
    Sphincs.TargetSum.Valid (digestDigits (th (m := Id) keccakF1600 P
        (Sphincs.hashDomainFields (.encoding layer tree leaf)) (msg ++ littleEndianBytes 4 ctr))) ∧
      v = wotsLeafOf P layer tree leaf (th (m := Id) keccakF1600 P
        (Sphincs.hashDomainFields (.encoding layer tree leaf)) (msg ++ littleEndianBytes 4 ctr)) values := by
  rw [sOtsLeaf_id] at h
  generalize th (m := Id) keccakF1600 P (Sphincs.hashDomainFields (.encoding layer tree leaf))
    (msg ++ littleEndianBytes 4 ctr) = d at h ⊢
  by_cases hv : Sphincs.TargetSum.Valid (digestDigits d)
  · rw [show Sphincs.TargetSum.decodeDigest d = some (digestDigits d) from by
      unfold Sphincs.TargetSum.decodeDigest; split <;> simp_all, Option.map_some,
      Option.some.injEq] at h
    exact ⟨hv, by rw [wotsLeafOf_eq]; exact h.symm⟩
  · rw [show Sphincs.TargetSum.decodeDigest d = none from by
      unfold Sphincs.TargetSum.decodeDigest; split <;> simp_all] at h
    exact absurd h (by simp)

theorem payload_aux (tops : Nat → E × E) : ∀ l : List Nat,
    (l.map (fun c => ((cellVal (tops c).1 : Digest), (cellVal (tops c).2 : Digest)))).flatMap
        (fun pair : Digest × Digest => nodePayload pair.1 pair.2) =
      (l.flatMap fun c => [(tops c).1, (tops c).2]).flatMap cellBytes
  | [] => rfl
  | c :: l => by
      have ih := payload_aux tops l
      show nodePayload (cellVal (tops c).1) (cellVal (tops c).2) ++
        (l.map (fun c => ((cellVal (tops c).1 : Digest), (cellVal (tops c).2 : Digest)))).flatMap
          (fun pair : Digest × Digest => nodePayload pair.1 pair.2) = _
      rw [ih]
      simp [nodePayload, bytesLE_cellVal]

/-- The FORS key's message over cells. -/
theorem forsKeyPayload_cells (tops : Nat → E × E) :
    Sphincs.Verification.forsKeyPayload (fun c => (cellVal (tops c.val).1, cellVal (tops c.val).2)) =
      ((List.range 24).flatMap fun c => [(tops c).1, (tops c).2]).flatMap cellBytes := by
  unfold Sphincs.Verification.forsKeyPayload
  have e : (List.ofFn fun c : Sphincs.ForsTreeIndex => ((cellVal (tops c.val).1 : Digest),
      (cellVal (tops c.val).2 : Digest))) =
      (List.range 24).map (fun c => ((cellVal (tops c).1 : Digest), (cellVal (tops c).2 : Digest))) :=
    ofFn_val_eq Sphincs.forsTreeCount (fun c => ((cellVal (tops c).1 : Digest), (cellVal (tops c).2 : Digest)))
  erw [e]
  exact payload_aux tops _

/-- A digest's 16 bytes as a cell's. -/
theorem bytes16_cell (x : E) : littleEndianBytes 16 (cellVal x) = [x].flatMap cellBytes := by
  simp [bytesLE_cellVal]

end
end LeanVM.Guest.B1.Sig
