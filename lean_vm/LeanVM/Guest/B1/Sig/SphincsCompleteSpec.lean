/-
  LeanVM.Guest.B1.Sig.SphincsCompleteSpec

  The completeness statements of leanSPHINCS's guest functions at leanVM `c4f4bc92`: `sp_wots`
  (`Data.core20`), a leaf, and `verify_sig_lean_sphincs` (`Data.core21`), which calls it three
  times, in the forms `main`'s completeness consumes.
-/

module

public import LeanVM.Guest.B1.Sig.Interface
public import LeanVM.Guest.Memory.Regions

/-!
# leanSPHINCS's completeness statements

`sp_wots(pp, at, encoding)` (`lean_ethereum.py:3816-3847`) recovers the leaf of the one-time key
at the address `at`, whose encoding digest is `encoding`; `verify_sig_lean_sphincs(signer,
byte_bits)` (`lean_ethereum.py:3881-3968`) calls it once per layer. So `verify_sig_lean_sphincs`'s
body holds only under a call relation that holds of its three calls, and its completeness is
stated under any call relation holding of every honest call of `sp_wots` (`SpWotsCalls`).

* `keyAddressCell layer tree leaf`: the address cell of the one-time key `K = (layer, tree, leaf)`
  with type `0`, its leaf in `lo` and its layer and tree in their fields (`OtsKey::tweak`,
  `wots.rs:36-38`): the guest's `at`, to which a chain step, the leaf hash and the encoding add
  their constants.
* `wotsLeafOf parameter layer tree leaf digest values`: the leaf the chain values `values` recover
  at the digits of `digest` (`Sphincs.Verification.otsLeaf` past its encoding).
* `sp_wots_complete_Spec`: for a digest of digit sum `T` (`TargetSum.Valid`), on a memory of at
  least `64` words, the body holds of some valuation whose arguments are the parameter's cell, the
  key's address and the digest's cell, under any call relation, returning the leaf's cell, for
  any chain values (they are hinted).
* `verify_sig_lean_sphincs_complete_loads_Spec`: for a claim held at `p` in its canonical cells, a
  signature that verifies it, the byte table at `bb` and a memory of at least `256` words, under
  any call relation holding of every honest `sp_wots` call, the body holds of some valuation whose
  arguments are `p` and `bb`, and its path loads only the claim's four words and the byte table.
* `SphincsCompleteSpecs`: both, as `main`'s completeness takes them.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open HashSig HashSig.OverPermutation

@[expose] public section

/-! ## The one-time key's values -/

/-- **The address cell of the one-time key `(layer, tree, leaf)`**, type `0`: limb `0` holds the leaf
(`lo`), limb `1` the layer and, from bit `8`, the tree (`addressBytes`, `TweakFields.at`). -/
def keyAddressCell (layer : Sphincs.Layer) (tree : Sphincs.TreeIndex) (leaf : Sphincs.TreeLeafIndex) :
    E :=
  cellOf128 (BitVec.ofNat 128 (leaf.val + 2 ^ 64 * (layer.val + 2 ^ 8 * tree.val)))

/-- **The leaf `values` recover at the digits of `digest`**: every chain walked from its digit to
its end, the ends hashed (`otsLeaf` past its encoding, over Keccak-f[1600]). -/
def wotsLeafOf (parameter : PublicParameter) (layer : Sphincs.Layer) (tree : Sphincs.TreeIndex)
    (leaf : Sphincs.TreeLeafIndex) (digest : Digest) (values : Sphincs.ChainIndex → Digest) :
    Digest :=
  Id.run do
    let ends ← sequenceFin fun chainIndex =>
      Sphincs.Verification.recoverChain (m := Id) keccakF1600 parameter layer tree leaf chainIndex
        (digestDigits digest chainIndex) (values chainIndex)
    Sphincs.Verification.leafHash (m := Id) keccakF1600 parameter layer tree leaf ends

/-! ## The functions, found -/

theorem sp_wots_params : Data.core20.params = [.n 0, .n 1, .n 2] := rfl

theorem verify_sig_lean_sphincs_params : Data.core21.params = [.n 0, .n 1] := rfl

theorem find_sp_wots : coreProgram.find? "sp_wots" = some Data.core20 :=
  Program.find?_of_indexOf? (j := 20) (by decide +kernel) rfl

/-! ## The statements -/

/-- **`sp_wots` is complete**: for a digest whose digits reach the target sum and any chain values,
on a memory of at least `64` words (its digit groups' range checks), its body holds, under any call
relation (it calls nothing), of some valuation whose arguments are the parameter's cell, the key's
address cell and the digest's cell, returning the cell of the leaf the values recover. -/
def sp_wots_complete_Spec : Prop :=
  ∀ (C : CallRel) (rd : Reader) (parameter : PublicParameter) (layer : Sphincs.Layer)
    (tree : Sphincs.TreeIndex) (leaf : Sphincs.TreeLeafIndex) (digest : Digest)
    (values : Sphincs.ChainIndex → Digest), MemOK rd 64 →
    Sphincs.TargetSum.Valid (digestDigits digest) →
      ∃ σ : Val, σ (.n 0) = cellOf128 parameter ∧ σ (.n 1) = keyAddressCell layer tree leaf ∧
        σ (.n 2) = cellOf128 digest ∧
        Stmt.HoldsList C rd σ Data.core20.body False
          (fun rs => rs = [cellOf128 (wotsLeafOf parameter layer tree leaf digest values)])

/-- **The call relation holds of every honest call of `sp_wots`**: on the parameter's cell, a key's
address cell and the cell of a digest of digit sum `T`, returning the leaf of any chain values. -/
def SpWotsCalls (C : CallRel) : Prop :=
  ∀ (parameter : PublicParameter) (layer : Sphincs.Layer) (tree : Sphincs.TreeIndex)
    (leaf : Sphincs.TreeLeafIndex) (digest : Digest) (values : Sphincs.ChainIndex → Digest),
    Sphincs.TargetSum.Valid (digestDigits digest) →
      C "sp_wots" [cellOf128 parameter, keyAddressCell layer tree leaf, cellOf128 digest]
        [cellOf128 (wotsLeafOf parameter layer tree leaf digest values)]

/-- **`verify_sig_lean_sphincs` is complete, loading the claim and the byte table**: for a claim held
at `p` in its canonical cells and a signature that verifies it, on a memory of at least `256` words
with the byte table at `bb`, under any call relation holding of every honest `sp_wots` call, its
body holds of some valuation whose arguments are `p` and `bb`, and whose path loads only from
`p·g^k`, `k < 4` (the claim), or `bb·g^v`, `v < 256` (the byte table). -/
def verify_sig_lean_sphincs_complete_loads_Spec : Prop :=
  ∀ (C : CallRel) (rd : Reader) (p bb : E) (pk : HashSig.PublicKey) (m : HashSig.Message)
    (sig : Sphincs.Signature), SpWotsCalls C → MemOK rd 256 → ByteBits rd bb →
    ClaimAt rd p (cellOf128 pk.root) (cellOf128 pk.parameter) (cellOf128 (m.extractLsb' 0 128))
      (cellOf128 (m.extractLsb' 128 128)) →
    Sphincs.verifyWithKeccak pk m sig = true →
      ∃ σ : Val, σ (.n 0) = p ∧ σ (.n 1) = bb ∧
        Stmt.HoldsList C rd σ Data.core21.body False (fun rs => rs = []) ∧
        ∀ es vs, walk σ Data.core21.body = .ret es vs → ∀ A ∈ loadAddrs σ es,
          (∃ k < 4, A = p.limb 0 * addressOfIndex k) ∨ ∃ v < 256, A = bb.limb 0 * addressOfIndex v

/-- **leanSPHINCS's guest functions are complete**: `sp_wots` and `verify_sig_lean_sphincs`, as
`main`'s completeness takes them. -/
structure SphincsCompleteSpecs : Prop where
  sp_wots : sp_wots_complete_Spec
  verify : verify_sig_lean_sphincs_complete_loads_Spec

end
end LeanVM.Guest.B1.Sig
