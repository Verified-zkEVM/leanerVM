/-
  LeanVM.Guest.B1.Sig.SphincsKeyComplete

  For `verify_sig_lean_sphincs`'s completeness: the forest key the Spec recovers from a signature's
  openings is the frame's sixteen top nodes, and what the verification checks fixes the root.
-/

module

public import LeanVM.Guest.B1.Sig.SphincsStagesComplete
public import LeanVM.Guest.B1.Sig.SphincsSound
public import Sphincs.WithHash
public import LeanVM.Guest.WithHash

/-!
# The forest key and the root

* `sKey_eq`: the forest key `forestRecover` reaches from the signature's openings, under the
  digest of the cells' integers, is the frame's top nodes;
* `SRoot_unique`: two signatures agreeing on what verification reads reach the same root.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier (eOfNat gen)
open Sphincs Sphincs.Concrete

@[expose] public section

attribute [local irreducible] sCoords kMsg codewordT merkleT fkArms foldArms

variable {rd : Reader}

/-- **The forest key the Spec recovers is the frame's top nodes**: the coordinates' facts and
their hints the signature's openings, under the digest of the cells' integers. -/
theorem sKey_eq {σ : Val} (hpre : SPre rd σ)
    (hcf : ∀ c < 8, CoordFacts σ c (cSt c).1 (cSt c).2.1 (cSt c).2.2) (sig : Sphincs.Signature)
    {N17 N18 : Nat} (hN17 : N17 < 2 ^ 128) (hidx : sIdx σ = N18 % 2 ^ 26) (E1 E2 : Nat → E)
    (hpost : ∀ k < 8, CoordPost (E1 k) (E2 k) k (cSt k).1 (cSt k).2.1 (cSt k).2.2 (sH sig N17 N18 k) σ) :
    @forestRecoverWithHash Id _ ⟨Node.keccakBits⟩ (spp (σ sPP))
      (digestIndex (BitVec.ofNat messageDigestBits (N17 + 2 ^ 128 * N18)))
      (digestMarks (BitVec.ofNat messageDigestBits (N17 + 2 ^ 128 * N18))) sig.forest =
      fun c => (sv (sT σ (2 * c.val)), sv (sT σ (2 * c.val + 1))) := by
  rw [forestRecover_id]
  funext c
  have hc8 : c.val < 8 := c.isLt
  have f := hcf c.val hc8
  have hP := hpost c.val hc8
  have hp := getD_pairs (fun k => (cCoord (0 + k)).2.2.2.2.1) (fun k => (cCoord (0 + k)).2.2.2.2.2)
    (.n 0) 8 c.val hc8
  have e := sCoords_tops 8 0
  have t1 : sT σ (2 * c.val) = σ (cCoord c.val).2.2.2.2.1 := by
    unfold sT
    rw [show sCs = sCoords 8 0 (cSt 0).1 (cSt 0).2.1 (cSt 0).2.2 from rfl, e, hp.1, Nat.zero_add]
  have t2 : sT σ (2 * c.val + 1) = σ (cCoord c.val).2.2.2.2.2 := by
    unfold sT
    rw [show sCs = sCoords 8 0 (cSt 0).1 (cSt 0).2.1 (cSt 0).2.2 from rfl, e, hp.2, Nat.zero_add]
  rw [t1, t2]
  have hop : coordOpening σ c.val (cSt c.val).1 (cSt c.val).2.1 (cSt c.val).2.2 = sig.forest c := by
    rw [coordOpening_eq (dS_lt _ _) (dT_lt _ _) (dA_lt _ _) (dT_lt _ _) (dA_lt _ _) hP]
    congr 1
    exact Fin.ext (Nat.mod_eq_of_lt hc8)
  rw [← hop]
  obtain ⟨m1, -, -⟩ := digestMarks_ofNat (c1 := N18) hN17 c 0
  obtain ⟨-, m2, m3⟩ := digestMarks_ofNat (c1 := N18) hN17 c 0
  obtain ⟨-, m4, m5⟩ := digestMarks_ofNat (c1 := N18) hN17 c 1
  obtain ⟨h0, -, hs0, hs1, -⟩ := hP
  obtain ⟨a0, -, t0', -⟩ := hs0
  obtain ⟨a1, -, t1', -⟩ := hs1
  refine coordKey_eq hpre f ?_ ?_ ?_ ?_ ?_ ?_
  · rw [m1, coordS, logG_eq (dS_lt N18 c.val) (by norm_num) h0]; rfl
  · rw [m2, subA, logG_eq (dA_lt N18 (2 * c.val)) (by norm_num) a0]; rfl
  · rw [m4, subA, logG_eq (dA_lt N18 (2 * c.val + 1)) (by norm_num) a1]; rfl
  · rw [m3, subT, logG_eq (dT_lt N17 (2 * c.val)) (by norm_num) t0']; rfl
  · rw [m5, subT, logG_eq (dT_lt N17 (2 * c.val + 1)) (by norm_num) t1']; rfl
  · rw [digestIndex_ofNat hN17, hidx]

/-- **What verification reads fixes the root.** -/
theorem SRoot_unique {pp : PublicParameter} {m : Sphincs.Message}
    {sig sig' : Sphincs.Signature} {r r' : Sphincs.Digest} (h : SRoot pp m sig r) (h' : SRoot pp m sig' r')
    (hr : sig'.randomness = sig.randomness) (hf : sig'.forest = sig.forest)
    (hc : sig'.counter = sig.counter) (hv : sig'.chainValues = sig.chainValues)
    (hl : sig'.path = sig.path) : r' = r := by
  obtain ⟨leaf, h1, h2⟩ := h
  obtain ⟨leaf', h1', h2'⟩ := h'
  rw [hr, hf, hc, hv] at h1'
  have e : leaf' = leaf := Option.some.inj (h1'.symm.trans h1)
  have hp : signaturePath sig' = signaturePath sig := by
    funext l
    unfold signaturePath
    rw [hl]
  rw [hr, e, hp] at h2'
  rw [← h2', h2]

end
end LeanVM.Guest.B1.Sig
