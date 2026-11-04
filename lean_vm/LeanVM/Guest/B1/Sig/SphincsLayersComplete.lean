/-
  LeanVM.Guest.B1.Sig.SphincsLayersComplete

  A layer of `verify_sig_lean_sphincs`'s hypertree past its encoding (`sp_wots`'s call and
  `sp_path`, `lean_ethereum.py:3740-3751` at leanVM `542b0353`) is complete under any call relation
  holding of every honest `sp_wots` call: the one-time leaf the statement's `otsLeaf` gives, its
  tree's root the statement's `treeFold`.
-/

module

public import LeanVM.Guest.B1.Sig.SphincsBridgeEnc

/-!
# A layer's tail, complete

* `call_complete`: a call returning one fresh value completes when the relation holds of it;
* `encCell`: the cell the guest's encoding `KECCAK` gives for the message cells `cs` and counter;
* `layerTail_complete`: `sp_wots`'s call at the key's address, on the encoding cell, then the path
  of the key's leaf: the root is the statement's tree fold of the leaf `otsLeaf` gives.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier (eOfNat kToNat)
open HashSig HashSig.OverPermutation

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-- **A call returning one fresh value completes** when the call relation holds of it. -/
theorem call_complete {f : String} {args : List V} {d : Nat} (σ : Val) (w : E) (hargs : NumBelow d args)
    (hC : C f (args.map σ) [w]) :
    Completes C rd d (d + 1) [.call f args [.n d]] σ (fun σ' => σ' (.n d) = w) := by
  refine ⟨Function.update σ (.n d) w, fun v hv => Function.update_of_ne (hv d le_rfl (by omega)) _ _,
    Function.update_self .., fun next kret hn => ⟨?_, hn⟩⟩
  have : args.map (Function.update σ (.n d) w) = args.map σ := List.map_congr_left fun v hv => by
    obtain ⟨j, hj, rfl⟩ := hargs v hv
    exact Function.update_of_ne (by simp; omega) _ _
  rw [this]
  simpa using hC

/-- The cell the guest's encoding gives: the digest of `P`, the key's address plus `TW_ENC`, the
message cells and the counter's word, cut after the counter's four bytes. -/
def encCell (pp : E) (layer : Sphincs.Layer) (tree : Sphincs.TreeIndex) (leaf : Sphincs.TreeLeafIndex)
    (cs : List E) (ctr : Sphincs.EncodingCounter) : E :=
  (digestHalves (keccak256 ((cellsBytes ([pp, keyAddressCell layer tree leaf + word (tw 4) 0 0] ++ cs ++
    [eOfNat ctr.toNat])).take (16 * (cs.length + 2) + 4)))).1

theorem canon_encCell (pp : E) (layer tree leaf) (cs : List E) (ctr : Sphincs.EncodingCounter) :
    IsCanonical128 (encCell pp layer tree leaf cs ctr) := by
  simp [IsCanonical128, encCell, digestHalves]

/-- **A layer's tail completes**: `sp_wots` called at the key's address on the encoding cell
returns the leaf `otsLeaf` gives, and the path from it reaches the statement's tree fold. -/
theorem layerTail_complete (hC : SpWotsCalls C) {P : PublicParameter} {layer : Sphincs.Layer}
    {tree : Sphincs.TreeIndex} {leaf : Sphincs.TreeLeafIndex} {cs : List E} {ctr : Sphincs.EncodingCounter}
    {values : Sphincs.ChainIndex → Digest} {v : Digest}
    (hots : Id.run (Sphincs.Verification.otsLeaf keccakF1600 P layer tree leaf (cs.flatMap cellBytes) ctr values) =
      some v)
    {path : Nat → Digest} {m : Nat} (hh : m + 1 ≤ 10) (hleaf : leaf.val < 2 ^ (m + 1))
    {adr lane : V} {off o d : Nat} (hoff : off ≤ 16) (hd : 1225 ≤ d) (ho : o < d) (hadr : NBv d adr)
    (hlnb : NBv d lane) (σ : Val) (hp : PadOK σ sPad) (hpp : σ sPP = cellOf128 P)
    (hadrv : σ adr = keyAddressCell layer tree leaf)
    (henc : σ (.n o) = encCell (cellOf128 P) layer tree leaf cs ctr) (hlane : σ lane = laneCell layer tree)
    (hbits : ∀ j < m + 1, σ (sBit (off + j)) = if leaf.val.testBit j then 1 else 0)
    (hvals : ∀ j, j + 1 < m + 1 → σ (sVal (off + j + 1)) = eOfNat (leaf.val >>> (j + 1))) :
    Completes C rd d (d + 1 + 21 * (m + 1) - 1)
      ([sWotsCall adr (.n o) d] ++ (sPath lane off (m + 1) 0 (.n d) (d + 1)).1) σ
      (fun σ' => cellVal (σ' (sPath lane off (m + 1) 0 (.n d) (d + 1)).2.2) =
          Id.run (Sphincs.Verification.treeFold keccakF1600 P layer tree leaf path (m + 1) v) ∧
        IsCanonical128 (σ' (sPath lane off (m + 1) 0 (.n d) (d + 1)).2.2)) := by
  -- the encoding's digest and the leaf
  set dEnc := th (m := Id) keccakF1600 P (Sphincs.hashDomainFields (.encoding layer tree leaf))
    (cs.flatMap cellBytes ++ littleEndianBytes 4 ctr) with hdEnc
  obtain ⟨hvalid, hv⟩ := otsLeaf_some hots
  have hcell : encCell (cellOf128 P) layer tree leaf cs ctr = cellOf128 dEnc := by
    rw [hdEnc, ← cellVal_cellOf128 P, encTh_cells, cellVal_cellOf128]
    exact (cellOf128_cellVal (canon_encCell _ _ _ _ _ _)).symm
  have hcall := hC P layer tree leaf dEnc values hvalid
  rw [← hv] at hcall
  have hpnb : NBv d sPP := ⟨2, by omega, rfl⟩
  refine Completes.append (m := d + 1) (by omega) (by omega)
    (by
      simp only [sWotsCall, valsList_cons, valsList_nil, Stmt.vals, List.append_nil]
      intro x hx
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with (rfl | rfl | rfl) | rfl
      · exact hpnb.mono' (by omega)
      · exact hadr.mono' (by omega)
      · exact ⟨o, by omega, rfl⟩
      · exact ⟨d, by omega, rfl⟩)
    (call_complete (C := C) (rd := rd) σ (cellOf128 v) (.cons hpnb (.cons hadr (.cons ⟨o, ho, rfl⟩ (.nil _))))
      (by simp only [List.map_cons, List.map_nil, hpp, hadrv, henc, hcell]; exact hcall))
    (fun σ1 he1 hl1 => ?_)
  have t1 : ∀ x, NBv d x → σ1 x = σ x := fun x hx => by
    obtain ⟨j, hj, rfl⟩ := hx; exact he1.apply (Or.inl hj)
  have hpath := sPath_complete (C := C) (rd := rd) (lane := lane) (off := off) hoff (e := leaf.val)
    (pp := cellOf128 P) (L := laneCell layer tree) (sib := fun l => cellOf128 (path l))
    (fun _ => isCanonical128_cellOf128 _) (by unfold laneCell keyAddressCell; exact isCanonical128_cellOf128 _) (isCanonical128_cellOf128 _)
    m 0 (.n d) (d + 1) σ1 (by omega) (by simpa using hleaf) (by omega) (hlnb.mono' (by omega)) ⟨d, by omega, rfl⟩
    (hp.congr (b := d) (by unfold sPad; omega) (fun j hj => (t1 (.n j) ⟨j, hj, rfl⟩).symm))
    (by rw [t1 _ hpnb]; exact hpp) (by rw [t1 _ hlnb]; exact hlane)
    (fun j hj => by
      rw [show sBit (off + j) = .n (51 + (off + j)) from rfl, t1 _ ⟨_, by omega, rfl⟩]; exact hbits j (by omega))
    (fun j hj => by
      obtain ⟨k, hk, ek⟩ := sVal_nb (i := off + j + 1) (by omega)
      rw [ek, t1 _ ⟨k, by omega, rfl⟩, ← ek]; exact hvals j (by omega))
    (by rw [hl1]; exact isCanonical128_cellOf128 _)
  refine hpath.mono (by omega) le_rfl (fun σ' ⟨q1, q2⟩ => ⟨?_, q2⟩)
  have := sTreeFold_cells (cellOf128 P) layer tree leaf (sib := fun l => cellOf128 (path l)) (path := path) hh
    (fun l _ => cellVal_cellOf128 _) (cellOf128 v)
  rw [cellVal_cellOf128] at this
  rw [q1, hl1, nIter_zero, ← this]
  exact congrArg (fun x => Id.run (Sphincs.Verification.treeFold keccakF1600 P layer tree leaf path (m + 1) x))
    (cellVal_cellOf128 v)

end
end LeanVM.Guest.B1.Sig
