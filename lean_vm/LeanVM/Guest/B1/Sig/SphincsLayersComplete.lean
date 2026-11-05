/-
  LeanVM.Guest.B1.Sig.SphincsLayersComplete

  A layer of `verify_sig_lean_sphincs`'s hypertree past its encoding (`sp_wots`'s call and
  `sp_path`, `lean_ethereum.py:3956-3967` at leanVM `9d8bce81`) is complete under any call relation
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

/-! ## The counter -/

/-- Byte `k` of a counter. -/
def ctrByte (ctr : Sphincs.EncodingCounter) (k : Nat) : Nat := ctr.toNat / 256 ^ k % 256

theorem flatMap_cellBytes_length : ∀ cs : List E, (cs.flatMap cellBytes).length = 16 * cs.length
  | [] => rfl
  | c :: cs => by
      simp only [List.flatMap_cons, List.length_append, length_cellBytes, flatMap_cellBytes_length cs,
        List.length_cons]; ring

theorem bFold_ctr (ctr : Sphincs.EncodingCounter) :
    bFold (ctr.toNat / 256 ^ 3) [ctrByte ctr 2, ctrByte ctr 1, ctrByte ctr 0] = ctr.toNat := by
  have : ctr.toNat < 2 ^ 32 := ctr.isLt
  simp only [bFold, ctrByte]
  generalize ctr.toNat = n at this ⊢
  norm_num at this ⊢
  omega

theorem ctr_top_lt (ctr : Sphincs.EncodingCounter) : ctr.toNat / 256 ^ 3 < 256 := by
  have : ctr.toNat < 2 ^ 32 := ctr.isLt; norm_num at this ⊢; omega

/-- The bytes of cells ending in a counter's word are zero past its four bytes. -/
theorem cellsBytes_ctr_zero (cs : List E) (ctr : Sphincs.EncodingCounter) :
    ∀ j, 16 * cs.length + 4 ≤ j → (cellsBytes (cs ++ [eOfNat ctr.toNat])).getD j 0 = 0 := by
  intro j hj
  have hc : ctr.toNat < 2 ^ 32 := ctr.isLt
  have hl := flatMap_cellBytes_length cs
  rw [cellsBytes_eq_flatMap, List.flatMap_append, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by omega), hl]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [cellBytes_eOfNat (by omega)]
  by_cases h16 : j - 16 * cs.length < 16
  · rw [List.getElem?_eq_getElem (by simp; omega), Option.getD_some, getElem_leBytes]
    have : ctr.toNat / 256 ^ (j - 16 * cs.length) = 0 := Nat.div_eq_of_lt (by
      calc ctr.toNat < 2 ^ 32 := hc
        _ ≤ 256 ^ 4 := by norm_num
        _ ≤ 256 ^ (j - 16 * cs.length) := Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [this]; rfl
  · rw [List.getElem?_eq_none (by simp; omega)]; rfl

/-! ## A layer above the bottom -/

theorem sUpper_split (adr below lane : V) (off height b : Nat) :
    sUpper adr below lane off height b =
      (hintW "sp_counter" (runV b 4) :: ((sFromBytes (.n (b + 3)) [.n (b + 2), .n (b + 1), .n b] g255W (b + 4)).1 ++
        ([cst (b + 37) (word (tw 4) 0 0), addS (.n (b + 38)) adr (.n (b + 37))] ++
          ((kMsg sPad [.cell sPP, .cell (.n (b + 38)), .cell below, .cell (.n (b + 36))] 52 false none (b + 39)).1 ++
            ([sWotsCall adr (.n (kMsg sPad [.cell sPP, .cell (.n (b + 38)), .cell below, .cell (.n (b + 36))] 52 false none
              (b + 39)).2.2) (kMsg sPad [.cell sPP, .cell (.n (b + 38)), .cell below, .cell (.n (b + 36))] 52 false none
              (b + 39)).2.1] ++
            (sPath lane off height 0 (.n (kMsg sPad [.cell sPP, .cell (.n (b + 38)), .cell below, .cell (.n (b + 36))] 52 false
              none (b + 39)).2.1) ((kMsg sPad [.cell sPP, .cell (.n (b + 38)), .cell below, .cell (.n (b + 36))] 52 false none
              (b + 39)).2.1 + 1)).1)))),
        (sPath lane off height 0 (.n (kMsg sPad [.cell sPP, .cell (.n (b + 38)), .cell below, .cell (.n (b + 36))] 52 false
          none (b + 39)).2.1) ((kMsg sPad [.cell sPP, .cell (.n (b + 38)), .cell below, .cell (.n (b + 36))] 52 false none
          (b + 39)).2.1 + 1)).2.1,
        (sPath lane off height 0 (.n (kMsg sPad [.cell sPP, .cell (.n (b + 38)), .cell below, .cell (.n (b + 36))] 52 false
          none (b + 39)).2.1) ((kMsg sPad [.cell sPP, .cell (.n (b + 38)), .cell below, .cell (.n (b + 36))] 52 false none
          (b + 39)).2.1 + 1)).2.2) := by
  simp [sUpper, sMarks, sFromBytes, sFromBytesRest, List.range_succ]

theorem upper_fb_val (b : Nat) :
    (sFromBytes (.n (b + 3)) [.n (b + 2), .n (b + 1), .n b] g255W (b + 4)).2.2 = .n (b + 36) := by
  simp [sFromBytes, sFromBytesRest]

/-- The counter's marks hinted from base `b`, high byte at `b + 3`. -/
def ctrMarks (ctr : Sphincs.EncodingCounter) (k : Nat) : E :=
  ofK (addressOfIndex (if k = 3 then ctr.toNat / 256 ^ 3 else ctrByte ctr k))

/-- **The counter's bytes complete** from base `b`: hinted, read off the table, the counter's word
at `b + 36`. -/
theorem ctr_complete (hm : MemOK rd 256) {bb : E} (hbb : ByteBits rd bb) (ctr : Sphincs.EncodingCounter)
    {b : Nat} (hb : 2 ≤ b) (σ : Val) (h1 : σ (.n 1) = bb) :
    Completes C rd b (b + 37) (hintW "sp_counter" (runV b 4) ::
      (sFromBytes (.n (b + 3)) [.n (b + 2), .n (b + 1), .n b] g255W (b + 4)).1) σ
      (fun σ' => σ' (.n (b + 36)) = eOfNat ctr.toNat ∧ ∀ k ≤ 3, BytePtr bb (σ' (.n (fbPtr (b + 4) k)))) := by
  refine Completes.reload ((updRun_ext σ b 4 (ctrMarks ctr)).mono le_rfl (by omega)) ?_
  have u : ∀ k < 4, updRun σ b 4 (ctrMarks ctr) (.n (b + k)) = ctrMarks ctr k := fun k hk =>
    updRun_at σ b 4 _ hk
  have hfb := sFromBytes_complete (C := C) hm hbb (K := 256) (v0 := ctr.toNat / 256 ^ 3) le_rfl (ctr_top_lt ctr)
    (.n (b + 3)) [.n (b + 2), .n (b + 1), .n b] [ctrByte ctr 2, ctrByte ctr 1, ctrByte ctr 0] (b + 4)
    (updRun σ b 4 (ctrMarks ctr)) (by omega) ⟨b + 3, by omega, rfl⟩ (by rw [u 3 (by norm_num)]; simp [ctrMarks])
    (.cons ⟨⟨b + 2, by omega, rfl⟩, by rw [u 2 (by norm_num)]; simp [ctrMarks], Nat.mod_lt _ (by norm_num)⟩
      (.cons ⟨⟨b + 1, by omega, rfl⟩, by rw [u 1 (by norm_num)]; simp [ctrMarks], Nat.mod_lt _ (by norm_num)⟩
      (.cons ⟨⟨b, by omega, rfl⟩, by have u0 := u 0 (by norm_num); rw [Nat.add_zero] at u0; rw [u0]; simp [ctrMarks],
        Nat.mod_lt _ (by norm_num)⟩ .nil)))
    (by rw [updRun_below σ b 4 _ ⟨1, by omega, rfl⟩]; exact h1) (by norm_num)
  rw [← g255W_k, upper_fb_val, bFold_ctr] at hfb
  obtain ⟨-, -, hnb⟩ := sFromBytes_shape (.n (b + 3)) [.n (b + 2), .n (b + 1), .n b] g255W (b + 4)
    ⟨b + 3, by omega, rfl⟩ (by simp only [List.mem_cons, List.not_mem_nil, or_false]
                               rintro m (rfl | rfl | rfl) <;> exact ⟨_, by omega, rfl⟩)
  refine Completes.append (xs := [hintW "sp_counter" (runV b 4)]) (m := b + 4) (by omega) (by omega)
    (by rw [valsList_hint]; intro v hv; simp only [runV, List.mem_map, List.mem_range] at hv
        obtain ⟨k, hk, rfl⟩ := hv; exact ⟨_, by omega, rfl⟩) (hintKeep_complete _ _ _ _ _) (fun σ2 _ e2 => ?_)
  subst e2
  exact hfb.mono le_rfl (by simp) (fun σ' h => h)

theorem kc_canon {σ : Val} {v : V} (h : IsCanonical128 (σ v)) : KCc σ (.cell v) := h

/-- **A layer above the bottom completes**: its counter's bytes, the encoding of the root below,
`sp_wots`'s call and the path: the root is the statement's tree fold of the leaf `otsLeaf` gives. -/
theorem sUpper_complete (hm : MemOK rd 256) {bb : E} (hbb : ByteBits rd bb) (hC : SpWotsCalls C)
    {P : PublicParameter} {layer : Sphincs.Layer} {tree : Sphincs.TreeIndex} {leaf : Sphincs.TreeLeafIndex}
    {Rc : E} {ctr : Sphincs.EncodingCounter} {values : Sphincs.ChainIndex → Digest} {v : Digest}
    (hots : Id.run (Sphincs.Verification.otsLeaf keccakF1600 P layer tree leaf ([Rc].flatMap cellBytes) ctr values) =
      some v)
    {path : Nat → Digest} {m : Nat} (hh : m + 1 ≤ 10) (hleaf : leaf.val < 2 ^ (m + 1))
    {adr below lane : V} {off b : Nat} (hoff : off ≤ 16) (hb : 1225 ≤ b) (hadr : NBv b adr) (hbel : NBv b below)
    (hlnb : NBv b lane) (σ : Val) (hp : PadOK σ sPad) (h1 : σ (.n 1) = bb) (hpp : σ sPP = cellOf128 P)
    (hadrv : σ adr = keyAddressCell layer tree leaf) (hbelv : σ below = Rc) (hRc : IsCanonical128 Rc)
    (hlane : σ lane = laneCell layer tree)
    (hbits : ∀ j < m + 1, σ (sBit (off + j)) = if leaf.val.testBit j then 1 else 0)
    (hvals : ∀ j, j + 1 < m + 1 → σ (sVal (off + j + 1)) = eOfNat (leaf.val >>> (j + 1))) :
    Completes C rd b (sUpper adr below lane off (m + 1) b).2.1 (sUpper adr below lane off (m + 1) b).1 σ
      (fun σ' => cellVal (σ' (sUpper adr below lane off (m + 1) b).2.2) =
          Id.run (Sphincs.Verification.treeFold keccakF1600 P layer tree leaf path (m + 1) v) ∧
        IsCanonical128 (σ' (sUpper adr below lane off (m + 1) b).2.2) ∧
        ∀ k ≤ 3, BytePtr bb (σ' (.n (fbPtr (b + 4) k)))) := by
  rw [sUpper_split]
  dsimp only
  set cells : List KC := [.cell sPP, .cell (.n (b + 38)), .cell below, .cell (.n (b + 36))] with hcells
  set K := kMsg sPad cells 52 false none (b + 39) with hK
  have hKo := kMsg_out sPad cells 52 false (b + 39)
  have hpnb : NBv b sPP := ⟨2, by omega, rfl⟩
  have hKle : b + 39 ≤ K.2.1 := kMsg_le (by unfold sPad; omega) (by
    rw [hcells]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro c (rfl | rfl | rfl | rfl)
    · exact hpnb.mono' (by omega)
    · exact ⟨_, by omega, rfl⟩
    · exact hbel.mono' (by omega)
    · exact ⟨_, by omega, rfl⟩)
  obtain ⟨hend, -⟩ := sPath_shape lane off m 0 (.n K.2.1) (K.2.1 + 1)
  rw [hend]
  -- the counter
  refine Completes.append (m := b + 37) (by omega) (by omega)
    (by
      rw [valsList_cons]
      refine NumBelow.append ?_ ((sFromBytes_shape (.n (b + 3)) [.n (b + 2), .n (b + 1), .n b] g255W (b + 4)
        ⟨b + 3, by omega, rfl⟩ (by simp only [List.mem_cons, List.not_mem_nil, or_false]
                                   rintro m (rfl | rfl | rfl) <;> exact ⟨_, by omega, rfl⟩)).2.2)
      intro x hx
      simp only [hintW, Stmt.vals, Atom.vals, Hint.vals, Dest.vals, runV, List.mem_map, List.mem_range] at hx
      obtain ⟨k, hk, rfl⟩ := hx; exact ⟨_, by omega, rfl⟩)
    (ctr_complete (C := C) hm hbb ctr (by omega) σ h1) (fun σ1 he1 ⟨hc1, hq1⟩ => ?_)
  have t1 : ∀ x, NBv b x → σ1 x = σ x := fun x hx => by obtain ⟨j, hj, rfl⟩ := hx; exact he1.apply (Or.inl hj)
  -- the encoding's address
  refine Completes.seq (m := b + 39) (xs := [cst (b + 37) (word (tw 4) 0 0), addS (.n (b + 38)) adr (.n (b + 37))])
    ⟨rfl, ⟨rfl, hadr.mono' (by omega), ⟨b + 37, by omega, rfl⟩⟩, rfl⟩ (by omega) (fun σ2 he2 hh2 => ?_)
  have t2 : ∀ x, NBv (b + 37) x → σ2 x = σ1 x := fun x hx => by
    obtain ⟨j, hj, rfl⟩ := hx; exact he2.apply (Or.inl hj)
  have hA2 : σ2 (.n (b + 38)) = keyAddressCell layer tree leaf + word (tw 4) 0 0 := by
    have c0 := hh2.atom (a := .const (.n (b + 37)) (word (tw 4) 0 0)) (by simp [cst])
    have a1 := hh2.atom (a := .add (.n (b + 38)) adr (.n (b + 37))) (by simp [addS])
    simp only [Atom.Holds] at c0 a1
    rw [a1, c0, t2 _ (hadr.mono' (by omega)), t1 _ hadr, hadrv]
  have hv2 : ∀ x ∈ [sPP, .n (b + 38), below, .n (b + 36)], NBv (b + 39) x := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro x (rfl | rfl | rfl | rfl)
    · exact hpnb.mono' (by omega)
    · exact ⟨_, by omega, rfl⟩
    · exact hbel.mono' (by omega)
    · exact ⟨_, by omega, rfl⟩
  have e2pp : σ2 sPP = cellOf128 P := by rw [t2 _ (hpnb.mono' (by omega)), t1 _ hpnb, hpp]
  have e2bel : σ2 below = Rc := by rw [t2 _ (hbel.mono' (by omega)), t1 _ hbel, hbelv]
  have e2c : σ2 (.n (b + 36)) = eOfNat ctr.toNat := by rw [t2 _ ⟨_, by omega, rfl⟩]; exact hc1
  have hp2 : PadOK σ2 sPad := hp.congr (b := b) (by unfold sPad; omega)
    (fun j hj => ((t2 (.n j) ⟨j, by omega, rfl⟩).trans (t1 (.n j) ⟨j, hj, rfl⟩)).symm)
  -- the encoding
  have hk := kMsg_complete (C := C) (rd := rd) (pad := sPad) (cells := cells) (len := 52) (tailRun := false)
    (b := b + 39) σ2 hp2 (by unfold sPad; omega)
    (by
      rw [hcells]
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro c (rfl | rfl | rfl | rfl)
      · refine ⟨hv2 _ (by simp), ?_⟩
        show IsCanonical128 (σ2 sPP)
        rw [e2pp]; exact isCanonical128_cellOf128 _
      · refine ⟨hv2 _ (by simp), ?_⟩
        show IsCanonical128 (σ2 (.n (b + 38)))
        rw [hA2]; exact canon_add (by unfold keyAddressCell; exact isCanonical128_cellOf128 _) (canon_word _ _)
      · refine ⟨hv2 _ (by simp), ?_⟩
        show IsCanonical128 (σ2 below)
        rw [e2bel]; exact hRc
      · refine ⟨hv2 _ (by simp), ?_⟩
        show IsCanonical128 (σ2 (.n (b + 36)))
        rw [e2c]; exact canon_eOfNat _)
    (fun h => by simp at h)
  obtain ⟨hkc, hknb, hkle⟩ := hk
  refine Completes.append (m := K.2.1) (by omega) (by omega) hknb hkc.withHolds (fun σ3 he3 ⟨_, hh3⟩ => ?_)
  have hA3 := atomsHold_of_holdsList (kMsg_atoms sPad cells 52 false none (b + 39)) hh3
  have hpad3 : PadOK σ3 sPad := hp2.congr (b := b + 39) (by unfold sPad; omega) he3.agree
  have hsound := kMsg_sound (rd := rd) hpad3 (cells := cells) (len := 52) (tailRun := false) (out := none)
    (b := b + 39) (fun h => by simp at h) hA3 (by simp [hcells])
  have t3 : ∀ x, NBv (b + 39) x → σ3 x = σ2 x := fun x hx => by
    obtain ⟨j, hj, rfl⟩ := hx; exact he3.apply (Or.inl hj)
  have hmap : cells.map (KC.val σ3) = [cellOf128 P, keyAddressCell layer tree leaf + word (tw 4) 0 0, Rc,
      eOfNat ctr.toNat] := by
    simp only [hcells, List.map_cons, List.map_nil, KC.val]
    rw [t3 _ (hv2 _ (by simp)), t3 _ (hv2 _ (by simp)), t3 _ (hv2 _ (by simp)), t3 _ (hv2 _ (by simp)), e2pp, hA2,
      e2bel, e2c]
  rw [hmap] at hsound
  specialize hsound (fun j hj => cellsBytes_ctr_zero [cellOf128 P, keyAddressCell layer tree leaf + word (tw 4) 0 0, Rc]
    ctr j (by simpa using hj))
  have henc : σ3 (.n K.2.2) = encCell (cellOf128 P) layer tree leaf [Rc] ctr := by
    exact (congrArg Prod.fst hsound).trans rfl
  -- the call and the path
  have t3b : ∀ x, NBv b x → σ3 x = σ x := fun x hx => by
    rw [t3 _ (hx.mono' (by omega)), t2 _ (hx.mono' (by omega)), t1 _ hx]
  have htail := layerTail_complete (C := C) (rd := rd) hC hots (path := path) hh hleaf (adr := adr) (lane := lane)
    (off := off) (o := K.2.2) (d := K.2.1) hoff (by omega)
    (Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (by norm_num)) hKo) (hadr.mono' (by omega)) (hlnb.mono' (by omega))
    σ3 hpad3 (by rw [t3b _ hpnb]; exact hpp) (by rw [t3b _ hadr]; exact hadrv) henc
    (by rw [t3b _ hlnb]; exact hlane)
    (fun j hj => by
      rw [show sBit (off + j) = .n (51 + (off + j)) from rfl, t3b _ ⟨_, by omega, rfl⟩]; exact hbits j hj)
    (fun j hj => by
      obtain ⟨k, hk, ek⟩ := sVal_nb (i := off + j + 1) (by omega)
      rw [ek, t3b _ ⟨k, by omega, rfl⟩, ← ek]; exact hvals j hj)
  refine (htail.keep (Q := fun σ' => ∀ k ≤ 3, BytePtr bb (σ' (.n (fbPtr (b + 4) k))))
    (Q' := fun σ' => ∀ k ≤ 3, BytePtr bb (σ' (.n (fbPtr (b + 4) k))))
    (fun k hk => by
      rw [t3 _ ⟨_, by simp only [fbPtr]; split <;> omega, rfl⟩, t2 _ ⟨_, by simp only [fbPtr]; split <;> omega, rfl⟩]
      exact hq1 k hk)
    (fun σ' he q k hk => by rw [he.apply (Or.inl (by simp only [fbPtr]; split <;> omega))]; exact q k hk)).mono
    (by omega) (by omega) (fun σ' ⟨⟨q1, q2⟩, q3⟩ => ⟨q1, q2, q3⟩)

end
end LeanVM.Guest.B1.Sig
