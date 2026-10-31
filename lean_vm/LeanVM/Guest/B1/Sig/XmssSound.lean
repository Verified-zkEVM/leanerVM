/-
  LeanVM.Guest.B1.Sig.XmssSound

  `verify_lean_xmss` is sound: whenever its body holds, the signature its frame holds verifies the
  claim at its argument (`verify_lean_xmss_sound_holds`).
-/

module

public import LeanVM.Guest.B1.Sig.XmssLayer
public import LeanVM.Guest.B1.Sig.XmssData

/-!
# `verify_lean_xmss`, sound

`xmssSigOf σ`: the leaf index the frame's bits spell, the bottom layer's part (`xPart 0 196`) and
the top layer's. `verify_lean_xmss_sound_holds : verify_lean_xmss_sound_Spec xmssSigOf`: the body
(`Data.core19.body = xBody`) holding, the prologue gives the parameter, the bits, the node indices,
the powers and the chain indices; the bottom layer, from the 80-byte digest of the message,
reaches a root `r0`; the top layer, from the 64-byte digest of `r0`, reaches the root the claim's
first cell is asserted to be.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier

@[expose] public section

attribute [local irreducible] kMsg codewordT merkleT xLayer

/-- **The leanXMSS signature `verify_lean_xmss` checks**, read off its valuation. -/
noncomputable def xmssSigOf (σ : Val) : LeanXmss.Signature :=
  ⟨⟨xLeaf σ, xLeaf_lt σ⟩, fun lay =>
    if lay = LeanXmss.bottomLayer then xPart 0 196 σ else xPart 1 (xLayer 0 196 (.n 0)).2.1 σ⟩

theorem xBody_split : xBody = xPrologue ++ ((xLayer 0 196 (.n 0)).1 ++
    ((xLayer 1 (xLayer 0 196 (.n 0)).2.1 (xLayer 0 196 (.n 0)).2.2).1 ++
      [loadS (.n (xLayer 1 (xLayer 0 196 (.n 0)).2.1 (xLayer 0 196 (.n 0)).2.2).2.1) (.n 0) 0,
        .atom (.assertEq (xLayer 1 (xLayer 0 196 (.n 0)).2.1 (xLayer 0 196 (.n 0)).2.2).2.2
          (.n (xLayer 1 (xLayer 0 196 (.n 0)).2.1 (xLayer 0 196 (.n 0)).2.2).2.1)), .ret []])) := by
  simp only [xBody, List.append_assoc]

/-- A message's bytes are its two cells', the first low. -/
theorem bytesLE_cellPairVal (c d : E) : HashSig.bytesLE 32 (cellPairVal c d) = cellBytes c ++ cellBytes d := by
  have h0 := cellNat_lt c
  have h1 := cellNat_lt d
  have ht : (cellPairVal c d).toNat = cellNat c + 2 ^ 128 * cellNat d := by
    rw [cellPairVal, BitVec.toNat_append, toNat_cellVal, toNat_cellVal, Nat.shiftLeft_eq, mul_comm,
      two_pow_mul_or h0]
    ring
  rw [bytesLE_eq, ht, cellBytes_eq_leBytes, cellBytes_eq_leBytes,
    show (2 : Nat) ^ 128 = 256 ^ 16 by norm_num, show 32 = 16 + 16 from rfl,
    leBytes_add_mul _ _ _ _ (by norm_num; omega)]

variable {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}

theorem xDigest0_atoms (b : Nat) : atomsOnly (xDigest0 b) = true := rfl

theorem xDigest0_pad (b k : Nat) (hk : k < 5) :
    cst (b + 10 + k) (word (if k = 0 then 1 else 0) 0 0) ∈ xDigest0 b := by
  simp only [xDigest0, List.mem_append, List.mem_map, List.mem_range]
  exact Or.inl (Or.inr ⟨k, hk, rfl⟩)

/-- **The bottom layer's digest**: the message's cells loaded, the padding run set, the digest of
`P`, the message's address, the two cells and the randomizer. -/
theorem xDigest0_sound (h : AtomsHold rd σ (xDigest0 196)) :
    LoadHolds rd (σ (.n 0)) 2 (σ (.n 199)) ∧ LoadHolds rd (σ (.n 0)) 3 (σ (.n 200)) ∧
      PadOK σ xPad ∧ σ (.n 198) = σ (xNode 0) + word (tw 12) 0 0 ∧
      σ (.n 211) = (hcell [σ (.n 1), σ (.n 198), σ (.n 199), σ (.n 200), σ (.n 196)]).1 := by
  have ld2 := h.atom (a := .load (.n 199) (.n 0) 2) (by simp [xDigest0, loadS])
  have ld3 := h.atom (a := .load (.n 200) (.n 0) 3) (by simp [xDigest0, loadS])
  have ad := h.atom (a := .add (.n 198) (xNode 0) (.n 197)) (by simp [xDigest0, addS])
  have c197 := h.atom (a := .const (.n 197) (word (tw 12) 0 0)) (by simp [xDigest0, cst])
  have cp := h.atom (a := .copy (.n 201) (.n 196)) (by simp [xDigest0, copyS])
  have c202 := h.atom (a := .const (.n 202) (word 1 0 0)) (by simp [xDigest0, cst])
  have c203 := h.atom (a := .const (.n 203) (word 0 0 0)) (by simp [xDigest0, cst])
  have c204 := h.atom (a := .const (.n 204) (word 0 0 0)) (by simp [xDigest0, cst])
  have c205 := h.atom (a := .const (.n 205) (word (2 ^ 63) 0 0)) (by simp [xDigest0, cst])
  have p0 : σ (.n 206) = word (if 0 = 0 then 1 else 0) 0 0 := h.atom (xDigest0_pad 196 0 (by norm_num))
  have p1 : σ (.n 207) = word (if 1 = 0 then 1 else 0) 0 0 := h.atom (xDigest0_pad 196 1 (by norm_num))
  have p2 : σ (.n 208) = word (if 2 = 0 then 1 else 0) 0 0 := h.atom (xDigest0_pad 196 2 (by norm_num))
  have p3 : σ (.n 209) = word (if 3 = 0 then 1 else 0) 0 0 := h.atom (xDigest0_pad 196 3 (by norm_num))
  have p4 : σ (.n 210) = word (if 4 = 0 then 1 else 0) 0 0 := h.atom (xDigest0_pad 196 4 (by norm_num))
  simp only [Atom.Holds, word_zero] at ad c197 cp c202 c203 c204 c205
  simp only [↓reduceIte, word_zero, one_ne_zero, OfNat.ofNat_ne_zero] at p0 p1 p2 p3 p4
  refine ⟨ld2, ld3, ⟨p0, p1, p2, p3, p4⟩, by rw [ad, c197], ?_⟩
  have hk : AtomsHold rd σ [kecS [.n 1, .n 198, .n 199, .n 200, .n 201, .n 202, .n 203, .n 204, .n 205,
      .n 207, .n 208, .n 209, .n 210] (runV 211 13) false false] :=
    h.sub fun x hx => by
      simp only [List.mem_singleton] at hx
      subst hx
      simp [xDigest0]
  have := kec80_sound hk c202 c203 c204 c205 p1 p2 p3 p4
  rw [← cp]
  exact congrArg Prod.fst this

theorem xDigest1_atoms (b : Nat) (root : V) : atomsOnly (xDigest1 b root) = true := rfl

/-- **The top layer's index and digest**: the digest of `P`, the message's address, the bottom root
and the randomizer. -/
theorem xDigest1_sound {b : Nat} {root : V} (hpad : PadOK σ xPad) (h : AtomsHold rd σ (xDigest1 b root)) :
    σ (.n (b + 1)) = σ (xNode 16) + word lxTop 0 0 ∧
      σ (.n (b + 4)) = σ (.n (b + 1)) + word (tw 12) 0 0 ∧
      σ (.n (b + 6)) = (hcell [σ (.n 1), σ (.n (b + 4)), σ root, σ (.n (b + 2))]).1 := by
  have c0 : σ (.n b) = word lxTop 0 0 := h.atom (a := .const (.n b) (word lxTop 0 0)) (by simp [xDigest1, cst])
  have a1 : σ (.n (b + 1)) = σ (xNode 16) + σ (.n b) :=
    h.atom (a := .add (.n (b + 1)) (xNode 16) (.n b)) (by simp [xDigest1, addS])
  have c3 : σ (.n (b + 3)) = word (tw 12) 0 0 :=
    h.atom (a := .const (.n (b + 3)) (word (tw 12) 0 0)) (by simp [xDigest1, cst])
  have a4 : σ (.n (b + 4)) = σ (.n (b + 1)) + σ (.n (b + 3)) :=
    h.atom (a := .add (.n (b + 4)) (.n (b + 1)) (.n (b + 3))) (by simp [xDigest1, addS])
  have hk : AtomsHold rd σ (k64 xPad (.n 1) (.n (b + 4)) root (.n (b + 2)) (b + 5) (b + 6)) :=
    h.sub fun x hx => by simp only [xDigest1, List.mem_append]; exact Or.inr hx
  exact ⟨by rw [a1, c0], by rw [a4, c3], congrArg Prod.fst (k64_sound hpad hk)⟩

theorem xIdxNat_zero (L : Nat) : xIdxNat 0 L = L := by simp [xIdxNat]

theorem xIdxNat_one {L : Nat} (hL : L < 2 ^ 32) :
    eOfNat (L >>> 16) + word lxTop 0 0 = eOfNat (xIdxNat 1 L) := by
  rw [add_comm, show lxTop = 2 ^ 32 * 2 ^ 23 by simp [lxTop], word_add_eOfNat (key_lt L 1 hL)]
  simp [xIdxNat]

/-- **`verify_lean_xmss` is sound**, for the signature its frame holds. -/
theorem verify_lean_xmss_sound_holds : verify_lean_xmss_sound_Spec xmssSigOf := by
  intro C rd σ rets h
  rw [xBody_eq, xBody_split] at h
  -- the prologue
  have s0 := holdsList_split_atoms (xs := xPrologue) xPrologue_atoms h
  obtain ⟨hld1, hpre⟩ := xPrologue_sound (atomsHold_of_holdsList xPrologue_atoms s0.1)
  have hL := xLeaf_lt σ
  -- the bottom layer
  have s1 := s0.2
  rw [show (xLayer 0 196 (.n 0)).1 = xDigest0 196 ++ (xStepAddrs (xIdx 0 196) (xA 0 196) ++
      ((xCw 0 196).1 ++ ([cst (xCw 0 196).2.1 (word (tw 2) 0 0),
        addS (.n ((xCw 0 196).2.1 + 1)) (xIdx 0 196) (.n (xCw 0 196).2.1)] ++
        ((xLeafK 0 196).1 ++ (xMk 0 196).1)))) by simp [xLayer]] at s1
  simp only [List.append_assoc] at s1
  have s2 := holdsList_split_atoms (xs := xDigest0 196) (xDigest0_atoms 196) s1
  obtain ⟨hld2, hld3, hpad, h198, h211⟩ := xDigest0_sound (atomsHold_of_holdsList (xDigest0_atoms 196) s2.1)
  have hidx0 : σ (xIdx 0 196) = eOfNat (xIdxNat 0 (xLeaf σ)) := by
    simp only [xIdx, ↓reduceIte, xIdxNat_zero]
    rw [hpre.nodes 0 (by norm_num)]
    rfl
  have hM0 : HashSig.bytesLE 32 (cellPairVal (σ (.n 199)) (σ (.n 200))) =
      [σ (.n 199), σ (.n 200)].flatMap cellBytes := by
    rw [bytesLE_cellPairVal]; simp
  have haMsg0 : cellBytes (σ (.n 198)) = LeanXmss.tweakBytes
      (.message ⟨0, by decide⟩ (LeanXmss.keyAt ⟨xLeaf σ, hL⟩ ⟨0, by decide⟩)) := by
    rw [h198, show σ (xNode 0) = eOfNat (xIdxNat 0 (xLeaf σ)) by
      rw [xIdxNat_zero, hpre.nodes 0 (by norm_num)]; rfl]
    exact xMsgAdr_bytes hL (by norm_num)
  have hd00 : σ (xD0 0 196) = (hcell (σ (.n 1) :: σ (.n 198) :: [σ (.n 199), σ (.n 200)] ++
      [σ (xRho 0 196)])).1 := by
    simp only [xD0, xRho, ↓reduceIte, List.cons_append, List.nil_append]
    exact h211
  have c0 := xLayerCore_sound (C := C) (rd := rd) (σ := σ) (kret := fun rs => rs = rets) (next := False)
    (msgCells := [σ (.n 199), σ (.n 200)]) (aMsg := σ (.n 198)) hpre hpad (layer := 0) (b := 196)
    (by norm_num) hidx0 hM0 haMsg0 hd00 (rest := (xLayer 1 (xLayer 0 196 (.n 0)).2.1 (xLayer 0 196 (.n 0)).2.2).1 ++
      [loadS (.n (xLayer 1 (xLayer 0 196 (.n 0)).2.1 (xLayer 0 196 (.n 0)).2.2).2.1) (.n 0) 0,
        .atom (.assertEq (xLayer 1 (xLayer 0 196 (.n 0)).2.1 (xLayer 0 196 (.n 0)).2.2).2.2
          (.n (xLayer 1 (xLayer 0 196 (.n 0)).2.1 (xLayer 0 196 (.n 0)).2.2).2.1)), .ret []]) s2.2
  -- the top layer
  have s3 := c0.1
  rw [show (xLayer 1 (xLayer 0 196 (.n 0)).2.1 (xLayer 0 196 (.n 0)).2.2).1 =
      xDigest1 (xLayer 0 196 (.n 0)).2.1 (xLayer 0 196 (.n 0)).2.2 ++
      (xStepAddrs (xIdx 1 (xLayer 0 196 (.n 0)).2.1) (xA 1 (xLayer 0 196 (.n 0)).2.1) ++
      ((xCw 1 (xLayer 0 196 (.n 0)).2.1).1 ++ ([cst (xCw 1 (xLayer 0 196 (.n 0)).2.1).2.1 (word (tw 2) 0 0),
        addS (.n ((xCw 1 (xLayer 0 196 (.n 0)).2.1).2.1 + 1)) (xIdx 1 (xLayer 0 196 (.n 0)).2.1)
          (.n (xCw 1 (xLayer 0 196 (.n 0)).2.1).2.1)] ++
        ((xLeafK 1 (xLayer 0 196 (.n 0)).2.1).1 ++ (xMk 1 (xLayer 0 196 (.n 0)).2.1).1)))) by
      simp [xLayer]] at s3
  simp only [List.append_assoc] at s3
  have s4 := holdsList_split_atoms (xs := xDigest1 (xLayer 0 196 (.n 0)).2.1 (xLayer 0 196 (.n 0)).2.2) (xDigest1_atoms (xLayer 0 196 (.n 0)).2.1 (xLayer 0 196 (.n 0)).2.2) s3
  obtain ⟨h1, h4, h6⟩ := xDigest1_sound hpad (atomsHold_of_holdsList (xDigest1_atoms (xLayer 0 196 (.n 0)).2.1 (xLayer 0 196 (.n 0)).2.2) s4.1)
  have hidx1 : σ (xIdx 1 (xLayer 0 196 (.n 0)).2.1) = eOfNat (xIdxNat 1 (xLeaf σ)) := by
    simp only [xIdx, one_ne_zero, ↓reduceIte]
    rw [h1, hpre.nodes 16 (by norm_num), xIdxNat_one hL]
  have hM1 : HashSig.bytesLE 16 (xv (σ (xLayer 0 196 (.n 0)).2.2)) = [σ (xLayer 0 196 (.n 0)).2.2].flatMap cellBytes := by
    rw [bytesLE_xv]; simp
  have haMsg1 : cellBytes (σ (.n ((xLayer 0 196 (.n 0)).2.1 + 4))) = LeanXmss.tweakBytes
      (.message ⟨1, by decide⟩ (LeanXmss.keyAt ⟨xLeaf σ, hL⟩ ⟨1, by decide⟩)) := by
    rw [h4, h1, hpre.nodes 16 (by norm_num), xIdxNat_one hL]
    exact xMsgAdr_bytes hL (by norm_num)
  have hd01 : σ (xD0 1 (xLayer 0 196 (.n 0)).2.1) = (hcell (σ (.n 1) :: σ (.n ((xLayer 0 196 (.n 0)).2.1 + 4)) :: [σ (xLayer 0 196 (.n 0)).2.2] ++ [σ (xRho 1 (xLayer 0 196 (.n 0)).2.1)])).1 := by
    simp only [xD0, xRho, one_ne_zero, ↓reduceIte, List.cons_append, List.nil_append]
    exact h6
  have c1 := xLayerCore_sound hpre hpad (layer := 1) (b := (xLayer 0 196 (.n 0)).2.1) (by norm_num) hidx1 hM1 haMsg1 hd01
    s4.2
  -- the root
  have hend := c1.1
  have hld0 : LoadHolds rd (σ (.n 0)) 0 (σ (.n (xLayer 1 (xLayer 0 196 (.n 0)).2.1 (xLayer 0 196 (.n 0)).2.2).2.1)) := hend.1
  have hroot : σ (xLayer 1 (xLayer 0 196 (.n 0)).2.1 (xLayer 0 196 (.n 0)).2.2).2.2 + σ (.n (xLayer 1 (xLayer 0 196 (.n 0)).2.1 (xLayer 0 196 (.n 0)).2.2).2.1) = 0 := hend.2.1
  have hrets : rets = [] := (hend.2.2).symm
  refine ⟨hrets, σ (.n (xLayer 1 (xLayer 0 196 (.n 0)).2.1 (xLayer 0 196 (.n 0)).2.2).2.1), σ (.n 1), σ (.n 199), σ (.n 200), ⟨hld0, hld1, hld2, hld3⟩, ?_⟩
  have e0 : (xLayer 0 196 (.n 0)).2.2 = (xMk 0 196).2.2 := by simp only [xLayer]
  have e1 : (xLayer 1 (xLayer 0 196 (.n 0)).2.1 (xLayer 0 196 (.n 0)).2.2).2.2 =
      (xMk 1 (xLayer 0 196 (.n 0)).2.1).2.2 := by simp only [xLayer]
  have lb : (xmssSigOf σ).layers LeanXmss.bottomLayer = xPart 0 196 σ := by simp [xmssSigOf]
  have lt : (xmssSigOf σ).layers LeanXmss.topLayer = xPart 1 (xLayer 0 196 (.n 0)).2.1 σ := by
    simp [xmssSigOf, LeanXmss.topLayer, LeanXmss.bottomLayer]
  have hr : σ (xMk 1 (xLayer 0 196 (.n 0)).2.1).2.2 =
      σ (.n (xLayer 1 (xLayer 0 196 (.n 0)).2.1 (xLayer 0 196 (.n 0)).2.2).2.1) := by
    rw [← e1]; exact e_add_eq_zero_iff.mp hroot
  rw [xmssVerify_iff]
  refine ⟨xv (σ (xLayer 0 196 (.n 0)).2.2), ?_, ?_⟩
  · rw [lb, e0]
    exact c0.2
  · rw [lt]
    have h2 := c1.2
    rw [hr] at h2
    exact h2

end
end LeanVM.Guest.B1.Sig
