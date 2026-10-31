/-
  LeanVM.Guest.B1.Sig.XmssLayersSound

  The layers of `verify_lean_xmss`, sound one at a time: the bottom layer after the prologue and
  the top layer reach `layerRoot` of the parts their frames hold.
-/

module

public import LeanVM.Guest.B1.Sig.XmssSound
public import Common.WithHash
public import LeanVM.Guest.WithHash

/-!
# The layers, sound

`xmss_sound0`: the prologue and the bottom layer holding, the prologue's facts and the bottom
layer's root over the message the argument holds. `xmss_sound1`: the top layer holding, its root
over the bottom root. The steps of `verify_lean_xmss_sound_holds`, stated for the completeness
proof, which reads the roots off its valuation.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier

@[expose] public section

attribute [local irreducible] kMsg codewordT merkleT xLayer

variable {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}

theorem xLayer_split (layer b : Nat) (root : V) : (xLayer layer b root).1 =
    (if layer = 0 then xDigest0 b else xDigest1 b root) ++ (xStepAddrs (xIdx layer b) (xA layer b) ++
      ((xCw layer b).1 ++ ([cst (xCw layer b).2.1 (word (tw 2) 0 0),
        addS (.n ((xCw layer b).2.1 + 1)) (xIdx layer b) (.n (xCw layer b).2.1)] ++
        ((xLeafK layer b).1 ++ (xMk layer b).1)))) := by
  simp [xLayer]

theorem xLayer_snd (layer b : Nat) (root : V) : (xLayer layer b root).2 = (xMk layer b).2 := by
  simp only [xLayer]

/-- **The prologue and the bottom layer, sound.** -/
theorem xmss_sound0 {rest : List Stmt} {next : Prop}
    (h : Stmt.HoldsList C rd σ (xPrologue ++ ((xLayer 0 196 (.n 0)).1 ++ rest)) next kret) :
    Stmt.HoldsList C rd σ rest next kret ∧ XPre σ ∧ PadOK σ xPad ∧
      @LeanXmss.Concrete.layerRootWithHash Id _ ⟨Node.keccakBits⟩ (xpp (σ (.n 1))) ⟨0, by decide⟩
        (LeanXmss.keyAt ⟨xLeaf σ, xLeaf_lt σ⟩ ⟨0, by decide⟩)
        (HashSig.bytesLE 32 (cellPairVal (σ (.n 199)) (σ (.n 200)))) (xPart 0 196 σ) =
        some (xv (σ (xLayer 0 196 (.n 0)).2.2)) := by
  have s0 := holdsList_split_atoms (xs := xPrologue) xPrologue_atoms h
  obtain ⟨-, hpre⟩ := xPrologue_sound (atomsHold_of_holdsList xPrologue_atoms s0.1)
  have hL := xLeaf_lt σ
  have s1 := s0.2
  rw [xLayer_split] at s1
  simp only [↓reduceIte, List.append_assoc] at s1
  have s2 := holdsList_split_atoms (xs := xDigest0 196) (xDigest0_atoms 196) s1
  obtain ⟨-, -, hpad, h198, h211⟩ := xDigest0_sound (atomsHold_of_holdsList (xDigest0_atoms 196) s2.1)
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
  have c0 := xLayerCore_sound (C := C) (rd := rd) (σ := σ) (kret := kret) (next := next)
    (msgCells := [σ (.n 199), σ (.n 200)]) (aMsg := σ (.n 198)) hpre hpad (layer := 0) (b := 196)
    (by norm_num) hidx0 hM0 haMsg0 hd00 (rest := rest) s2.2
  refine ⟨c0.1, hpre, hpad, ?_⟩
  rw [xLayer_snd]
  exact c0.2

/-- **The top layer, sound**, over the bottom root `root`. -/
theorem xmss_sound1 (hpre : XPre σ) (hpad : PadOK σ xPad) {b : Nat} {root : V} {rest : List Stmt}
    {next : Prop} (h : Stmt.HoldsList C rd σ ((xLayer 1 b root).1 ++ rest) next kret) :
    Stmt.HoldsList C rd σ rest next kret ∧
      @LeanXmss.Concrete.layerRootWithHash Id _ ⟨Node.keccakBits⟩ (xpp (σ (.n 1))) ⟨1, by decide⟩
        (LeanXmss.keyAt ⟨xLeaf σ, xLeaf_lt σ⟩ ⟨1, by decide⟩) (HashSig.bytesLE 16 (xv (σ root)))
        (xPart 1 b σ) = some (xv (σ (xLayer 1 b root).2.2)) := by
  have hL := xLeaf_lt σ
  rw [xLayer_split] at h
  simp only [one_ne_zero, ↓reduceIte, List.append_assoc] at h
  have s4 := holdsList_split_atoms (xs := xDigest1 b root) (xDigest1_atoms b root) h
  obtain ⟨h1, h4, h6⟩ := xDigest1_sound hpad (atomsHold_of_holdsList (xDigest1_atoms b root) s4.1)
  have hidx1 : σ (xIdx 1 b) = eOfNat (xIdxNat 1 (xLeaf σ)) := by
    simp only [xIdx, one_ne_zero, ↓reduceIte]
    rw [h1, hpre.nodes 16 (by norm_num), xIdxNat_one hL]
  have hM1 : HashSig.bytesLE 16 (xv (σ root)) = [σ root].flatMap cellBytes := by
    rw [bytesLE_xv]; simp
  have haMsg1 : cellBytes (σ (.n (b + 4))) = LeanXmss.tweakBytes
      (.message ⟨1, by decide⟩ (LeanXmss.keyAt ⟨xLeaf σ, hL⟩ ⟨1, by decide⟩)) := by
    rw [h4, h1, hpre.nodes 16 (by norm_num), xIdxNat_one hL]
    exact xMsgAdr_bytes hL (by norm_num)
  have hd01 : σ (xD0 1 b) = (hcell (σ (.n 1) :: σ (.n (b + 4)) :: [σ root] ++ [σ (xRho 1 b)])).1 := by
    simp only [xD0, xRho, one_ne_zero, ↓reduceIte, List.cons_append, List.nil_append]
    exact h6
  have c1 := xLayerCore_sound hpre hpad (layer := 1) (b := b) (by norm_num) hidx1 hM1 haMsg1 hd01 s4.2
  refine ⟨c1.1, ?_⟩
  rw [xLayer_snd]
  exact c1.2

end
end LeanVM.Guest.B1.Sig
