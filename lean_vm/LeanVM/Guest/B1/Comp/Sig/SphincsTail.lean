/-
  LeanVM.Guest.B1.Comp.Sig.SphincsTail

  `verify_sig_lean_sphincs`'s tail (the one-time signature and the tree) complete over a
  completeness model (`sTail_complete`).
-/

module

public import LeanVM.Guest.B1.Comp.Sig.Codeword
public import LeanVM.Guest.B1.Comp.Sig.HashValues
public import LeanVM.Guest.B1.Comp.Sig.Merkle
public import LeanVM.Guest.B1.Comp.Sig.SphincsScheme
public import LeanVM.Guest.B1.Sig.SphincsTailComplete
public import LeanVM.Guest.B1.Sig.Model.Sphincs

/-!
# The tail over a completeness model

The leanSPHINCS counterpart of `xTail_comp`: the codeword's chains, the leaf and the tree preset to
the model's answers, every string answered because the scheme's run with the model's answered hash
returns (`sRecoverChain_cellsE`, `sLeafHash_cellsE`, `sTreeFold_cellsE`).
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.E2E.Complete

@[expose] public section

variable {CM : CompModel} {C : CallRel} {rd : Reader} {inst : HasQuery Sphincs.HashSpec Option}

/-- **The tail is complete over the model** (`sTail_complete`): over an encoding digest at `e + 5`
that decodes, from chain values and siblings whose recovered chains, leaf and tree the scheme's run
with the model's answers returns, the root is the run's. -/
theorem sTail_comp (hq : SQW CM.H inst) (hrd : MemOK rd 64) {σ : Val} {N U e : Nat} (he : 210 ≤ e)
    (hpre : SPre σ N U) (hidx : σ (.n 142) = eOfNat N) (hpp : IsCanonical128 (σ (.n 1)))
    {leaf : Sphincs.LeafIndex} (hleaf : leaf.val = N) {enc : Sphincs.Encoding}
    (hdec : Sphincs.TargetSum.decodeDigest (sv (σ (.n (e + 5)))) = some enc) (hd0c : IsCanonical128 (σ (.n (e + 5))))
    {vals sibs : Nat → E} (hvals : ∀ i, IsCanonical128 (vals i)) (hsibs : ∀ l, IsCanonical128 (sibs l))
    {tips : Sphincs.ChainIndex → Sphincs.Digest} {leafD r : Sphincs.Digest}
    (htips : ∀ i, @Sphincs.Concrete.recoverChain Option _ inst (spp (σ (.n 1))) Sphincs.topLayer 0 leaf i (enc i)
      (sv (vals i.val)) = some (tips i))
    (hleafD : @Sphincs.Concrete.leafHash Option _ inst (spp (σ (.n 1))) Sphincs.topLayer 0 leaf tips = some leafD)
    (hr : @Sphincs.Concrete.treeFold Option _ inst (spp (σ (.n 1))) Sphincs.topLayer 0 leaf (fun l => sv (sibs l))
      Sphincs.maxLayerHeight leafD = some r) :
    CompletesB CM.sem C rd (e + 7) (sMk e).2.2 (sTail e) σ (fun σ' =>
      sv (σ' (sMk e).2.1) = r ∧ IsCanonical128 (σ' (sMk e).2.1) ∧ AgreeBelow (e + 7) σ σ') := by
  have hN := hpre.ltN
  obtain ⟨henc, hsum, hval⟩ := sDecode_some hdec
  set dig : Nat → Nat := fun i => (sv (σ (.n (e + 5)))).toNat / 4 ^ i % 4 with hdig_def
  have hdig : ∀ i, dig i < 4 := fun i => Nat.mod_lt _ (by norm_num)
  have hc := cCodeword_snd_gt spW (fun s => .n (e + 7 + s)) 21 sTarget (.n (e + 5)) (e + 17)
  have htipB := cCodeword_tips_lt spW (fun s => .n (e + 7 + s)) 21 sTarget (.n (e + 5)) (e + 17)
  rw [show cCodeword spW (fun s => .n (e + 7 + s)) 21 sTarget (.n (e + 5)) (e + 17) = sCw e from rfl] at hc htipB
  have hmkge := merkle_snd_ge (.n 1) (fun l => .n (19 + l)) (fun l => .n (142 - 3 * l))
    (fun l => tw 3 + (l + 1) * hiMul) (fun l => l + 1 == 26) 26 0 (sLeaf e).2 ((sCw e).2.1 + 2 + hashValuesSize 64)
  rw [show merkle (.n 1) (fun l => .n (19 + l)) (fun l => .n (142 - 3 * l)) (fun l => tw 3 + (l + 1) * hiMul)
    (fun l => l + 1 == 26) 26 0 (sLeaf e).2 ((sCw e).2.1 + 2 + hashValuesSize 64) = sMk e from rfl] at hmkge
  have hleafB : NB ((sCw e).2.1 + 2 + hashValuesSize 64) (sLeaf e).2 := hashValues_snd_lt _ _ _ _ _
  have hwB : spW.Below (e + 17) := ⟨⟨1, by omega, rfl⟩, ⟨2, by omega, rfl⟩, fun _ => ⟨0, by omega, rfl⟩,
    ⟨142, by omega, rfl⟩⟩
  have hpwB : ∀ s < 10, NB (e + 17) (V.n (e + 7 + s)) := fun s hs => ⟨_, by omega, rfl⟩
  simp only [sTail]
  set c := (sCw e).2.1
  set tip : Nat → V := fun i => ((sCw e).2.2.getD i (.n 0, .n 0)).1
  -- the powers
  refine CompletesB.append (m := e + 17) (by omega) (by omega) (sPowers_below (e + 7))
    (CompletesB.of_free (F := []) (powers_free (e + 7)) (powers_complete (e + 7)))
    fun σ1 _ ⟨hp1, hag1⟩ => ?_
  have h1 : ∀ k < e + 7, σ1 (.n k) = σ (.n k) := fun k hk => (hag1 k hk).symm
  -- the chains' steps are answered
  have hch : ∀ (i : Sphincs.ChainIndex) (adr : Nat → E),
      tipAns CM false (σ (.n 1)) adr (eOfNat N) i.val (dig i.val) (vals i.val) ∧
      sv (tipPairC CM false (σ (.n 1)) adr (eOfNat N) i.val (dig i.val) (vals i.val)).1 = tips i := by
    intro i adr
    have e0 := sRecoverChain_cellsE (pp := σ (.n 1)) (idx := eOfNat N) hq (fun s => sp_chain_addr hN i s leaf hleaf)
      (enc i) (vals i.val)
    rw [htips i, show (enc i).val = dig i.val from henc i, tipPairWith_sp CM.H _ _ adr] at e0
    obtain ⟨p, hp, hpt⟩ := Option.map_eq_some_iff.mp e0.symm
    obtain ⟨ha, rfl⟩ := (tipPairWith_eq_some_iff _ _ _ _ _ _ _).mp hp
    exact ⟨ha, hpt⟩
  -- the codeword
  have hcan1 : spW.Canon σ1 := ⟨by show IsCanonical128 (σ1 (.n 1)); rw [h1 1 (by omega)]; exact hpp,
    fun h => absurd h Bool.false_ne_true,
    fun _ => by show IsCanonical128 (σ1 (.n 142)); rw [h1 142 (by omega), hidx]; exact isCanonical128_eOfNat _⟩
  have hcomp := cCodeword_comp (C := C) (w := spW) (power := fun s => .n (e + 7 + s)) hrd (G := 21)
    (by norm_num) (target := sTarget) (d0 := .n (e + 5)) (b := e + 17) (σ := σ1) (by omega) hwB hpwB
    ⟨e + 5, by omega, rfl⟩ (by show σ1 (.n 2) = mdw 48 true; rw [h1 2 (by omega)]; exact hpre.md48) hcan1
    hp1 (dig := dig) hdig (xs := vals) hvals
    (fun i hi => by
      show tipAns CM false (σ1 (.n 1)) (fun _ => σ1 (.n 0)) (σ1 (.n 142)) i (dig i) (vals i)
      rw [h1 1 (by omega), h1 142 (by omega), hidx]
      exact (hch ⟨i, by simp [Sphincs.numChains]; omega⟩ _).1)
    (by rw [sTarget_eq]; exact congrArg (gen ^ ·) hsum.symm)
    (by rw [h1 _ (by omega), ← cellOf_cellVal hd0c, ← lit_toNat (cellVal (σ (.n (e + 5))))]; exact congrArg lit hval)
  refine CompletesB.append (m := c) (by omega) (by omega)
    (show NumBelow (sCw e).2.1 (Stmt.valsList (sCw e).1) from
      cCodeword_below (by norm_num) (by omega) hwB hpwB ⟨e + 5, by omega, rfl⟩) hcomp.withExt
    fun σ2 _ ⟨hT2, he2'⟩ => ?_
  have h2 : ∀ k < e + 17, σ2 (.n k) = σ1 (.n k) := fun k hk => (he2'.agree k hk).symm
  have hp2 : σ2 (.n 1) = σ (.n 1) := by rw [h2 1 (by omega), h1 1 (by omega)]
  have hidx2 : σ2 (.n 142) = eOfNat N := by rw [h2 142 (by omega), h1 142 (by omega), hidx]
  -- the leaf address
  set A0 := word (tw 2) 0 0
  have ne : ∀ i j : Nat, i ≠ j → (V.n i) ≠ V.n j := fun i j h e => h (by cases e; rfl)
  refine CompletesB.append (m := c + 2) (by omega) (by omega)
    (show NumBelow (c + 2) (Stmt.valsList [cst c A0, addS (.n (c + 1)) (.n 142) (.n c)]) from
      .cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩
        (.nil _)))))
    (P := fun σ' => σ' (.n (c + 1)) = σ2 (.n 142) + A0 ∧ AgreeBelow c σ2 σ')
    (CompletesB.atom_cons A0 (by omega) (.cons ⟨_, by omega, rfl⟩ (.nil _)) (Function.update_self _ _ _)
      (CompletesB.atom_cons (σ2 (.n 142) + A0) (by omega)
        (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.nil _))))
        (by
          show Function.update (Function.update σ2 (.n c) A0) (.n (c + 1)) (σ2 (.n 142) + A0) (.n (c + 1)) =
            Function.update (Function.update σ2 (.n c) A0) (.n (c + 1)) (σ2 (.n 142) + A0) (.n 142) +
            Function.update (Function.update σ2 (.n c) A0) (.n (c + 1)) (σ2 (.n 142) + A0) (.n c)
          have h1 : 142 ≠ c := by omega
          have h2 : 142 ≠ c + 1 := by omega
          simp [h1, h2])
        (CompletesB.nil _ _ _ ⟨Function.update_self _ _ _, fun k hk => by
          rw [Function.update_of_ne (ne _ _ (by omega)), Function.update_of_ne (ne _ _ (by omega))]⟩)))
    fun σ3 _ ⟨hA3, hag3⟩ => ?_
  have h3 : ∀ k < c, σ3 (.n k) = σ2 (.n k) := fun k hk => (hag3 k hk).symm
  have hp3 : σ3 (.n 1) = σ (.n 1) := by rw [h3 1 (by omega), hp2]
  have htip3 : ∀ i < 64, σ3 (tip i) = (tipPairC CM false (σ (.n 1)) (fun _ => σ2 (.n 0)) (eOfNat N) i (dig i)
      (vals i)).1 := fun i hi => by
    obtain ⟨k, hk, e⟩ := htipB i hi
    have := (hT2 i hi).1
    simp only [tip] at e ⊢
    rw [e, h3 k hk, ← e]
    refine this.trans ?_
    show (tipPairC CM false (σ2 (.n 1)) (fun _ => σ2 (.n 0)) (σ2 (.n 142)) i (dig i) (vals i)).1 = _
    rw [hp2, hidx2]
  have hcanT : ∀ i < 64, IsCanonical128 (σ3 (tip i)) := fun i hi => by
    rw [htip3 i hi]; exact canonical_tipPairC _ _ _ _ _ _ (hvals i)
  have htipsE : tips = fun i => sv (σ3 (tip i.val)) := by
    funext i; rw [htip3 i.val i.isLt, (hch i _).2]
  -- the leaf is answered
  have hleafAdr : cellBytes (σ3 (.n (c + 1))) = Sphincs.tweakBytes (.leaf Sphincs.topLayer 0 leaf) := by
    rw [hA3, hidx2, sp_tag_addr hN (by norm_num), ← hleaf, ← sTweak]
    rfl
  have hlf := sLeafHash_cellsE (pp := σ3 (.n 1)) hq (fun i => σ3 (tip i)) hleafAdr
  rw [hp3, ← htipsE, hleafD, show Sphincs.numChains = 64 from rfl] at hlf
  obtain ⟨o, ho, hlo⟩ := Option.map_eq_some_iff.mp hlf.symm
  obtain ⟨hlans, rfl⟩ := hcellWith_eq_some_iff.mp ho
  have hv : CompletesB CM.sem C rd (c + 2) (c + 2 + hashValuesSize 64) (sLeaf e).1 σ3
      (fun σ' => σ' (sLeaf e).2 =
        (hcellC CM (σ3 (.n 1) :: σ3 (.n (c + 1)) :: (List.range 64).map fun i => σ3 (tip i))).1) :=
    hashValues_comp (Or.inl (by norm_num)) (by norm_num)
      ⟨⟨1, by omega, rfl⟩, ⟨c + 1, by omega, rfl⟩, fun i hi => (htipB i hi).mono (by omega)⟩
      ⟨by rw [hp3]; exact hpp,
        by rw [hA3, hidx2]; exact isCanonical128_add (isCanonical128_eOfNat _) (isCanonical128_word _ _), hcanT⟩
      (by rw [hp3]; exact hlans)
  refine CompletesB.append (m := c + 2 + hashValuesSize 64) (by omega) (by omega)
    (hashValues_below (by norm_num) ⟨⟨1, by omega, rfl⟩, ⟨c + 1, by omega, rfl⟩,
      fun i hi => (htipB i hi).mono (by omega)⟩) hv.withExt fun σ4 _ ⟨hleaf4, he4'⟩ => ?_
  have hσ4 : ∀ k < e + 7, σ4 (.n k) = σ (.n k) := fun k hk => by
    rw [← he4'.agree k (by omega), h3 k (by omega), h2 k (by omega), h1 k hk]
  have hleafc : IsCanonical128 (σ4 (sLeaf e).2) := by rw [hleaf4]; exact (isCanonical128_hcellC _).1
  have hnode4 : ∀ l, l + 1 < 26 → σ4 (.n (142 - 3 * (l + 1))) = eOfNat (N / 2 ^ (l + 1)) := fun l hl => by
    rw [hσ4 _ (by omega)]; exact hpre.nodes (l + 1) hl
  have hA : ∀ l < Sphincs.maxLayerHeight, cellBytes (mAddr σ4 (fun l => .n (142 - 3 * l))
      (fun l => tw 3 + (l + 1) * hiMul) (fun l => l + 1 == 26) l) =
      Sphincs.tweakBytes (.node Sphincs.topLayer 0 (l + 1) (leaf.val / 2 ^ (l + 1))) := fun l hl => by
    rw [hleaf]
    exact sp_node_addr hN hl (hnode4 l)
  -- the tree is answered
  have htr := sTreeFold_cellsE (pp := σ (.n 1)) hq hA sibs Sphincs.maxLayerHeight le_rfl (σ4 (sLeaf e).2)
  rw [hleaf4, hp3, hlo, hr] at htr
  obtain ⟨y, hy, hyr⟩ := Option.map_eq_some_iff.mp htr.symm
  obtain ⟨hyans, hyv⟩ := (mFoldWith_eq_some_iff _ _ _ _ _ _ _).mp hy
  rw [hleaf] at hyans hyv
  rw [show Sphincs.maxLayerHeight = 26 from rfl] at hyans hyv
  -- the tree
  have hmk := merkle_comp (CM := CM) (C := C) (rd := rd) (pp := .n 1) (bit := fun l => .n (19 + l))
    (node := fun l => .n (142 - 3 * l)) (addr := fun l => tw 3 + (l + 1) * hiMul) (isEnd := fun l => l + 1 == 26)
    (β := fun l => N.testBit l) (sibs := sibs)
    26 0 _ _ σ4 ⟨1, by omega, rfl⟩ hleafB
      (fun l' _ hl' => ⟨⟨_, by omega, rfl⟩, ⟨_, by omega, rfl⟩⟩)
      (fun l' _ hl' => ⟨by
          show σ4 (.n (19 + l')) = _
          rw [hσ4 _ (by omega)]; exact hpre.bits l' (by omega),
        hsibs l', by
          unfold mAddr
          split
          · exact isCanonical128_word _ _
          · rename_i hne
            rw [hnode4 l' (by simp only [beq_iff_eq] at hne; omega)]
            exact isCanonical128_add (isCanonical128_word _ _) (isCanonical128_eOfNat _)⟩)
      (by rw [hσ4 1 (by omega)]; exact hpp) hleafc
      (by rw [hσ4 1 (by omega), hleaf4, hp3]; exact hyans)
  rw [show merkle (.n 1) (fun l => .n (19 + l)) (fun l => .n (142 - 3 * l)) (fun l => tw 3 + (l + 1) * hiMul)
    (fun l => l + 1 == 26) 26 0 (sLeaf e).2 (c + 2 + hashValuesSize 64) = sMk e from rfl] at hmk
  refine hmk.withExt.mono le_rfl le_rfl fun σ5 ⟨hroot5, he5⟩ => ⟨?_, ?_, fun k hk => ?_⟩
  · rw [hroot5, hσ4 1 (by omega), hleaf4, hp3, hyv, hyr]
  · rw [hroot5]; exact mFoldC_canonical _ _ _ _ _ _ _ (Or.inl (by norm_num))
  · rw [← he5.agree k (by omega), hσ4 k hk]

end
end LeanVM.Guest.B1.Sig
