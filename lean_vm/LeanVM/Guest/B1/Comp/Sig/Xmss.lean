/-
  LeanVM.Guest.B1.Comp.Sig.Xmss

  `verify_lean_xmss` complete over a completeness model: the digests, a layer's tail, the two
  layers and the body, for a claim some signature verifies with the model's answered hash.
-/

module

public import LeanVM.Guest.B1.Comp.Sig.Codeword
public import LeanVM.Guest.B1.Comp.Sig.HashValues
public import LeanVM.Guest.B1.Comp.Sig.Merkle
public import LeanVM.Guest.B1.Comp.Sig.XmssScheme
public import LeanVM.Guest.B1.Sig.Model.Xmss
public import LeanVM.Guest.B1.Sig.XmssIff
public import LeanVM.E2E.Runs

/-!
# `verify_lean_xmss` over a completeness model

The deployed completeness (`XmssComplete.lean`, `XmssIff.lean`) over a `CompModel`, every hash
preset to the model's answer (`hcellC`, `hmidC`, `hbC`, `tipPairC`, `mFoldC`), the strings
answered because the scheme's run with the model's answered hash returns:

| deployed | here |
|---|---|
| `xDigest0_complete`, `xDigest1_complete` | `xDigest0_comp`, `xDigest1_comp` |
| `xTail_complete` | `xTail_comp` (the chains, leaf and tree from their `Option` runs) |
| `xLayer0_complete`, `xLayer1_complete` | `xLayer0_comp`, `xLayer1_comp` (from `layerRoot_someW`) |
| `verify_lean_xmss_complete` | `verify_lean_xmss_comp` (from `verify_someW`) |
| `verify_lean_xmss_iff.mpr` | `verify_lean_xmss_rel_comp`; at the deployed model `verify_lean_xmss_rel_of_comp` |
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value LeanXmss LeanXmss.Concrete
open LeanVM.E2E.Complete

@[expose] public section

variable {CM : CompModel} {C : CallRel} {rd : Reader}

/-! ## Chains: the index does not enter a leanXMSS step -/

theorem chainFromC_lx (pp : E) (adr : Nat → E) (idx : E) (i : Nat) :
    ∀ m s v, chainFromC CM true pp adr idx i m s v = chainFromC CM true pp adr 0 i m s v ∧
      (chainAns CM true pp adr idx i m s v ↔ chainAns CM true pp adr 0 i m s v)
  | 0, _, _ => ⟨rfl, Iff.rfl⟩
  | m + 1, s, v => by
      simp only [chainFromC, chainAns, stepCells, ↓reduceIte]
      exact ⟨(chainFromC_lx pp adr idx i m _ _).1, and_congr Iff.rfl (chainFromC_lx pp adr idx i m _ _).2⟩

theorem tipPairC_lx (pp : E) (adr : Nat → E) (idx : E) (i d : Nat) (x : E) :
    tipPairC CM true pp adr idx i d x = tipPairC CM true pp adr 0 i d x ∧
      (tipAns CM true pp adr idx i d x ↔ tipAns CM true pp adr 0 i d x) := by
  unfold tipPairC tipAns
  by_cases hd : d = 3
  · simp [hd]
  · simp only [hd, ↓reduceIte, ne_eq, not_false_eq_true, forall_const]
    exact chainFromC_lx pp adr idx i _ _ _

/-! ## The digests -/

/-- **The bottom layer's message digest over the model** (`xDigest0_complete`): two compressions
of the model's chain of its cells, answered. -/
theorem xDigest0_comp {σ : Val} {b : Nat} (hb9 : 129 ≤ b) {m0 m1 rho : E}
    (hl2 : LoadHolds rd (σ (.n 0)) 2 m0) (hl3 : LoadHolds rd (σ (.n 0)) 3 m1)
    (hpp : IsCanonical128 (σ (.n 1))) (hm0 : IsCanonical128 m0) (hm1 : IsCanonical128 m1)
    (hrho : IsCanonical128 rho) (hA : IsCanonical128 (σ (.n 128)))
    (hans : AnsCells CM [σ (.n 1), σ (.n 128) + word (tw 12) 0 0, m0, m1, rho]) :
    CompletesB CM.sem C rd b (b + 16) (xDigest0 b) σ (fun σ' =>
      σ' (.n (b + 2)) = σ (.n 128) + word (tw 12) 0 0 ∧
      σ' (.n (b + 14)) = (hcellC CM [σ (.n 1), σ (.n 128) + word (tw 12) 0 0, m0, m1, rho]).1 ∧
      AgreeBelow b σ σ') := by
  set A := σ (.n 128) + word (tw 12) 0 0
  set x := hmidC CM ![σ (.n 1), A, m0, m1]
  set o := hbC CM (blockBytes ![σ (.n 1), A, m0, m1] ++ [rho].flatMap cellBytes)
  set σ' := upds σ [(b, rho), (b + 1, word (tw 12) 0 0), (b + 2, A), (b + 3, m0), (b + 4, m1), (b + 5, iv0),
    (b + 6, iv1), (b + 7, mdw 64 false), (b + 8, x.1), (b + 9, x.2), (b + 10, word 0 0 0), (b + 11, word 0 0 0),
    (b + 12, word 0 0 0), (b + 13, mdw 80 true), (b + 14, o.1), (b + 15, o.2)]
  have he : Ext b (b + 16) σ σ' := upds_ext σ _ (by simp)
  have hk : ∀ k < b, σ' (.n k) = σ (.n k) := fun k hk => (he.agree k hk).symm
  have v : ∀ j < 16, σ' (.n (b + j)) = [rho, word (tw 12) 0 0, A, m0, m1, iv0, iv1, mdw 64 false, x.1, x.2,
      word 0 0 0, word 0 0 0, word 0 0 0, mdw 80 true, o.1, o.2].getD j 0 := fun j hj => by
    interval_cases j <;> simp [σ', upds]
  have hr : ([rho].flatMap cellBytes).length = 16 := by rw [length_flatMap_cellBytes']; rfl
  have hcmp := compress_two_C (CM := CM) (b0 := ![σ (.n 1), A, m0, m1])
    (blockBytes_one rho) (by rw [hr]; omega) (by rw [hr]; omega)
    (fin4_canonical.mpr ⟨hpp, isCanonical128_add hA (isCanonical128_word _ _), hm0, hm1⟩)
    (fin4_canonical.mpr ⟨hrho, isCanonical128_zero, isCanonical128_zero, isCanonical128_zero⟩)
    (by
      have e : blockBytes ![σ (.n 1), A, m0, m1] ++ [rho].flatMap cellBytes =
          [σ (.n 1), A, m0, m1, rho].flatMap cellBytes := by
        simp only [blockBytes_four, ← List.flatMap_append]; rfl
      rw [e]; exact hans)
  rw [hr] at hcmp
  refine ⟨σ', he, ⟨?_, ?_, he.agree⟩, fun next kret hn => ?_⟩
  · rw [v 2 (by omega)]; rfl
  · rw [v 14 (by omega)]
    show o.1 = _
    simp only [o, blockBytes_four, hcellC, ← List.flatMap_append]
    rfl
  · simp only [xDigest0, ivs, cst, b2s, addS, hintW, List.cons_append, List.nil_append, holdsListB_cons_atom,
      holdsListB_nil, Atom.HoldsB, true_and]
    have v0 := v 0 (by omega)
    rw [Nat.add_zero] at v0
    rw [v0, v 1 (by omega), v 2 (by omega), v 3 (by omega), v 4 (by omega), v 5 (by omega),
      show b + 5 + 1 = b + 6 by omega, v 6 (by omega), v 7 (by omega), v 8 (by omega), v 9 (by omega),
      v 10 (by omega), v 11 (by omega), v 12 (by omega), v 13 (by omega), v 14 (by omega), v 15 (by omega),
      hk 1 (by omega), hk 128 (by omega), hk 0 (by omega)]
    simp only [List.getD_cons_succ, List.getD_cons_zero, word_zero]
    obtain ⟨hc1, hc2⟩ := hcmp
    refine ⟨?_, ?_, hl2, hl3, ?_, ?_, ?_, hc1, ?_, ?_, ?_, ?_, hc2, hn⟩ <;> trivial

/-- **The top layer's message digest over the model** (`xDigest1_complete`). -/
theorem xDigest1_comp {σ : Val} {b : Nat} {root : V} (hb9 : 129 ≤ b) (hroot : NB b root) {rho : E}
    (hpp : IsCanonical128 (σ (.n 1))) (hrc : IsCanonical128 (σ root)) (hrho : IsCanonical128 rho)
    (hA : IsCanonical128 (σ (.n 80)))
    (hans : AnsCells CM [σ (.n 1), σ (.n 80) + word lxTop 0 0 + word (tw 12) 0 0, σ root, rho]) :
    CompletesB CM.sem C rd b (b + 10) (xDigest1 b root) σ (fun σ' =>
      σ' (.n (b + 1)) = σ (.n 80) + word lxTop 0 0 ∧
      σ' (.n (b + 4)) = σ (.n 80) + word lxTop 0 0 + word (tw 12) 0 0 ∧
      σ' (.n (b + 8)) = (hcellC CM [σ (.n 1), σ (.n 80) + word lxTop 0 0 + word (tw 12) 0 0, σ root, rho]).1 ∧
      AgreeBelow b σ σ') := by
  set I := σ (.n 80) + word lxTop 0 0
  set A := I + word (tw 12) 0 0
  set o := hcellC CM [σ (.n 1), A, σ root, rho]
  set σ' := upds σ [(b, word lxTop 0 0), (b + 1, I), (b + 2, rho), (b + 3, word (tw 12) 0 0), (b + 4, A),
    (b + 5, iv0), (b + 6, iv1), (b + 7, mdw 64 true), (b + 8, o.1), (b + 9, o.2)]
  have he : Ext b (b + 10) σ σ' := upds_ext σ _ (by simp)
  have hk : ∀ k < b, σ' (.n k) = σ (.n k) := fun k hk => (he.agree k hk).symm
  have v : ∀ j < 10, σ' (.n (b + j)) = [word lxTop 0 0, I, rho, word (tw 12) 0 0, A, iv0, iv1, mdw 64 true,
      o.1, o.2].getD j 0 := fun j hj => by
    interval_cases j <;> simp [σ', upds]
  have hcmp := compress4_C (CM := CM)
    ⟨hpp, isCanonical128_add (isCanonical128_add hA (isCanonical128_word _ _)) (isCanonical128_word _ _), hrc,
      hrho⟩ hans
  obtain ⟨kr, hkr, rfl⟩ := hroot
  refine ⟨σ', he, ⟨?_, ?_, ?_, he.agree⟩, fun next kret hn => ?_⟩
  · rw [v 1 (by omega)]; rfl
  · rw [v 4 (by omega)]; rfl
  · rw [v 8 (by omega)]; rfl
  · simp only [xDigest1, ivs, cst, b2s, addS, hintW, List.cons_append, List.nil_append, holdsListB_cons_atom,
      holdsListB_nil, Atom.HoldsB, true_and]
    have v0 := v 0 (by omega)
    rw [Nat.add_zero] at v0
    rw [v0, v 1 (by omega), v 2 (by omega), v 3 (by omega), v 4 (by omega), v 5 (by omega),
      show b + 5 + 1 = b + 6 by omega, v 6 (by omega), v 7 (by omega), v 8 (by omega), v 9 (by omega),
      hk 1 (by omega), hk 80 (by omega), hk kr hkr]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hcmp, hn⟩ <;> trivial


/-! ## The tail of a layer -/

variable {inst : HasQuery LeanXmss.HashSpec Option}

/-- **The tail of a layer is complete over the model** (`xTail_complete`): over a digest that
decodes, from chain values and siblings whose recovered chains, leaf and tree the scheme's run with
the model's answers returns, the root is the run's. -/
theorem xTail_comp (hq : XQW CM.H inst) {σ : Val} {L layer a : Nat} {idx d0 : V} (hl : layer < 2)
    (hrd : MemOK rd 64) (hpre : XPre σ L) {key : KeyIndex} (hkey : key.val = L / 2 ^ (16 * layer))
    (hidx : σ idx = eOfNat (xIdx layer L)) (ha : 139 ≤ a) (hidxB : NB a idx) (hd0B : NB a d0)
    (hpp : IsCanonical128 (σ (.n 1))) {enc : Encoding} (hdec : Codeword.decode (xv (σ d0)) = some enc)
    (hd0c : IsCanonical128 (σ d0)) {vals sibs : Nat → E} (hvals : ∀ i, IsCanonical128 (vals i))
    (hsibs : ∀ l, IsCanonical128 (sibs l)) {tips : ChainIndex → LeanXmss.Digest}
    {leafD r : LeanXmss.Digest}
    (htips : ∀ i, @recoverChain Option _ inst (xpp (σ (.n 1))) ⟨layer, hl⟩ key i (enc i) (xv (vals i.val)) =
      some (tips i))
    (hleafD : @leafHash Option _ inst (xpp (σ (.n 1))) ⟨layer, hl⟩ key tips = some leafD)
    (hr : @treeFold Option _ inst (xpp (σ (.n 1))) ⟨layer, hl⟩ key (fun l => xv (sibs l.val)) layerHeight
      leafD = some r) :
    CompletesB CM.sem C rd a (xTail layer a idx d0).2.1 (xTail layer a idx d0).1 σ (fun σ' =>
      xv (σ' (xTail layer a idx d0).2.2) = r ∧ IsCanonical128 (σ' (xTail layer a idx d0).2.2) ∧
        AgreeBelow a σ σ') := by
  set lay : Layer := ⟨layer, hl⟩
  obtain ⟨henc, hsum, hval⟩ := decode_some hdec
  set dig : Nat → Nat := fun i => (xv (σ d0)).toNat / 4 ^ i % 4 with hdig_def
  have hdig : ∀ i, dig i < 4 := fun i => Nat.mod_lt _ (by norm_num)
  have hL := hpre.lt
  have hcw : cCodeword (xW a idx) (fun s => .n (129 + s)) 19 xTarget d0 (a + 6) =
      cCodeword (xW' a idx) (fun s => .n (129 + s)) 19 xTarget d0 (a + 6) := cCodeword_congr (xW_congr a idx)
  simp only [xTail]
  rw [hcw]
  simp only [List.append_assoc]
  set cw := cCodeword (xW' a idx) (fun s => .n (129 + s)) 19 xTarget d0 (a + 6) with hcw_def
  set c := cw.2.1
  set tip : Nat → V := fun i => (cw.2.2.getD i (.n 0, .n 0)).1
  set leaf := hashValues (.n 1) (.n (c + 1)) tip 58 (c + 2)
  have hc6 : a + 6 < c := cCodeword_snd_gt _ _ _ _ _ _
  have htipB : ∀ i < 58, NB c (tip i) := cCodeword_tips_lt _ _ 19 _ _ _
  have hleafB : NB (c + 2 + hashValuesSize 58) leaf.2 := hashValues_snd_lt _ _ _ _ _
  have hmkge := merkle_snd_ge (.n 1) (fun l => .n (3 + 16 * layer + l)) (fun l => .n (128 - 3 * (16 * layer + l)))
    (fun l => tw 3 + (l + 1) * hiMul + layer * lxTop) (fun l => 16 * layer + l + 1 == 32) 16 0 leaf.2
    (c + 2 + hashValuesSize 58)
  have hw'B : (xW' a idx).Below (a + 6) :=
    ⟨⟨1, by omega, rfl⟩, ⟨2, by omega, rfl⟩, fun s => ⟨_, by have := Nat.min_le_right s 2; omega, rfl⟩,
      hidxB.mono (by omega)⟩
  have hpwB : ∀ s < 10, NB (a + 6) (V.n (129 + s)) := fun s hs => ⟨_, by omega, rfl⟩
  refine CompletesB.append (m := a + 6) (by omega) (by omega) (xStepAddrs_below hidxB)
    (CompletesB.of_free (F := []) (xStepAddrs_free idx a) (xStepAddrs_complete hidxB))
    fun σ1 he1 ⟨hS1, hag1⟩ => ?_
  have h1 : ∀ k < a, σ1 (.n k) = σ (.n k) := fun k hk => (hag1 k hk).symm
  have hidx1 : σ1 idx = σ idx := he1.below hidxB
  have hcan1 : (xW' a idx).Canon σ1 := ⟨by rw [Wots.pp', xW', xW]; rw [h1 1 (by omega)]; exact hpp,
    fun _ s => by
      simp only [Wots.adr', xW']
      rw [(hS1 (min s 2) (by omega)).2, hidx]
      exact isCanonical128_add (isCanonical128_eOfNat _) (isCanonical128_word _ _),
    fun h => absurd h (by simp [xW', xW])⟩
  -- the chains' steps are answered
  set adr1 : Nat → E := fun s => σ1 (.n (a + 2 * min s 2 + 1)) with hadr1_def
  have hadr1 : ∀ s : ChainStep, cellBytes (adr1 s.val) = tweakBytes (.chain lay key s) := fun s => by
    have hs : s.val < 3 := s.isLt
    simp only [hadr1_def]
    rw [Nat.min_eq_left (by omega), (hS1 s.val hs).2, hidx, chain_addr hL hl hs, tweakBytes_chain, hkey]
  have hch : ∀ i : ChainIndex, tipAns CM true (σ (.n 1)) adr1 0 i.val (dig i.val) (vals i.val) ∧
      xv (tipPairC CM true (σ (.n 1)) adr1 0 i.val (dig i.val) (vals i.val)).1 = tips i := by
    intro i
    have e := recoverChain_cellsE (pp := σ (.n 1)) (i := i) hq hadr1 (enc i) (vals i.val)
    rw [htips i, show (enc i).val = dig i.val from henc i] at e
    obtain ⟨p, hp, hpt⟩ := Option.map_eq_some_iff.mp e.symm
    obtain ⟨ha, rfl⟩ := (tipPairWith_eq_some_iff _ _ _ _ _ _ _).mp hp
    exact ⟨ha, hpt⟩
  have hcomp := cCodeword_comp (C := C) (w := xW' a idx) (power := fun s => .n (129 + s)) hrd (G := 19)
    (by norm_num) (target := xTarget) (d0 := d0) (b := a + 6) (σ := σ1) (by omega) hw'B hpwB (hd0B.mono (by omega))
    (by show σ1 (.n 2) = mdw 64 true; rw [h1 2 (by omega)]; exact hpre.md) hcan1
    (fun s hs => by show σ1 (.n (129 + s)) = _; rw [h1 _ (by omega)]; exact hpre.pow s hs)
    (dig := dig) hdig (xs := vals) hvals
    (fun i hi => by
      show tipAns CM true (σ1 (.n 1)) adr1 (σ1 idx) i (dig i) (vals i)
      rw [(tipPairC_lx _ _ _ _ _ _).2, h1 1 (by omega)]
      exact (hch ⟨i, by simp [numChains]; omega⟩).1)
    (by rw [xTarget_eq]; exact congrArg (gen ^ ·) hsum.symm)
    (by rw [he1.below hd0B, ← cellOf_cellVal hd0c, show cellVal (σ d0) = xv (σ d0) from rfl, ← lit_toNat]
        exact congrArg lit hval)
  refine CompletesB.append (m := c) (by omega) (by omega) (cCodeword_below (by norm_num) (by omega) hw'B hpwB
    (hd0B.mono (by omega))) hcomp.withExt fun σ2 he2 ⟨hT2, he2'⟩ => ?_
  have h2 : ∀ k < a + 6, σ2 (.n k) = σ1 (.n k) := fun k hk => (he2'.agree k hk).symm
  have hidx2 : σ2 idx = σ idx := by rw [he2'.below (hidxB.mono (by omega)), hidx1]
  have hp2 : σ2 (.n 1) = σ (.n 1) := by rw [h2 1 (by omega), h1 1 (by omega)]
  -- the leaf address
  set A0 := word (tw 2) 0 0
  have ne : ∀ i j : Nat, i ≠ j → (V.n i) ≠ V.n j := fun i j h e => h (by cases e; rfl)
  obtain ⟨kI, hkI, hkIe⟩ := hidxB
  rw [hkIe] at hidx1 hidx2 hidx hS1 ⊢
  refine CompletesB.append (m := c + 2) (by omega) (by omega)
    (show NumBelow (c + 2) (Stmt.valsList [cst c A0, addS (.n (c + 1)) (.n kI) (.n c)]) from
      .cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩
        (.nil _)))))
    (P := fun σ' => σ' (.n (c + 1)) = σ2 (.n kI) + A0 ∧ AgreeBelow c σ2 σ')
    (CompletesB.atom_cons A0 (by omega) (.cons ⟨_, by omega, rfl⟩ (.nil _)) (Function.update_self _ _ _)
      (CompletesB.atom_cons (σ2 (.n kI) + A0) (by omega)
        (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.nil _))))
        (by
          show Function.update (Function.update σ2 (.n c) A0) (.n (c + 1)) (σ2 (.n kI) + A0) (.n (c + 1)) =
            Function.update (Function.update σ2 (.n c) A0) (.n (c + 1)) (σ2 (.n kI) + A0) (.n kI) +
            Function.update (Function.update σ2 (.n c) A0) (.n (c + 1)) (σ2 (.n kI) + A0) (.n c)
          have h1 : kI ≠ c := by omega
          have h2 : kI ≠ c + 1 := by omega
          simp [h1, h2])
        (CompletesB.nil _ _ _ ⟨Function.update_self _ _ _, fun k hk => by
          rw [Function.update_of_ne (ne _ _ (by omega)), Function.update_of_ne (ne _ _ (by omega))]⟩)))
    fun σ3 he3 ⟨hA3, hag3⟩ => ?_
  have h3 : ∀ k < c, σ3 (.n k) = σ2 (.n k) := fun k hk => (hag3 k hk).symm
  have hp3 : σ3 (.n 1) = σ (.n 1) := by rw [h3 1 (by omega), hp2]
  have hI : IsCanonical128 (σ2 (.n kI)) := by rw [hidx2, hidx]; exact isCanonical128_eOfNat _
  have htip3 : ∀ i < 58, σ3 (tip i) = (tipPairC CM true (σ (.n 1)) (fun s => σ2 (.n (a + 2 * min s 2 + 1)))
      (σ2 idx) i (dig i) (vals i)).1 := fun i hi => by
    obtain ⟨k, hk, e⟩ := htipB i hi
    have := (hT2 i hi).1
    simp only [tip] at e ⊢
    rw [e, h3 k hk, ← e]
    refine this.trans ?_
    show (tipPairC CM true (σ2 (.n 1)) (fun s => σ2 (.n (a + 2 * min s 2 + 1))) (σ2 idx) i (dig i) (vals i)).1 = _
    rw [hp2]
  have hadr2 : (fun s => σ2 (.n (a + 2 * min s 2 + 1))) = adr1 := by
    funext s; simp only [hadr1_def]; rw [h2 _ (by have := Nat.min_le_right s 2; omega)]
  have htip3' : ∀ i < 58, σ3 (tip i) = (tipPairC CM true (σ (.n 1)) adr1 0 i (dig i) (vals i)).1 := fun i hi => by
    rw [htip3 i hi, hadr2, (tipPairC_lx _ _ _ _ _ _).1]
  have htipsE : tips = fun i => xv (σ3 (tip i.val)) := by
    funext i; rw [htip3' i.val i.isLt, (hch i).2]
  have hcanT : ∀ i < 58, IsCanonical128 (σ3 (tip i)) := fun i hi => by
    rw [htip3 i hi]; exact canonical_tipPairC _ _ _ _ _ _ (hvals i)
  -- the leaf is answered
  have hleafAdr : cellBytes (σ3 (.n (c + 1))) = tweakBytes (.leaf lay key) := by
    rw [hA3, hidx2, hidx, tag_addr hL hl (by norm_num), tweakBytes_leaf, hkey]
  have hlf := leafHash_cellsE (pp := σ3 (.n 1)) hq (fun i => σ3 (tip i)) hleafAdr
  rw [hp3, ← htipsE, hleafD, show numChains = 58 from rfl] at hlf
  obtain ⟨o, ho, hlo⟩ := Option.map_eq_some_iff.mp hlf.symm
  obtain ⟨hlans, rfl⟩ := hcellWith_eq_some_iff.mp ho
  have hv := hashValues_comp (CM := CM) (C := C) (rd := rd) (σ := σ3) (pp := .n 1) (a := .n (c + 1)) (val := tip)
    (n := 58) (b := c + 2) (Or.inr (by norm_num)) (by norm_num)
    ⟨⟨1, by omega, rfl⟩, ⟨c + 1, by omega, rfl⟩, fun i hi => (htipB i hi).mono (by omega)⟩
    ⟨by rw [hp3]; exact hpp, by rw [hA3]; exact isCanonical128_add hI (isCanonical128_word _ _), hcanT⟩
    (by rw [hp3]; exact hlans)
  refine CompletesB.append (m := c + 2 + hashValuesSize 58) (by omega) (by omega)
    (hashValues_below (by norm_num) ⟨⟨1, by omega, rfl⟩, ⟨c + 1, by omega, rfl⟩,
      fun i hi => (htipB i hi).mono (by omega)⟩) hv.withExt fun σ4 he4 ⟨hleaf4, he4'⟩ => ?_
  have hσ4 : ∀ k < a, σ4 (.n k) = σ (.n k) := fun k hk => by
    rw [← he4'.agree k (by omega), h3 k (by omega), h2 k (by omega), h1 k hk]
  have hpre4 : XPre σ4 L := hpre.congr fun k hk => (hσ4 k (by omega)).symm
  have hleafc : IsCanonical128 (σ4 leaf.2) := by rw [hleaf4]; exact (isCanonical128_hcellC _).1
  -- the tree is answered
  have htr := treeFold_cellsE (pp := σ (.n 1)) hq (node_cells hl hpre hkey) sibs layerHeight le_rfl (σ4 leaf.2)
  rw [hleaf4, hp3, hlo, hr] at htr
  obtain ⟨y, hy, hyr⟩ := Option.map_eq_some_iff.mp htr.symm
  obtain ⟨hyans, hyv⟩ := (mFoldWith_eq_some_iff _ _ _ _ _ _ _).mp hy
  rw [show layerHeight = 16 from rfl] at hyans hyv
  have hMA : mAddr σ4 (fun l => .n (128 - 3 * (16 * layer + l))) (fun l => tw 3 + (l + 1) * hiMul + layer * lxTop)
      (fun l => 16 * layer + l + 1 == 32) = mAddr σ (fun l => .n (128 - 3 * (16 * layer + l)))
      (fun l => tw 3 + (l + 1) * hiMul + layer * lxTop) (fun l => 16 * layer + l + 1 == 32) :=
    mAddr_congr hσ4 (by omega)
  have hmk := merkle_comp (CM := CM) (C := C) (rd := rd) (pp := .n 1) (bit := fun l => .n (3 + 16 * layer + l))
    (node := fun l => .n (128 - 3 * (16 * layer + l))) (addr := fun l => tw 3 + (l + 1) * hiMul + layer * lxTop)
    (isEnd := fun l => 16 * layer + l + 1 == 32) (β := fun l => key.val.testBit l) (sibs := sibs) 16 0 leaf.2
    (c + 2 + hashValuesSize 58) σ4 ⟨1, by omega, rfl⟩ hleafB
    (fun l' _ hl' => ⟨⟨_, by omega, rfl⟩, ⟨_, by omega, rfl⟩⟩)
    (fun l' _ hl' => ⟨by
        show σ4 (.n (3 + 16 * layer + l')) = _
        rw [show 3 + 16 * layer + l' = 3 + (16 * layer + l') by omega, hpre4.bits _ (by omega), hkey,
          Nat.testBit_div_two_pow, Nat.add_comm l'],
      hsibs l', canonical_mAddr hpre4 hl (by omega)⟩)
    (by rw [hσ4 1 (by omega)]; exact hpp) hleafc
    (by rw [hMA, hσ4 1 (by omega), hleaf4, hp3]; exact hyans)
  refine hmk.withExt.mono le_rfl le_rfl fun σ5 ⟨hroot5, he5⟩ => ⟨?_, ?_, fun k hk => ?_⟩
  · rw [hroot5, hMA, hσ4 1 (by omega), hleaf4, hp3, hyv, hyr]
  · rw [hroot5]; exact mFoldC_canonical _ _ _ _ _ _ _ (Or.inl (by norm_num))
  · rw [← he5.agree k (by omega), ← hσ4 k hk]



/-! ## The layers -/

/-- **The bottom layer is complete over the model** (`xLayer0_complete`): for a layer signature
whose root the scheme's run with the model's answers recovers. -/
theorem xLayer0_comp (hq : XQW CM.H inst) (hrd : MemOK rd 64) {σ : Val} {L b : Nat} {root : V} (hpre : XPre σ L)
    {key : KeyIndex} (hkey : key.val = L) (hb : 139 ≤ b) {m0 m1 : E} (hl2 : LoadHolds rd (σ (.n 0)) 2 m0)
    (hl3 : LoadHolds rd (σ (.n 0)) 3 m1) (hpp : IsCanonical128 (σ (.n 1))) (hm0 : IsCanonical128 m0)
    (hm1 : IsCanonical128 m1) {part : LayerSignature} {r : LeanXmss.Digest}
    (hr : @layerRoot Option _ inst (xpp (σ (.n 1))) bottomLayer key (cellBytes m0 ++ cellBytes m1) part =
      some (some r)) :
    CompletesB CM.sem C rd b (xLayer 0 b root).2.1 (xLayer 0 b root).1 σ (fun σ' =>
      σ' (xLayer 0 b root).2.2 = cellOf r ∧ AgreeBelow b σ σ') := by
  obtain ⟨dD, enc, tips, leafD, hdD, hdec, htips, hleafD, htree⟩ := layerRoot_someW hr
  have hkey' : key.val = L / 2 ^ (16 * 0) := by rw [hkey]; simp
  have hidx : σ (.n 128) = eOfNat (xIdx 0 L) := by
    have := hpre.nodes 0 (by omega)
    simpa [xIdx] using this
  have hgt := xLayer_snd_gt 0 b root (by omega)
  rw [xLayer_zero] at hgt ⊢
  dsimp only at hgt ⊢
  have hmd := messageDigest_cellsE (pp := σ (.n 1)) (rho := cellOf part.randomness) hq
    (a := σ (.n 128) + word (tw 12) 0 0) (cs := [m0, m1]) (lay := bottomLayer) (key := key)
    (Mi := cellBytes m0 ++ cellBytes m1) (by
      rw [hidx, tag_addr hpre.lt (by omega) (by omega), tweakBytes_message, hkey',
        show (bottomLayer : Layer).val = 0 from rfl]) (by simp)
  rw [show xv (cellOf part.randomness) = part.randomness from cellVal_cellOf _, hdD] at hmd
  obtain ⟨o, ho, hdo⟩ := Option.map_eq_some_iff.mp hmd.symm
  obtain ⟨hans, rfl⟩ := hcellWith_eq_some_iff.mp ho
  refine CompletesB.append (m := b + 16) (by omega) (by omega) (xDigest0_below b (by omega))
    (xDigest0_comp (rho := cellOf part.randomness) (by omega) hl2 hl3 hpp hm0 hm1 (isCanonical128_cellOf _)
      (by rw [hidx]; exact isCanonical128_eOfNat _) (by simpa using hans))
    fun σ1 he1 ⟨hA1, hd1, hag1⟩ => ?_
  have h1 : ∀ k < b, σ1 (.n k) = σ (.n k) := fun k hk => (hag1 k hk).symm
  have hpre1 : XPre σ1 L := hpre.congr fun k hk => (h1 k (by omega)).symm
  have hdec1 : Codeword.decode (xv (σ1 (.n (b + 14)))) = some enc := by
    rw [hd1, ← hdec, ← hdo]; simp
  have hd1c : IsCanonical128 (σ1 (.n (b + 14))) := by rw [hd1]; exact (isCanonical128_hcellC _).1
  have hpath : part.path = fun l => xv (sibsOf part l.val) := funext fun l => (xv_sibsOf part l).symm
  refine (xTail_comp (inst := inst) hq (layer := 0) (a := b + 16) (by omega) hrd hpre1 hkey'
    (by rw [h1 128 (by omega)]; exact hidx) (by omega) ⟨128, by omega, rfl⟩ ⟨b + 14, by omega, rfl⟩
    (by rw [h1 1 (by omega)]; exact hpp) hdec1 hd1c (canonical_valsOf part) (canonical_sibsOf part)
    (tips := tips) (leafD := leafD) (r := r) (fun i => by rw [h1 1 (by omega), xv_valsOf]; exact htips i)
    (by rw [h1 1 (by omega)]; exact hleafD) (by rw [h1 1 (by omega), ← hpath]; exact htree)).mono le_rfl le_rfl
    fun σ2 ⟨heq, hcan, hag2⟩ => ⟨?_, fun k hk => (hag1 k hk).trans (hag2 k (by omega))⟩
  rw [← cellOf_cellVal hcan, show cellVal _ = xv _ from rfl, heq]

/-- **The top layer is complete over the model** (`xLayer1_complete`). -/
theorem xLayer1_comp (hq : XQW CM.H inst) (hrd : MemOK rd 64) {σ : Val} {L b : Nat} {root : V} (hpre : XPre σ L)
    {key : KeyIndex} (hkey : key.val = L / 2 ^ 16) (hb : 139 ≤ b) (hroot : NB b root)
    (hpp : IsCanonical128 (σ (.n 1))) (hrc : IsCanonical128 (σ root)) {part : LayerSignature} {r : LeanXmss.Digest}
    (hr : @layerRoot Option _ inst (xpp (σ (.n 1))) topLayer key (cellBytes (σ root)) part = some (some r)) :
    CompletesB CM.sem C rd b (xLayer 1 b root).2.1 (xLayer 1 b root).1 σ (fun σ' =>
      σ' (xLayer 1 b root).2.2 = cellOf r ∧ AgreeBelow b σ σ') := by
  obtain ⟨dD, enc, tips, leafD, hdD, hdec, htips, hleafD, htree⟩ := layerRoot_someW hr
  have hkey' : key.val = L / 2 ^ (16 * 1) := by rw [hkey]
  have hI := idx_top hpre
  have hgt := xLayer_snd_gt 1 b root (by omega)
  rw [xLayer_one] at hgt ⊢
  dsimp only at hgt ⊢
  have hmd := messageDigest_cellsE (pp := σ (.n 1)) (rho := cellOf part.randomness) hq
    (a := σ (.n 80) + word lxTop 0 0 + word (tw 12) 0 0) (cs := [σ root]) (lay := topLayer) (key := key)
    (Mi := cellBytes (σ root)) (by
      rw [hI, tag_addr hpre.lt (by omega) (by omega), tweakBytes_message, hkey',
        show (topLayer : Layer).val = 1 from rfl]) (by simp)
  rw [show xv (cellOf part.randomness) = part.randomness from cellVal_cellOf _, hdD] at hmd
  obtain ⟨o, ho, hdo⟩ := Option.map_eq_some_iff.mp hmd.symm
  obtain ⟨hans, rfl⟩ := hcellWith_eq_some_iff.mp ho
  refine CompletesB.append (m := b + 10) (by omega) (by omega) (xDigest1_below b (by omega) hroot)
    (xDigest1_comp (rho := cellOf part.randomness) (by omega) hroot hpp hrc (isCanonical128_cellOf _)
      (by have := hpre.nodes 16 (by omega); rw [show 128 - 3 * 16 = 80 by omega] at this
          rw [this]; exact isCanonical128_eOfNat _) (by simpa using hans))
    fun σ1 he1 ⟨hI1, hA1, hd1, hag1⟩ => ?_
  have h1 : ∀ k < b, σ1 (.n k) = σ (.n k) := fun k hk => (hag1 k hk).symm
  have hpre1 : XPre σ1 L := hpre.congr fun k hk => (h1 k (by omega)).symm
  have hdec1 : Codeword.decode (xv (σ1 (.n (b + 8)))) = some enc := by
    rw [hd1, ← hdec, ← hdo]; simp
  have hd1c : IsCanonical128 (σ1 (.n (b + 8))) := by rw [hd1]; exact (isCanonical128_hcellC _).1
  have hpath : part.path = fun l => xv (sibsOf part l.val) := funext fun l => (xv_sibsOf part l).symm
  refine (xTail_comp (inst := inst) hq (layer := 1) (a := b + 10) (by omega) hrd hpre1 hkey'
    (by rw [hI1, hI]) (by omega) ⟨b + 1, by omega, rfl⟩ ⟨b + 8, by omega, rfl⟩
    (by rw [h1 1 (by omega)]; exact hpp) hdec1 hd1c (canonical_valsOf part) (canonical_sibsOf part)
    (tips := tips) (leafD := leafD) (r := r) (fun i => by rw [h1 1 (by omega), xv_valsOf]; exact htips i)
    (by rw [h1 1 (by omega)]; exact hleafD) (by rw [h1 1 (by omega), ← hpath]; exact htree)).mono le_rfl le_rfl
    fun σ2 ⟨heq, hcan, hag2⟩ => ⟨?_, fun k hk => (hag1 k hk).trans (hag2 k (by omega))⟩
  rw [← cellOf_cellVal hcan, show cellVal _ = xv _ from rfl, heq]

/-! ## The body -/

/-- **`verify_lean_xmss` is complete over the model** (`verify_lean_xmss_complete`): for a claim
at `p` that some signature verifies with the model's answered hash, on a memory holding at least
64 words, the body holds under the model's semantics from a valuation with `p` as its argument. -/
theorem verify_lean_xmss_comp (hrd : MemOK rd 64) {p : E} {pk : LeanXmss.PublicKey} {m : LeanXmss.Message}
    {sig : LeanXmss.Signature} (hc : ClaimAt rd p (claimCells pk.root pk.parameter m))
    (hv : Node.xmssVerifyWith CM.H pk m sig = some true) :
    ∃ σ : Val, σ (.n 0) = p ∧ Stmt.HoldsListB CM.sem C rd σ xBody False (fun rs => rs = []) := by
  have hv' : @LeanXmss.Concrete.verify Option _ ⟨fun x ↦ Node.digestBits <$> CM.H x⟩ pk m sig =
      some true := hv
  generalize hI : (⟨fun x ↦ Node.digestBits <$> CM.H x⟩ : HasQuery LeanXmss.HashSpec Option) = inst at hv'
  have hq : XQW CM.H inst := hI ▸ xqw_with CM.H
  obtain ⟨r0, h0, h1⟩ := verify_someW hv'
  have h0' : @layerRoot Option _ inst (xpp (cellOf pk.parameter)) bottomLayer (keyAt sig.leafIndex bottomLayer)
      (cellBytes (cellOf (m.extractLsb' 0 128)) ++ cellBytes (cellOf (m.extractLsb' 128 128)))
      (sig.layers bottomLayer) = some (some r0) := by
    rw [← message_bytes, show xpp (cellOf pk.parameter) = pk.parameter from cellVal_cellOf _]
    exact h0
  have h1' : @layerRoot Option _ inst (xpp (cellOf pk.parameter)) topLayer (keyAt sig.leafIndex topLayer)
      (cellBytes (cellOf r0)) (sig.layers topLayer) = some (some pk.root) := by
    rw [cellBytes_cellOf r0, show xpp (cellOf pk.parameter) = pk.parameter from cellVal_cellOf _]
    exact h1
  have hL : sig.leafIndex.val < 2 ^ 32 := sig.leafIndex.isLt
  have hgt0 := xLayer_snd_gt 0 139 (.n 0) (by omega)
  have hgt1 := xLayer_snd_gt 1 (xLayer 0 139 (.n 0)).2.1 (xLayer 0 139 (.n 0)).2.2 (by omega)
  have hroot0 := xLayer_root_lt 0 139 (.n 0) (by omega)
  have hroot1 := xLayer_root_lt 1 (xLayer 0 139 (.n 0)).2.1 (xLayer 0 139 (.n 0)).2.2 (by omega)
  rw [xBody_split]
  set l0 := xLayer 0 139 (.n 0)
  set l1 := xLayer 1 l0.2.1 l0.2.2
  have hcomp : CompletesB CM.sem C rd 1 (l1.2.1 + 1) (xPrologue ++ (l0.1 ++ (l1.1 ++
      [.atom (.load (.n l1.2.1) (.n 0) 0), .atom (.assertEq l1.2.2 (.n l1.2.1))]))) (fun _ => p) (fun _ => True) := by
    refine CompletesB.append (m := 139) (by omega) (by omega) xPrologue_below (CompletesB.of_free (F := []) xPrologue_free (xPrologue_complete (hc 1) hL))
      fun σ1 _ ⟨hpre1, hpp1, hag1⟩ => ?_
    have hp1 : σ1 (.n 0) = p := (hag1 0 (by omega)).symm
    have hpar : σ1 (.n 1) = cellOf pk.parameter := hpp1
    refine CompletesB.append (m := l0.2.1) (by omega) (by omega) (xLayer0_below 139 le_rfl _)
      (xLayer0_comp (inst := inst) hq hrd hpre1
        (key := keyAt sig.leafIndex bottomLayer) (keyAt_bottom_val _) le_rfl (by rw [hp1]; exact hc 2)
        (by rw [hp1]; exact hc 3) (by rw [hpar]; exact isCanonical128_cellOf _) (isCanonical128_cellOf _)
        (isCanonical128_cellOf _) (part := sig.layers bottomLayer) (r := r0)
        (by rw [hpar]; exact h0'))
      fun σ2 _ ⟨hr2, hag2⟩ => ?_
    have hpre2 : XPre σ2 sig.leafIndex.val := hpre1.congr hag2
    have h21 : σ2 (.n 1) = cellOf pk.parameter := (hag2 1 (by omega)).symm.trans hpar
    refine CompletesB.append (m := l1.2.1) (by omega) (by omega) (xLayer1_below _ (by omega) hroot0)
      (xLayer1_comp (inst := inst) hq hrd hpre2
        (key := keyAt sig.leafIndex topLayer) (keyAt_top_val _) (by omega) hroot0
        (by rw [h21]; exact isCanonical128_cellOf _) (by rw [hr2]; exact isCanonical128_cellOf _)
        (part := sig.layers topLayer) (r := pk.root)
        (by rw [h21, hr2]; exact h1'))
      fun σ3 _ ⟨hr3, hag3⟩ => ?_
    have h30 : σ3 (.n 0) = p := ((hag3 0 (by omega)).symm.trans (hag2 0 (by omega)).symm).trans hp1
    obtain ⟨kr, hkr, hkre⟩ := hroot1
    have hne0 : (V.n 0) ≠ V.n l1.2.1 := fun e => by simp only [V.mk.injEq] at e; omega
    have hner : l1.2.2 ≠ V.n l1.2.1 := fun e => by rw [hkre] at e; simp only [V.mk.injEq] at e; omega
    refine CompletesB.atom_cons (cellOf pk.root) le_rfl
      (.cons ⟨_, by omega, rfl⟩ (.cons ⟨0, by omega, rfl⟩ (.nil _))) ?_ ?_
    · show LoadHolds rd (Function.update σ3 (.n l1.2.1) (cellOf pk.root) (.n 0)) 0
        (Function.update σ3 (.n l1.2.1) (cellOf pk.root) (.n l1.2.1))
      rw [Function.update_self, Function.update_of_ne hne0, h30]
      exact hc 0
    refine CompletesB.atom_cons0 (.cons ⟨kr, by omega, hkre⟩ (.cons ⟨_, by omega, rfl⟩ (.nil _))) ?_
      (CompletesB.nil _ _ _ trivial)
    show Function.update σ3 (.n l1.2.1) (cellOf pk.root) l1.2.2 +
      Function.update σ3 (.n l1.2.1) (cellOf pk.root) (.n l1.2.1) = 0
    rw [Function.update_self, Function.update_of_ne hner, hr3]
    exact e_add_eq_zero_iff.mpr rfl
  obtain ⟨σ', he, -, hh⟩ := hcomp
  refine ⟨σ', he.apply (Or.inl (by norm_num)), ?_⟩
  have hret : Stmt.HoldsListB CM.sem C rd σ' [.ret []] False (fun rs => rs = []) := by
    simp only [Stmt.HoldsListB, Stmt.HoldsB, List.map_nil]
  rw [holdsListB_append]
  exact hh _ _ hret




/-- **`verify_lean_xmss` is its meaning's completeness over the model** (`verify_lean_xmss_iff.mpr`):
on a memory holding at least 64 words, a claim some signature verifies with the model's answered
hash is in the call relation under the model's semantics. -/
theorem verify_lean_xmss_rel_comp {CM : CompModel} {rd : Reader} (hrd : MemOK rd 64) {args rets : List E}
    (h : Meaning_verify_lean_xmssWith CM.H rd args rets) :
    coreProgram.RelB CM.sem rd "verify_lean_xmss" args rets := by
  obtain ⟨p, ha, hr, pk, m, hc, sig, hv⟩ := h
  obtain ⟨σ, hσ, hb⟩ := verify_lean_xmss_comp (C := coreProgram.RelB CM.sem rd) hrd hc hv
  refine (relB_iff_sem find_verify_lean_xmss args rets).mpr ⟨σ, by rw [ha]; simp [hσ], ?_⟩
  rw [hr]
  exact hb

/-- The deployed `verify_lean_xmss_iff.mpr`, from the model's at `CompModel.deployed`. -/
theorem verify_lean_xmss_rel_of_comp {rd : Reader} (hrd : MemOK rd 64) {args rets : List E}
    (h : Meaning_verify_lean_xmss rd args rets) : coreProgram.Rel rd "verify_lean_xmss" args rets := by
  obtain ⟨p, ha, hr, pk, m, hc, sig, hv⟩ := h
  have := verify_lean_xmss_rel_comp (CM := CompModel.deployed) hrd
    ⟨p, ha, hr, pk, m, hc, sig, by rw [show CompModel.deployed.H = fun x ↦ some (blake2sBytes x) from rfl,
      LeanVM.E2E.xmssVerifyWith_some_blake2s, hv]⟩
  rwa [show CompModel.deployed.sem = blakeDeployed from rfl, relB_deployed] at this

end
end LeanVM.Guest.B1.Sig
