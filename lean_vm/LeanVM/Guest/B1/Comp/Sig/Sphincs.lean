/-
  LeanVM.Guest.B1.Comp.Sig.Sphincs

  `verify_sig_lean_sphincs` complete over a completeness model: for a claim some signature
  verifies with the model's answered hash, the body holds under the model's semantics.
-/

module

public import LeanVM.Guest.B1.Comp.Sig.SphincsBody
public import LeanVM.Guest.B1.Comp.Sig.SphincsTail
public import LeanVM.Guest.B1.Comp.Sig.SphincsCoord
public import LeanVM.Guest.B1.Comp.Sig.Xmss
public import LeanVM.Guest.B1.Sig.SphincsIff

/-!
# `verify_sig_lean_sphincs` over a completeness model

The deployed `verify_sig_lean_sphincs_complete` (`SphincsIff.lean`) over a `CompModel`: the scheme's
run with the model's answered hash taken apart (`sVerify_someInv`, `sOtsLeaf_someInv`,
`sForestRecover_someInv`), every block's hashes preset to the model's answers — the prologue
(`sPrologue_comp`), the coordinates (`sCoords_comp`, the forest keys complete over the model,
`FkCompleteC`), the lanes, the forest key's digest (`hashValues_comp`), the counter (`sCounter_comp`)
and the tail (`sTail_comp`).

* `verify_sig_lean_sphincs_comp`: the body;
* `verify_sig_lean_sphincs_rel_comp`: its meaning with the model's hash is in the call relation
  under the model's semantics (`verify_sig_lean_sphincs_iff.mpr`); at the deployed model
  `verify_sig_lean_sphincs_rel_of_comp`.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.E2E.Complete

@[expose] public section

variable {CM : CompModel} {C : CallRel} {rd : Reader}

theorem holds_of_completesB {p : E} {X : List Stmt} {hi : Nat}
    (h : CompletesB CM.sem C rd 1 hi X (fun _ => p) (fun _ => True)) :
    ∃ σ : Val, σ (.n 0) = p ∧ Stmt.HoldsListB CM.sem C rd σ (X ++ [.ret []]) False (fun rs => rs = []) := by
  obtain ⟨σ', he, -, hh⟩ := h
  refine ⟨σ', he.apply (Or.inl (by norm_num)), ?_⟩
  have hret : Stmt.HoldsListB CM.sem C rd σ' [.ret []] False (fun rs => rs = []) := by
    simp only [Stmt.HoldsListB, Stmt.HoldsB, List.map_nil]
  rw [holdsListB_append]
  exact hh _ _ hret


/-- **`verify_sig_lean_sphincs` is complete over the model** (`verify_sig_lean_sphincs_complete`): for
a claim at `p` that some signature verifies with the model's answered hash, on a memory holding at
least 256 words, with the forest keys complete over the model, the body holds under the model's
semantics from a valuation with `p` as its argument. -/
theorem verify_sig_lean_sphincs_comp (hfk : FkCompleteC CM C) (hrd : MemOK rd 256) {p : E}
    {pk : Sphincs.PublicKey} {m : Sphincs.Message} {sig : Sphincs.Signature}
    (hc : ClaimAt rd p (claimCells pk.root pk.parameter m))
    (hv : Node.sphincsVerifyWith CM.H pk m sig = some true) :
    ∃ σ : Val, σ (.n 0) = p ∧ Stmt.HoldsListB CM.sem C rd σ sBody False (fun rs => rs = []) := by
  have hv' : @Sphincs.Concrete.verify Option _ ⟨fun x ↦ Node.digestBits <$> CM.H x⟩ pk m sig = some true := hv
  generalize hI : (⟨fun x ↦ Node.digestBits <$> CM.H x⟩ : HasQuery Sphincs.HashSpec Option) = inst at hv'
  have hq : SQW CM.H inst := hI ▸ sqw_with CM.H
  obtain ⟨D, fk, lv, hD0, hF, hots, htree⟩ := sVerify_someInv hv'
  -- the message digest
  set pp := cellOf pk.parameter
  set m0 := cellOf (m.extractLsb' 0 128)
  set m1 := cellOf (m.extractLsb' 128 128)
  set rho := cellOf sig.randomness
  have hspp : spp pp = pk.parameter := cellVal_cellOf _
  have hsrho : sv rho = sig.randomness := cellVal_cellOf _
  have hmsg : Sphincs.bytesLE 32 m = cellBytes m0 ++ cellBytes m1 := by
    exact (sphincs_bytesLE_eq 32 m).trans ((bytesLE_eq 32 m).symm.trans (message_bytes m))
  have htw12 : cellBytes (word (tw 12) 0 0) = Sphincs.tweakBytes .message := by
    rw [Sphincs.tweakBytes, Sphincs.hashDomainFields, sTweak, word_eq_eOfNat]
    rfl
  have hmd := sMessageDigest_cellsE (H := CM.H) (inst := inst) (pp := pp) (rho := rho) (root := pk.root) hq
    htw12 hmsg
  rw [hspp, hsrho, hD0] at hmd
  obtain ⟨o, ho, hDo⟩ := Option.map_eq_some_iff.mp hmd.symm
  obtain ⟨hans0, rfl⟩ := hcellWith_eq_some_iff.mp ho
  set H := hcellC CM [pp, word (tw 12) 0 0, m0, m1, rho]
  set x0 := cellNat H.1
  set x1 := cellNat H.2
  have hx0 : x0 < 2 ^ 128 := cellNat_lt _
  subst hDo
  rw [← dMarks_eq x0 x1] at hF
  rw [← hspp] at hF hots htree
  set N := x1 % 2 ^ 26
  set U := x1 / 2 ^ 106
  set index := Sphincs.Concrete.digestIndex (BitVec.ofNat Sphincs.messageDigestBits (x0 + 2 ^ 128 * x1))
  have hindex : index.val = N := digestIndex_ofNat hx0
  have hN : N < 2 ^ 26 := Nat.mod_lt _ (by positivity)
  have hU : U < 2 ^ 22 := by
    have := cellNat_lt H.2
    exact (Nat.div_lt_iff_lt_mul (by positivity)).mpr (by norm_num at this ⊢; omega)
  set marks := dMarks x0 x1
  set openings : Nat → Sphincs.CoordOpening := fun r => sig.forest ⟨r % 8, Nat.mod_lt _ (by norm_num)⟩
  have hopen : (fun c : Sphincs.Coord => openings c.val) = sig.forest :=
    funext fun c => congrArg _ (Fin.ext (Nat.mod_eq_of_lt c.isLt))
  rw [← hopen] at hF
  set leaf := Sphincs.Concrete.leafIndexAt index Sphincs.topLayer
  have hleaf : leaf.val = N := (leafIndexAt_top index).trans hindex
  obtain ⟨dg, enc, tips, henc, hdecE, hrec, hleafD⟩ := sOtsLeaf_someInv hots
  obtain ⟨tops, hcR, hroots⟩ := sForestRecover_someInv hF
  set topsN : Nat → Sphincs.Digest × Sphincs.Digest := fun r => tops ⟨r % 8, Nat.mod_lt _ (by norm_num)⟩
  -- the layout
  rw [sBody_split]
  have hbge := sCoords_snd_ge 8 0 (.n 209) 210
  obtain ⟨hbB, houts⟩ := sCoords_outs_lt 8 0 (.n 209) 210 ⟨209, by omega, rfl⟩
  set cs := sCoords 8 0 (.n 209) 210
  set b := cs.2.1
  have hmkge := sMk_ge (b + 45 + 2 + hashValuesSize 16 + 126)
  have hhv16 : 0 < hashValuesSize 16 := by decide
  -- the prologue
  refine holds_of_completesB (hi := (sMk (b + 45 + 2 + hashValuesSize 16 + 126)).2.2 + 1) ?_
  refine CompletesB.append (m := 210) (by omega) (by omega) sPrologue_below
    (sPrologue_comp (pp := pp) (m0 := m0) (m1 := m1) (rho := rho) (hc 1) (hc 2) (hc 3)
      (isCanonical128_cellOf _) (isCanonical128_cellOf _) (isCanonical128_cellOf _) (isCanonical128_cellOf _)
      hans0 hN hU) fun σ1 _ ⟨hpre1, hp1, _, _, _, hH1, hag1⟩ => ?_
  have h01 : σ1 (.n 0) = p := (hag1 0 (by omega)).symm
  have hidx1 : σ1 (.n 142) = eOfNat index.val := by
    rw [hindex]; have := hpre1.nodes 0 (by omega); simpa using this
  have h17 : σ1 (.n 17) = H.1 := congrArg Prod.fst hH1
  have h18 : σ1 (.n 18) = H.2 := congrArg Prod.snd hH1
  -- the coordinates
  refine CompletesB.append (m := b) (by omega) (by omega) (sCoords_below 8 0 (.n 209) 210 (by omega) ⟨209, by omega, rfl⟩)
    (sCoords_comp (CM := CM) (C := C) (rd := rd) (inst := inst) hq hfk hrd index marks openings topsN 8 0 (.n 209)
      210 σ1 (by omega) (by omega) ⟨209, by omega, rfl⟩ hpre1.md64 (by rw [hp1]; exact isCanonical128_cellOf _) hidx1
      (fun r hr => by
        have e : (⟨(0 + r) % 8, Nat.mod_lt _ (by norm_num)⟩ : Sphincs.Coord) =
            ⟨0 + r, by simp only [Sphincs.forestCoords]; omega⟩ := Fin.ext (Nat.mod_eq_of_lt (by omega))
        show _ = some (tops ⟨(0 + r) % 8, Nat.mod_lt _ (by norm_num)⟩)
        rw [hp1, e]
        exact hcR _))
    fun σ2 _ ⟨hrec2, hbd2, hag2⟩ => ?_
  simp only [Nat.zero_add] at hrec2 hbd2
  have hag21 : ∀ k < 210, σ2 (.n k) = σ1 (.n k) := fun k hk => (hag2 k hk).symm
  -- the lanes
  have hwd : ∀ k < 16, NB b (if k % 2 = 0 then (cs.2.2.1.getD (k / 2) (.n 0, .n 0)).1
      else (cs.2.2.1.getD (k / 2) (.n 0, .n 0)).2) := fun k hk => by
    obtain ⟨h1, h2, -, -⟩ := houts (k / 2) (by omega)
    split
    · exact h1
    · exact h2
  have hwv : ∀ k < 16, σ2 (if k % 2 = 0 then (cs.2.2.1.getD (k / 2) (.n 0, .n 0)).1
      else (cs.2.2.1.getD (k / 2) (.n 0, .n 0)).2) =
      eOfNat ((marks (k / 2)).word ⟨k % 2, Nat.mod_lt _ (by omega)⟩).val := fun k hk => by
    obtain ⟨-, -, -, hw0, hw1⟩ := hrec2 (k / 2) (by omega)
    rcases Nat.mod_two_eq_zero_or_one k with hk2 | hk2
    · simp only [hk2, ↓reduceIte]
      rw [hw0, word_eq_eOfNat]
      rfl
    · simp only [hk2, Nat.one_ne_zero, ↓reduceIte]
      rw [hw1, word_eq_eOfNat]
      rfl
  have h17' : σ2 (.n 17) = lit (∑ k ∈ Finset.range 16,
      ((marks (k / 2)).word ⟨k % 2, Nat.mod_lt _ (by omega)⟩).val * 2 ^ (8 * k)) :=
    (hag21 17 (by omega)).trans (h17.trans ((lit_cellNat_of (isCanonical128_hcellC _).1).symm.trans
      (dMarks_lanes x1 hx0).symm))
  have h18' : σ2 cs.2.2.2.2 = σ2 (.n 18) := by
    rw [hbd2, hpre1.bound, hag21 18 (by omega), h18]
    exact (dMarks_bound x1 hx0).trans (lit_cellNat_of (isCanonical128_hcellC _).2)
  refine CompletesB.append (m := b + 45) (by omega) (by omega) (sLanes_below hwd hbB (by omega))
    (sLanes_comp (by omega) hwd hbB (t := fun k => ((marks (k / 2)).word ⟨k % 2, Nat.mod_lt _ (by omega)⟩).val)
      (fun k _ => ((marks (k / 2)).word _).isLt) hwv h17' h18') fun σ3 _ hag3 => ?_
  have hag31 : ∀ k < 210, σ3 (.n k) = σ1 (.n k) := fun k hk => (hag3 k (by omega)).symm.trans (hag21 k hk)
  have hkeep3 : ∀ v : V, NB b v → σ3 v = σ2 v := fun v ⟨k, hk, e⟩ => by rw [e]; exact (hag3 k hk).symm
  -- the forest key
  refine CompletesB.append (m := b + 45 + 2) (by omega) (by omega) (addr142_below (by omega) _)
    (CompletesB.of_free (F := []) rfl
      (addr142_complete (C := C) (rd := rd) (σ := σ3) (k := b + 45) (by omega) (word (tw 20) 0 0)))
    fun σ4 _ ⟨h41, hag4⟩ => ?_
  have hag41 : ∀ k < 210, σ4 (.n k) = σ1 (.n k) := fun k hk => (hag4 k (by omega)).symm.trans (hag31 k hk)
  have htopB : ∀ k < 16, NB b (if k % 2 = 0 then (cs.2.2.2.1.getD (k / 2) (.n 0, .n 0)).1
      else (cs.2.2.2.1.getD (k / 2) (.n 0, .n 0)).2) := fun k hk => by
    obtain ⟨-, -, h1, h2⟩ := houts (k / 2) (by omega)
    split
    · exact h1
    · exact h2
  have htop4 : ∀ k < 16, σ4 (if k % 2 = 0 then (cs.2.2.2.1.getD (k / 2) (.n 0, .n 0)).1
      else (cs.2.2.2.1.getD (k / 2) (.n 0, .n 0)).2) = σ2 (if k % 2 = 0 then (cs.2.2.2.1.getD (k / 2) (.n 0, .n 0)).1
      else (cs.2.2.2.1.getD (k / 2) (.n 0, .n 0)).2) := fun k hk => by
    obtain ⟨j, hj, e⟩ := htopB k hk
    rw [e, ← hag4 j (by omega), hkeep3 _ ⟨j, hj, rfl⟩]
  have htopc : ∀ k < 16, IsCanonical128 (σ4 (if k % 2 = 0 then (cs.2.2.2.1.getD (k / 2) (.n 0, .n 0)).1
      else (cs.2.2.2.1.getD (k / 2) (.n 0, .n 0)).2)) := fun k hk => by
    rw [htop4 k hk]
    obtain ⟨-, hc1, hc2, -, -⟩ := hrec2 (k / 2) (by omega)
    split
    · exact hc1
    · exact hc2
  have hp4 : σ4 (.n 1) = pp := by rw [hag41 1 (by omega), hp1]
  have h142_4 : σ4 (.n 142) = eOfNat N := by rw [hag41 142 (by omega), hidx1, hindex]
  have hA4 : σ4 (.n (b + 45 + 1)) = eOfNat N + word (tw 20) 0 0 := by
    rw [h41, hag31 142 (by omega), hidx1, hindex]
  -- the forest key's digest is answered
  have hR : cellBytes (σ4 (.n (b + 45 + 1))) = Sphincs.tweakBytes (.roots index) := by
    rw [hA4, show tw 20 = 2 ^ 56 * 20 by simp only [tw]; ring, sp_add_word (by omega),
      Sphincs.tweakBytes, Sphincs.hashDomainFields, sTweak]
    refine congrArg (fun n => cellBytes (eOfNat n)) ?_
    rw [sp_addrNat (by omega) (by omega) (by omega) (by omega), hindex]
    ring
  set T : Nat → E := fun k => σ4 (if k % 2 = 0 then (cs.2.2.2.1.getD (k / 2) (.n 0, .n 0)).1
    else (cs.2.2.2.1.getD (k / 2) (.n 0, .n 0)).2) with hT
  have htopsE : tops = fun c => (sv (T (2 * c.val)), sv (T (2 * c.val + 1))) := funext fun c => by
    have hc8 := c.isLt
    simp only [Sphincs.forestCoords] at hc8
    have h := (hrec2 c.val c.isLt).1
    have e : topsN c.val = tops c := congrArg tops (Fin.ext (Nat.mod_eq_of_lt c.isLt))
    rw [← e, h, hT]
    dsimp only
    rw [htop4 _ (by omega), htop4 _ (by omega)]
    simp only [show 2 * c.val % 2 = 0 by omega, show (2 * c.val + 1) % 2 = 1 by omega,
      show 2 * c.val / 2 = c.val by omega, show (2 * c.val + 1) / 2 = c.val by omega, ↓reduceIte, Nat.one_ne_zero]
    rfl
  rw [htopsE, sHash_cellsE (H := CM.H) hq (rootsPayload_cells (pp := pp) hR T)] at hroots
  obtain ⟨o2, ho2, hfko⟩ := Option.map_eq_some_iff.mp hroots
  obtain ⟨hans2, rfl⟩ := hcellWith_eq_some_iff.mp ho2
  have hv := hashValues_comp (CM := CM) (C := C) (rd := rd) (σ := σ4) (pp := .n 1) (a := .n (b + 45 + 1))
    (val := fun k => if k % 2 = 0 then (cs.2.2.2.1.getD (k / 2) (.n 0, .n 0)).1
      else (cs.2.2.2.1.getD (k / 2) (.n 0, .n 0)).2) (n := 16) (b := b + 45 + 2) (Or.inl (by norm_num)) (by norm_num)
    ⟨⟨1, by omega, rfl⟩, ⟨_, by omega, rfl⟩, fun i hi => (htopB i hi).mono (by omega)⟩
    ⟨by rw [hp4]; exact isCanonical128_cellOf _,
      by rw [hA4]; exact isCanonical128_add (isCanonical128_eOfNat _) (isCanonical128_word _ _), htopc⟩
    (by rw [hp4]; exact hans2)
  refine CompletesB.append (m := b + 45 + 2 + hashValuesSize 16) (by omega) (by omega)
    (hashValues_below (by norm_num) ⟨⟨1, by omega, rfl⟩, ⟨_, by omega, rfl⟩, fun i hi => (htopB i hi).mono (by omega)⟩)
    hv.withExt fun σ5 _ ⟨hfk5, he5⟩ => ?_
  have hag51 : ∀ k < 210, σ5 (.n k) = σ1 (.n k) := fun k hk => (he5.agree k (by omega)).symm.trans (hag41 k hk)
  have hp5 : σ5 (.n 1) = pp := by rw [hag51 1 (by omega), hp1]
  have h142_5 : σ5 (.n 142) = eOfNat N := by rw [hag51 142 (by omega), hidx1, hindex]
  -- the counter
  have hfkB := hashValues_snd_lt (.n 1) (.n (b + 45 + 1)) (fun k => if k % 2 = 0 then
    (cs.2.2.2.1.getD (k / 2) (.n 0, .n 0)).1 else (cs.2.2.2.1.getD (k / 2) (.n 0, .n 0)).2) 16 (b + 45 + 2)
  have hCn : (sig.layers Sphincs.topLayer).counter.toNat < 2 ^ 32 := (sig.layers Sphincs.topLayer).counter.isLt
  -- the encoding digest is answered
  have hfk' : fk = sv (σ5 (hashValues (.n 1) (.n (b + 45 + 1)) (fun k => if k % 2 = 0 then
      (cs.2.2.2.1.getD (k / 2) (.n 0, .n 0)).1 else (cs.2.2.2.1.getD (k / 2) (.n 0, .n 0)).2) 16 (b + 45 + 2)).2) := by
    rw [hfk5, hp4, hfko]
  have htw4 : cellBytes (σ5 (.n 142) + word (tw 4) 0 0) = Sphincs.tweakBytes (.encoding Sphincs.topLayer 0 leaf) := by
    rw [h142_5, sp_tag_addr hN (by norm_num), ← hleaf, ← sTweak]
    rfl
  have hctrB : Sphincs.bytesLE 4 (sig.layers Sphincs.topLayer).counter =
      leBytes (sig.layers Sphincs.topLayer).counter.toNat 4 := sphincs_bytesLE_eq 4 _
  rw [hfk', sHash_bytesE (H := CM.H) hq (r := cellBytes pp ++ cellBytes (σ5 (.n 142) + word (tw 4) 0 0) ++
      cellBytes (σ5 (hashValues (.n 1) (.n (b + 45 + 1)) (fun k => if k % 2 = 0 then
      (cs.2.2.2.1.getD (k / 2) (.n 0, .n 0)).1 else (cs.2.2.2.1.getD (k / 2) (.n 0, .n 0)).2) 16 (b + 45 + 2)).2) ++
      leBytes (sig.layers Sphincs.topLayer).counter.toNat 4) (by
        show Sphincs.bytesLE 16 (spp pp) ++ Sphincs.tweakBytes _ ++ _ = _
        rw [bytesLE_spp, ← htw4, bytesLE_sv, hctrB]
        simp only [List.append_assoc])] at henc
  obtain ⟨o3, ho3, hdgo⟩ := Option.map_eq_some_iff.mp henc
  obtain ⟨hans3, rfl⟩ := hbWith_eq_some_iff.mp ho3
  refine CompletesB.append (m := b + 45 + 2 + hashValuesSize 16 + 133) (by omega) (by omega)
    (sCounter_below hfkB (by omega))
    (sCounter_comp (CM := CM) (C := C) (rd := rd) (σ := σ5) (by omega) hfkB hCn (by rw [hp5]; exact isCanonical128_cellOf _)
      (by rw [h142_5]; exact isCanonical128_add (isCanonical128_eOfNat _) (isCanonical128_word _ _))
      (by rw [hfk5]; exact (isCanonical128_hcellC _).1) (by rw [hp5]; exact hans3))
      fun σ6 _ ⟨_, he61, he65, hag6⟩ => ?_
  rw [hp5] at he65
  rw [← hdgo, ← he65] at hdecE
  -- the tail
  set e := b + 45 + 2 + hashValuesSize 16 + 126 with he_def
  have hag61 : ∀ k < 210, σ6 (.n k) = σ1 (.n k) := fun k hk => (hag6 k (by omega)).symm.trans (hag51 k hk)
  have hp6 : σ6 (.n 1) = pp := by rw [hag61 1 (by omega), hp1]
  have h142_6 : σ6 (.n 142) = eOfNat N := by rw [hag61 142 (by omega), hidx1, hindex]
  have hpath : Sphincs.Concrete.signaturePath sig Sphincs.topLayer =
      fun l => sv (finCells (sig.layers Sphincs.topLayer).path l) := funext fun l => by
    unfold Sphincs.Concrete.signaturePath finCells
    by_cases hl : l < Sphincs.layerHeight Sphincs.topLayer
    · simp only [hl, ↓reduceDIte]
      exact (cellVal_cellOf _).symm
    · simp only [hl, ↓reduceDIte]
      exact sv_zero.symm
  have hrec' : ∀ i, @Sphincs.Concrete.recoverChain Option _ inst (spp (σ6 (.n 1))) Sphincs.topLayer 0 leaf i (enc i)
      (sv (finCells (sig.layers Sphincs.topLayer).chainValues i.val)) = some (tips i) := fun i => by
    have := hrec i
    rw [sv_finCells (sig.layers Sphincs.topLayer).chainValues] at this
    rw [hp6]; exact this
  refine CompletesB.append (m := (sMk e).2.2) (by omega) (by omega) (sTail_below (by omega))
    ((sTail_comp (CM := CM) (C := C) (rd := rd) hq (hrd.mono (by norm_num)) (σ := σ6) (e := e) (by omega)
      (hpre1.congr hag61) h142_6 (by rw [hp6]; exact isCanonical128_cellOf _) hleaf hdecE
      (by rw [he65]; exact (isCanonical128_hbC _).1) (canonical_finCells (sig.layers Sphincs.topLayer).chainValues)
      (canonical_finCells (sig.layers Sphincs.topLayer).path) (leafD := lv) (r := pk.root) hrec'
      (by rw [hp6]; exact hleafD) (by rw [hp6, ← hpath]; exact htree)).mono (by omega) le_rfl fun σ' h => h)
    fun σ7 _ ⟨hroot7, hcan7, hag7⟩ => ?_
  -- the root
  have hrootc : σ7 (sMk e).2.1 = cellOf pk.root := by rw [← hroot7]; exact (cellOf_cellVal hcan7).symm
  have h70 : σ7 (.n 0) = p := by rw [← hag7 0 (by omega), hag61 0 (by omega), h01]
  -- the claim's root
  obtain ⟨kr, hkr, hkre⟩ := sMk_root_lt e
  have hne0 : (V.n 0) ≠ V.n (sMk e).2.2 := fun h => by simp only [V.mk.injEq] at h; omega
  have hner : (sMk e).2.1 ≠ V.n (sMk e).2.2 := fun h => by rw [hkre] at h; simp only [V.mk.injEq] at h; omega
  refine CompletesB.atom_cons (cellOf pk.root) le_rfl
    (.cons ⟨_, by omega, rfl⟩ (.cons ⟨0, by omega, rfl⟩ (.nil _))) ?_ ?_
  · show LoadHolds rd (Function.update σ7 (.n (sMk e).2.2) (cellOf pk.root) (.n 0)) 0
      (Function.update σ7 (.n (sMk e).2.2) (cellOf pk.root) (.n (sMk e).2.2))
    rw [Function.update_self, Function.update_of_ne hne0, h70]
    exact hc 0
  refine CompletesB.atom_cons0 (.cons ⟨kr, by omega, hkre⟩ (.cons ⟨_, by omega, rfl⟩ (.nil _))) ?_
    (CompletesB.nil _ _ _ trivial)
  show Function.update σ7 (.n (sMk e).2.2) (cellOf pk.root) (sMk e).2.1 +
    Function.update σ7 (.n (sMk e).2.2) (cellOf pk.root) (.n (sMk e).2.2) = 0
  rw [Function.update_self, Function.update_of_ne hner, hrootc]
  exact e_add_eq_zero_iff.mpr rfl

/-- **`verify_sig_lean_sphincs` is its meaning's completeness over the model**
(`verify_sig_lean_sphincs_iff.mpr`): on a memory holding at least 256 words, a claim some signature
verifies with the model's answered hash is in the call relation under the model's semantics. -/
theorem verify_sig_lean_sphincs_rel_comp {CM : CompModel} {rd : Reader} (hrd : MemOK rd 256)
    {args rets : List E} (h : Meaning_verify_sig_lean_sphincsWith CM.H rd args rets) :
    coreProgram.RelB CM.sem rd "verify_sig_lean_sphincs" args rets := by
  obtain ⟨p, ha, hr, pk, m, hc, sig, hv⟩ := h
  obtain ⟨σ, hσ, hb⟩ := verify_sig_lean_sphincs_comp (C := coreProgram.RelB CM.sem rd) fkCompleteC_relB hrd hc hv
  refine (relB_iff_sem find_verify_sig_lean_sphincs args rets).mpr ⟨σ, by rw [ha]; simp [hσ], ?_⟩
  rw [hr]
  exact hb

/-- The deployed `verify_sig_lean_sphincs_iff.mpr`, from the model's at `CompModel.deployed`. -/
theorem verify_sig_lean_sphincs_rel_of_comp {rd : Reader} (hrd : MemOK rd 256) {args rets : List E}
    (h : Meaning_verify_sig_lean_sphincs rd args rets) :
    coreProgram.Rel rd "verify_sig_lean_sphincs" args rets := by
  obtain ⟨p, ha, hr, pk, m, hc, sig, hv⟩ := h
  have := verify_sig_lean_sphincs_rel_comp (CM := CompModel.deployed) hrd
    ⟨p, ha, hr, pk, m, hc, sig, by rw [show CompModel.deployed.H = fun x ↦ some (blake2sBytes x) from rfl,
      LeanVM.E2E.sphincsVerifyWith_some_blake2s, hv]⟩
  rwa [show CompModel.deployed.sem = blakeDeployed from rfl, relB_deployed] at this

end
end LeanVM.Guest.B1.Sig
