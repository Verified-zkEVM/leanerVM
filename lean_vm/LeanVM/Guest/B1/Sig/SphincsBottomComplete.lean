/-
  LeanVM.Guest.B1.Sig.SphincsBottomComplete

  The hypertree's addresses and the bottom layer's encoding of `verify_sig_lean_sphincs`
  (`lean_ethereum.py:3720-3740` at leanVM `542b0353`) are complete: each layer's key address and
  tree lane from the index's fields, the counter's bytes, and the 804-byte encoding of the FORS key.
-/

module

public import LeanVM.Guest.B1.Sig.SphincsLayersComplete

/-!
# The addresses and the bottom encoding, complete

* `laneCell_val`, `word0_eq`, `eOfNat_mul_word0`: lanes over limbs;
* `idx_fields`: the index's three fields and each layer's tree and leaf;
* `sLanes_vals`: `sLanes sH` gives the three key addresses and two lanes;
* `sBottomPre_complete`: the addresses, the bottom counter and the encoding of the FORS key, its
  output `encCell` of the 48 top nodes.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier (eOfNat kToNat)
open HashSig HashSig.OverPermutation

@[expose] public section

variable {C : CallRel} {rd : Reader}

theorem laneCell_val (layer : Sphincs.Layer) (tree : Sphincs.TreeIndex) :
    laneCell layer tree = E.ofLimbs 0 (K.ofBits (layer.val + 2 ^ 8 * tree.val)) 0 := by
  have h1 : layer.val < 3 := layer.isLt
  have h2 : tree.val < 2 ^ 26 := tree.isLt
  rw [laneCell, keyAddressCell_eq, keyNat, Fin.val_mk, Nat.zero_add, eOfNat192_two_pow_64_mul (by omega)]

theorem word0_eq (n : Nat) : word 0 n 0 = E.ofLimbs 0 (K.ofBits n) 0 := by
  rw [word, Value.ofBits_zero]

theorem eOfNat_mul_word0 {t : Nat} (h : 2 ^ 8 * t < 2 ^ 64) :
    eOfNat t * word 0 256 0 = E.ofLimbs 0 (K.ofBits (2 ^ 8 * t)) 0 := by
  rw [word0_eq, mul_comm, eOfNat, ofLimbs_mul_ofK, zero_mul, show (256 : Nat) = 2 ^ 8 by norm_num,
    ofBits_two_pow_mul h]

/-- The index's fields and the layers' trees and leaves. -/
theorem idx_fields {D : Nat} (idx : Sphincs.Index) (hidx : idx.val = D % 2 ^ 26) :
    fieldNat D 0 = (Sphincs.leafOfIndex 0 idx).val ∧ fieldNat D 1 = (Sphincs.leafOfIndex 1 idx).val ∧
      fieldNat D 2 = (Sphincs.leafOfIndex 2 idx).val ∧
      (Sphincs.treeOfIndex 0 idx).val = 2 ^ 8 * fieldNat D 2 + fieldNat D 1 ∧
      (Sphincs.treeOfIndex 1 idx).val = fieldNat D 2 ∧ (Sphincs.treeOfIndex 2 idx).val = 0 := by
  have l0 : (Sphincs.leafOfIndex 0 idx).val = idx.val / 1 % 256 := rfl
  have l1 : (Sphincs.leafOfIndex 1 idx).val = idx.val / 256 % 256 := rfl
  have l2 : (Sphincs.leafOfIndex 2 idx).val = idx.val / 65536 % 1024 := rfl
  have t0 : (Sphincs.treeOfIndex 0 idx).val = idx.val / 256 := rfl
  have t1 : (Sphincs.treeOfIndex 1 idx).val = idx.val / 65536 := rfl
  have t2 : (Sphincs.treeOfIndex 2 idx).val = idx.val / 67108864 := rfl
  rw [l0, l1, l2, t0, t1, t2, hidx]
  simp only [fieldNat, sFieldOff, sFieldLen]
  norm_num
  omega

theorem laneCell_eq_of {layer : Sphincs.Layer} {tree : Sphincs.TreeIndex} {x : E} {n : Nat}
    (h : x = E.ofLimbs 0 (K.ofBits n) 0) (hn : n = layer.val + 2 ^ 8 * tree.val) : x = laneCell layer tree := by
  rw [h, laneCell_val, hn]

/-- **The hypertree's addresses**: `sLanes sH` gives the key addresses of the three layers at
`sH + 9`, `sH + 10`, `sH + 12` and the lanes of the two lower trees at `sH + 4`, `sH + 8`. -/
theorem sLanes_vals {σ : Val} {D : Nat} (idx : Sphincs.Index) (hidx : idx.val = D % 2 ^ 26) (hv : ValsAt σ D)
    {b : Nat} (h : AtomsHold rd σ (sLanes b)) :
    σ (.n (b + 4)) = laneCell 0 (Sphincs.treeOfIndex 0 idx) ∧ σ (.n (b + 8)) = laneCell 1 (Sphincs.treeOfIndex 1 idx) ∧
      σ (.n (b + 9)) = keyAddressCell 0 (Sphincs.treeOfIndex 0 idx) (Sphincs.leafOfIndex 0 idx) ∧
      σ (.n (b + 10)) = keyAddressCell 1 (Sphincs.treeOfIndex 1 idx) (Sphincs.leafOfIndex 1 idx) ∧
      σ (.n (b + 12)) = keyAddressCell 2 (Sphincs.treeOfIndex 2 idx) (Sphincs.leafOfIndex 2 idx) := by
  obtain ⟨f0, f1, f2, t0, t1, t2⟩ := idx_fields idx hidx
  have v0 : σ (sVal 0) = eOfNat (fieldNat D 0) := by
    have := valsAt_field hv (f := 0) (by norm_num) (k := 0) (by simp [sFieldLen]); simpa [sFieldOff] using this
  have v8 : σ (sVal 8) = eOfNat (fieldNat D 1) := by
    have := valsAt_field hv (f := 1) (by norm_num) (k := 0) (by simp [sFieldLen]); simpa [sFieldOff] using this
  have v16 : σ (sVal 16) = eOfNat (fieldNat D 2) := by
    have := valsAt_field hv (f := 2) (by norm_num) (k := 0) (by simp [sFieldLen]); simpa [sFieldOff] using this
  have e1 := fieldNat_lt D 1
  have e2 := fieldNat_lt D 2
  simp only [sFieldLen] at e1 e2
  norm_num at e1 e2
  have a := fun (x : Atom) (hx : Stmt.atom x ∈ sLanes b) => h x hx
  have c0 := a (.const (.n b) (word 256 0 0)) (by simp [sLanes, cst])
  have m1 := a (.mul (.n (b + 1)) (sVal 16) (.n b)) (by simp [sLanes, mulS])
  have a2 := a (.add (.n (b + 2)) (sVal 8) (.n (b + 1))) (by simp [sLanes, addS])
  have c3 := a (.const (.n (b + 3)) (word 0 256 0)) (by simp [sLanes, cst])
  have m4 := a (.mul (.n (b + 4)) (.n (b + 2)) (.n (b + 3))) (by simp [sLanes, mulS])
  have c5 := a (.const (.n (b + 5)) (word 0 256 0)) (by simp [sLanes, cst])
  have m6 := a (.mul (.n (b + 6)) (sVal 16) (.n (b + 5))) (by simp [sLanes, mulS])
  have c7 := a (.const (.n (b + 7)) (word 0 1 0)) (by simp [sLanes, cst])
  have a8 := a (.add (.n (b + 8)) (.n (b + 6)) (.n (b + 7))) (by simp [sLanes, addS])
  have a9 := a (.add (.n (b + 9)) (sVal 0) (.n (b + 4))) (by simp [sLanes, addS])
  have a10 := a (.add (.n (b + 10)) (sVal 8) (.n (b + 8))) (by simp [sLanes, addS])
  have c11 := a (.const (.n (b + 11)) (word 0 2 0)) (by simp [sLanes, cst])
  have a12 := a (.add (.n (b + 12)) (sVal 16) (.n (b + 11))) (by simp [sLanes, addS])
  simp only [Atom.Holds] at c0 m1 a2 c3 m4 c5 m6 c7 a8 a9 a10 c11 a12
  have hv2 : σ (.n (b + 2)) = eOfNat (2 ^ 8 * fieldNat D 2 + fieldNat D 1) := by
    rw [a2, m1, c0, v8, v16, show (256 : Nat) = 2 ^ 8 by norm_num, word_eq_eOfNat, mul_comm (eOfNat (fieldNat D 2)),
      eOfNat_two_pow_mul (by omega), add_comm, eOfNat_add_of_lt (by omega)]
  have hl0 : σ (.n (b + 4)) = laneCell 0 (Sphincs.treeOfIndex 0 idx) := by
    refine laneCell_eq_of (n := 2 ^ 8 * (2 ^ 8 * fieldNat D 2 + fieldNat D 1)) ?_ (by rw [t0]; simp)
    rw [m4, hv2, c3, eOfNat_mul_word0 (by omega)]
  have hl1 : σ (.n (b + 8)) = laneCell 1 (Sphincs.treeOfIndex 1 idx) := by
    refine laneCell_eq_of (n := 2 ^ 8 * fieldNat D 2 + 1) ?_ (by rw [t1]; show _ = 1 + _; ring)
    rw [a8, m6, v16, c5, c7, eOfNat_mul_word0 (by omega), word0_eq, ofLimbs_add, add_zero, ← ofBits_xor,
      two_pow_mul_xor (by norm_num)]
  refine ⟨hl0, hl1, ?_, ?_, ?_⟩
  · rw [a9, hl0, v0, keyAddressCell_lane, f0, add_comm]
  · rw [a10, hl1, v8, keyAddressCell_lane, f1, add_comm]
  · rw [a12, c11, v16, keyAddressCell_lane, f2, add_comm]
    congr 1
    rw [laneCell_val, word0_eq, t2]
    rfl

/-! ## The bottom encoding -/

theorem sH_eq : sH = 6817 := by decide +kernel

/-- The FORS key's top nodes, in order. -/
def topsList (tops : Nat → E × E) : List E := (List.range 24).flatMap fun k => [(tops k).1, (tops k).2]

theorem topsList_length (tops : Nat → E × E) : (topsList tops).length = 48 := by
  simp [topsList, List.length_flatMap]

open scoped Dec in
theorem sFors_tops : sFors.2.2 = (List.range 24).flatMap fun k => [V.n (1454 + 233 * k), V.n (1455 + 233 * k)] := by
  decide +kernel

/-- The bottom encoding's cells: `P`, the address, the FORS key's 48 top nodes, the counter. -/
def botCells : List V :=
  [V.n 1224, V.n 6831] ++ ((List.range 24).flatMap fun k => [V.n (1454 + 233 * k), V.n (1455 + 233 * k)]) ++
    [V.n 6869]

/-- The bottom layer before its key's call: the addresses, the counter, the FORS key's
encoding. -/
def sBotPre : List Stmt :=
  sLanes sH ++ [cst (sH + 13) (word (tw 4) 0 0), addS (.n (sH + 14)) (.n (sH + 9)) (.n (sH + 13)),
    hintW "sp_counter" (runV (sH + 15) 4)] ++ sCtrB.1 ++ [copyS (.n sCtrB.2.1) sCtrB.2.2] ++ sEncB.1

theorem sBotPre_eq : sBotPre = sLanes 6817 ++ ([cst 6830 (word (tw 4) 0 0), addS (.n 6831) (.n 6826) (.n 6830)] ++
    ((hintW "sp_counter" (runV 6832 4) :: (sFromBytes (.n 6835) [.n 6834, .n 6833, .n 6832] g255W 6836).1) ++
      ([copyS (.n 6869) (.n 6868)] ++
        (kMsg sPad (botCells.map KC.cell) 804 true none 6870).1))) := by
  rw [sBotPre, sEncB, sEncCells, sFors_tops, sCtrB, sH_eq]
  simp [sMarks, sFromBytes, sFromBytesRest, List.range_succ, botCells]

theorem sEncB_snd : sEncB.2.1 = 6997 ∧ sEncB.2.2 = 6984 := by decide +kernel

theorem botK_eq : kMsg sPad (botCells.map KC.cell) 804 true none 6870 = sEncB := by
  rw [sEncB, sEncCells, sFors_tops, sCtrB, sH_eq]
  simp [sMarks, sFromBytes, sFromBytesRest, List.range_succ, botCells]

theorem mem_botCells {x : V} (hx : x ∈ botCells) :
    x = .n 1224 ∨ x = .n 6831 ∨ x = .n 6869 ∨ ∃ k < 24, x = .n (1454 + 233 * k) ∨ x = .n (1455 + 233 * k) := by
  simp only [botCells, List.mem_append, List.mem_cons, List.mem_flatMap, List.mem_range, List.not_mem_nil,
    or_false] at hx
  rcases hx with ((h | h) | ⟨k, hk, h⟩) | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inr ⟨k, hk, h⟩))
  · exact Or.inr (Or.inr (Or.inl h))

theorem botCells_map (σ : Val) (tops : Nat → E × E)
    (ht : ∀ k < 24, σ (.n (1454 + 233 * k)) = (tops k).1 ∧ σ (.n (1455 + 233 * k)) = (tops k).2) :
    (botCells.map KC.cell).map (KC.val σ) = [σ (.n 1224), σ (.n 6831)] ++ topsList tops ++ [σ (.n 6869)] := by
  simp only [botCells, List.map_append, List.map_map, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append]
  congr 2
  simp only [topsList, List.map_flatMap]
  congr 1
  · refine List.flatMap_congr fun k hk => ?_
    have := ht k (List.mem_range.mp hk)
    simp [KC.val, this.1, this.2]

/-- **The bottom layer before its call completes**: the addresses from the index's fields, the
counter's bytes and the FORS key's encoding. -/
theorem sBotPre_complete (hm : MemOK rd 256) {bb : E} (hbb : ByteBits rd bb) {P : PublicParameter} {D : Nat}
    (idx : Sphincs.Index) (hidx : idx.val = D % 2 ^ 26) (ctr : Sphincs.EncodingCounter) (tops : Nat → E × E)
    (htc : ∀ k, IsCanonical128 (tops k).1 ∧ IsCanonical128 (tops k).2) (σ : Val) (hp : PadOK σ sPad)
    (h1 : σ (.n 1) = bb) (h1224 : σ (.n 1224) = cellOf128 P) (hv : ValsAt σ D)
    (ht : ∀ k < 24, σ (.n (1454 + 233 * k)) = (tops k).1 ∧ σ (.n (1455 + 233 * k)) = (tops k).2) :
    Completes C rd 6817 6997 sBotPre σ (fun σ' =>
      σ' (.n 6821) = laneCell 0 (Sphincs.treeOfIndex 0 idx) ∧ σ' (.n 6825) = laneCell 1 (Sphincs.treeOfIndex 1 idx) ∧
      σ' (.n 6826) = keyAddressCell 0 (Sphincs.treeOfIndex 0 idx) (Sphincs.leafOfIndex 0 idx) ∧
      σ' (.n 6827) = keyAddressCell 1 (Sphincs.treeOfIndex 1 idx) (Sphincs.leafOfIndex 1 idx) ∧
      σ' (.n 6829) = keyAddressCell 2 (Sphincs.treeOfIndex 2 idx) (Sphincs.leafOfIndex 2 idx) ∧
      σ' (.n 6984) = encCell (cellOf128 P) 0 (Sphincs.treeOfIndex 0 idx) (Sphincs.leafOfIndex 0 idx)
        (topsList tops) ctr ∧
      ∀ k ≤ 3, BytePtr bb (σ' (.n (fbPtr 6836 k)))) := by
  rw [sBotPre_eq]
  -- the addresses
  refine Completes.seq (m := 6830) (seqB_ok (by decide +kernel)) (by norm_num) (fun σ1 he1 hh1 => ?_)
  obtain ⟨l0, l1, a0, a1, a2⟩ := sLanes_vals (rd := rd) idx hidx
    (valsAt_congr hv (fun k hk => (he1.apply (Or.inl (by omega))).symm)) hh1
  refine Completes.seq (m := 6832) (xs := [cst 6830 (word (tw 4) 0 0), addS (.n 6831) (.n 6826) (.n 6830)])
    (seqB_ok (by decide +kernel)) (by norm_num) (fun σ2 he2 hh2 => ?_)
  have hA2 : σ2 (.n 6831) = keyAddressCell 0 (Sphincs.treeOfIndex 0 idx) (Sphincs.leafOfIndex 0 idx) + word (tw 4) 0 0 := by
    have c0 := hh2.atom (a := .const (.n 6830) (word (tw 4) 0 0)) (by simp [cst])
    have ad := hh2.atom (a := .add (.n 6831) (.n 6826) (.n 6830)) (by simp [addS])
    simp only [Atom.Holds] at c0 ad
    rw [ad, c0, he2.apply (Or.inl (by norm_num)), a0]
  -- the counter
  have t21 : ∀ k < 6817, σ2 (.n k) = σ (.n k) := fun k hk => by
    rw [he2.apply (Or.inl (by omega)), he1.apply (Or.inl (by omega))]
  refine Completes.append (m := 6869) (by norm_num) (by norm_num)
    (by
      rw [valsList_cons]
      refine NumBelow.append ?_ ((sFromBytes_shape (.n 6835) [.n 6834, .n 6833, .n 6832] g255W 6836
        ⟨6835, by omega, rfl⟩ (by simp only [List.mem_cons, List.not_mem_nil, or_false]
                                  rintro m (rfl | rfl | rfl) <;> exact ⟨_, by omega, rfl⟩)).2.2)
      exact numBelow_of_all (by decide +kernel))
    (ctr_complete (C := C) hm hbb ctr (b := 6832) (by norm_num) σ2 (by rw [t21 1 (by norm_num)]; exact h1))
    (fun σ3 he3 ⟨hc3, hq3⟩ => ?_)
  refine Completes.seq (m := 6870) (xs := [copyS (.n 6869) (.n 6868)]) (seqB_ok (by decide +kernel)) (by norm_num)
    (fun σ4 he4 hh4 => ?_)
  have hc4 : σ4 (.n 6869) = eOfNat ctr.toNat := by
    have cp := hh4.atom (a := .copy (.n 6869) (.n 6868)) (by simp [copyS])
    simp only [Atom.Holds] at cp
    rw [cp, he4.apply (Or.inl (by norm_num))]; exact hc3
  have t4 : ∀ k < 6832, σ4 (.n k) = σ2 (.n k) := fun k hk => by
    rw [he4.apply (Or.inl (by omega)), he3.apply (Or.inl (by omega))]
  have t40 : ∀ k < 6817, σ4 (.n k) = σ (.n k) := fun k hk => by rw [t4 k (by omega), t21 k hk]
  -- the encoding
  have hp4 : PadOK σ4 sPad := hp.congr (b := 6817) (by unfold sPad; omega) (fun j hj => (t40 j hj).symm)
  have hcells : ∀ c ∈ botCells.map KC.cell, KCb 6870 c ∧ KCc σ4 c := by
    intro c hc
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hc
    rcases mem_botCells hx with rfl | rfl | rfl | ⟨k, hk, rfl | rfl⟩
    · refine ⟨⟨_, by omega, rfl⟩, ?_⟩
      show IsCanonical128 (σ4 _)
      rw [t40 _ (by omega), h1224]; exact isCanonical128_cellOf128 _
    · refine ⟨⟨_, by omega, rfl⟩, ?_⟩
      show IsCanonical128 (σ4 _)
      rw [t4 _ (by omega), hA2]
      exact canon_add (by unfold keyAddressCell; exact isCanonical128_cellOf128 _) (canon_word _ _)
    · refine ⟨⟨_, by omega, rfl⟩, ?_⟩
      show IsCanonical128 (σ4 _)
      rw [hc4]; exact canon_eOfNat _
    · refine ⟨⟨_, by omega, rfl⟩, ?_⟩
      show IsCanonical128 (σ4 _)
      rw [t40 _ (by omega), (ht k hk).1]; exact (htc k).1
    · refine ⟨⟨_, by omega, rfl⟩, ?_⟩
      show IsCanonical128 (σ4 _)
      rw [t40 _ (by omega), (ht k hk).2]; exact (htc k).2
  have htr : TailCells (blockOf (kMsgCells (botCells.map KC.cell) 804 6870) 0) := by
    intro k hk
    have e : blockOf (kMsgCells (botCells.map KC.cell) 804 6870) 0 =
        [.cell (.n 1224), .cell (.n 6831), .cell (.n 1454), .cell (.n 1455), .cell (.n 1687), .cell (.n 1688),
          .cell (.n 1920), .cell (.n 1921), .cell (.n 2153)] := by
      simp [blockOf, kMsgCells, kXorByte, kBlocksOf, botCells, List.range_succ]
    rw [e] at hk
    simp only [List.getD_cons_succ, List.getD_cons_zero, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩
  obtain ⟨hkc, hknb, -⟩ := kMsg_complete (C := C) (rd := rd) (pad := sPad) (len := 804) (tailRun := true)
    (b := 6870) σ4 hp4 (by unfold sPad; omega) hcells (fun _ => htr)
  rw [botK_eq] at hkc hknb ⊢
  rw [sEncB_snd.1] at hkc hknb
  obtain ⟨σ5, he5, ⟨-, hh5⟩, hhold⟩ := hkc.withHolds
  have hA5 := atomsHold_of_holdsList (kMsg_atoms sPad (botCells.map KC.cell) 804 true none 6870) (by
    rw [botK_eq]; exact hh5)
  have hpad5 : PadOK σ5 sPad := hp4.congr (b := 6870) (by unfold sPad; omega) he5.agree
  have t5 : ∀ k < 6870, σ5 (.n k) = σ4 (.n k) := fun k hk => he5.apply (Or.inl hk)
  have hs := kMsg_sound (rd := rd) hpad5 (cells := botCells.map KC.cell) (len := 804) (tailRun := true)
    (out := none) (b := 6870) (fun _ => htr) hA5 (by simp [botCells])
  have hmap : (botCells.map KC.cell).map (KC.val σ5) = ([cellOf128 P,
      keyAddressCell 0 (Sphincs.treeOfIndex 0 idx) (Sphincs.leafOfIndex 0 idx) + word (tw 4) 0 0] ++ topsList tops) ++
      [eOfNat ctr.toNat] := by
    rw [botCells_map σ5 tops (fun k hk => by
      rw [t5 _ (by omega), t5 _ (by omega), t40 _ (by omega), t40 _ (by omega)]; exact ht k hk)]
    rw [t5 _ (by norm_num), t5 _ (by norm_num), t5 _ (by norm_num), t40 _ (by norm_num), h1224, t4 _ (by norm_num),
      hA2, hc4]
  rw [hmap] at hs
  specialize hs (fun j hj => cellsBytes_ctr_zero _ ctr j (by simp [topsList_length] at hj ⊢; omega))
  rw [botK_eq, sEncB_snd.2] at hs
  refine ⟨σ5, he5, ⟨?_, ?_, ?_, ?_, ?_, ?_, fun k hk => ?_⟩, hhold⟩
  · rw [t5 _ (by norm_num), t4 _ (by norm_num), he2.apply (Or.inl (by norm_num))]; exact l0
  · rw [t5 _ (by norm_num), t4 _ (by norm_num), he2.apply (Or.inl (by norm_num))]; exact l1
  · rw [t5 _ (by norm_num), t4 _ (by norm_num), he2.apply (Or.inl (by norm_num))]; exact a0
  · rw [t5 _ (by norm_num), t4 _ (by norm_num), he2.apply (Or.inl (by norm_num))]; exact a1
  · rw [t5 _ (by norm_num), t4 _ (by norm_num), he2.apply (Or.inl (by norm_num))]; exact a2
  · rw [encCell, topsList_length]
    exact congrArg Prod.fst hs
  · rw [t5 _ (by simp only [fbPtr]; split <;> omega), he4.apply (Or.inl (by simp only [fbPtr]; split <;> omega))]
    exact hq3 k hk

end
end LeanVM.Guest.B1.Sig
