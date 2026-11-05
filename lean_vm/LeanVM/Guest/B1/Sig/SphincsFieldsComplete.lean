/-
  LeanVM.Guest.B1.Sig.SphincsFieldsComplete

  The digest's fields of `verify_sig_lean_sphincs` (`lean_ethereum.py:3860-3884` at leanVM
  `1a379148`) are complete: the bits of the two digest calls' cells hinted, pinned Boolean, shifted,
  placed into the lanes, the digest rebuilt from them and the unused bits read off the byte table.
-/

module

public import LeanVM.Guest.B1.Sig.SphincsDigestComplete

/-!
# The fields, complete

`D = cellNat (n17) + 2^128 cellNat (n18) + 2^256 cellNat (n38)` is the digest the two calls give (its
low `266` bits are the fields). Hinting its bits makes the fields' values and lanes `D`'s
(`sShifts_vals`, `sPl_sound`), and the checks hold: the first call's two cells are their lanes
(`cell_of_lanes`), the second call's high lane is what the unused bytes leave (`high_inK`).

* `digestD`, `unusedNat`, `unusedByte`: the digest's integer, its unused bits `266 ..< 320` and their
  bytes;
* `sFields_complete`: the fields' block, `n51 ..< n1225`, its post `FieldsPost`.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier (eOfNat kToNat)

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-- The digest's integer from the two calls' cells. -/
def digestD (c17 c18 c38 : E) : Nat := cellNat c17 + 2 ^ 128 * cellNat c18 + 2 ^ 256 * cellNat c38

/-- The digest's unused bits, `266 ..< 320`: the second call's low limb past its ten field bits. -/
def unusedNat (c38 : E) : Nat := kToNat (c38.limb 0) / 2 ^ 10

/-- Byte `k` of the unused bits. -/
def unusedByte (c38 : E) (k : Nat) : Nat := unusedNat c38 / 256 ^ k % 256

theorem unusedNat_lt (c38 : E) : unusedNat c38 < 2 ^ 54 := by
  have := kToNat_lt (c38.limb 0)
  unfold unusedNat; omega

theorem cellNat_eq (x : E) : cellNat x = kToNat (x.limb 0) + 2 ^ 64 * kToNat (x.limb 1) := rfl

theorem eOfNat_kToNat (a : K) : eOfNat (kToNat a) = ofK a := by
  rw [eOfNat, ofBits_kToNat]

theorem word_y : word 0 1 0 = y := by
  rw [word, Value.ofBits_zero, ofBits_one, y_eq]

theorem word_yinv : word 1 0 1 = y⁻¹ := by
  rw [word, Value.ofBits_zero, ofBits_one, y_inv]

/-- The lanes of the digest's first call. -/
theorem laneNat_low {c17 c18 c38 : E} :
    laneNat (digestD c17 c18 c38) 0 = kToNat (c17.limb 0) ∧
      laneNat (digestD c17 c18 c38) 1 = kToNat (c17.limb 1) ∧
      laneNat (digestD c17 c18 c38) 2 = kToNat (c18.limb 0) ∧
      laneNat (digestD c17 c18 c38) 3 = kToNat (c18.limb 1) := by
  have a0 := kToNat_lt (c17.limb 0)
  have a1 := kToNat_lt (c17.limb 1)
  have a2 := kToNat_lt (c18.limb 0)
  have a3 := kToNat_lt (c18.limb 1)
  simp only [laneNat, digestD, cellNat_eq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

theorem digestD_high {c17 c18 c38 : E} :
    digestD c17 c18 c38 / 2 ^ 256 % 2 ^ 10 = kToNat (c38.limb 0) % 2 ^ 10 := by
  have h1 := cellNat_lt c17
  have h2 := cellNat_lt c18
  have hlo : cellNat c17 + 2 ^ 128 * cellNat c18 < 2 ^ 256 := by omega
  have hd : digestD c17 c18 c38 / 2 ^ 256 = cellNat c38 := by
    rw [digestD, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hlo, zero_add]
  rw [hd, cellNat_eq, show 2 ^ 64 * kToNat (c38.limb 1) = 2 ^ 10 * (2 ^ 54 * kToNat (c38.limb 1)) by ring,
    Nat.add_mul_mod_self_left]

/-- **A canonical cell is its two lanes**, the high one times `y`. -/
theorem cell_of_lanes {x : E} (hx : IsCanonical128 x) :
    x = eOfNat (kToNat (x.limb 0)) + eOfNat (kToNat (x.limb 1)) * word 0 1 0 := by
  rw [eOfNat_kToNat, eOfNat_kToNat, word_y, mul_comm, ofK_add_y_mul_ofK]
  exact eq_ofLimbs_of_canonical hx

/-- **The second call's high lane is in `K`**: its cell, the field bits' lane and the unused bits
times `g^10` leave `y` times its high limb, which `y⁻¹` brings into `K`. -/
theorem high_inK {x : E} (hx : IsCanonical128 x) :
    (x + eOfNat (kToNat (x.limb 0) % 2 ^ 10) + eOfNat (unusedNat x) * word 1024 0 0) * word 1 0 1 =
      ofK (x.limb 1) := by
  have hl := kToNat_lt (x.limb 0)
  have hsplit : eOfNat (unusedNat x) * word 1024 0 0 + eOfNat (kToNat (x.limb 0) % 2 ^ 10) =
      ofK (x.limb 0) := by
    rw [show (1024 : Nat) = 2 ^ 10 by norm_num, word_eq_eOfNat, mul_comm, eOfNat_two_pow_mul (by
      unfold unusedNat; omega), eOfNat_add_of_lt (Nat.mod_lt _ (by norm_num)), unusedNat,
      Nat.div_add_mod, eOfNat_kToNat]
  have e : x + eOfNat (kToNat (x.limb 0) % 2 ^ 10) + eOfNat (unusedNat x) * word 1024 0 0 =
      E.ofLimbs 0 (x.limb 1) 0 := by
    rw [add_assoc, add_comm (eOfNat _), hsplit]
    have hxe := eq_ofLimbs_of_canonical hx
    generalize x.limb 0 = a at hxe ⊢
    generalize x.limb 1 = b at hxe ⊢
    subst hxe
    rw [ofK_eq_ofLimbs, ofLimbs_add, k_add_self, add_zero, add_zero]
  rw [e, word_yinv, ofLimbs_mul_y_inv, zero_add, ← ofK_eq_ofLimbs]

end
end LeanVM.Guest.B1.Sig

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier (eOfNat kToNat)

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-! ## The block -/

/-- The first call's cells rebuilt, before the unused bytes. -/
def fcA : List Stmt := [cst 1147 (word 0 1 0), mulS (.n 1148) (sLane 1) (.n 1147)]
def fcB : List Stmt := [cst 1149 (word 0 1 0), mulS (.n 1150) (sLane 3) (.n 1149)]
/-- The unused bytes' value. -/
def fcU : List Stmt × Nat × V := sFromBytes (.n 1157) [.n 1156, .n 1155, .n 1154, .n 1153, .n 1152, .n 1151] g63W 1158
/-- The second call's high lane. -/
def fcC : List Stmt :=
  [addS (.n 1218) (.n 38) (.n 1060), cst 1219 (word 1024 0 0), mulS (.n 1220) (.n 1217) (.n 1219),
    addS (.n 1221) (.n 1218) (.n 1220), cst 1222 (word 1 0 1), mulS (.n 1223) (.n 1221) (.n 1222)]

/-- The fields' block of the body. -/
def sFieldsBlock : List Stmt :=
  sBits ++ sBooleans ++ sShifts ++ [cst 1061 (word 0 0 0)] ++ sPl.1 ++ (sCheck sPl.2.1).1 ++
    [copyS (.n 1224) sPP]

open scoped Dec in
theorem sCheck_eq : (sCheck sPl.2.1).1 = fcA ++ addS (.n 17) (sLane 0) (.n 1148) :: (fcB ++
    addS (.n 18) (sLane 2) (.n 1150) :: hintW "sp_unused" (runV 1151 7) :: (fcU.1 ++ (fcC ++
      [.atom (.assertInK (.n 1223) (.n 1217))]))) := by
  decide +kernel

theorem fcU_val : fcU.2.2 = .n 1217 := by decide +kernel

theorem sFieldsBlock_eq : sFieldsBlock = (sBits ++ sBooleans) ++ ((sShifts ++ [cst 1061 (word 0 0 0)] ++ sPl.1) ++
    (fcA ++ addS (.n 17) (sLane 0) (.n 1148) :: (fcB ++ addS (.n 18) (sLane 2) (.n 1150) ::
      hintW "sp_unused" (runV 1151 7) :: (fcU.1 ++ (fcC ++ (.atom (.assertInK (.n 1223) (.n 1217)) ::
        [copyS (.n 1224) sPP])))))) := by
  rw [sFieldsBlock, sCheck_eq]
  simp

theorem fChecks_nb : NumBelow 317 (Stmt.valsList (sBits ++ sBooleans)) := numBelow_of_all (by decide +kernel)
theorem fChecks_atoms : atomsOnly (sBits ++ sBooleans) = true := by decide +kernel
theorem fSeq_ok : SeqOK 317 (sShifts ++ [cst 1061 (word 0 0 0)] ++ sPl.1) 1147 := seqB_ok (by decide +kernel)
theorem fcA_ok : SeqOK 1147 fcA 1149 := seqB_ok (by decide +kernel)
theorem fcB_ok : SeqOK 1149 fcB 1151 := seqB_ok (by decide +kernel)
theorem fcC_ok : SeqOK 1218 fcC 1224 := seqB_ok (by decide +kernel)

theorem sVal_nb {i : Nat} (hi : i < 266) : ∃ k < 1061, sVal i = .n k := by
  obtain ⟨hf, h1, h2⟩ := sFieldOf_spec hi
  refine ⟨_, ?_, rfl⟩
  generalize sFieldOf i = f at hf h1 h2
  simp only [sFieldBase, sFieldOff, sFieldLen] at *
  interval_cases f <;> simp at * <;> omega

/-- **What the fields give**: the bits and values of `D`, the index its low `26` bits, and the
unused bytes' pointers the byte table's. -/
def FieldsPost (σ : Val) (D : Nat) (bb : E) : Prop :=
  BitsAt σ D ∧ ValsAt σ D ∧ σ sIdx = eOfNat (D % 2 ^ 26) ∧ ∀ k ≤ 6, BytePtr bb (σ (.n (fbPtr 1158 k)))

theorem bitsAt_congr {σ σ' : Val} {D : Nat} (h : BitsAt σ D) (hσ : AgreeBelow 317 σ σ') : BitsAt σ' D :=
  fun i hi => by rw [show sBit i = .n (51 + i) from rfl, ← hσ (51 + i) (by omega)]; exact h i hi

theorem valsAt_congr {σ σ' : Val} {D : Nat} (h : ValsAt σ D) (hσ : AgreeBelow 1061 σ σ') : ValsAt σ' D :=
  fun i hi => by rw [hσ.apply (sVal_nb hi)]; exact h i hi

theorem fieldsPost_congr {σ σ' : Val} {D : Nat} {bb : E} (h : FieldsPost σ D bb) (hσ : AgreeBelow 1218 σ σ') :
    FieldsPost σ' D bb := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨bitsAt_congr h1 (hσ.mono (by norm_num)), valsAt_congr h2 (hσ.mono (by norm_num)), ?_, fun k hk => ?_⟩
  · rw [sIdx_eq, ← hσ 1067 (by norm_num)]; rw [sIdx_eq] at h3; exact h3
  · rw [← hσ _ (by simp only [fbPtr]; split <;> omega)]; exact h4 k hk

theorem bFold_unused (x : E) :
    bFold (unusedByte x 6) [unusedByte x 5, unusedByte x 4, unusedByte x 3, unusedByte x 2, unusedByte x 1,
      unusedByte x 0] = unusedNat x := by
  have := unusedNat_lt x
  simp only [bFold, unusedByte]
  generalize unusedNat x = U at this ⊢
  norm_num
  omega

theorem sBooleans_mem {a : Atom} (h : Stmt.atom a ∈ sBooleans) :
    ∃ k, 51 ≤ k ∧ k < 317 ∧ a = .mul (.n k) (.n k) (.n k) := by
  simp only [sBooleans, booleans, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_map] at h
  rcases h with ⟨b, hb, hm⟩ | ⟨j, hj, e⟩
  · simp only [mulS, List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at hm
    rcases hm with rfl | rfl
    · exact ⟨51 + b, by omega, by omega, rfl⟩
    · exact ⟨179 + b, by omega, by omega, rfl⟩
  · simp only [mulS, Stmt.atom.injEq] at e
    exact ⟨307 + j, by omega, by omega, e.symm⟩

/-- A bit of `D`. -/
theorem bit_mul_self (D i : Nat) : (if D.testBit i then (1 : E) else 0) =
    (if D.testBit i then (1 : E) else 0) * (if D.testBit i then (1 : E) else 0) := by
  split <;> simp

/-- **The fields complete**: the bits hinted from the digest's cells, every field shifted and
placed, both calls' cells checked against the lanes and the unused bytes, and `P` copied into the
FORS key's first cell. -/
theorem sFields_complete (hm : MemOK rd 256) {bb : E} (hbb : ByteBits rd bb) (σ : Val)
    (h1 : σ (.n 1) = bb) (hc17 : IsCanonical128 (σ (.n 17))) (hc18 : IsCanonical128 (σ (.n 18)))
    (hc38 : IsCanonical128 (σ (.n 38))) :
    Completes C rd 51 1225 sFieldsBlock σ (fun σ' =>
      FieldsPost σ' (digestD (σ (.n 17)) (σ (.n 18)) (σ (.n 38))) bb ∧ σ' (.n 1224) = σ sPP) := by
  set D := digestD (σ (.n 17)) (σ (.n 18)) (σ (.n 38)) with hD
  set f : Nat → E := fun i => if D.testBit i then 1 else 0 with hf
  rw [sFieldsBlock_eq]
  refine Completes.reload ((updRun_ext σ 51 266 f).mono le_rfl (by norm_num)) ?_
  set σb := updRun σ 51 266 f with hσb
  have hbits : ∀ i < 266, σb (.n (51 + i)) = f i := fun i hi => updRun_at σ 51 266 f hi
  have hlowb : ∀ k < 51, σb (.n k) = σ (.n k) := fun k hk => updRun_below σ 51 266 f ⟨k, hk, rfl⟩
  -- the bits' checks
  have hchk : AtomsHold rd σb (sBits ++ sBooleans) := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · simp only [sBits, List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at ha
      rcases ha with rfl | rfl | rfl <;> trivial
    · obtain ⟨k, hk1, hk2, rfl⟩ := sBooleans_mem ha
      show σb _ = σb _ * σb _
      rw [show k = 51 + (k - 51) by omega, hbits (k - 51) (by omega)]
      exact bit_mul_self D _
  refine Completes.append (m := 317) (by norm_num) (by norm_num) fChecks_nb
    (completes_atoms (Post := fun σ' => σ' = σb) fChecks_atoms (Ext.refl _ _ _) rfl hchk)
    (fun σ' _ e => ?_)
  subst e
  -- the shifts and the placements
  refine Completes.seq fSeq_ok (by norm_num) (fun σ2 he2 hh2 => ?_)
  have hb2 : BitsAt σ2 D := fun i hi => by
    rw [show sBit i = .n (51 + i) from rfl, he2.apply (Or.inl (by omega)), hbits i hi]
  have hv2 : ValsAt σ2 D := sShifts_vals hb2 hh2.left.left
  obtain ⟨hlanes, hidx, hlast⟩ := sPl_sound hv2 hh2.right
  have hlow2 : ∀ k < 51, σ2 (.n k) = σ (.n k) := fun k hk => by
    rw [he2.apply (Or.inl (by omega)), hlowb k hk]
  obtain ⟨l0, l1, l2, l3⟩ := laneNat_low (c17 := σ (.n 17)) (c18 := σ (.n 18)) (c38 := σ (.n 38))
  obtain ⟨e0, e1, e2, e3⟩ := sLane_eq
  -- the first call's cells
  refine Completes.seq fcA_ok (by norm_num) (fun σ3 he3 hh3 => ?_)
  have hA3 : σ3 (.n 1148) = σ2 (sLane 1) * word 0 1 0 := by
    have m := hh3.atom (a := .mul (.n 1148) (sLane 1) (.n 1147)) (by simp [fcA, mulS])
    have c := hh3.atom (a := .const (.n 1147) (word 0 1 0)) (by simp [fcA, cst])
    simp only [Atom.Holds] at m c
    rw [m, c, e1, he3.apply (Or.inl (by norm_num))]
  have ck17 : (Atom.add (.n 17) (sLane 0) (.n 1148)).Holds rd σ3 := by
    show σ3 (.n 17) = σ3 (sLane 0) + σ3 (.n 1148)
    rw [hA3, e0, he3.apply (Or.inl (by norm_num)), he3.apply (Or.inl (by norm_num)), hlow2 17 (by norm_num),
      ← e0, hlanes 0 (by norm_num), hlanes 1 (by norm_num), l0, l1]
    exact cell_of_lanes hc17
  refine Completes.checks (xs := [addS (.n 17) (sLane 0) (.n 1148)]) rfl
    (fun a ha => by simp only [addS, List.mem_singleton, Stmt.atom.injEq] at ha; subst ha; exact ck17)
    (by rw [e0]; exact numBelow_of_all (by decide +kernel)) (by norm_num) ?_
  refine Completes.seq fcB_ok (by norm_num) (fun σ4 he4 hh4 => ?_)
  have t42 : ∀ k < 1147, σ4 (.n k) = σ2 (.n k) := fun k hk => by
    rw [he4.apply (Or.inl (by omega)), he3.apply (Or.inl (by omega))]
  have hB4 : σ4 (.n 1150) = σ2 (sLane 3) * word 0 1 0 := by
    have m := hh4.atom (a := .mul (.n 1150) (sLane 3) (.n 1149)) (by simp [fcB, mulS])
    have c := hh4.atom (a := .const (.n 1149) (word 0 1 0)) (by simp [fcB, cst])
    simp only [Atom.Holds] at m c
    rw [m, c, e3, t42 _ (by norm_num)]
  have ck18 : (Atom.add (.n 18) (sLane 2) (.n 1150)).Holds rd σ4 := by
    show σ4 (.n 18) = σ4 (sLane 2) + σ4 (.n 1150)
    rw [hB4, e2, t42 _ (by norm_num), t42 _ (by norm_num), hlow2 18 (by norm_num), ← e2,
      hlanes 2 (by norm_num), hlanes 3 (by norm_num), l2, l3]
    exact cell_of_lanes hc18
  refine Completes.checks (xs := [addS (.n 18) (sLane 2) (.n 1150)]) rfl
    (fun a ha => by simp only [addS, List.mem_singleton, Stmt.atom.injEq] at ha; subst ha; exact ck18)
    (by rw [e2]; exact numBelow_of_all (by decide +kernel)) (by norm_num) ?_
  -- the unused bytes
  set c38 := σ (.n 38) with hc38d
  set g : Nat → E := fun k => ofK (addressOfIndex (unusedByte c38 k)) with hg
  refine Completes.reload ((updRun_ext σ4 1151 7 g).mono le_rfl (by norm_num)) ?_
  set σu := updRun σ4 1151 7 g with hσu
  refine Completes.append (xs := [hintW "sp_unused" (runV 1151 7)]) (m := 1158) (by norm_num) (by norm_num)
    (by rw [valsList_hint]; exact numBelow_of_all (by decide +kernel)) (hintKeep_complete _ _ _ _ _)
    (fun σ5 _ e5 => ?_)
  subst e5
  have u : ∀ k < 7, σu (.n (1151 + k)) = g k := fun k hk => updRun_at σ4 1151 7 g hk
  have tu : ∀ k < 1151, σu (.n k) = σ4 (.n k) := fun k hk => updRun_below σ4 1151 7 g ⟨k, hk, rfl⟩
  have hbyte : ∀ k, unusedByte c38 k < 256 := fun k => Nat.mod_lt _ (by norm_num)
  have htop : unusedByte c38 6 < 64 := by
    have := unusedNat_lt c38
    unfold unusedByte; omega
  have hfb := sFromBytes_complete (C := C) hm hbb (K := 64) (v0 := unusedByte c38 6) (by norm_num) htop
    (.n 1157) [.n 1156, .n 1155, .n 1154, .n 1153, .n 1152, .n 1151]
    [unusedByte c38 5, unusedByte c38 4, unusedByte c38 3, unusedByte c38 2, unusedByte c38 1, unusedByte c38 0]
    1158 σu (by norm_num) ⟨1157, by norm_num, rfl⟩ (u 6 (by norm_num))
    (.cons ⟨⟨1156, by norm_num, rfl⟩, u 5 (by norm_num), hbyte 5⟩
      (.cons ⟨⟨1155, by norm_num, rfl⟩, u 4 (by norm_num), hbyte 4⟩
      (.cons ⟨⟨1154, by norm_num, rfl⟩, u 3 (by norm_num), hbyte 3⟩
      (.cons ⟨⟨1153, by norm_num, rfl⟩, u 2 (by norm_num), hbyte 2⟩
      (.cons ⟨⟨1152, by norm_num, rfl⟩, u 1 (by norm_num), hbyte 1⟩
      (.cons ⟨⟨1151, by norm_num, rfl⟩, u 0 (by norm_num), hbyte 0⟩ .nil))))))
    (by rw [tu 1 (by norm_num), t42 1 (by norm_num), hlow2 1 (by norm_num)]; exact h1) (by norm_num)
  rw [← g63W_k, bFold_unused] at hfb
  obtain ⟨-, -, hfbnb⟩ := sFromBytes_shape (.n 1157) [.n 1156, .n 1155, .n 1154, .n 1153, .n 1152, .n 1151] g63W
    1158 ⟨1157, by norm_num, rfl⟩ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro m (rfl | rfl | rfl | rfl | rfl | rfl) <;> exact ⟨_, by norm_num, rfl⟩)
  refine Completes.append (m := 1218) (by norm_num) (by norm_num) hfbnb hfb (fun σ6 he6 ⟨hu6, hp6⟩ => ?_)
  rw [show (sFromBytes (.n 1157) [.n 1156, .n 1155, .n 1154, .n 1153, .n 1152, .n 1151] g63W 1158).2.2 = .n 1217
    from fcU_val] at hu6
  -- the second call's high lane
  refine Completes.seq fcC_ok (by norm_num) (fun σ7 he7 hh7 => ?_)
  have t72 : ∀ k < 1147, σ7 (.n k) = σ2 (.n k) := fun k hk => by
    rw [he7.apply (Or.inl (by omega)), he6.apply (Or.inl (by omega)), tu k (by omega), t42 k hk]
  have h1217 : σ7 (.n 1217) = eOfNat (unusedNat c38) := by rw [he7.apply (Or.inl (by norm_num))]; exact hu6
  have hcC : σ7 (.n 1223) = ofK (c38.limb 1) := by
    have a0 := hh7.atom (a := .add (.n 1218) (.n 38) (.n 1060)) (by simp [fcC, addS])
    have c1 := hh7.atom (a := .const (.n 1219) (word 1024 0 0)) (by simp [fcC, cst])
    have m2 := hh7.atom (a := .mul (.n 1220) (.n 1217) (.n 1219)) (by simp [fcC, mulS])
    have a3 := hh7.atom (a := .add (.n 1221) (.n 1218) (.n 1220)) (by simp [fcC, addS])
    have c4 := hh7.atom (a := .const (.n 1222) (word 1 0 1)) (by simp [fcC, cst])
    have m5 := hh7.atom (a := .mul (.n 1223) (.n 1221) (.n 1222)) (by simp [fcC, mulS])
    simp only [Atom.Holds] at a0 c1 m2 a3 c4 m5
    rw [m5, c4, a3, m2, c1, a0, h1217, t72 38 (by norm_num), t72 1060 (by norm_num), hlow2 38 (by norm_num),
      ← sPl_lane, hlast, digestD_high]
    exact high_inK hc38
  have ckK : (Atom.assertInK (.n 1223) (.n 1217)).Holds rd σ7 :=
    ⟨by rw [hcC]; exact ofK_isInK _, by rw [h1217]; exact eOfNat_isInK _⟩
  refine Completes.checks (xs := [.atom (.assertInK (.n 1223) (.n 1217))]) rfl
    (fun a ha => by simp only [List.mem_singleton, Stmt.atom.injEq] at ha; subst ha; exact ckK)
    (numBelow_of_all (by decide +kernel)) (by norm_num) ?_
  -- `P` into the FORS key
  have hfp7 : FieldsPost σ7 D bb := by
    have ag : AgreeBelow 1147 σ2 σ7 := fun k hk => (t72 k hk).symm
    refine ⟨bitsAt_congr hb2 (ag.mono (by norm_num)), valsAt_congr hv2 (ag.mono (by norm_num)), ?_,
      fun k hk => ?_⟩
    · rw [sIdx_eq, ← ag 1067 (by norm_num), ← sIdx_eq]; exact hidx
    · rw [he7.apply (Or.inl (by simp only [fbPtr]; split <;> omega))]; exact hp6 k hk
  have hP7 : σ7 sPP = σ sPP := by rw [show sPP = .n 2 from rfl, t72 2 (by norm_num), hlow2 2 (by norm_num)]
  refine ((seq_completes (C := C) (rd := rd) (b := 1224) (b' := 1225) (ss := [copyS (.n 1224) sPP])
    (seqB_ok (by decide +kernel)) σ7).keep (Q := fun σ' => FieldsPost σ' D bb ∧ σ' sPP = σ sPP)
    (Q' := fun σ' => FieldsPost σ' D bb ∧ σ' sPP = σ sPP) ⟨hfp7, hP7⟩
    (fun σ' he ⟨q1, q2⟩ => ⟨fieldsPost_congr q1 (fun k hk => (he.apply (Or.inl (by omega))).symm),
      by rw [show sPP = .n 2 from rfl, he.apply (Or.inl (by norm_num))]; exact q2⟩)).mono le_rfl le_rfl
    (fun σ' ⟨hh, q1, q2⟩ => ⟨q1, ?_⟩)
  have := hh.atom (a := .copy (.n 1224) sPP) (by simp [copyS])
  simp only [Atom.Holds] at this
  rw [this, q2]

end
end LeanVM.Guest.B1.Sig
