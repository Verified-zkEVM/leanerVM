/-
  LeanVM.Guest.B1.Sig.SphincsSound

  `verify_sig_lean_sphincs` (`lean_ethereum.py:3842-3929` at leanVM `c4f4bc92`) is sound: under a
  call relation that unfolds at a frame map, on a memory image of at most `2^32` words, whenever
  its body holds it returns no words, and with the byte table at its second argument the signature
  read off its valuation and its three `sp_wots` frames verifies the claim at its first
  (`verify_sig_lean_sphincs_sound_holds`).
-/

module

public import LeanVM.Guest.B1.Sig.SphincsSoundDigest
public import LeanVM.Guest.B1.Sig.SphincsSoundFors
public import LeanVM.Guest.B1.Sig.SphincsSoundLayer
public import LeanVM.Guest.B1.Sig.SphincsSig
public import LeanVM.Guest.B1.Sig.SphincsData

/-!
# `verify_sig_lean_sphincs`, sound

The body (`Data.core20.body = sBody`) is four blocks of atoms around the three calls of `sp_wots`
(`sBody_split`): the prologue, the FORS trees, the hypertree's addresses and the bottom encoding
(`sBlockA`); the bottom path and the middle layer's counter and encoding (`sBlockB`); the middle
path and the top layer's (`sBlockC`); the top path and the root's check (`sBlockD`).

`verify_sig_lean_sphincs_sound_holds` reads the stages off them: the message digest is the hinted
bits' number `D` (`sFieldsDigest_sound`), the FORS key the trees' top nodes (`sForsTrees_sound`,
`forsRecover_cells`), each layer reaches its root from the one below (`layer_of_cells`: the
encoding's digest, `sp_wots`'s leaf through the frame map, the path), and the top root is the
claim's; `verifyWithKeccak_iff_stages` assembles them.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier (eOfNat kToNat)
open HashSig HashSig.OverPermutation
open Sphincs Sphincs.Verification

@[expose] public section

/-! ## The blocks -/

/-- The statements of an upper layer before its call: the counter and the encoding. -/
def sUpperPre (adr below : V) (b : Nat) : List Stmt :=
  [hintW "sp_counter" (runV b 4)] ++ (sUpperCtrOf b).1 ++
    [cst (sUpperCtrOf b).2.1 (word (tw 4) 0 0), addS (.n ((sUpperCtrOf b).2.1 + 1)) adr (.n (sUpperCtrOf b).2.1)] ++
    (sUpperEncOf below b).1

/-- An upper layer's path. -/
def sUpperPath (lane : V) (off height : Nat) (below : V) (b : Nat) : List Stmt × Nat × V :=
  sPath lane off height 0 (.n (sUpperEncOf below b).2.1) ((sUpperEncOf below b).2.1 + 1)

/-- The prologue, the FORS trees, the addresses and the bottom encoding. -/
def sBlockA : List Stmt :=
  sDigests ++ sFieldsBlock ++ sFors.1 ++ sLanes sH ++
    [cst (sH + 13) (word (tw 4) 0 0), addS (.n (sH + 14)) (.n (sH + 9)) (.n (sH + 13)),
      hintW "sp_counter" (runV (sH + 15) 4)] ++ sCtrB.1 ++ [copyS (.n sCtrB.2.1) sCtrB.2.2] ++ sEncB.1

/-- The bottom path, the middle layer's counter and encoding. -/
def sBlockB : List Stmt := sPathB.1 ++ sUpperPre (.n (sH + 10)) sPathB.2.2 sBaseM

/-- The middle path, the top lane, the top layer's counter and encoding. -/
def sBlockC : List Stmt :=
  (sUpperPath (.n (sH + 8)) 8 8 sPathB.2.2 sBaseM).1 ++ [cst sUpperM.2.1 (word 0 2 0)] ++
    sUpperPre (.n (sH + 12)) sUpperM.2.2 sBaseT

/-- The top path and the root's check. -/
def sBlockD : List Stmt :=
  (sUpperPath (.n sUpperM.2.1) 16 10 sUpperM.2.2 sBaseT).1 ++
    [loadS (.n sUpperT.2.1) (.n 0) 0, .atom (.assertEq sUpperT.2.2 (.n sUpperT.2.1))]

theorem sUpperM_eq : sUpperM = (sUpperPre (.n (sH + 10)) sPathB.2.2 sBaseM ++
    sWotsCall (.n (sH + 10)) (.n (sUpperEncOf sPathB.2.2 sBaseM).2.2) (sUpperEncOf sPathB.2.2 sBaseM).2.1 ::
      (sUpperPath (.n (sH + 8)) 8 8 sPathB.2.2 sBaseM).1, (sUpperPath (.n (sH + 8)) 8 8 sPathB.2.2 sBaseM).2.1,
    (sUpperPath (.n (sH + 8)) 8 8 sPathB.2.2 sBaseM).2.2) := by
  rw [sUpperM, sUpper_eq]
  simp [sUpperPre, sUpperPath, sBaseM]

theorem sUpperT_eq : sUpperT = (sUpperPre (.n (sH + 12)) sUpperM.2.2 sBaseT ++
    sWotsCall (.n (sH + 12)) (.n (sUpperEncOf sUpperM.2.2 sBaseT).2.2) (sUpperEncOf sUpperM.2.2 sBaseT).2.1 ::
      (sUpperPath (.n sUpperM.2.1) 16 10 sUpperM.2.2 sBaseT).1,
    (sUpperPath (.n sUpperM.2.1) 16 10 sUpperM.2.2 sBaseT).2.1,
    (sUpperPath (.n sUpperM.2.1) 16 10 sUpperM.2.2 sBaseT).2.2) := by
  rw [sUpperT, sUpper_eq]
  simp [sUpperPre, sUpperPath, sBaseT]

/-- **The body around its three calls.** -/
theorem sBody_split : sBody = sBlockA ++
    sWotsCall (.n (sH + 9)) (.n sEncB.2.2) sEncB.2.1 :: (sBlockB ++
      sWotsCall (.n (sH + 10)) (.n (sUpperEncOf sPathB.2.2 sBaseM).2.2) (sUpperEncOf sPathB.2.2 sBaseM).2.1 ::
        (sBlockC ++
          sWotsCall (.n (sH + 12)) (.n (sUpperEncOf sUpperM.2.2 sBaseT).2.2) (sUpperEncOf sUpperM.2.2 sBaseT).2.1 ::
            (sBlockD ++ [.ret []]))) := by
  have eM := congrArg Prod.fst sUpperM_eq
  have eT := congrArg Prod.fst sUpperT_eq
  simp only at eM eT
  rw [sBody, eM, eT]
  simp only [sBlockA, sBlockB, sBlockC, sBlockD, sFieldsBlock, List.append_assoc, List.cons_append,
    List.nil_append]

theorem sBlockA_atoms : atomsOnly sBlockA = true := by decide +kernel
theorem sBlockB_atoms : atomsOnly sBlockB = true := by decide +kernel
theorem sBlockC_atoms : atomsOnly sBlockC = true := by decide +kernel
theorem sBlockD_atoms : atomsOnly sBlockD = true := by decide +kernel

/-! ## The calls of `sp_wots` -/

/-- **A call of `sp_wots`** under a call relation that unfolds at `V`: at a key's address, the
encoding's digits reach the target sum and the leaf is the one the chain values of its frame
recover. -/
theorem wots_call_sound {C : CallRel} {rd : Reader} {V : FrameMap} (hV : UnfoldsV rd C V) {a b c d : E}
    (hc : C "sp_wots" [a, b, c] [d]) :
    ∀ (layer : Layer) (tree : TreeIndex) (lf : TreeLeafIndex), b = keyAddressCell layer tree lf →
      TargetSum.Valid (digestDigits (cellVal c)) ∧
        cellVal d = wotsLeafOf (cellVal a) layer tree lf (cellVal c) (spValues (V "sp_wots" [a, b, c] [d])) := by
  obtain ⟨fn, hf, hp, hb⟩ := hV _ _ _ hc
  rw [find_sp_wots] at hf
  cases hf
  rw [sp_wots_params] at hp
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hp
  obtain ⟨h0, h1, h2⟩ := hp
  obtain ⟨leaf, hl, -, hw⟩ := sp_wots_sound hb
  simp only [List.cons.injEq, and_true] at hl
  intro layer tree lf hk
  rw [← h1] at hk
  have := hw layer tree lf hk
  rw [h0, h2, ← hl] at this
  exact this

/-! ## The fields along a path -/

variable {σ : Val}

theorem field_bits {D f : Nat} (hb : BitsAt σ D) (hf : f < 27) :
    ∀ l < sFieldLen f, σ (sBit (sFieldOff f + l)) = if (fieldNat D f).testBit l then 1 else 0 := by
  intro l hl
  have := field_facts hf
  rw [hb _ (by omega), testBit_fieldNat D f l hl]

theorem field_vals {D f : Nat} (hv : ValsAt σ D) (hf : f < 27) :
    ∀ l, l + 1 < sFieldLen f → σ (sVal (sFieldOff f + l + 1)) = eOfNat (fieldNat D f >>> (l + 1)) :=
  fun l hl => by rw [add_assoc]; exact valsAt_field hv hf hl

/-- **A path along field `f`**: from the leaf `cur`, the root is the fold of `tNode` at the lane,
the leaf the field's value. -/
theorem field_path {D f : Nat} (hp : PadOK σ sPad) (hb : BitsAt σ D) (hv : ValsAt σ D) (hf : f < 27)
    {rd : Reader} {lane cur : V} {x : Nat} (hA : AtomsHold rd σ (sPath lane (sFieldOff f) (sFieldLen f) 0 cur x).1) :
    σ (sPath lane (sFieldOff f) (sFieldLen f) 0 cur x).2.2 = pFold (pathNode σ lane (sFieldOff f) (fieldNat D f) x)
      (sFieldLen f) (σ cur) :=
  sPath_sound_all hp (fieldNat_lt D f) (field_bits hb hf) (field_vals hv hf) hA

/-! ## The digest's index and leaves -/

theorem testBit_mod_div (D n k m : Nat) (h : k + m ≤ n) : D % 2 ^ n / 2 ^ k % 2 ^ m = D / 2 ^ k % 2 ^ m := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases hi : i < m
  · simp [hi, show i + k < n by omega]
  · simp [hi]

theorem digestIndex_ofNat (D : Nat) : (digestIndex (BitVec.ofNat messageDigestBits D)).val = D % 2 ^ 26 := by
  show ((BitVec.ofNat messageDigestBits D).extractLsb' 0 indexBits).toNat = _
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_zero, show indexBits = 26 from rfl]
  exact Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (show 26 ≤ messageDigestBits by decide))

theorem digestForsLeaves_ofNat (D : Nat) (c : ForsTreeIndex) :
    (digestForsLeaves (BitVec.ofNat messageDigestBits D) c).val = fieldNat D (3 + c.val) := by
  have hc : c.val < 24 := c.isLt
  show ((BitVec.ofNat messageDigestBits D).extractLsb' (indexBits + forsTreeHeight * c.val) forsTreeHeight).toNat = _
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, fieldNat, fOff_eq, fLen_eq,
    show indexBits + forsTreeHeight * c.val = fOff c.val by simp [fOff, indexBits, forsTreeHeight],
    show forsTreeHeight = 10 from rfl]
  exact testBit_mod_div D _ _ _ (by show 26 + 10 * c.val + 10 ≤ 26 + 24 * 10; omega)

/-! ## An upper layer's counter and encoding -/

/-- **An upper layer's counter and encoding, sound**: the counter is a word below `2^32`, and the
encoding's digest is the statement's of the root `below` and the counter, at the key's address. -/
theorem sUpperPre_sound {κ : Nat} (hκ : κ ≤ 32) {L : MemoryImage κ} (hbb : ByteBits L.read (σ (.n 1)))
    (hp : PadOK σ sPad) {adr below : V} {b : Nat} (h : AtomsHold L.read σ (sUpperPre adr below b))
    {l : Layer} {t : TreeIndex} {lf : TreeLeafIndex} (hadr : σ adr = keyAddressCell l t lf) :
    ∃ N < 2 ^ 32, σ (sUpperCtrOf b).2.2 = eOfNat N ∧
      cellVal (σ (.n (sUpperEncOf below b).2.2)) = th (m := Id) keccakF1600 (cellVal (σ sPP))
        (hashDomainFields (.encoding l t lf))
        ([σ below].flatMap cellBytes ++ littleEndianBytes 4 (BitVec.ofNat 32 (cellNat (eOfNat N)))) := by
  have hc : AtomsHold L.read σ (sUpperCtrOf b).1 := h.left.left.right
  obtain ⟨N, hN, hlt⟩ := sFromBytes_sound hκ hbb (K := 256) (by norm_num) (le_refl _) g255W_eq
    (by simp [sMarks]) hc
  have hlt' : N < 2 ^ 32 := by simpa [sMarks] using hlt
  have e1 : σ (.n (sUpperCtrOf b).2.1) = word (tw 4) 0 0 := h.left.right.atom (a := .const _ _) (by simp [cst])
  have e2 : σ (.n ((sUpperCtrOf b).2.1 + 1)) = σ adr + σ (.n (sUpperCtrOf b).2.1) :=
    h.left.right.atom (a := .add _ _ _) (by simp [addS])
  refine ⟨N, hlt', hN, ?_⟩
  have hE : sUpperEncOf below b = kMsg sPad ([.cell sPP, .cell (.n ((sUpperCtrOf b).2.1 + 1))] ++
      [below].map KC.cell ++ [.cell (sUpperCtrOf b).2.2]) (16 * ([below].length + 2) + 4) false none
      ((sUpperCtrOf b).2.1 + 2) := rfl
  have hR := h.right
  rw [hE] at hR ⊢
  have := encDigest_sound (cs := [below]) hp hlt' hN (l := l) (t := t) (lf := lf) (by rw [e2, e1, hadr])
    (fun h => by simp at h) hR
  exact this

/-! ## The FORS key -/

theorem sForsBase_eq (c : Nat) : sForsBase c = 1225 + 233 * c := by
  rw [sForsBase, sForsTrees_end]

/-- Tree `k`'s two top nodes, over the cells of the digest `D` and the hinted values. -/
def sTops (σ : Val) (D k : Nat) : E × E :=
  fTops (σ sPP) (eOfNat (D % 2 ^ 26)) k (fieldNat D (3 + k)) (σ (.n (1225 + 233 * k))) (forsSib σ k (1225 + 233 * k))

/-- **The FORS key, sound**: its bytes are those of the trees' top nodes. -/
theorem sForsKey_sound {rd : Reader} {D : Nat} (hp : PadOK σ sPad) (hbits : BitsAt σ D) (hvals : ValsAt σ D)
    (hidx : σ sIdx = eOfNat (D % 2 ^ 26)) (hFors : AtomsHold rd σ sFors.1) {pk : PublicKey} {m : Message}
    {V : FrameMap} (hdig : sDigestOf pk m (sphincsSigOf σ V) = BitVec.ofNat messageDigestBits D)
    (hP : pk.parameter = cellVal (σ sPP)) :
    forsKeyPayload (sForsKeyOf pk m (sphincsSigOf σ V)) = (sFors.2.2.map σ).flatMap cellBytes := by
  have htops := sForsTrees_sound (s := fun c => fieldNat D (3 + c)) hp hidx (fun c _ => fieldNat_fors_lt D c)
    (fun c hc => fors_bits hc hbits) (fun c hc => fors_vals hc hvals) 24 0 1225 (by norm_num) hFors
  have hkey : sForsKeyOf pk m (sphincsSigOf σ V) = fun c => (cellVal (sTops σ D c.val).1, cellVal (sTops σ D c.val).2) := by
    unfold sForsKeyOf
    rw [hdig, hP, forsRecover_cells (σ sPP) _ _ _ (secretOf := fun c => σ (.n (1225 + 233 * c)))
      (sibOf := fun c => forsSib σ c (1225 + 233 * c))
      (fun c => by simp only [sphincsSigOf, sForsOpeningOf, sForsBase_eq])
      (fun c l h => by simp only [sphincsSigOf, sForsOpeningOf, sForsBase_eq, forsSib, fOff])]
    funext c
    rw [digestForsLeaves_ofNat, digestIndex_ofNat]
    rfl
  rw [hkey]
  refine Eq.trans (forsKeyPayload_cells (sTops σ D)) ?_
  rw [show sFors = sForsTrees 24 0 1225 from rfl, sForsTrees_base, List.map_flatMap]
  congr 1
  refine List.flatMap_congr fun k hk => ?_
  have hk24 := List.mem_range.mp hk
  have e := htops k hk24
  simp only [Nat.zero_add] at e
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]
  exact ⟨(congrArg Prod.fst e).symm, (congrArg Prod.snd e).symm⟩

/-! ## The hypertree's addresses -/

theorem word256_lo : word 256 0 0 = word (2 ^ 8) 0 0 := rfl
theorem word256_hi : word 0 256 0 = word 0 (2 ^ 8) 0 := rfl

/-- **The hypertree's lanes and key addresses**: from the index's three fields. -/
theorem sLanes_sound {rd : Reader} {D : Nat} (hvals : ValsAt σ D) (h : AtomsHold rd σ (sLanes sH)) (idx : Index)
    (hidx : idx.val = D % 2 ^ 26) :
    σ (.n (sH + 4)) = laneCell 0 (treeOfIndex 0 idx) ∧ σ (.n (sH + 8)) = laneCell 1 (treeOfIndex 1 idx) ∧
      σ (.n (sH + 9)) = keyAddressCell 0 (treeOfIndex 0 idx) (leafOfIndex 0 idx) ∧
      σ (.n (sH + 10)) = keyAddressCell 1 (treeOfIndex 1 idx) (leafOfIndex 1 idx) ∧
      σ (.n (sH + 12)) = keyAddressCell 2 (treeOfIndex 2 idx) (leafOfIndex 2 idx) ∧
      word 0 2 0 = laneCell 2 (treeOfIndex 2 idx) := by
  have v0 : σ (sVal 0) = eOfNat (fieldNat D 0) := valsAt_field hvals (f := 0) (by norm_num) (k := 0) (by decide)
  have v8 : σ (sVal 8) = eOfNat (fieldNat D 1) := valsAt_field hvals (f := 1) (by norm_num) (k := 0) (by decide)
  have v16 : σ (sVal 16) = eOfNat (fieldNat D 2) := valsAt_field hvals (f := 2) (by norm_num) (k := 0) (by decide)
  have f0 : fieldNat D 0 = D % 2 ^ 8 := by simp [fieldNat, sFieldOff, sFieldLen]
  have f1 : fieldNat D 1 = D / 2 ^ 8 % 2 ^ 8 := by simp [fieldNat, sFieldOff, sFieldLen]
  have f2 : fieldNat D 2 = D / 2 ^ 16 % 2 ^ 10 := by simp [fieldNat, sFieldOff, sFieldLen]
  rw [f0] at v0
  rw [f1] at v8
  rw [f2] at v16
  have a0 : σ (.n sH) = word 256 0 0 := h.atom (a := .const (.n sH) _) (by simp [sLanes, cst])
  have a1 : σ (.n (sH + 1)) = σ (sVal 16) * σ (.n sH) := h.atom (a := .mul (.n (sH + 1)) _ _) (by simp [sLanes, mulS])
  have a2 : σ (.n (sH + 2)) = σ (sVal 8) + σ (.n (sH + 1)) := h.atom (a := .add (.n (sH + 2)) _ _) (by simp [sLanes, addS])
  have a3 : σ (.n (sH + 3)) = word 0 256 0 := h.atom (a := .const (.n (sH + 3)) _) (by simp [sLanes, cst])
  have a4 : σ (.n (sH + 4)) = σ (.n (sH + 2)) * σ (.n (sH + 3)) := h.atom (a := .mul (.n (sH + 4)) _ _) (by simp [sLanes, mulS])
  have a5 : σ (.n (sH + 5)) = word 0 256 0 := h.atom (a := .const (.n (sH + 5)) _) (by simp [sLanes, cst])
  have a6 : σ (.n (sH + 6)) = σ (sVal 16) * σ (.n (sH + 5)) := h.atom (a := .mul (.n (sH + 6)) _ _) (by simp [sLanes, mulS])
  have a7 : σ (.n (sH + 7)) = word 0 1 0 := h.atom (a := .const (.n (sH + 7)) _) (by simp [sLanes, cst])
  have a8 : σ (.n (sH + 8)) = σ (.n (sH + 6)) + σ (.n (sH + 7)) := h.atom (a := .add (.n (sH + 8)) _ _) (by simp [sLanes, addS])
  have a9 : σ (.n (sH + 9)) = σ (sVal 0) + σ (.n (sH + 4)) := h.atom (a := .add (.n (sH + 9)) _ _) (by simp [sLanes, addS])
  have a10 : σ (.n (sH + 10)) = σ (sVal 8) + σ (.n (sH + 8)) := h.atom (a := .add (.n (sH + 10)) _ _) (by simp [sLanes, addS])
  have a11 : σ (.n (sH + 11)) = word 0 2 0 := h.atom (a := .const (.n (sH + 11)) _) (by simp [sLanes, cst])
  have a12 : σ (.n (sH + 12)) = σ (sVal 16) + σ (.n (sH + 11)) := h.atom (a := .add (.n (sH + 12)) _ _) (by simp [sLanes, addS])
  have hD1 : D / 2 ^ 8 % 2 ^ 8 < 2 ^ 8 := Nat.mod_lt _ (by norm_num)
  have hD2 : D / 2 ^ 16 % 2 ^ 10 < 2 ^ 10 := Nat.mod_lt _ (by norm_num)
  -- the lanes
  have lb : σ (.n (sH + 4)) = word 0 (2 ^ 8 * (2 ^ 8 * (D / 2 ^ 16 % 2 ^ 10) + D / 2 ^ 8 % 2 ^ 8)) 0 := by
    rw [a4, a3, a2, a1, a0, v8, v16, word256_lo, word256_hi, word_two_pow_mul_eOfNat (by omega), add_comm,
      ← eOfNat_add_low hD1, eOfNat_mul_word_hi (by omega)]
  have lm : σ (.n (sH + 8)) = word 0 (1 + 2 ^ 8 * (D / 2 ^ 16 % 2 ^ 10)) 0 := by
    rw [a8, a7, a6, a5, v16, word256_hi, eOfNat_mul_word_hi (by omega), word_hi_add, two_pow_mul_xor (by norm_num),
      add_comm]
  have t0 : (treeOfIndex 0 idx).val = 2 ^ 8 * (D / 2 ^ 16 % 2 ^ 10) + D / 2 ^ 8 % 2 ^ 8 := by
    simp [treeOfIndex, bitsBelowLayer, layerHeight, hidx, layerCount]
    omega
  have t1 : (treeOfIndex 1 idx).val = D / 2 ^ 16 % 2 ^ 10 := by
    simp [treeOfIndex, bitsBelowLayer, layerHeight, hidx, layerCount]
    omega
  have t2 : (treeOfIndex 2 idx).val = 0 := by
    simp [treeOfIndex, bitsBelowLayer, layerHeight, hidx, layerCount]
  have e0 : (leafOfIndex 0 idx).val = D % 2 ^ 8 := by
    simp [leafOfIndex, bitsBelowLayer, layerHeight, hidx, layerCount]
  have e1 : (leafOfIndex 1 idx).val = D / 2 ^ 8 % 2 ^ 8 := by
    simp [leafOfIndex, bitsBelowLayer, layerHeight, hidx, layerCount]
    omega
  have e2 : (leafOfIndex 2 idx).val = D / 2 ^ 16 % 2 ^ 10 := by
    simp [leafOfIndex, bitsBelowLayer, layerHeight, hidx, layerCount]
    omega
  have L0 : laneCell 0 (treeOfIndex 0 idx) = σ (.n (sH + 4)) := by
    rw [lb, laneCell_eq, t0, show ((0 : Layer) : Nat) = 0 from rfl, Nat.zero_add]
  have L1 : laneCell 1 (treeOfIndex 1 idx) = σ (.n (sH + 8)) := by
    rw [lm, laneCell_eq, t1, show ((1 : Layer) : Nat) = 1 from rfl]
  have L2 : laneCell 2 (treeOfIndex 2 idx) = word 0 2 0 := by
    rw [laneCell_eq, t2]
    rfl
  refine ⟨L0.symm, L1.symm, ?_, ?_, ?_, L2.symm⟩
  · rw [keyAddressCell_lane, L0, e0, a9, v0, add_comm]
  · rw [keyAddressCell_lane, L1, e1, a10, v8, add_comm]
  · rw [keyAddressCell_lane, L2, e2, a12, v16, a11, add_comm]

theorem leafOfIndex_vals {D : Nat} (idx : Index) (hidx : idx.val = D % 2 ^ 26) :
    (leafOfIndex 0 idx).val = fieldNat D 0 ∧ (leafOfIndex 1 idx).val = fieldNat D 1 ∧
      (leafOfIndex 2 idx).val = fieldNat D 2 := by
  simp only [fieldNat, sFieldOff, sFieldLen]
  refine ⟨?_, ?_, ?_⟩
  · simp [leafOfIndex, bitsBelowLayer, layerHeight, hidx, layerCount]
  · simp [leafOfIndex, bitsBelowLayer, layerHeight, hidx, layerCount]
    omega
  · simp [leafOfIndex, bitsBelowLayer, layerHeight, hidx, layerCount]
    omega

/-! ## A layer -/

/-- A message cell that is a cell. -/
def kcCell : KC → Bool
  | .cell _ => true
  | _ => false

theorem tailCells_of (blk : List KC) (h : [4, 5, 6, 7].all (fun i => kcCell (blk.getD i .zero)) = true) :
    TailCells blk := by
  intro k hk
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h
  have key : ∀ k : KC, kcCell k = true → ∃ v, k = .cell v := fun k hk => by
    cases k with
    | cell v => exact ⟨v, rfl⟩
    | _ => simp [kcCell] at hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact key _ h.1
  · exact key _ h.2.1
  · exact key _ h.2.2.1
  · exact key _ h.2.2.2

theorem sFors_tops_length : sFors.2.2.length = 48 := by
  rw [show sFors = sForsTrees 24 0 1225 from rfl, sForsTrees_base]
  simp

/-- The bottom encoding's cells. -/
theorem sEncB_eq : sEncB = kMsg sPad ([.cell (.n 1224), .cell (.n (sH + 14))] ++ sFors.2.2.map KC.cell ++
    [.cell (.n sCtrB.2.1)]) (16 * (sFors.2.2.length + 2) + 4) true none (sCtrB.2.1 + 1) := by
  rw [sFors_tops_length, sEncB, sEncCells]
  simp

theorem sEncB_tail : TailCells (blockOf (kMsgCells ([.cell (.n 1224), .cell (.n (sH + 14))] ++
    sFors.2.2.map KC.cell ++ [.cell (.n sCtrB.2.1)]) (16 * (sFors.2.2.length + 2) + 4) (sCtrB.2.1 + 1)) 0) :=
  tailCells_of _ (by decide +kernel)

variable {C : CallRel} {Vm : FrameMap}

theorem sig_counter0 : ((sphincsSigOf σ Vm).layers 0).counter = BitVec.ofNat 32 (cellNat (σ sCtrB.2.2)) := by
  simp only [sphincsSigOf, sLayerOf, sCtrOf]
  rfl

theorem sig_values0 : ((sphincsSigOf σ Vm).layers 0).chainValues =
    spValues (Vm "sp_wots" [σ sPP, σ (.n (sH + 9)), σ (.n sEncB.2.2)] [σ (.n sEncB.2.1)]) := by
  simp only [sphincsSigOf, sLayerOf, sAtOf, sEncOf, sLeafOf]
  rfl

theorem sig_path0 : ∀ j < layerHeight 0, cellVal (siblingOf σ (sBit (sFieldOff 0 + j)) (sEncB.2.1 + 1 + 21 * j)) =
    layerPath (sphincsSigOf σ Vm) 0 j := by
  intro j hj
  simp only [layerPath, hj, ↓reduceDIte, sphincsSigOf, sLayerOf, sOffOf, sLeafOf, sFieldOff]
  rfl

/-- **The bottom layer, sound**: from the FORS key's bytes it reaches the root its path computes. -/
theorem bottom_reaches {κ : Nat} (hκ : κ ≤ 32) {L : MemoryImage κ} (hV : UnfoldsV L.read C Vm)
    (hbb : ByteBits L.read (σ (.n 1))) {D : Nat} (hp : PadOK σ sPad) (hbits : BitsAt σ D) (hvals : ValsAt σ D)
    (hidx : σ sIdx = eOfNat (D % 2 ^ 26)) (h1224 : σ (.n 1224) = σ sPP) (hFors : AtomsHold L.read σ sFors.1)
    (hLanes : AtomsHold L.read σ (sLanes sH))
    (h3 : AtomsHold L.read σ [cst (sH + 13) (word (tw 4) 0 0), addS (.n (sH + 14)) (.n (sH + 9)) (.n (sH + 13)),
      hintW "sp_counter" (runV (sH + 15) 4)])
    (hCtr : AtomsHold L.read σ sCtrB.1) (hCp : AtomsHold L.read σ [copyS (.n sCtrB.2.1) sCtrB.2.2])
    (hEnc : AtomsHold L.read σ sEncB.1)
    (c0 : C "sp_wots" [σ sPP, σ (.n (sH + 9)), σ (.n sEncB.2.2)] [σ (.n sEncB.2.1)])
    (hPath : AtomsHold L.read σ sPathB.1) {pk : PublicKey} {m : Message}
    (hdig : sDigestOf pk m (sphincsSigOf σ Vm) = BitVec.ofNat messageDigestBits D)
    (hP : pk.parameter = cellVal (σ sPP)) :
    LayerReaches pk.parameter (digestIndex (sDigestOf pk m (sphincsSigOf σ Vm))) (sphincsSigOf σ Vm) 0
      (forsKeyPayload (sForsKeyOf pk m (sphincsSigOf σ Vm))) (cellVal (σ sPathB.2.2)) := by
  have hidxv : (digestIndex (sDigestOf pk m (sphincsSigOf σ Vm))).val = D % 2 ^ 26 := by
    rw [hdig, digestIndex_ofNat]
  obtain ⟨L0, -, A0, -, -, -⟩ := sLanes_sound hvals hLanes _ hidxv
  obtain ⟨e0, -, -⟩ := leafOfIndex_vals _ hidxv
  obtain ⟨N, hN, hlt⟩ := sFromBytes_sound hκ hbb (K := 256) (by norm_num) (le_refl _) g255W_eq
    (by simp [sMarks]) hCtr
  have hlt' : N < 2 ^ 32 := by simpa [sMarks] using hlt
  have hN' : σ sCtrB.2.2 = eOfNat N := hN
  have hcp : σ (.n sCtrB.2.1) = σ sCtrB.2.2 := hCp.atom (a := .copy _ _) (by simp [copyS])
  have h13 : σ (.n (sH + 13)) = word (tw 4) 0 0 := h3.atom (a := .const _ _) (by simp [cst])
  have h14 : σ (.n (sH + 14)) = σ (.n (sH + 9)) + σ (.n (sH + 13)) := h3.atom (a := .add _ _ _) (by simp [addS])
  have hEnc' := hEnc
  rw [sEncB_eq] at hEnc'
  have henc := encDigest_sound (pp := .n 1224) hp hlt' (hcp.trans hN') (l := 0)
    (t := treeOfIndex 0 (digestIndex (sDigestOf pk m (sphincsSigOf σ Vm))))
    (lf := leafOfIndex 0 (digestIndex (sDigestOf pk m (sphincsSigOf σ Vm)))) (by rw [h14, h13, A0])
    (fun _ => sEncB_tail) hEnc'
  rw [← sEncB_eq, h1224, ← sForsKey_sound hp hbits hvals hidx hFors hdig hP, ← hN', ← hP] at henc
  have hpath := field_path (f := 0) hp hbits hvals (by norm_num) (lane := .n (sH + 4)) (cur := .n sEncB.2.1)
    (x := sEncB.2.1 + 1) hPath
  have e : σ sPathB.2.2 = pFold (tNode (σ sPP) (laneCell 0 (treeOfIndex 0 (digestIndex (sDigestOf pk m
      (sphincsSigOf σ Vm))))) (leafOfIndex 0 (digestIndex (sDigestOf pk m (sphincsSigOf σ Vm)))).val
      fun j => siblingOf σ (sBit (sFieldOff 0 + j)) (sEncB.2.1 + 1 + 21 * j)) (layerHeight 0) (σ (.n sEncB.2.1)) := by
    rw [e0, ← L0]
    exact hpath
  rw [e]
  rw [← sig_counter0 (Vm := Vm)] at henc
  exact layer_of_cells (atC := σ (.n (sH + 9))) hP.symm henc A0 (wots_call_sound hV c0) sig_values0 sig_path0

/-- **An upper layer, sound**: from the bytes of the root below it reaches the root its path
computes. -/
theorem upper_reaches {κ : Nat} (hκ : κ ≤ 32) {L : MemoryImage κ} (hV : UnfoldsV L.read C Vm)
    (hbb : ByteBits L.read (σ (.n 1))) {D : Nat} (hp : PadOK σ sPad) (hbits : BitsAt σ D) (hvals : ValsAt σ D)
    {adr lane below : V} {b f : Nat} (hf : f < 27) {P : PublicParameter} (hP : cellVal (σ sPP) = P)
    {idx : Index} {sig : Sphincs.Signature} {l : Layer}
    (hpre : AtomsHold L.read σ (sUpperPre adr below b))
    (call : C "sp_wots" [σ sPP, σ adr, σ (.n (sUpperEncOf below b).2.2)] [σ (.n (sUpperEncOf below b).2.1)])
    (hpath : AtomsHold L.read σ (sUpperPath lane (sFieldOff f) (sFieldLen f) below b).1)
    (hadr : σ adr = keyAddressCell l (treeOfIndex l idx) (leafOfIndex l idx))
    (hlane : σ lane = laneCell l (treeOfIndex l idx)) (hleaf : (leafOfIndex l idx).val = fieldNat D f)
    (hh : layerHeight l = sFieldLen f)
    (hctr : (sig.layers l).counter = BitVec.ofNat 32 (cellNat (σ (sUpperCtrOf b).2.2)))
    (hvals' : (sig.layers l).chainValues =
      spValues (Vm "sp_wots" [σ sPP, σ adr, σ (.n (sUpperEncOf below b).2.2)] [σ (.n (sUpperEncOf below b).2.1)]))
    (hsib : ∀ j < layerHeight l, layerPath sig l j =
      cellVal (siblingOf σ (sBit (sFieldOff f + j)) ((sUpperEncOf below b).2.1 + 1 + 21 * j))) :
    LayerReaches P idx sig l (littleEndianBytes 16 (cellVal (σ below)))
      (cellVal (σ (sUpperPath lane (sFieldOff f) (sFieldLen f) below b).2.2)) := by
  obtain ⟨N, hN, hctrN, henc⟩ := sUpperPre_sound hκ hbb hp hpre hadr
  rw [← hctrN, ← hctr, ← bytes16_cell, hP] at henc
  have hp' : σ (sUpperPath lane (sFieldOff f) (sFieldLen f) below b).2.2 = pFold (pathNode σ lane (sFieldOff f)
      (fieldNat D f) ((sUpperEncOf below b).2.1 + 1)) (sFieldLen f) (σ (.n (sUpperEncOf below b).2.1)) :=
    field_path hp hbits hvals hf hpath
  rw [hp', show pathNode σ lane (sFieldOff f) (fieldNat D f) ((sUpperEncOf below b).2.1 + 1) =
    tNode (σ sPP) (laneCell l (treeOfIndex l idx)) (leafOfIndex l idx).val
      (fun j => siblingOf σ (sBit (sFieldOff f + j)) ((sUpperEncOf below b).2.1 + 1 + 21 * j)) by
    rw [pathNode, hlane, hleaf], ← hh]
  exact layer_of_cells hP henc hadr (wots_call_sound hV call) hvals' fun j hj => (hsib j hj).symm

theorem sig_counter1 : ((sphincsSigOf σ Vm).layers 1).counter = BitVec.ofNat 32 (cellNat (σ (sUpperCtrOf sBaseM).2.2)) := by
  simp only [sphincsSigOf, sLayerOf, sCtrOf]
  rfl

theorem sig_values1 : ((sphincsSigOf σ Vm).layers 1).chainValues =
    spValues (Vm "sp_wots" [σ sPP, σ (.n (sH + 10)), σ (.n (sUpperEncOf sPathB.2.2 sBaseM).2.2)]
      [σ (.n (sUpperEncOf sPathB.2.2 sBaseM).2.1)]) := by
  simp only [sphincsSigOf, sLayerOf, sAtOf, sEncOf, sLeafOf]
  rfl

theorem sig_path1 : ∀ j < layerHeight 1, layerPath (sphincsSigOf σ Vm) 1 j =
    cellVal (siblingOf σ (sBit (sFieldOff 1 + j)) ((sUpperEncOf sPathB.2.2 sBaseM).2.1 + 1 + 21 * j)) := by
  intro j hj
  simp only [layerPath, hj, ↓reduceDIte, sphincsSigOf, sLayerOf, sOffOf, sLeafOf, sFieldOff]
  rfl

theorem sig_counter2 : ((sphincsSigOf σ Vm).layers 2).counter = BitVec.ofNat 32 (cellNat (σ (sUpperCtrOf sBaseT).2.2)) := by
  simp only [sphincsSigOf, sLayerOf, sCtrOf]
  rfl

theorem sig_values2 : ((sphincsSigOf σ Vm).layers 2).chainValues =
    spValues (Vm "sp_wots" [σ sPP, σ (.n (sH + 12)), σ (.n (sUpperEncOf sUpperM.2.2 sBaseT).2.2)]
      [σ (.n (sUpperEncOf sUpperM.2.2 sBaseT).2.1)]) := by
  simp only [sphincsSigOf, sLayerOf, sAtOf, sEncOf, sLeafOf]
  rfl

theorem sig_path2 : ∀ j < layerHeight 2, layerPath (sphincsSigOf σ Vm) 2 j =
    cellVal (siblingOf σ (sBit (sFieldOff 2 + j)) ((sUpperEncOf sUpperM.2.2 sBaseT).2.1 + 1 + 21 * j)) := by
  intro j hj
  simp only [layerPath, hj, ↓reduceDIte, sphincsSigOf, sLayerOf, sOffOf, sLeafOf, sFieldOff]
  rfl

/-! ## The theorem -/

/-- **`verify_sig_lean_sphincs` is sound**, for the signature read off its valuation and the frames
of its `sp_wots` calls. -/
theorem verify_sig_lean_sphincs_sound_holds : verify_sig_lean_sphincs_sound_Spec sphincsSigOf := by
  intro C Vm κ L hκ hV σ rets h
  rw [sBody_eq, sBody_split] at h
  obtain ⟨hA, h⟩ := holdsList_split_atoms sBlockA_atoms h
  have hA := atomsHold_of_holdsList sBlockA_atoms hA
  obtain ⟨c0, h⟩ := h
  obtain ⟨hB, h⟩ := holdsList_split_atoms sBlockB_atoms h
  have hB := atomsHold_of_holdsList sBlockB_atoms hB
  obtain ⟨c1, h⟩ := h
  obtain ⟨hC, h⟩ := holdsList_split_atoms sBlockC_atoms h
  have hC := atomsHold_of_holdsList sBlockC_atoms hC
  obtain ⟨c2, h⟩ := h
  obtain ⟨hD, h⟩ := holdsList_split_atoms sBlockD_atoms h
  have hD := atomsHold_of_holdsList sBlockD_atoms hD
  refine ⟨h.symm, fun hbb => ?_⟩
  have hA' : AtomsHold L.read σ (sDigests ++ sFieldsBlock ++ sFors.1 ++ sLanes sH ++
    [cst (sH + 13) (word (tw 4) 0 0), addS (.n (sH + 14)) (.n (sH + 9)) (.n (sH + 13)),
      hintW "sp_counter" (runV (sH + 15) 4)] ++ sCtrB.1 ++ [copyS (.n sCtrB.2.1) sCtrB.2.2] ++ sEncB.1) := hA
  have hB' : AtomsHold L.read σ (sPathB.1 ++ sUpperPre (.n (sH + 10)) sPathB.2.2 sBaseM) := hB
  have hC' : AtomsHold L.read σ ((sUpperPath (.n (sH + 8)) 8 8 sPathB.2.2 sBaseM).1 ++
    [cst sUpperM.2.1 (word 0 2 0)] ++ sUpperPre (.n (sH + 12)) sUpperM.2.2 sBaseT) := hC
  have hD' : AtomsHold L.read σ ((sUpperPath (.n sUpperM.2.1) 16 10 sUpperM.2.2 sBaseT).1 ++
    [loadS (.n sUpperT.2.1) (.n 0) 0, .atom (.assertEq sUpperT.2.2 (.n sUpperT.2.1))]) := hD
  obtain ⟨hp, lP, l5, l6, h1224, D, -, hbits, hvals, hidx, hmd⟩ :=
    sFieldsDigest_sound hκ hbb hA'.left.left.left.left.left.left
  have hload : LoadHolds L.read (σ (.n 0)) 0 (σ (.n sUpperT.2.1)) :=
    hD'.right.atom (a := .load (.n sUpperT.2.1) (.n 0) 0) (by simp [loadS])
  have hroot : σ sUpperT.2.2 = σ (.n sUpperT.2.1) :=
    e_add_eq_zero_iff.mp (hD'.right.atom (a := .assertEq sUpperT.2.2 (.n sUpperT.2.1)) (by simp))
  have hlaneT : σ (.n sUpperM.2.1) = word 0 2 0 := hC'.left.right.atom (a := .const _ _) (by simp [cst])
  refine ⟨σ (.n sUpperT.2.1), σ sPP, σ (.n 5), σ (.n 6), ⟨hload, lP, l5, l6⟩, ?_⟩
  rw [verifyWithKeccak_iff_stages]
  have hdig : sDigestOf (sphincsClaimOf (σ (.n sUpperT.2.1)) (σ sPP) (σ (.n 5)) (σ (.n 6))).1
      (sphincsClaimOf (σ (.n sUpperT.2.1)) (σ sPP) (σ (.n 5)) (σ (.n 6))).2 (sphincsSigOf σ Vm) =
      BitVec.ofNat messageDigestBits D := hmd
  have hidxv : (digestIndex (sDigestOf (sphincsClaimOf (σ (.n sUpperT.2.1)) (σ sPP) (σ (.n 5)) (σ (.n 6))).1
      (sphincsClaimOf (σ (.n sUpperT.2.1)) (σ sPP) (σ (.n 5)) (σ (.n 6))).2 (sphincsSigOf σ Vm))).val =
      D % 2 ^ 26 := by rw [hdig, digestIndex_ofNat]
  obtain ⟨-, L1, -, A1, A2, L2⟩ := sLanes_sound hvals hA'.left.left.left.left.right _ hidxv
  obtain ⟨-, e1, e2⟩ := leafOfIndex_vals _ hidxv
  have h0 := bottom_reaches hκ hV hbb hp hbits hvals hidx h1224 hA'.left.left.left.left.left.right
    hA'.left.left.left.left.right hA'.left.left.left.right hA'.left.left.right hA'.left.right hA'.right c0
    hB'.left hdig rfl
  have h1 := upper_reaches (sig := sphincsSigOf σ Vm) (l := 1) hκ hV hbb hp hbits hvals (f := 1) (by norm_num)
    rfl hB'.right c1 hC'.left.left A1 L1 e1 rfl sig_counter1 sig_values1 sig_path1
  have h2 := upper_reaches (sig := sphincsSigOf σ Vm) (l := 2) hκ hV hbb hp hbits hvals (f := 2) (by norm_num)
    rfl hC'.right c2 hD'.left A2 (hlaneT.trans L2) e2 rfl sig_counter2 sig_values2 sig_path2
  have eM : sUpperM.2.2 = (sUpperPath (.n (sH + 8)) (sFieldOff 1) (sFieldLen 1) sPathB.2.2 sBaseM).2.2 := by
    rw [sUpperM_eq]
    rfl
  have eT : (sUpperPath (.n sUpperM.2.1) (sFieldOff 2) (sFieldLen 2) sUpperM.2.2 sBaseT).2.2 = sUpperT.2.2 := by
    rw [sUpperT_eq]
    rfl
  refine ⟨_, _, h0, h1, ?_⟩
  rw [eT, hroot, eM] at h2
  exact h2

end
end LeanVM.Guest.B1.Sig
