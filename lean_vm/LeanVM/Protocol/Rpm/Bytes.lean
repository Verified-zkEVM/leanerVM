/-
  LeanVM.Protocol.Rpm.Bytes

  The Keccak state, the digest and Keccak-256 of `LeanVM/Spec/` against those of `lean_rpm`:
  the bijections, and Keccak-256 over a permutation as `lean_rpm`'s sponge over it.
-/

import LeanVM.Spec.Rpm
import LeanVM.Protocol.Verifier.Load
import LeanRpm.Keccak

/-!
# Lanes and bytes

`LeanVM/Spec/` holds a Keccak state as `25` lanes of `64` bits (`KState`) and a digest as four
lanes (`Digest`); `lean_rpm` holds them as bytes (`LeanRpm.KState`: 32 digest bytes, 104 more
bytes of the rate, 64 bytes of capacity; `LeanRpm.KDigest`: 32 bytes). Byte `8i + k` is byte `k`
of lane `i`, little-endian (`KState.toRpm`, `Digest.ofRpm`, `LeanVM/Spec/Rpm.lean`).

* `stateEquiv`, `digestEquiv`: the two bijections.
* `keccak256With_rpm`: Keccak-256 over a permutation `π` of the lane states (`keccak256With`,
  `LeanVM/Spec/Rpm.lean`) is `lean_rpm`'s Keccak-256 sponge (`LeanRpm.keccak256With`: rate 136
  bytes, capacity 512 bits, the padding `0x01 ‖ 0^* ‖ 0x80`, the zero state, the first 32 bytes)
  over `π` read on bytes, in every monad. In particular the deployed Keccak-256 is `lean_rpm`'s
  sponge over the deployed Keccak-f[1600] read on bytes (`keccak256_eq_rpm`).
* `admissible_toRpm`: a state keeping lanes `16..24` of another keeps its capacity and its byte
  `135`, so the block that leads from one to the other is non-final (`LeanRpm.keccakNF`).
-/

namespace LeanVM.Rpm

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakHash

/-! ## A lane and its bytes -/

theorem or_mul_two_pow {a n : ℕ} (b : ℕ) (ha : a < 2 ^ n) : a ||| b * 2 ^ n = a + b * 2 ^ n := by
  rw [Nat.or_comm, Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt ha]; ring

theorem bytes8_or {x0 x1 x2 x3 x4 x5 x6 x7 : ℕ} (h0 : x0 < 256) (h1 : x1 < 256) (h2 : x2 < 256)
    (h3 : x3 < 256) (h4 : x4 < 256) (h5 : x5 < 256) (h6 : x6 < 256) (h7 : x7 < 256) :
    (x0 % 18446744073709551616 ||| x1 * 256 % 18446744073709551616 |||
      x2 * 65536 % 18446744073709551616 ||| x3 * 16777216 % 18446744073709551616 |||
      x4 * 4294967296 % 18446744073709551616 ||| x5 * 1099511627776 % 18446744073709551616 |||
      x6 * 281474976710656 % 18446744073709551616 |||
      x7 * 72057594037927936 % 18446744073709551616) =
    (x0 + 256 * (x1 + 256 * (x2 + 256 * (x3 + 256 * (x4 + 256 * (x5 + 256 * (x6 + 256 * x7))))))) %
      18446744073709551616 := by
  rw [Nat.mod_eq_of_lt (by omega : x0 < _), Nat.mod_eq_of_lt (by omega : x1 * 256 < _),
    Nat.mod_eq_of_lt (by omega : x2 * 65536 < _), Nat.mod_eq_of_lt (by omega : x3 * 16777216 < _),
    Nat.mod_eq_of_lt (by omega : x4 * 4294967296 < _),
    Nat.mod_eq_of_lt (by omega : x5 * 1099511627776 < _),
    Nat.mod_eq_of_lt (by omega : x6 * 281474976710656 < _),
    Nat.mod_eq_of_lt (by omega : x7 * 72057594037927936 < _), Nat.mod_eq_of_lt (by omega)]
  rw [show (256 : ℕ) = 2 ^ 8 by rfl, or_mul_two_pow _ (by omega)]
  rw [show (65536 : ℕ) = 2 ^ 16 by rfl, or_mul_two_pow _ (by omega)]
  rw [show (16777216 : ℕ) = 2 ^ 24 by rfl, or_mul_two_pow _ (by omega)]
  rw [show (4294967296 : ℕ) = 2 ^ 32 by rfl, or_mul_two_pow _ (by omega)]
  rw [show (1099511627776 : ℕ) = 2 ^ 40 by rfl, or_mul_two_pow _ (by omega)]
  rw [show (281474976710656 : ℕ) = 2 ^ 48 by rfl, or_mul_two_pow _ (by omega)]
  rw [show (72057594037927936 : ℕ) = 2 ^ 56 by rfl, or_mul_two_pow _ (by omega)]
  ring

/-- `leLane` reads the eight bytes from `8i` as `laneOfBytes` does. -/
theorem leLane_eq_laneOfBytes (bs : List UInt8) (i : ℕ) :
    leLane bs i = laneOfBytes (bs.drop (8 * i)) := by
  apply UInt64.toNat_inj.mp
  have hb : ∀ k, (bs[8 * i + k]?.getD 0).toNat < 256 := fun k ↦ UInt8.toNat_lt _
  have e : ∀ k, (bs.drop (8 * i)).getD k 0 = bs.getD (8 * i + k) 0 := fun k ↦ by
    simp [List.getD_eq_getElem?_getD]
  simp only [leLane, laneOfBytes, e, List.range_succ, List.range_zero, List.nil_append,
    List.foldl_append, List.foldr_append, List.foldl_cons, List.foldl_nil, List.foldr_cons,
    List.foldr_nil, UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt8.toNat_toUInt64,
    List.getD_eq_getElem?_getD, UInt64.zero_or]
  have h0 := hb 0
  simp only [Nat.add_zero] at h0
  have h1 := hb 1; have h2 := hb 2; have h3 := hb 3; have h4 := hb 4; have h5 := hb 5
  have h6 := hb 6; have h7 := hb 7
  generalize (bs[8 * i]?.getD 0).toNat = x0 at *
  generalize (bs[8 * i + 1]?.getD 0).toNat = x1 at *
  generalize (bs[8 * i + 2]?.getD 0).toNat = x2 at *
  generalize (bs[8 * i + 3]?.getD 0).toNat = x3 at *
  generalize (bs[8 * i + 4]?.getD 0).toNat = x4 at *
  generalize (bs[8 * i + 5]?.getD 0).toNat = x5 at *
  generalize (bs[8 * i + 6]?.getD 0).toNat = x6 at *
  generalize (bs[8 * i + 7]?.getD 0).toNat = x7 at *
  simp only [Nat.shiftLeft_eq, Nat.mul_zero, Nat.add_zero]
  norm_num
  exact bytes8_or h0 h1 h2 h3 h4 h5 h6 h7

/-- The bytes of `laneOfBytes b` are the first eight of `b`, missing ones `0`. -/
theorem wordBytes_laneOfBytes' (b : List UInt8) :
    wordBytes (laneOfBytes b) = (List.range 8).map fun k ↦ b.getD k 0 := by
  have hb : ∀ k, (b.getD k 0).toNat < 256 := fun k ↦ UInt8.toNat_lt _
  have h0 := hb 0; have h1 := hb 1; have h2 := hb 2; have h3 := hb 3; have h4 := hb 4
  have h5 := hb 5; have h6 := hb 6; have h7 := hb 7
  simp only [wordBytes, laneOfBytes, List.range_succ, List.range_zero, List.nil_append,
    List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, List.cons_append, List.nil_append, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply UInt8.toNat_inj.mp <;>
    simp only [UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow] <;>
    generalize (b.getD 0 0).toNat = x0 at * <;>
    generalize (b.getD 1 0).toNat = x1 at * <;>
    generalize (b.getD 2 0).toNat = x2 at * <;>
    generalize (b.getD 3 0).toNat = x3 at * <;>
    generalize (b.getD 4 0).toNat = x4 at * <;>
    generalize (b.getD 5 0).toNat = x5 at * <;>
    generalize (b.getD 6 0).toNat = x6 at * <;>
    generalize (b.getD 7 0).toNat = x7 at * <;>
    norm_num <;> omega

/-- The bytes of `leLane bs i` are bytes `8i` to `8i + 7` of `bs`, missing ones `0`. -/
theorem wordBytes_leLane (bs : List UInt8) (i : ℕ) :
    wordBytes (leLane bs i) = (List.range 8).map fun k ↦ bs.getD (8 * i + k) 0 := by
  rw [leLane_eq_laneOfBytes, wordBytes_laneOfBytes']
  refine List.map_congr_left fun k _ ↦ ?_
  simp [List.getD_eq_getElem?_getD]

/-! ## Lists of lanes and their bytes -/

/-- The bytes of a list of lanes, each little-endian. -/
def lanesBytes (l : List UInt64) : List UInt8 := l.flatMap wordBytes

@[simp] theorem lanesBytes_nil : lanesBytes [] = [] := rfl

@[simp] theorem lanesBytes_cons (a : UInt64) (l : List UInt64) :
    lanesBytes (a :: l) = wordBytes a ++ lanesBytes l := rfl

@[simp] theorem length_lanesBytes (l : List UInt64) : (lanesBytes l).length = 8 * l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih, wordBytes_length]; ring

theorem drop_lanesBytes (l : List UInt64) (i : ℕ) :
    (lanesBytes l).drop (8 * i) = lanesBytes (l.drop i) := by
  induction l generalizing i with
  | nil => simp
  | cons a l ih =>
    cases i with
    | zero => simp
    | succ i =>
      rw [lanesBytes_cons, show 8 * (i + 1) = 8 + 8 * i by ring, ← List.drop_drop,
        List.drop_left' (wordBytes_length a), ih, List.drop_succ_cons]

theorem leLane_lanesBytes (l : List UInt64) (i : ℕ) (hi : i < l.length) :
    leLane (lanesBytes l) i = l[i] := by
  rw [leLane_eq_laneOfBytes, drop_lanesBytes, List.drop_eq_getElem_cons hi, lanesBytes_cons,
    laneOfBytes_wordBytes_append]

theorem getD_lanesBytes (l : List UInt64) (j : ℕ) (hj : j < 8 * l.length) :
    (lanesBytes l).getD j 0 = (wordBytes (l[j / 8]'(by omega))).getD (j % 8) 0 := by
  have hj' : j / 8 < l.length := by omega
  conv_lhs => rw [show j = 8 * (j / 8) + j % 8 by omega]
  rw [List.getD_eq_getElem?_getD, ← List.getElem?_drop, drop_lanesBytes,
    List.drop_eq_getElem_cons hj', lanesBytes_cons,
    List.getElem?_append_left (by rw [wordBytes_length]; omega), ← List.getD_eq_getElem?_getD]

theorem lanesBytes_ofFn_leLane (bs : List UInt8) (n : ℕ) (h : bs.length = 8 * n) :
    lanesBytes (List.ofFn fun i : Fin n ↦ leLane bs i) = bs := by
  refine List.ext_getElem (by simp [h]) fun j h1 h2 ↦ ?_
  have hj : j < 8 * (List.ofFn fun i : Fin n ↦ leLane bs i).length := by simp [h] at h2 ⊢; omega
  have e := getD_lanesBytes _ j hj
  rw [List.getD_eq_getElem _ _ h1] at e
  rw [e, List.getElem_ofFn, wordBytes_leLane, List.getD_eq_getElem _ _ (by simp; omega)]
  simp only [List.getElem_map, List.getElem_range]
  rw [List.getD_eq_getElem _ _ (by omega)]
  congr 1
  omega

/-! ## The state -/

@[simp] theorem length_toBytes (x : LeanRpm.KState) : x.toBytes.length = 200 := by
  simp [LeanRpm.KState.toBytes]

/-- Lengths of byte lists, for `omega`. -/
macro "len_omega" : tactic =>
  `(tactic| (simp only [List.length_append, List.length_ofFn, Vector.length_toList,
    LeanRpm.KState.toBytes] at *; omega))

theorem ofBytes_toBytes (x : LeanRpm.KState) : LeanRpm.KState.ofBytes x.toBytes = x := by
  obtain ⟨⟨a, b⟩, c⟩ := x
  simp only [LeanRpm.KState.ofBytes, LeanRpm.KState.toBytes, Prod.mk.injEq]
  refine ⟨⟨Vector.ext fun i hi ↦ ?_, Vector.ext fun i hi ↦ ?_⟩, Vector.ext fun i hi ↦ ?_⟩ <;>
    simp only [Vector.getElem_ofFn] <;>
    rw [List.getD_eq_getElem _ _ (by len_omega)]
  · rw [List.getElem_append_left (by len_omega), List.getElem_append_left (by len_omega),
      Vector.getElem_toList]
  · rw [List.getElem_append_left (by len_omega), List.getElem_append_right (by len_omega),
      Vector.getElem_toList]
    simp only [Vector.length_toList, Nat.add_sub_cancel_left]
  · rw [List.getElem_append_right (by len_omega), Vector.getElem_toList]
    simp only [List.length_append, Vector.length_toList, Nat.add_sub_cancel_left]

theorem toBytes_ofBytes (bs : List UInt8) (h : bs.length = 200) :
    (LeanRpm.KState.ofBytes bs).toBytes = bs := by
  refine List.ext_getElem (by len_omega) fun j h1 h2 ↦ ?_
  simp only [LeanRpm.KState.ofBytes, LeanRpm.KState.toBytes, Vector.toList_ofFn]
  by_cases j1 : j < 32
  · rw [List.getElem_append_left (by len_omega), List.getElem_append_left (by len_omega),
      List.getElem_ofFn, List.getD_eq_getElem _ _ (by omega)]
  · by_cases j2 : j < 136
    · rw [List.getElem_append_left (by len_omega), List.getElem_append_right (by len_omega),
        List.getElem_ofFn, List.getD_eq_getElem _ _ (by len_omega)]
      simp only [List.length_ofFn]
      congr 1; omega
    · rw [List.getElem_append_right (by len_omega), List.getElem_ofFn,
        List.getD_eq_getElem _ _ (by len_omega)]
      simp only [List.length_append, List.length_ofFn]
      have e : 136 + (j - (32 + 104)) = j := by omega
      simp only [e]

/-- The lane state of 200 bytes: lane `i` is bytes `8i` to `8i + 7`, little-endian. -/
def KState.ofRpm (x : LeanRpm.KState) : KState := Vector.ofFn fun i : Fin 25 ↦ leLane x.toBytes i

theorem toBytes_toRpm (s : KState) : (KState.toRpm s).toBytes = lanesBytes s.toList :=
  toBytes_ofBytes (lanesBytes s.toList) (by simp)

theorem ofRpm_toRpm (s : KState) : KState.ofRpm (KState.toRpm s) = s := by
  refine Vector.ext fun i hi ↦ ?_
  rw [KState.ofRpm, Vector.getElem_ofFn, toBytes_toRpm, leLane_lanesBytes _ _ (by simpa)]
  simp

theorem toRpm_ofRpm (x : LeanRpm.KState) : KState.toRpm (KState.ofRpm x) = x := by
  show LeanRpm.KState.ofBytes (lanesBytes (KState.ofRpm x).toList) = x
  rw [KState.ofRpm, Vector.toList_ofFn, lanesBytes_ofFn_leLane _ 25 (by simp), ofBytes_toBytes]

/-- **The Keccak state as lanes and as bytes.** -/
def stateEquiv : KState ≃ LeanRpm.KState where
  toFun := KState.toRpm
  invFun := KState.ofRpm
  left_inv := ofRpm_toRpm
  right_inv := toRpm_ofRpm

@[simp] theorem stateEquiv_apply (s : KState) : stateEquiv s = KState.toRpm s := rfl

@[simp] theorem stateEquiv_symm_apply (x : LeanRpm.KState) :
    stateEquiv.symm x = KState.ofRpm x := rfl

/-- Byte `j` of a state is byte `j % 8` of lane `j / 8`. -/
theorem toBytes_toRpm_getElem (s : KState) (j : ℕ) (hj : j < 200) :
    (KState.toRpm s).toBytes[j]'(by simp; omega) =
      (wordBytes (s[j / 8]'(by omega))).getD (j % 8) 0 := by
  have h := getD_lanesBytes s.toList j (by simp; omega)
  rw [← toBytes_toRpm, List.getD_eq_getElem _ _ (by simp; omega)] at h
  rw [h]
  simp

/-- The zero state. -/
theorem lanesBytes_replicate_zero (n : ℕ) :
    lanesBytes (List.replicate n 0) = List.replicate (8 * n) 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, lanesBytes_cons, ih, show 8 * (n + 1) = 8 + 8 * n by ring,
      ← List.replicate_append_replicate]
    rfl

theorem toRpm_zero : KState.toRpm (Vector.replicate 25 0) = LeanRpm.KState.zero := by
  rw [← ofBytes_toBytes LeanRpm.KState.zero]
  show LeanRpm.KState.ofBytes (lanesBytes (Vector.replicate 25 0).toList) = _
  rw [Vector.toList_replicate, lanesBytes_replicate_zero]
  simp only [LeanRpm.KState.zero, LeanRpm.KState.toBytes, Vector.toList_replicate,
    List.replicate_append_replicate]

/-! ## The digest -/

/-- The 32 bytes of a digest. -/
def Digest.toRpm (d : Digest) : LeanRpm.KDigest :=
  Vector.ofFn fun i : Fin 32 ↦ (lanesBytes d.toList).getD i 0

theorem toList_digestToRpm (d : Digest) : (Digest.toRpm d).toList = lanesBytes d.toList := by
  refine List.ext_getElem (by simp) fun j h1 h2 ↦ ?_
  simp only [Digest.toRpm, Vector.toList_ofFn, List.getElem_ofFn]
  rw [List.getD_eq_getElem _ _ h2]

theorem digestOfRpm_toRpm (d : Digest) : Digest.ofRpm (Digest.toRpm d) = d := by
  have e : ∀ k (hk : k < 4), leLane (Digest.toRpm d).toList k = d[k] := fun k hk ↦ by
    rw [toList_digestToRpm, leLane_lanesBytes _ _ (by simpa)]
    simp
  refine Vector.ext fun i hi ↦ ?_
  interval_cases i
  · exact e 0 (by norm_num)
  · exact e 1 (by norm_num)
  · exact e 2 (by norm_num)
  · exact e 3 (by norm_num)

theorem digestToRpm_ofRpm (d : LeanRpm.KDigest) : Digest.toRpm (Digest.ofRpm d) = d := by
  apply Vector.toList_inj.mp
  rw [toList_digestToRpm]
  have e : (Digest.ofRpm d).toList = List.ofFn fun i : Fin 4 ↦ leLane d.toList i := by
    simp [Digest.ofRpm, List.ofFn_succ]
  rw [e, lanesBytes_ofFn_leLane _ 4 (by simp)]

/-- **The digest as lanes and as bytes.** -/
def digestEquiv : Digest ≃ LeanRpm.KDigest where
  toFun := Digest.toRpm
  invFun := Digest.ofRpm
  left_inv := digestOfRpm_toRpm
  right_inv := digestToRpm_ofRpm

@[simp] theorem digestEquiv_apply (d : Digest) : digestEquiv d = Digest.toRpm d := rfl

@[simp] theorem digestEquiv_symm_apply (d : LeanRpm.KDigest) :
    digestEquiv.symm d = Digest.ofRpm d := rfl

/-! ## Absorbing a block -/

theorem wordBytes_getD (w : UInt64) (k : ℕ) (hk : k < 8) :
    (wordBytes w).getD k 0 = (w >>> (8 * k).toUInt64).toUInt8 := by
  rw [wordBytes, List.getD_eq_getElem _ _ (by simpa using hk)]
  simp

theorem wordBytes_xor_getD (a b : UInt64) (k : ℕ) (hk : k < 8) :
    (wordBytes (a ^^^ b)).getD k 0 = (wordBytes a).getD k 0 ^^^ (wordBytes b).getD k 0 := by
  rw [wordBytes_getD _ _ hk, wordBytes_getD _ _ hk, wordBytes_getD _ _ hk, UInt64.shiftRight_xor,
    UInt64.toUInt8_xor]

theorem wordBytes_leLane_getD (bs : List UInt8) (i k : ℕ) (hk : k < 8) :
    (wordBytes (leLane bs i)).getD k 0 = bs.getD (8 * i + k) 0 := by
  rw [wordBytes_leLane, List.getD_eq_getElem _ _ (by simpa using hk)]
  simp

theorem lane_eq_getElem (s : KState) (i : ℕ) (hi : i < 25) : Keccak.lane s i = s[i] := by
  simp [Keccak.lane, Array.getD_eq_getD_getElem?, hi]

/-- Byte `j` of a state, through `toRpm`. -/
theorem lanesBytes_getD (s : KState) (j : ℕ) (hj : j < 200) :
    (lanesBytes s.toList).getD j 0 = (wordBytes (s[j / 8]'(by omega))).getD (j % 8) 0 := by
  rw [getD_lanesBytes _ _ (by simp; omega)]
  simp

theorem toRpm_fst_fst (s : KState) (j : ℕ) (hj : j < 32) :
    (KState.toRpm s).1.1[j] = (wordBytes (s[j / 8]'(by omega))).getD (j % 8) 0 := by
  rw [← lanesBytes_getD s j (by omega)]
  simp [KState.toRpm, LeanRpm.KState.ofBytes, lanesBytes]

theorem toRpm_fst_snd (s : KState) (j : ℕ) (hj : j < 104) :
    (KState.toRpm s).1.2[j] =
      (wordBytes (s[(32 + j) / 8]'(by omega))).getD ((32 + j) % 8) 0 := by
  rw [← lanesBytes_getD s (32 + j) (by omega)]
  simp [KState.toRpm, LeanRpm.KState.ofBytes, lanesBytes]

theorem toRpm_snd (s : KState) (j : ℕ) (hj : j < 64) :
    (KState.toRpm s).2[j] =
      (wordBytes (s[(136 + j) / 8]'(by omega))).getD ((136 + j) % 8) 0 := by
  rw [← lanesBytes_getD s (136 + j) (by omega)]
  simp [KState.toRpm, LeanRpm.KState.ofBytes, lanesBytes]

/-- **XORing a block's lanes into the rate is XORing its bytes** (`absorbBlock`, `absorb`). -/
theorem toRpm_absorbInput (s : KState) (block : List UInt8) :
    KState.toRpm (Vector.ofFn fun i : Fin 25 ↦
        if i.val < 17 then Keccak.lane s i ^^^ leLane block i else Keccak.lane s i) =
      LeanRpm.absorb (KState.toRpm s) (LeanRpm.KBlock.ofBytes block) := by
  set v : KState := Vector.ofFn fun i : Fin 25 ↦
    if i.val < 17 then Keccak.lane s i ^^^ leLane block i else Keccak.lane s i with hv
  have hin : ∀ i (hi : i < 17), v[i]'(by omega) = s[i]'(by omega) ^^^ leLane block i := by
    intro i hi
    rw [hv, Vector.getElem_ofFn]
    simp only [hi, ↓reduceIte, lane_eq_getElem s i (by omega)]
  have hout : ∀ i (hi : 17 ≤ i) (hi' : i < 25), v[i] = s[i] := by
    intro i hi hi'
    rw [hv, Vector.getElem_ofFn]
    simp only [show ¬ i < 17 by omega, ↓reduceIte, lane_eq_getElem s i hi']
  have hblk : ∀ j (hj : j < 136), (wordBytes (v[j / 8]'(by omega))).getD (j % 8) 0 =
      (wordBytes (s[j / 8]'(by omega))).getD (j % 8) 0 ^^^ block.getD j 0 := by
    intro j hj
    rw [hin (j / 8) (by omega), wordBytes_xor_getD _ _ _ (by omega),
      wordBytes_leLane_getD _ _ _ (by omega)]
    congr 2
    omega
  refine Prod.ext (Prod.ext (Vector.ext fun j hj ↦ ?_) (Vector.ext fun j hj ↦ ?_))
    (Vector.ext fun j hj ↦ ?_)
  · change _ = (Vector.zipWith (· ^^^ ·) (KState.toRpm s).1.1 _)[j]
    rw [Vector.getElem_zipWith, toRpm_fst_fst _ _ hj, toRpm_fst_fst _ _ hj, hblk j (by omega),
      LeanRpm.KBlock.ofBytes, Vector.getElem_ofFn]
  · change _ = (Vector.zipWith (· ^^^ ·) (KState.toRpm s).1.2 _)[j]
    rw [Vector.getElem_zipWith, toRpm_fst_snd _ _ hj, toRpm_fst_snd _ _ hj,
      hblk (32 + j) (by omega), LeanRpm.KBlock.ofBytes, Vector.getElem_ofFn]
  · change (KState.toRpm v).2[j] = (KState.toRpm s).2[j]
    rw [toRpm_snd _ _ hj, toRpm_snd _ _ hj, hout _ (by omega) (by omega)]

/-! ## The padding -/

theorem length_padBlock (data : List UInt8) (h : data.length < 136) :
    (padBlock data).length = 136 := by
  simp only [padBlock, List.length_modify, List.length_append, List.length_replicate, rate]
  omega

/-- The last block: the padding of fewer than `136` bytes is `padBlock`. -/
theorem keccakPadBytes_eq_padBlock (data : List UInt8) (h : data.length < 136) :
    LeanRpm.keccakPadBytes data = padBlock data := by
  have hm : data.length % 136 = data.length := Nat.mod_eq_of_lt h
  unfold LeanRpm.keccakPadBytes
  simp only [hm]
  apply List.ext_getElem?
  intro j
  simp only [padBlock, rate, padFirst, padLast, List.getElem?_modify]
  by_cases hj : j < data.length
  · split_ifs <;> simp_all [List.getElem?_append_left hj]
    omega
  · split_ifs <;> simp_all [List.getElem?_append_right (Nat.le_of_not_lt hj),
      List.getElem?_replicate]
    · decide
    · rw [show j - 135 = (j - 136) + 1 by omega]; rfl
    · rw [show j - data.length = (134 - data.length) + 1 by omega, List.getElem?_cons_succ,
        List.getElem?_append_right (by simp), List.length_replicate, Nat.sub_self]
      have e : 134 - data.length + 1 < 136 - data.length := by omega
      simp only [List.getElem?_cons_zero, e, ↓reduceIte]
    · rw [show j - data.length = (j - data.length - 1) + 1 by omega, List.getElem?_cons_succ,
        List.getElem?_append]
      simp only [List.length_replicate, List.getElem?_replicate]
      split_ifs <;> simp_all <;> omega

/-- Long data: the padding of at least `136` bytes is the first block, then the padding of the
rest. -/
theorem keccakPadBytes_of_le (data : List UInt8) (h : 136 ≤ data.length) :
    LeanRpm.keccakPadBytes data = data.take 136 ++ LeanRpm.keccakPadBytes (data.drop 136) := by
  have hm : (data.drop 136).length % 136 = data.length % 136 := by
    rw [List.length_drop]; omega
  unfold LeanRpm.keccakPadBytes
  rw [hm]
  split_ifs <;> simp only [List.append_assoc, ← List.append_assoc (data.take 136),
    List.take_append_drop]

theorem toBlocks_of_le (l : List UInt8) (h : 136 ≤ l.length) :
    LeanRpm.toBlocks l = LeanRpm.KBlock.ofBytes (l.take 136) :: LeanRpm.toBlocks (l.drop 136) := by
  match l, h with
  | b :: bs, _ => rw [LeanRpm.toBlocks]

/-! ## Keccak-256 over a permutation -/

section Sponge

variable {m : Type → Type} [Monad m] [LawfulMonad m] (π : LeanRpm.KState → m LeanRpm.KState)

/-- A permutation of the byte states, read on lane states. -/
def lanePerm : KState → m KState := fun s ↦ KState.ofRpm <$> π (KState.toRpm s)

omit [LawfulMonad m] in
theorem absorbBlockWith_lanePerm (s : KState) (block : List UInt8) :
    absorbBlockWith (lanePerm π) s block =
      KState.ofRpm <$> π (LeanRpm.absorb (KState.toRpm s) (LeanRpm.KBlock.ofBytes block)) := by
  rw [absorbBlockWith, lanePerm, toRpm_absorbInput]

theorem absorbWith_lanePerm : ∀ (n : ℕ) (s : KState) (data : List UInt8), data.length / 136 = n →
    absorbWith (lanePerm π) n s data =
      KState.ofRpm <$> LeanRpm.absorbAll π (KState.toRpm s)
        (LeanRpm.toBlocks (LeanRpm.keccakPadBytes data))
  | 0, s, data, h => by
    have hl : data.length < 136 := by omega
    rw [keccakPadBytes_eq_padBlock data hl, toBlocks_of_le _ (by rw [length_padBlock _ hl]),
      List.take_of_length_le (by rw [length_padBlock _ hl]),
      List.drop_of_length_le (by rw [length_padBlock _ hl])]
    simp only [absorbWith, absorbBlockWith_lanePerm, LeanRpm.absorbAll_cons, LeanRpm.toBlocks,
      LeanRpm.absorbAll_nil, bind_pure]
  | n + 1, s, data, h => by
    have hl : 136 ≤ data.length := by omega
    have hd : (data.drop 136).length / 136 = n := by rw [List.length_drop]; omega
    have h136 : (data.take 136).length = 136 := by rw [List.length_take]; omega
    rw [keccakPadBytes_of_le data hl,
      toBlocks_of_le _ (by rw [List.length_append, h136]; omega),
      List.take_append_of_le_length (by rw [h136]), List.take_take, Nat.min_self,
      List.drop_append_of_le_length (by rw [h136]),
      List.drop_of_length_le (by rw [h136]), List.nil_append]
    simp only [absorbWith, absorbBlockWith_lanePerm, LeanRpm.absorbAll_cons, bind_map_left,
      map_bind, rate]
    refine bind_congr fun y ↦ ?_
    rw [absorbWith_lanePerm n _ _ hd, toRpm_ofRpm]

theorem leLane_append_left (l r : List UInt8) (i : ℕ) (h : 8 * i + 8 ≤ l.length) :
    leLane (l ++ r) i = leLane l i := by
  unfold leLane
  refine List.foldl_ext _ _ _ fun a k hk ↦ ?_
  simp only [List.mem_range] at hk
  rw [List.getD_append _ _ _ _ (by omega)]

/-- **Keccak-256 over a permutation is `lean_rpm`'s Keccak-256 sponge over it**, in every
monad: the sponge of rate 136 bytes and capacity 512 bits, with the Keccak padding, from the zero
state, its first 32 bytes read as four little-endian lanes. -/
theorem keccak256With_rpm (data : Bytes) :
    keccak256With (lanePerm π) data = Digest.ofRpm <$> LeanRpm.keccak256With π data := by
  rw [keccak256With, absorbWith_lanePerm π (data.length / rate) _ data rfl, toRpm_zero, LeanRpm.keccak256With,
    LeanRpm.spongeWith, bind_map_left, Functor.map_map, map_eq_bind_pure_comp]
  refine bind_congr fun y ↦ ?_
  have e : ∀ i (hi : i < 4), Keccak.lane (KState.ofRpm y) i = leLane y.1.1.toList i := by
    intro i hi
    rw [lane_eq_getElem _ _ (by omega), KState.ofRpm, Vector.getElem_ofFn]
    show leLane (y.1.1.toList ++ y.1.2.toList ++ y.2.toList) i = _
    rw [List.append_assoc, leLane_append_left _ _ _ (by simp only [Vector.length_toList]; omega)]
  have hv : (#v[Keccak.lane (KState.ofRpm y) 0, Keccak.lane (KState.ofRpm y) 1,
      Keccak.lane (KState.ofRpm y) 2, Keccak.lane (KState.ofRpm y) 3] : Digest) =
        Digest.ofRpm y.1.1 := by
    simp only [Digest.ofRpm, e 0 (by norm_num), e 1 (by norm_num), e 2 (by norm_num),
      e 3 (by norm_num)]
  rw [hv]
  rfl

end Sponge

/-- Keccak-256 over `keccakF` is the deployed Keccak-256. -/
theorem absorbWith_keccakF : ∀ (n : ℕ) (s : KState) (data : List UInt8),
    absorbWith (m := Id) keccakF n s data = KeccakHash.absorb n s data
  | 0, _, _ => rfl
  | n + 1, _, _ => absorbWith_keccakF n _ _

theorem keccak256With_keccakF (data : Bytes) :
    keccak256With (m := Id) keccakF data = keccak256 data := by
  simp only [keccak256With, absorbWith_keccakF]
  rfl

/-- **The deployed Keccak-256 is `lean_rpm`'s Keccak-256 sponge** (`LeanRpm.keccak256With`) over
the deployed Keccak-f[1600] read on bytes. -/
theorem keccak256_eq_rpm (data : Bytes) :
    keccak256 data = Digest.ofRpm
      (LeanRpm.keccak256With (m := Id) (fun x ↦ KState.toRpm (keccakF (KState.ofRpm x))) data) := by
  have h : lanePerm (m := Id) (fun x ↦ KState.toRpm (keccakF (KState.ofRpm x))) =
      (keccakF : KState → Id KState) := by
    funext s
    show KState.ofRpm (KState.toRpm (keccakF (KState.ofRpm (KState.toRpm s)))) = keccakF s
    rw [ofRpm_toRpm, ofRpm_toRpm]
  have e := keccak256With_rpm (m := Id) (fun x ↦ KState.toRpm (keccakF (KState.ofRpm x))) data
  rw [h, keccak256With_keccakF] at e
  exact e.trans (Id.run_map _ _)

/-! ## Keeping the capacity -/

/-- A state keeping lanes `16..24` of another keeps its capacity (lanes `17..24`, bytes
`136..199`) and its byte `135` (the top byte of lane `16`). -/
theorem toRpm_keep (x y : KState) (h : ∀ i : Fin 25, 16 ≤ i.val → x[i] = y[i]) :
    (KState.toRpm x).2 = (KState.toRpm y).2 ∧
      (KState.toRpm x).1.2[103] = (KState.toRpm y).1.2[103] := by
  have h' : ∀ i (hi : 16 ≤ i) (hi' : i < 25), x[i] = y[i] := fun i hi hi' ↦ by
    simpa only [Fin.getElem_fin] using h ⟨i, hi'⟩ hi
  refine ⟨Vector.ext fun j hj ↦ ?_, ?_⟩
  · rw [toRpm_snd _ _ hj, toRpm_snd _ _ hj, h' _ (by omega) (by omega)]
  · rw [toRpm_fst_snd _ _ (by norm_num), toRpm_fst_snd _ _ (by norm_num),
      h' _ (by norm_num) (by norm_num)]

/-- **A duplexing that keeps lanes `16..24` absorbs a non-final block**: from `y` to `x`, the
capacity is kept and the block's last byte is zero (`LeanRpm.keccakNF_blockTo`). -/
theorem keccakNF_of_keep (x y : KState) (h : ∀ i : Fin 25, 16 ≤ i.val → x[i] = y[i]) :
    (KState.toRpm x).2 = (KState.toRpm y).2 ∧
      LeanRpm.keccakNF (LeanRpm.blockTo (KState.toRpm y) (KState.toRpm x)) :=
  ⟨(toRpm_keep x y h).1, LeanRpm.keccakNF_blockTo _ _ (toRpm_keep x y h).2⟩

end LeanVM.Rpm
