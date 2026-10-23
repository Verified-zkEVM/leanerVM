/-
  LeanVM.Guest.B1.Sig.SphincsAddr

  The address cells `verify_sig_lean_sphincs` hashes are the tweaks of leanSPHINCS's hash domains:
  the index's word plus the guest's constants, summed in the field, are the packed fields' bytes.
-/

module

public import LeanVM.Guest.B1.Sig.SphincsDigest

/-!
# The addresses

`eOfNat_add_high`: a word plus a word above its bits is their sum. `sAdr_bytes`: the packed
fields `lo + 2^32 hi + 2^56 (tag + 32 step)` are the tweak bytes. Each domain's address:
`fchainAdr_bytes`, `childLeafAdr_bytes`, `subNodeAdr_bytes`, `superAdr_bytes`, `topNodeAdr_bytes`,
`encAdr_bytes`, `chainAdr_bytes`, `leafAdr_bytes`, `nodeAdr_bytes`, `msgAdr_bytes`.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Guest LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol.Verifier (eOfNat)

@[expose] public section

theorem eOfNat_add_high {x y k : Nat} (hx : x < 2 ^ k) :
    eOfNat x + eOfNat (2 ^ k * y) = eOfNat (x + 2 ^ k * y) := by
  rw [add_comm, Value.eOfNat_add_of_lt hx, add_comm]

theorem sAdr_bytes {lo hi tag step : Nat} (hlo : lo < 2 ^ 32) (hhi : hi < 2 ^ 24) (htag : tag < 32)
    (hstep : step < 8) :
    cellBytes (eOfNat (lo + 2 ^ 32 * hi + 2 ^ 56 * (tag + 32 * step))) =
      Sphincs.fieldBytes (Sphincs.tweakFields tag step hi lo) := by
  rw [sTweak]
  congr 2
  unfold addrNat
  rw [Nat.mod_eq_of_lt hlo, Nat.mod_eq_of_lt hhi, Nat.mod_eq_of_lt htag, Nat.mod_eq_of_lt hstep]

theorem word_shift {n k y : Nat} (h : n = 2 ^ k * y) : word n 0 0 = eOfNat (2 ^ k * y) := by
  rw [word_eq_eOfNat, h]

/-- A leaf's address word: `idx + c·2^32 + s·2^35`. -/
theorem leafAt_word {idx c s : Nat} (hidx : idx < 2 ^ 26) :
    eOfNat idx + word (c * hiMul + s * 2 ^ 35) 0 0 = eOfNat (idx + 2 ^ 32 * (c + 8 * s)) := by
  rw [word_shift (k := 32) (y := c + 8 * s) (by simp [hiMul]; ring), eOfNat_add_high]
  omega

/-- A key's address word: the leaf's plus `j·2^39 + a·2^40`. -/
theorem keyAt_word {idx c s j a : Nat} (hidx : idx < 2 ^ 26) (hc : c < 8) (hs : s < 16) :
    eOfNat idx + word (c * hiMul + s * 2 ^ 35) 0 0 + word (j * 2 ^ 39 + a * 2 ^ 40) 0 0 =
      eOfNat (idx + 2 ^ 32 * (c + 8 * s) + 2 ^ 39 * (j + 2 * a)) := by
  rw [leafAt_word hidx, word_shift (k := 39) (y := j + 2 * a) (by ring), eOfNat_add_high]
  omega

theorem fchainAdr_bytes {idx c s j a i t : Nat} (hidx : idx < 2 ^ 26) (hc : c < 8) (hs : s < 16)
    (hj : j < 2) (ha : a < 8) (hi : i < 6) (ht : t < 4) :
    cellBytes (eOfNat idx + word (c * hiMul + s * 2 ^ 35) 0 0 + word (j * 2 ^ 39 + a * 2 ^ 40) 0 0 +
        eOfNat (tw 15 + i * 2 ^ 43 + t * stepMul)) =
      Sphincs.fieldBytes (Sphincs.tweakFields 15 t (c + 8 * s + 128 * j + 256 * a + 2048 * i) idx) := by
  have e : eOfNat idx + word (c * hiMul + s * 2 ^ 35) 0 0 + word (j * 2 ^ 39 + a * 2 ^ 40) 0 0 +
      eOfNat (tw 15 + i * 2 ^ 43 + t * stepMul) =
      eOfNat (idx + 2 ^ 32 * (c + 8 * s + 128 * j + 256 * a + 2048 * i) + 2 ^ 56 * (15 + 32 * t)) := by
    rw [keyAt_word hidx hc hs, show tw 15 + i * 2 ^ 43 + t * stepMul = 2 ^ 43 * (i + 2 ^ 13 * (15 + 32 * t)) by
      simp [tw, stepMul]; ring,
      eOfNat_add_high (x := idx + 2 ^ 32 * (c + 8 * s) + 2 ^ 39 * (j + 2 * a)) (k := 43) (by omega)]
    exact congrArg eOfNat (by ring)
  rw [e]
  exact sAdr_bytes (by omega) (by omega) (by omega) (by omega)

theorem childLeafAdr_bytes {idx c s j a : Nat} (hidx : idx < 2 ^ 26) (hc : c < 8) (hs : s < 16)
    (hj : j < 2) (ha : a < 8) :
    cellBytes (eOfNat idx + word (c * hiMul + s * 2 ^ 35) 0 0 + word (j * 2 ^ 39 + a * 2 ^ 40) 0 0 +
        word (tw 16) 0 0) =
      Sphincs.fieldBytes (Sphincs.tweakFields 16 0 (c + 8 * s + 128 * j + 256 * a) idx) := by
  have e : eOfNat idx + word (c * hiMul + s * 2 ^ 35) 0 0 + word (j * 2 ^ 39 + a * 2 ^ 40) 0 0 +
      word (tw 16) 0 0 = eOfNat (idx + 2 ^ 32 * (c + 8 * s + 128 * j + 256 * a) + 2 ^ 56 * (16 + 32 * 0)) := by
    rw [keyAt_word hidx hc hs, word_shift (k := 43) (y := 2 ^ 13 * 16) (by simp [tw]),
      eOfNat_add_high (x := idx + 2 ^ 32 * (c + 8 * s) + 2 ^ 39 * (j + 2 * a)) (k := 43) (by omega)]
    exact congrArg eOfNat (by ring)
  rw [e]
  exact sAdr_bytes (by omega) (by omega) (by omega) (by omega)

theorem div_two_pow_lt {a n l : Nat} (ha : a < 2 ^ (n + 1)) : a / 2 ^ (l + 1) < 2 ^ n := by
  have : a / 2 ^ (l + 1) ≤ a / 2 := Nat.div_le_div_left (by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (l + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)) (by norm_num)
  have h2 : a / 2 < 2 ^ n := by
    rw [Nat.div_lt_iff_lt_mul (by norm_num)]
    rw [pow_succ] at ha
    exact ha
  omega

theorem subNodeAdr_bytes {idx c s j a l : Nat} (hidx : idx < 2 ^ 26) (hc : c < 8) (hs : s < 16)
    (hj : j < 2) (ha : a < 8) (hl : l < 2) :
    cellBytes (eOfNat idx + word (c * hiMul + s * 2 ^ 35) 0 0 + word (j * 2 ^ 39 + a * 2 ^ 40) 0 0 +
        word (a * 2 ^ 40 ^^^ (tw 17 + (l + 1) * 2 ^ 40 + a / 2 ^ (l + 1) * 2 ^ 42)) 0 0) =
      Sphincs.fieldBytes (Sphincs.tweakFields 17 0
        (c + 8 * s + 128 * j + 256 * (l + 1) + 1024 * (a / 2 ^ (l + 1))) idx) := by
  have hq : a / 2 ^ (l + 1) < 2 ^ 2 := div_two_pow_lt (n := 2) (by simpa using ha)
  have e1 : word (j * 2 ^ 39 + a * 2 ^ 40) 0 0 = eOfNat (2 ^ 39 * j) + eOfNat (2 ^ 40 * a) := by
    rw [word_eq_eOfNat, eOfNat_add_high (x := 2 ^ 39 * j) (k := 40) (by omega)]
    exact congrArg eOfNat (by ring)
  have e2 : word (a * 2 ^ 40 ^^^ (tw 17 + (l + 1) * 2 ^ 40 + a / 2 ^ (l + 1) * 2 ^ 42)) 0 0 =
      eOfNat (2 ^ 40 * a) + eOfNat (2 ^ 40 * ((l + 1) + 4 * (a / 2 ^ (l + 1)) + 2 ^ 16 * 17)) := by
    rw [word_eq_eOfNat, Value.eOfNat_xor, show a * 2 ^ 40 = 2 ^ 40 * a by ring,
      show tw 17 + (l + 1) * 2 ^ 40 + a / 2 ^ (l + 1) * 2 ^ 42 =
        2 ^ 40 * ((l + 1) + 4 * (a / 2 ^ (l + 1)) + 2 ^ 16 * 17) by simp [tw]; ring]
  have e3 : eOfNat idx + word (c * hiMul + s * 2 ^ 35) 0 0 + word (j * 2 ^ 39 + a * 2 ^ 40) 0 0 +
      word (a * 2 ^ 40 ^^^ (tw 17 + (l + 1) * 2 ^ 40 + a / 2 ^ (l + 1) * 2 ^ 42)) 0 0 =
      eOfNat idx + word (c * hiMul + s * 2 ^ 35) 0 0 + eOfNat (2 ^ 39 * j) +
        eOfNat (2 ^ 40 * ((l + 1) + 4 * (a / 2 ^ (l + 1)) + 2 ^ 16 * 17)) := by
    rw [e1, e2]
    have : eOfNat (2 ^ 40 * a) + eOfNat (2 ^ 40 * a) = 0 := e_add_self _
    linear_combination this
  have e : eOfNat idx + word (c * hiMul + s * 2 ^ 35) 0 0 + eOfNat (2 ^ 39 * j) +
      eOfNat (2 ^ 40 * ((l + 1) + 4 * (a / 2 ^ (l + 1)) + 2 ^ 16 * 17)) =
      eOfNat (idx + 2 ^ 32 * (c + 8 * s + 128 * j + 256 * (l + 1) + 1024 * (a / 2 ^ (l + 1))) +
        2 ^ 56 * (17 + 32 * 0)) := by
    rw [leafAt_word hidx, eOfNat_add_high (x := idx + 2 ^ 32 * (c + 8 * s)) (k := 39) (by omega),
      eOfNat_add_high (x := idx + 2 ^ 32 * (c + 8 * s) + 2 ^ 39 * j) (k := 40) (by omega)]
    exact congrArg eOfNat (by ring)
  rw [e3, e]
  exact sAdr_bytes (by omega) (by omega) (by omega) (by omega)

theorem superAdr_bytes {idx c s : Nat} (hidx : idx < 2 ^ 26) (hc : c < 8) (hs : s < 16) :
    cellBytes (eOfNat idx + word (c * hiMul + s * 2 ^ 35) 0 0 + word (tw 18) 0 0) =
      Sphincs.fieldBytes (Sphincs.tweakFields 18 0 (c + 8 * s) idx) := by
  have e : eOfNat idx + word (c * hiMul + s * 2 ^ 35) 0 0 + word (tw 18) 0 0 =
      eOfNat (idx + 2 ^ 32 * (c + 8 * s) + 2 ^ 56 * (18 + 32 * 0)) := by
    rw [leafAt_word hidx, word_shift (k := 39) (y := 2 ^ 17 * 18) (by simp [tw]),
      eOfNat_add_high (x := idx + 2 ^ 32 * (c + 8 * s)) (k := 39) (by omega)]
    exact congrArg eOfNat (by ring)
  rw [e]
  exact sAdr_bytes (by omega) (by omega) (by omega) (by omega)

theorem topNodeAdr_bytes {idx c s l : Nat} (hidx : idx < 2 ^ 26) (hc : c < 8) (hs : s < 16)
    (hl : l < 3) :
    cellBytes (eOfNat idx + word (c * hiMul + s * 2 ^ 35) 0 0 +
        word (s * 2 ^ 35 ^^^ (tw 19 + (l + 1) * (8 * hiMul) + s / 2 ^ (l + 1) * (64 * hiMul))) 0 0) =
      Sphincs.fieldBytes (Sphincs.tweakFields 19 0 (c + 8 * (l + 1) + 64 * (s / 2 ^ (l + 1))) idx) := by
  have hq : s / 2 ^ (l + 1) < 2 ^ 3 := div_two_pow_lt (n := 3) (by simpa using hs)
  have e1 : word (c * hiMul + s * 2 ^ 35) 0 0 = eOfNat (2 ^ 32 * c) + eOfNat (2 ^ 35 * s) := by
    rw [word_eq_eOfNat, eOfNat_add_high (x := 2 ^ 32 * c) (k := 35) (by omega)]
    congr 1
    simp [hiMul]
    ring
  have e2 : word (s * 2 ^ 35 ^^^ (tw 19 + (l + 1) * (8 * hiMul) + s / 2 ^ (l + 1) * (64 * hiMul))) 0 0 =
      eOfNat (2 ^ 35 * s) + eOfNat (2 ^ 35 * ((l + 1) + 8 * (s / 2 ^ (l + 1)) + 2 ^ 21 * 19)) := by
    rw [word_eq_eOfNat, Value.eOfNat_xor, show s * 2 ^ 35 = 2 ^ 35 * s by ring,
      show tw 19 + (l + 1) * (8 * hiMul) + s / 2 ^ (l + 1) * (64 * hiMul) =
        2 ^ 35 * ((l + 1) + 8 * (s / 2 ^ (l + 1)) + 2 ^ 21 * 19) by simp [tw, hiMul]; ring]
  have e3 : eOfNat idx + word (c * hiMul + s * 2 ^ 35) 0 0 +
      word (s * 2 ^ 35 ^^^ (tw 19 + (l + 1) * (8 * hiMul) + s / 2 ^ (l + 1) * (64 * hiMul))) 0 0 =
      eOfNat idx + eOfNat (2 ^ 32 * c) +
        eOfNat (2 ^ 35 * ((l + 1) + 8 * (s / 2 ^ (l + 1)) + 2 ^ 21 * 19)) := by
    rw [e1, e2]
    have : eOfNat (2 ^ 35 * s) + eOfNat (2 ^ 35 * s) = 0 := e_add_self _
    linear_combination this
  have e : eOfNat idx + eOfNat (2 ^ 32 * c) +
      eOfNat (2 ^ 35 * ((l + 1) + 8 * (s / 2 ^ (l + 1)) + 2 ^ 21 * 19)) =
      eOfNat (idx + 2 ^ 32 * (c + 8 * (l + 1) + 64 * (s / 2 ^ (l + 1))) + 2 ^ 56 * (19 + 32 * 0)) := by
    rw [eOfNat_add_high (x := idx) (k := 32) (by omega),
      eOfNat_add_high (x := idx + 2 ^ 32 * c) (k := 35) (by omega)]
    exact congrArg eOfNat (by ring)
  rw [e3, e]
  exact sAdr_bytes (by omega) (by omega) (by omega) (by omega)

theorem encAdr_bytes {idx : Nat} (hidx : idx < 2 ^ 26) :
    cellBytes (eOfNat idx + word (tw 4) 0 0) = Sphincs.fieldBytes (Sphincs.tweakFields 4 0 0 idx) := by
  have e : eOfNat idx + word (tw 4) 0 0 = eOfNat (idx + 2 ^ 32 * 0 + 2 ^ 56 * (4 + 32 * 0)) := by
    rw [word_shift (k := 56) (y := 4) (by simp [tw]),
      eOfNat_add_high (x := idx) (k := 56) (by omega)]
    congr 1
  rw [e]
  exact sAdr_bytes (by omega) (by omega) (by omega) (by omega)

theorem chainAdr_bytes {idx i st : Nat} (hidx : idx < 2 ^ 26) (hi : i < 64) (hst : st < 3) :
    cellBytes (eOfNat idx + word (tw 1 + i * hiMul + st * stepMul) 0 0) =
      Sphincs.fieldBytes (Sphincs.tweakFields 1 st i idx) := by
  have e : eOfNat idx + word (tw 1 + i * hiMul + st * stepMul) 0 0 =
      eOfNat (idx + 2 ^ 32 * i + 2 ^ 56 * (1 + 32 * st)) := by
    rw [word_shift (k := 32) (y := i + 2 ^ 24 * (1 + 32 * st)) (by simp [tw, hiMul, stepMul]; ring),
      eOfNat_add_high (x := idx) (k := 32) (by omega)]
    exact congrArg eOfNat (by ring)
  rw [e]
  exact sAdr_bytes (by omega) (by omega) (by omega) (by omega)

theorem leafAdr_bytes {idx : Nat} (hidx : idx < 2 ^ 26) :
    cellBytes (eOfNat idx + word (tw 2) 0 0) = Sphincs.fieldBytes (Sphincs.tweakFields 2 0 0 idx) := by
  have e : eOfNat idx + word (tw 2) 0 0 = eOfNat (idx + 2 ^ 32 * 0 + 2 ^ 56 * (2 + 32 * 0)) := by
    rw [word_shift (k := 56) (y := 2) (by simp [tw]),
      eOfNat_add_high (x := idx) (k := 56) (by omega)]
    congr 1
  rw [e]
  exact sAdr_bytes (by omega) (by omega) (by omega) (by omega)

theorem msgAdr_bytes : cellBytes (word (tw 12) 0 0) = Sphincs.fieldBytes (Sphincs.tweakFields 12 0 0 0) := by
  have e : word (tw 12) 0 0 = eOfNat (0 + 2 ^ 32 * 0 + 2 ^ 56 * (12 + 32 * 0)) := by
    rw [word_eq_eOfNat]
    rfl
  rw [e]
  exact sAdr_bytes (by omega) (by omega) (by omega) (by omega)

theorem nodeAdr_bytes {idx l : Nat} (hidx : idx < 2 ^ 26) (hl : l < 26) :
    cellBytes (word (tw 3 + (l + 1) * hiMul) 0 0 +
        (if l + 1 = 26 then 0 else eOfNat (idx >>> (l + 1)))) =
      Sphincs.fieldBytes (Sphincs.tweakFields 3 0 (l + 1) (idx / 2 ^ (l + 1))) := by
  have hq : idx >>> (l + 1) < 2 ^ 26 := lt_of_le_of_lt (Nat.shiftRight_le _ _) hidx
  have hw : word (tw 3 + (l + 1) * hiMul) 0 0 = eOfNat (2 ^ 32 * ((l + 1) + 2 ^ 24 * 3)) :=
    word_shift (by simp [tw, hiMul]; ring)
  rw [hw, ← Nat.shiftRight_eq_div_pow]
  have e : eOfNat (2 ^ 32 * ((l + 1) + 2 ^ 24 * 3)) +
      (if l + 1 = 26 then 0 else eOfNat (idx >>> (l + 1))) =
      eOfNat (idx >>> (l + 1) + 2 ^ 32 * (l + 1) + 2 ^ 56 * (3 + 32 * 0)) := by
    split
    · rename_i h26
      have h0 : idx >>> (l + 1) = 0 := by
        rw [h26, Nat.shiftRight_eq_div_pow]; exact Nat.div_eq_of_lt hidx
      rw [h0, add_zero]
      exact congrArg eOfNat (by ring)
    · rw [add_comm, eOfNat_add_high (x := idx >>> (l + 1)) (k := 32) (by omega)]
      exact congrArg eOfNat (by ring)
  rw [e]
  exact sAdr_bytes (by omega) (by omega) (by omega) (by omega)

end
end LeanVM.Guest.B1.Sig
