/-
  LeanVM.Guest.B1.Sig.SphincsFields

  The fields of `verify_sig_lean_sphincs`'s digest (`lean_ethereum.py:3860-3874`, `sp_shifts`,
  `sp_place`, at leanVM `1a379148`): from the bits of an integer `D`, each field's value and right
  shifts, and the 64-bit lanes the fields are placed into.
-/

module

public import LeanVM.Guest.B1.Sig.SphincsKec

/-!
# The digest's fields

The digest's bits are hinted at `sBit i` (`n(51 + i)`); `BitsAt σ D` says they are the bits of `D`.
The fields are the hypertree's three (heights `8, 8, 10`) and the 24 FORS trees' (`10` bits), field
`f` from bit `sFieldOff f`, its value `fieldNat D f`.

* `sShifts_vals`: `sp_shifts` gives `σ (sVal i)`, the value of `i`'s field shifted right by
  `i - off`;
* `LaneAt`, `laneNat`, `sPlace_sound`, `sPlaces_sound`: `sp_place` places each field into the lane
  being rebuilt, a completed lane `j` holding the word of `D`'s bits `64 j ..< 64 j + 64`;
* `sPl_lanes`, `sIdx_val`, `sPl_last`: the four lanes, the index `idx` (the low `26` bits) and the
  lane after the last field (bits `256 ..< 266`).
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier (eOfNat)

@[expose] public section

variable {rd : Reader} {σ : Val}

/-! ## Fields -/

/-- The value of field `f` of the integer `D`. -/
def fieldNat (D f : Nat) : Nat := D / 2 ^ sFieldOff f % 2 ^ sFieldLen f

/-- **The digest's bits are those of `D`**: `sBit i` holds bit `i`, for the `266` bits the fields
read. -/
def BitsAt (σ : Val) (D : Nat) : Prop := ∀ i < 266, σ (sBit i) = if D.testBit i then 1 else 0

theorem field_facts {f : Nat} (hf : f < 27) :
    1 ≤ sFieldLen f ∧ sFieldLen f ≤ 10 ∧ sFieldOff (f + 1) = sFieldOff f + sFieldLen f ∧
      sFieldOff f + sFieldLen f ≤ 266 := by
  interval_cases f <;> simp [sFieldLen, sFieldOff]

theorem sFieldOf_spec {i : Nat} (hi : i < 266) :
    sFieldOf i < 27 ∧ sFieldOff (sFieldOf i) ≤ i ∧ i < sFieldOff (sFieldOf i) + sFieldLen (sFieldOf i) := by
  simp only [sFieldOf]
  split_ifs <;> simp [sFieldOff, sFieldLen] <;> (try split_ifs) <;> omega

theorem sFieldOf_of {f i : Nat} (hf : f < 27) (h1 : sFieldOff f ≤ i) (h2 : i < sFieldOff f + sFieldLen f) :
    sFieldOf i = f := by
  have := field_facts hf
  simp only [sFieldOf]
  interval_cases f <;> simp [sFieldOff, sFieldLen] at h1 h2 ⊢ <;> split_ifs <;> omega

theorem testBit_fieldNat (D f j : Nat) (hj : j < sFieldLen f) :
    (fieldNat D f).testBit j = D.testBit (sFieldOff f + j) := by
  rw [fieldNat, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  simp [hj, Nat.add_comm]

theorem fieldNat_lt (D f : Nat) : fieldNat D f < 2 ^ sFieldLen f := Nat.mod_lt _ (by positivity)

theorem one_ne_zero_E : (1 : E) ≠ 0 := one_ne_zero

theorem bitsOf_field {D f : Nat} (hf : f < 27) (hb : BitsAt σ D) :
    bitsOf σ (51 + sFieldOff f) (sFieldLen f) = fieldNat D f := by
  obtain ⟨-, h10, -, h266⟩ := field_facts hf
  rw [bitsOf, ← bitsVal_testBit (fieldNat_lt D f)]
  refine bitsVal_congr fun j hj => ?_
  rw [testBit_fieldNat D f j hj]
  have := hb (sFieldOff f + j) (by omega)
  rw [show sBit (sFieldOff f + j) = .n (51 + sFieldOff f + j) by simp [sBit]; omega] at this
  rw [this]
  split <;> simp_all

theorem isBit_of_bitsAt {D : Nat} (hb : BitsAt σ D) {i : Nat} (hi : i < 266) : IsBit (σ (sBit i)) := by
  rw [hb i hi]
  split <;> simp [IsBit]

/-- **`sp_shifts`**: `sVal i` holds the value of `i`'s field shifted right by `i - off`. -/
theorem sShifts_vals {D : Nat} (hb : BitsAt σ D) (h : AtomsHold rd σ sShifts) :
    ∀ i < 266, σ (sVal i) = eOfNat (fieldNat D (sFieldOf i) >>> (i - sFieldOff (sFieldOf i))) := by
  intro i hi
  obtain ⟨hf, h1, h2⟩ := sFieldOf_spec hi
  set f := sFieldOf i with hfdef
  obtain ⟨hl1, hl10, -, h266⟩ := field_facts hf
  have hsub : ∀ x ∈ shifts (51 + sFieldOff f) (sFieldLen f) (sFieldBase f), x ∈ sShifts := by
    intro x hx
    simp only [sShifts, List.mem_flatMap, List.mem_range]
    exact ⟨f, hf, hx⟩
  have hs := shifts_sound (σ := σ) (bitBase := 51 + sFieldOff f) (n := sFieldLen f)
    (outBase := sFieldBase f) (by omega) (by omega) (fun j hj => by
      have := isBit_of_bitsAt hb (i := sFieldOff f + j) (by omega)
      rwa [show sBit (sFieldOff f + j) = .n (51 + sFieldOff f + j) by simp [sBit]; omega] at this)
    (h.sub hsub) (sFieldOff f + sFieldLen f - 1 - i) (by omega)
  rw [bitsOf_field hf hb] at hs
  rw [show sVal i = .n (sFieldBase f + 3 * (sFieldOff f + sFieldLen f - 1 - i)) by
    simp only [sVal, ← hfdef], hs]
  congr 2
  omega

/-! ## Lanes -/

/-- Lane `j` of `D`: its bits `64 j ..< 64 j + 64`. -/
def laneNat (D j : Nat) : Nat := D / 2 ^ (64 * j) % 2 ^ 64

/-- **The lane being rebuilt before bit `o`**: unless `o` starts a lane, it holds the word of `D`'s
bits from the lane's start to `o`. -/
def LaneAt (σ : Val) (D o : Nat) (lane : V) : Prop :=
  o % 64 ≠ 0 → σ lane = eOfNat (D / 2 ^ (64 * (o / 64)) % 2 ^ (o % 64))

theorem mod_split (X r n : Nat) : X % 2 ^ (r + n) = 2 ^ r * (X / 2 ^ r % 2 ^ n) + X % 2 ^ r := by
  rw [← two_pow_mul_xor (Nat.mod_lt _ (by positivity))]
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [Nat.testBit_xor, Nat.testBit_mod_two_pow, Nat.testBit_two_pow_mul,
    Nat.testBit_div_two_pow]
  by_cases hj : j < r
  · simp [hj, show j < r + n by omega, show ¬ r ≤ j by omega]
  · simp only [hj, decide_false, Bool.false_and, Bool.xor_false, show r ≤ j by omega, decide_true,
      Bool.true_and]
    rw [show j - r + r = j by omega]
    by_cases hj2 : j < r + n
    · simp [hj2, show j - r < n by omega]
    · simp [hj2, show ¬ j - r < n by omega]

theorem field_div {D o n k : Nat} (hk : k ≤ n) :
    D / 2 ^ o % 2 ^ n / 2 ^ k = D / 2 ^ (o + k) % 2 ^ (n - k) := by
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [Nat.testBit_div_two_pow, Nat.testBit_mod_two_pow]
  rw [show j + (o + k) = j + k + o by omega]
  by_cases hj : j < n - k
  · simp [hj, show j + k < n by omega]
  · simp [hj, show ¬ j + k < n by omega]

theorem field_mod {D o n k : Nat} (hk : k ≤ n) : D / 2 ^ o % 2 ^ n % 2 ^ k = D / 2 ^ o % 2 ^ k :=
  Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hk)

theorem two_pow_mul_lt {r v k : Nat} (hv : v < 2 ^ k) (h : r + k ≤ 64) : 2 ^ r * v < 2 ^ 64 := by
  calc 2 ^ r * v < 2 ^ r * 2 ^ k := Nat.mul_lt_mul_of_pos_left hv (by positivity)
    _ = 2 ^ (r + k) := (pow_add _ _ _).symm
    _ ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) h

theorem word_pow_eq (k : Nat) : word (2 ^ k) 0 0 = eOfNat (2 ^ k) := word_eq_eOfNat _

/-- The values of the fields, as `sShifts_vals` gives them. -/
def ValsAt (σ : Val) (D : Nat) : Prop :=
  ∀ i < 266, σ (sVal i) = eOfNat (fieldNat D (sFieldOf i) >>> (i - sFieldOff (sFieldOf i)))

theorem valsAt_field {D f : Nat} (hv : ValsAt σ D) (hf : f < 27) {k : Nat} (hk : k < sFieldLen f) :
    σ (sVal (sFieldOff f + k)) = eOfNat (fieldNat D f >>> k) := by
  obtain ⟨-, -, -, h266⟩ := field_facts hf
  rw [hv _ (by omega), sFieldOf_of hf (by omega) (by omega)]
  congr 2
  omega

theorem sPlace_eq1 {lane : V} {off n b : Nat} (h1 : (off + n - 1) / 64 = off / 64) (h2 : off % 64 = 0)
    (h3 : (off + n) % 64 ≠ 0) : sPlace lane off n b = ([], b, sVal off, none) := by
  simp [sPlace, h1, h2, h3]

theorem sPlace_eq2 {lane : V} {off n b : Nat} (h1 : (off + n - 1) / 64 = off / 64) (h2 : off % 64 ≠ 0)
    (h3 : (off + n) % 64 ≠ 0) : sPlace lane off n b = ([cst b (word (2 ^ (off % 64)) 0 0),
      mulS (.n (b + 1)) (sVal off) (.n b), addS (.n (b + 2)) lane (.n (b + 1))], b + 3, .n (b + 2), none) := by
  simp [sPlace, h1, h2, h3]

theorem sPlace_eq3 {lane : V} {off n b : Nat} (h1 : (off + n - 1) / 64 = off / 64) (h2 : off % 64 ≠ 0)
    (h3 : (off + n) % 64 = 0) : sPlace lane off n b = ([cst b (word (2 ^ (off % 64)) 0 0),
      mulS (.n (b + 1)) (sVal off) (.n b), addS (.n (b + 2)) lane (.n (b + 1)), copyS (.n (b + 3)) (.n (b + 2))],
      b + 4, .n (b + 2), some (off / 64, .n (b + 3))) := by
  simp [sPlace, h1, h2, h3]

theorem sPlace_eq4 {lane : V} {off n b : Nat} (h1 : (off + n - 1) / 64 ≠ off / 64) :
    sPlace lane off n b = ([cst b (word (2 ^ (64 - off % 64)) 0 0),
      mulS (.n (b + 1)) (sVal (off + (64 - off % 64))) (.n b),
      addS (.n (b + 2)) (sVal off) (.n (b + 1)), cst (b + 3) (word (2 ^ (off % 64)) 0 0),
      mulS (.n (b + 4)) (.n (b + 2)) (.n (b + 3)), addS (.n (b + 5)) lane (.n (b + 4))],
      b + 6, sVal (off + (64 - off % 64)), some (off / 64, .n (b + 5))) := by
  simp [sPlace, h1]

/-- **`sp_place` of field `f`**: from the lane rebuilt so far, the lane after the field and the
lane it completes, if any. -/
theorem sPlace_sound {D f : Nat} (hf : f < 27) (hv : ValsAt σ D) {lane : V} {b : Nat}
    (hl : LaneAt σ D (sFieldOff f) lane)
    (h : AtomsHold rd σ (sPlace lane (sFieldOff f) (sFieldLen f) b).1) :
    LaneAt σ D (sFieldOff f + sFieldLen f) (sPlace lane (sFieldOff f) (sFieldLen f) b).2.2.1 ∧
      ∀ p ∈ (sPlace lane (sFieldOff f) (sFieldLen f) b).2.2.2.toList, σ p.2 = eOfNat (laneNat D p.1) := by
  obtain ⟨hl1, hl10, -, h266⟩ := field_facts hf
  have hvk : ∀ k < sFieldLen f, σ (sVal (sFieldOff f + k)) = eOfNat (fieldNat D f >>> k) :=
    fun k hk => valsAt_field hv hf hk
  have hFl := fieldNat_lt D f
  have hFo : fieldNat D f = D / 2 ^ sFieldOff f % 2 ^ sFieldLen f := rfl
  generalize fieldNat D f = F at hvk hFl hFo
  generalize sFieldOff f = o at hl h hvk hFo h266 ⊢
  generalize sFieldLen f = n at hl1 hl10 h hvk hFl hFo h266 ⊢
  have hv0 : σ (sVal o) = eOfNat F := by simpa using hvk 0 (by omega)
  obtain ⟨q, r, hr64, hor⟩ : ∃ q r, r < 64 ∧ o = 64 * q + r :=
    ⟨o / 64, o % 64, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod o 64).symm⟩
  have hq : o / 64 = q := by omega
  have hr : o % 64 = r := by omega
  set X := D / 2 ^ (64 * q) with hX
  have hFX : F = X / 2 ^ r % 2 ^ n := by rw [hFo, hX, Nat.div_div_eq_div_mul, ← pow_add, hor]
  have sub3 : ∀ {b' : Nat} {x : Stmt}, ∀ y ∈ [cst b' (word (2 ^ (o % 64)) 0 0), mulS (.n (b' + 1)) (sVal o) (.n b'),
      addS (.n (b' + 2)) lane (.n (b' + 1))], y ∈ [cst b' (word (2 ^ (o % 64)) 0 0),
      mulS (.n (b' + 1)) (sVal o) (.n b'), addS (.n (b' + 2)) lane (.n (b' + 1)), x] := by
    intro b' x y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy ⊢
    rcases hy with h | h | h <;> simp [h]
  by_cases h1 : (o + n - 1) / 64 = o / 64
  · have hrn : r + n ≤ 64 := by omega
    by_cases h2 : o % 64 = 0
    · have h3 : (o + n) % 64 ≠ 0 := by omega
      rw [sPlace_eq1 h1 h2 h3]
      refine ⟨fun _ => ?_, fun p hp => by simp at hp⟩
      show σ (sVal o) = _
      have hr0 : r = 0 := by omega
      rw [hv0, hFX, hr0, show (o + n) / 64 = q by omega, show (o + n) % 64 = n by omega]
      simp [hX]
    · have hlane : σ lane = eOfNat (X % 2 ^ r) := by rw [hl h2, hq, hr]
      have key : ∀ {b' : Nat}, AtomsHold rd σ [cst b' (word (2 ^ (o % 64)) 0 0),
          mulS (.n (b' + 1)) (sVal o) (.n b'), addS (.n (b' + 2)) lane (.n (b' + 1))] →
          σ (.n (b' + 2)) = eOfNat (X % 2 ^ (r + n)) := by
        intro b' hh
        have c := hh.atom (a := .const (.n b') (word (2 ^ (o % 64)) 0 0)) (by simp [cst])
        have m := hh.atom (a := .mul (.n (b' + 1)) (sVal o) (.n b')) (by simp [mulS])
        have a := hh.atom (a := .add (.n (b' + 2)) lane (.n (b' + 1))) (by simp [addS])
        simp only [Atom.Holds] at c m a
        rw [a, m, c, hv0, hlane, hr, word_pow_eq, mul_comm (eOfNat F),
          eOfNat_two_pow_mul (two_pow_mul_lt hFl hrn), add_comm,
          eOfNat_add_of_lt (Nat.mod_lt _ (by positivity)), mod_split X r n, hFX]
      by_cases h3 : (o + n) % 64 = 0
      · rw [sPlace_eq3 h1 h2 h3] at h ⊢
        refine ⟨fun h' => absurd h3 h', ?_⟩
        intro p hp
        simp only [Option.toList_some, List.mem_singleton] at hp
        subst hp
        have cp := h.atom (a := .copy (.n (b + 3)) (.n (b + 2))) (by simp [copyS])
        simp only [Atom.Holds] at cp
        show σ (.n (b + 3)) = _
        rw [cp, key (h.sub sub3), show r + n = 64 by omega, laneNat, hq]
      · rw [sPlace_eq2 h1 h2 h3] at h ⊢
        refine ⟨fun _ => ?_, fun p hp => by simp at hp⟩
        show σ (.n (b + 2)) = _
        rw [key h, show (o + n) / 64 = q by omega, show (o + n) % 64 = r + n by omega]
  · have hrn : 64 < r + n := by omega
    have hr0 : o % 64 ≠ 0 := by omega
    have hlane : σ lane = eOfNat (X % 2 ^ r) := by rw [hl hr0, hq, hr]
    rw [sPlace_eq4 h1] at h ⊢
    rw [hr] at h ⊢
    have hkn : 64 - r < n := by omega
    have hvk' : σ (sVal (o + (64 - r))) = eOfNat (F >>> (64 - r)) := hvk _ hkn
    generalize hk : 64 - r = k at h hkn hvk' ⊢
    have c0 : σ (.n b) = word (2 ^ k) 0 0 := h.atom (a := .const (.n b) (word (2 ^ k) 0 0)) (by simp [cst])
    have m1 : σ (.n (b + 1)) = σ (sVal (o + k)) * σ (.n b) :=
      h.atom (a := .mul (.n (b + 1)) (sVal (o + k)) (.n b)) (by simp [mulS])
    have a2 : σ (.n (b + 2)) = σ (sVal o) + σ (.n (b + 1)) :=
      h.atom (a := .add (.n (b + 2)) (sVal o) (.n (b + 1))) (by simp [addS])
    have c3 : σ (.n (b + 3)) = word (2 ^ r) 0 0 :=
      h.atom (a := .const (.n (b + 3)) (word (2 ^ r) 0 0)) (by simp [cst])
    have m4 : σ (.n (b + 4)) = σ (.n (b + 2)) * σ (.n (b + 3)) :=
      h.atom (a := .mul (.n (b + 4)) (.n (b + 2)) (.n (b + 3))) (by simp [mulS])
    have a5 : σ (.n (b + 5)) = σ lane + σ (.n (b + 4)) :=
      h.atom (a := .add (.n (b + 5)) lane (.n (b + 4))) (by simp [addS])
    have hFk : F >>> k < 2 ^ (n - k) := by
      rw [Nat.shiftRight_eq_div_pow, hFo, field_div hkn.le]; exact Nat.mod_lt _ (by positivity)
    have e1 : σ (.n (b + 1)) = eOfNat (2 ^ k * (F >>> k)) := by
      rw [m1, c0, hvk', word_pow_eq, mul_comm (eOfNat (F >>> k)),
        eOfNat_two_pow_mul (two_pow_mul_lt hFk (by omega))]
    have hsplitF : F = 2 ^ k * (F >>> k) + F % 2 ^ k := by
      rw [Nat.shiftRight_eq_div_pow]; exact (Nat.div_add_mod F (2 ^ k)).symm
    have hFmk : F % 2 ^ k < 2 ^ k := Nat.mod_lt _ (by positivity)
    have hFs : eOfNat F = eOfNat (2 ^ k * (F >>> k)) + eOfNat (F % 2 ^ k) := by
      rw [eOfNat_add_of_lt hFmk, ← hsplitF]
    have e2 : σ (.n (b + 2)) = eOfNat (F % 2 ^ k) := by
      rw [a2, hv0, e1, hFs, add_comm (eOfNat (2 ^ k * (F >>> k))), add_assoc, e_add_self, add_zero]
    have e4 : σ (.n (b + 4)) = eOfNat (2 ^ r * (F % 2 ^ k)) := by
      rw [m4, e2, c3, word_pow_eq, mul_comm (eOfNat (F % 2 ^ k)),
        eOfNat_two_pow_mul (two_pow_mul_lt hFmk (by omega))]
    refine ⟨fun _ => ?_, ?_⟩
    · show σ (sVal (o + k)) = _
      rw [hvk', Nat.shiftRight_eq_div_pow, hFo, field_div hkn.le]
      congr 2
      · congr 2; omega
      · congr 1; omega
    · intro p hp
      simp only [Option.toList_some, List.mem_singleton] at hp
      subst hp
      show σ (.n (b + 5)) = _
      rw [a5, e4, hlane, add_comm, eOfNat_add_of_lt (Nat.mod_lt _ (by positivity)), laneNat, hq,
        ← hX, show (64 : Nat) = r + k by omega, mod_split X r k, hFX,
        Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hkn.le)]

theorem sPlaces_succ (m f : Nat) (lane : V) (b : Nat) :
    sPlaces (m + 1) f lane b =
      ((sPlace lane (sFieldOff f) (sFieldLen f) b).1 ++
          (sPlaces m (f + 1) (sPlace lane (sFieldOff f) (sFieldLen f) b).2.2.1
            (sPlace lane (sFieldOff f) (sFieldLen f) b).2.1).1,
        (sPlaces m (f + 1) (sPlace lane (sFieldOff f) (sFieldLen f) b).2.2.1
          (sPlace lane (sFieldOff f) (sFieldLen f) b).2.1).2.1,
        (sPlaces m (f + 1) (sPlace lane (sFieldOff f) (sFieldLen f) b).2.2.1
          (sPlace lane (sFieldOff f) (sFieldLen f) b).2.1).2.2.1,
        (sPlace lane (sFieldOff f) (sFieldLen f) b).2.2.2.toList ++
          (sPlaces m (f + 1) (sPlace lane (sFieldOff f) (sFieldLen f) b).2.2.1
            (sPlace lane (sFieldOff f) (sFieldLen f) b).2.1).2.2.2) := rfl

/-- **`sp_place` of fields `f ..< f + m`**: every lane completed holds its bits, and the lane after
is rebuilt to the next field's offset. -/
theorem sPlaces_sound {D : Nat} (hv : ValsAt σ D) :
    ∀ (m f : Nat) (lane : V) (b : Nat), f + m ≤ 27 → LaneAt σ D (sFieldOff f) lane →
      AtomsHold rd σ (sPlaces m f lane b).1 →
      LaneAt σ D (sFieldOff (f + m)) (sPlaces m f lane b).2.2.1 ∧
        ∀ p ∈ (sPlaces m f lane b).2.2.2, σ p.2 = eOfNat (laneNat D p.1)
  | 0, f, lane, b, _, hl, _ => ⟨by simpa [sPlaces] using hl, fun p hp => by simp [sPlaces] at hp⟩
  | m + 1, f, lane, b, hfm, hl, h => by
      rw [sPlaces_succ] at h ⊢
      obtain ⟨-, -, hoff, -⟩ := field_facts (f := f) (by omega)
      obtain ⟨l1, p1⟩ := sPlace_sound (rd := rd) (f := f) (by omega) hv hl h.left
      rw [← hoff] at l1
      obtain ⟨l2, p2⟩ := sPlaces_sound hv m (f + 1) _ _ (by omega) l1 h.right
      refine ⟨by rw [show f + (m + 1) = f + 1 + m by omega]; exact l2, fun p hp => ?_⟩
      rcases List.mem_append.mp hp with hp | hp
      · exact p1 p hp
      · exact p2 p hp

theorem sPlaces_add (m k f : Nat) (lane : V) (b : Nat) :
    (sPlaces (m + k) f lane b).1 = (sPlaces m f lane b).1 ++
      (sPlaces k (f + m) (sPlaces m f lane b).2.2.1 (sPlaces m f lane b).2.1).1 := by
  induction m generalizing f lane b with
  | zero => simp [sPlaces]
  | succ m ih =>
      rw [show m + 1 + k = (m + k) + 1 by omega, sPlaces_succ, sPlaces_succ, ih]
      simp [show f + 1 + m = f + (m + 1) by omega]

theorem sPl_pairs : sPl.2.2.2 = [(0, .n 1082), (1, .n 1106), (2, .n 1127), (3, .n 1146)] := by
  decide +kernel

theorem sPl_lane : sPl.2.2.1 = .n 1060 := by decide +kernel

theorem sIdx_eq : sIdx = .n 1067 := by decide +kernel

theorem sLane_eq : sLane 0 = .n 1082 ∧ sLane 1 = .n 1106 ∧ sLane 2 = .n 1127 ∧ sLane 3 = .n 1146 := by
  decide +kernel

/-- **The fields placed**: the four lanes hold `D`'s 64-bit lanes, the index its low `26` bits and
the lane after the last field its bits `256 ..< 266`. -/
theorem sPl_sound {D : Nat} (hv : ValsAt σ D) (h : AtomsHold rd σ sPl.1) :
    (∀ j < 4, σ (sLane j) = eOfNat (laneNat D j)) ∧ σ sIdx = eOfNat (D % 2 ^ 26) ∧
      σ sPl.2.2.1 = eOfNat (D / 2 ^ 256 % 2 ^ 10) := by
  have hl0 : LaneAt σ D (sFieldOff 0) (.n 1061) := fun h' => absurd rfl h'
  obtain ⟨l27, hp⟩ := sPlaces_sound (rd := rd) hv 27 0 (.n 1061) 1062 le_rfl hl0 h
  have h3 : AtomsHold rd σ (sPlaces 3 0 (.n 1061) 1062).1 := by
    have := h
    rw [show sPl.1 = (sPlaces (3 + 24) 0 (.n 1061) 1062).1 from rfl, sPlaces_add] at this
    exact this.left
  obtain ⟨l3, -⟩ := sPlaces_sound (rd := rd) hv 3 0 (.n 1061) 1062 (by norm_num) hl0 h3
  refine ⟨fun j hj => ?_, ?_, ?_⟩
  · obtain ⟨e0, e1, e2, e3⟩ := sLane_eq
    have hm : ∀ p ∈ sPl.2.2.2, σ p.2 = eOfNat (laneNat D p.1) := hp
    rw [sPl_pairs] at hm
    interval_cases j
    · rw [e0]; exact hm (0, .n 1082) (by simp)
    · rw [e1]; exact hm (1, .n 1106) (by simp)
    · rw [e2]; exact hm (2, .n 1127) (by simp)
    · rw [e3]; exact hm (3, .n 1146) (by simp)
  · have := l3 (by decide)
    rw [show sIdx = (sPlaces 3 0 (.n 1061) 1062).2.2.1 from rfl, this]
    norm_num [sFieldOff]
  · have := l27 (by decide)
    rw [show sPl.2.2.1 = (sPlaces 27 0 (.n 1061) 1062).2.2.1 from rfl, this]
    norm_num [sFieldOff]

end
end LeanVM.Guest.B1.Sig
