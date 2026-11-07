/-
  LeanVM.Guest.B1.Sig.SphincsSoundDigest

  The message digest of `verify_sig_lean_sphincs` (`lean_ethereum.py:3972-4065` at leanVM 834e6614)
  is sound: the message hinted is the claim's, `H_msg`'s two calls hash `R | PK.seed | PK.root | M'
  | BE_32(i)`, and whatever bits are hinted, they are the digest's, each field's values theirs.
-/

module

public import LeanVM.Guest.B1.Sig.SphincsFields
public import LeanVM.Guest.B1.Sig.SphincsBytes
public import LeanVM.Guest.WithHashBridge

/-!
# The message digest, sound

* `kec97_sound`: a one-block `KECCAK` of six cells and a counter byte, 97 bytes, writes the digest
  halves of their hash (`hcellLen`);
* `sMsg_sound`: the claim's keys and message cells loaded, the cells `M'` puts the message in;
* `sDigests_sound`: the padding run, and `H_msg`'s two calls;
* `sCheck_sound`: the bits' number is the digest's: the first call's cells and the second call's low
  two bytes;
* `sDigestBlock_sound`: the whole block.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier (eOfNat kToNat)

@[expose] public section

variable {rd : Reader} {σ : Val}

/-! ## A 97-byte `keccak` -/

/-- The digest cells of the Keccak-256 hash of the first `len` bytes of cells. -/
def hcellLen (cs : List E) (len : Nat) : E × E := digestHalves (keccak256 ((cellsBytes cs).take len))

theorem padCells_seven (a b c d e f g : E) :
    padCells [a, b, c, d, e, f, g] 97 = [a, b, c, d, e, f, g + word 256 0 0, 0, word (2 ^ 63) 0 0] := by
  simp [padCells, xorByte, padRead, rate, byteCell]

theorem cellBytes_word_getD {i j : Nat} (hi : i < 256) (hj : 1 ≤ j) :
    (cellBytes (word i 0 0)).getD j 0 = 0 := by
  rw [cellBytes_eq_leBytes, word_eq_eOfNat, cellNat_eOfNat (by omega)]
  by_cases hj16 : j < 16
  · rw [List.getD_eq_getElem _ _ (by simp [leBytes]; omega), getElem_leBytes]
    rw [Nat.div_eq_of_lt (lt_of_lt_of_le hi (by
      calc (256 : Nat) = 256 ^ 1 := by norm_num
        _ ≤ 256 ^ j := Nat.pow_le_pow_right (by norm_num) hj))]
    rfl
  · rw [List.getD_eq_default _ _ (by simp [leBytes]; omega)]

/-- **A 97-byte `keccak`**: six cells and a counter byte `i`, one block from the zero state. -/
theorem kec97_sound {ins : List V} {o : Nat} {a b c d e f : E} {i : Nat} (hi : i < 256)
    (hK : AtomsHold rd σ [kecS ins (runV o 13) false false])
    (hrate : ∀ k < 9, σ (ins.getD k (.n 0)) =
      [a, b, c, d, e, f, word (i + 256) 0 0, 0, word (2 ^ 63) 0 0].getD k 0)
    (hcap : ∀ k, 9 ≤ k → k < 13 → σ (ins.getD k (.n 0)) = 0) :
    (σ (.n o), σ (.n (o + 1))) = hcellLen [a, b, c, d, e, f, word i 0 0] 97 := by
  have hk := hK.atom (List.mem_singleton_self _)
  obtain ⟨hl, -, hk⟩ := hk
  have hget : ∀ k : Fin 13, cells13 (ins.map σ) k = σ (ins.getD k.val (.n 0)) := fun k => by
    simp only [cells13, List.getD_eq_getElem?_getD, List.getElem?_map]
    rw [List.getElem?_eq_getElem (by omega)]
    rfl
  have hpad : padCells [a, b, c, d, e, f, word i 0 0] 97 =
      [a, b, c, d, e, f, word (i + 256) 0 0, 0, word (2 ^ 63) 0 0] := by
    rw [padCells_seven, word_eq_eOfNat, word_eq_eOfNat, word_eq_eOfNat, ← Value.eOfNat_xor,
      Nat.xor_comm, show (256 : Nat) = 2 ^ 8 * 1 by norm_num, two_pow_mul_xor (by omega), add_comm,
      word_eq_eOfNat]
  have := keccak_one (cells := [a, b, c, d, e, f, word i 0 0]) (len := 97) (by simp) (by simp [rate])
    (fun j hj => by
      simp only [cellsBytes, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rw [show cellBytes a ++ (cellBytes b ++ (cellBytes c ++ (cellBytes d ++ (cellBytes e ++
          (cellBytes f ++ cellBytes (word i 0 0)))))) = (cellBytes a ++ cellBytes b ++ cellBytes c ++
          cellBytes d ++ cellBytes e ++ cellBytes f) ++ cellBytes (word i 0 0) by simp,
        getD_append_right' (by simp [cellBytes_eq_leBytes, leBytes]; omega)]
      exact cellBytes_word_getD hi (by simp [cellBytes_eq_leBytes, leBytes]; omega))
    (fun k hk => by rw [hget, hpad]; exact hrate k hk)
    (fun k hk => by rw [hget]; exact hcap k hk k.isLt) hk
  rw [hcellLen, ← this.2]
  simp [cells13, runV]

/-! ## `H_msg` -/

/-- The cells `H_msg`'s call `i` hashes, 97 bytes of them: `R`, `PK.seed`, `PK.root`, `M'`'s three
cells and the counter's last byte. -/
def hmsgCells (σ : Val) (i : Nat) : List E :=
  [σ sRand, σ sPP, σ sRoot, σ sM0, σ sM1, σ sM2, word i 0 0]

theorem word_257 : word 1 0 0 + word 256 0 0 = word (1 + 256) 0 0 := by
  rw [word_eq_eOfNat, word_eq_eOfNat, word_eq_eOfNat, ← Value.eOfNat_xor]
  rfl

/-- **`H_msg`'s two calls, sound**: the padding run, and each call's outputs the digest halves of
its 97 bytes. -/
theorem sDigests_sound (h : AtomsHold rd σ sDigests) :
    PadOK σ sPad ∧ (σ sHm0, σ sHm0b) = hcellLen (hmsgCells σ 0) 97 ∧
      (σ sHm1, σ (.n 380)) = hcellLen (hmsgCells σ 1) 97 := by
  have c : ∀ (k : Nat) (w : E), Stmt.atom (.const (.n k) w) ∈ sDigests → σ (.n k) = w :=
    fun k w hm => h.atom hm
  have cp : ∀ (k : Nat) (v : V), Stmt.atom (.copy (.n k) v) ∈ sDigests → σ (.n k) = σ v :=
    fun k v hm => h.atom hm
  have p0 := c 353 (word 1 0 0) (by simp [sDigests, padRun, sPad, cst, List.range_succ])
  have p1 := c 354 (word 0 0 0) (by simp [sDigests, padRun, sPad, cst, List.range_succ])
  have p2 := c 355 (word 0 0 0) (by simp [sDigests, padRun, sPad, cst, List.range_succ])
  have p3 := c 356 (word 0 0 0) (by simp [sDigests, padRun, sPad, cst, List.range_succ])
  have p4 := c 357 (word 0 0 0) (by simp [sDigests, padRun, sPad, cst, List.range_succ])
  rw [word_zero] at p1 p2 p3 p4
  have hp : PadOK σ sPad := ⟨p0, p1, p2, p3, p4⟩
  have k0 := c 350 (word 256 0 0) (by simp [sDigests, cst])
  have k1 := c 351 (word 0 0 0) (by simp [sDigests, cst])
  have k2 := c 352 (word (2 ^ 63) 0 0) (by simp [sDigests, cst])
  have k3 := c 371 (word 1 0 0) (by simp [sDigests, cst])
  have k4 := c 372 (word 256 0 0) (by simp [sDigests, cst])
  have k5 := c 377 (word 0 0 0) (by simp [sDigests, cst])
  have k6 := c 378 (word (2 ^ 63) 0 0) (by simp [sDigests, cst])
  have a373 : σ (.n 373) = σ (.n 371) + σ (.n 372) := h.atom (a := .add (.n 373) _ _) (by simp [sDigests, addS])
  have c348 := cp 348 sM1 (by simp [sDigests, copyS])
  have c349 := cp 349 sM2 (by simp [sDigests, copyS])
  have c374 := cp 374 sM1 (by simp [sDigests, copyS])
  have c375 := cp 375 sM2 (by simp [sDigests, copyS])
  have c376 := cp 376 (.n 373) (by simp [sDigests, copyS])
  rw [word_zero] at k1 k5
  refine ⟨hp, ?_, ?_⟩
  · refine kec97_sound (ins := sHIns 348) (i := 0) (by norm_num) (h.sub fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx; simp [sDigests]) (fun k hk => ?_) (fun k h1 h2 => ?_)
    · interval_cases k <;> simp [sHIns, c348, c349, k0, k1, k2]
    · interval_cases k <;> simp [sHIns, sPad, p1, p2, p3, p4]
  · refine kec97_sound (ins := sHIns 374) (i := 1) (by norm_num) (h.sub fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx; simp [sDigests]) (fun k hk => ?_) (fun k h1 h2 => ?_)
    · interval_cases k <;> simp [sHIns, c374, c375, c376, a373, k3, k4, k5, k6, word_257]
    · interval_cases k <;> simp [sHIns, sPad, p1, p2, p3, p4]

/-! ## The message -/

/-- `M'`'s framing as a number: `0x00 | 11 | "leanSPHINCS"`, little endian. -/
def framingNat : Nat := 5788091310693681920 + 2 ^ 64 * 357611489608

theorem word_eq192 {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    word a b 0 = eOfNat192 (a + 2 ^ 64 * b) := by
  unfold word eOfNat192
  rw [← ofBits_mod (a + 2 ^ 64 * b), show (a + 2 ^ 64 * b) % 2 ^ 64 = a by omega,
    show (a + 2 ^ 64 * b) / 2 ^ 64 = b by omega, show (a + 2 ^ 64 * b) / 2 ^ 128 = 0 by omega]

theorem spFraming_eq : spFraming = eOfNat192 framingNat := word_eq192 (by norm_num) (by norm_num)

theorem pw_64 : word 0 1 0 = pw 64 := by simp [pw]

theorem mul_word_y {a : Nat} (ha : a < 2 ^ 64) : eOfNat a * word 0 1 0 = eOfNat192 (2 ^ 64 * a) := by
  rw [pw_64, pw_mul (by norm_num) (by simpa using ha)]

/-- **A lane's bytes, sound**: its three low bytes and its five high ones. -/
theorem sLaneBytes_sound {κ : Nat} (hκ : κ ≤ 32) {L : MemoryImage κ} (hbb : ByteBits L.read (σ (.n 1)))
    {j : Nat} (h : AtomsHold L.read σ (sLaneBytes j)) :
    ∃ lo hi, lo < 2 ^ 24 ∧ hi < 2 ^ 40 ∧ σ (sLo j) = eOfNat lo ∧ σ (sHi j) = eOfNat hi := by
  have h' : AtomsHold L.read σ (((sFromMarks (4 + 8 * j) 3 (sLaneBase j)).1 ++
      [copyS (sLo j) (sFromMarks (4 + 8 * j) 3 (sLaneBase j)).2.2]) ++
      ((sFromMarks (7 + 8 * j) 5 (sLaneBase j + 25)).1 ++
      [copyS (sHi j) (sFromMarks (7 + 8 * j) 5 (sLaneBase j + 25)).2.2])) := by
    simpa [sLaneBytes] using h
  obtain ⟨lo, h1, h2⟩ := sFromMarks_sound hκ hbb (by norm_num) (by norm_num) h'.left.left
  obtain ⟨hi, h3, h4⟩ := sFromMarks_sound hκ hbb (by norm_num) (by norm_num) h'.right.left
  have c1 : σ (sLo j) = σ (sFromMarks (4 + 8 * j) 3 (sLaneBase j)).2.2 :=
    h'.left.right.atom (a := .copy _ _) (by simp [copyS])
  have c2 : σ (sHi j) = σ (sFromMarks (7 + 8 * j) 5 (sLaneBase j + 25)).2.2 :=
    h'.right.right.atom (a := .copy _ _) (by simp [copyS])
  exact ⟨lo, hi, h2, h4, c1.trans h1, c2.trans h3⟩

/-- **A lane, sound**: `lo + hi · g^24`. -/
theorem sLane_sound {j lo hi : Nat} (hj : j < 4) (hlo : lo < 2 ^ 24) (h : AtomsHold rd σ sLanes)
    (h1 : σ (sLo j) = eOfNat lo) (h2 : σ (sHi j) = eOfNat hi) (hhi : hi < 2 ^ 40) :
    σ (sLane j) = eOfNat (lo + 2 ^ 24 * hi) := by
  have mem : ∀ x ∈ [cst (308 + 3 * j) (word (2 ^ 24) 0 0), mulS (.n (309 + 3 * j)) (sHi j) (.n (308 + 3 * j)),
      addS (sLane j) (sLo j) (.n (309 + 3 * j))], x ∈ sLanes := fun x hx =>
    List.mem_flatMap.mpr ⟨j, List.mem_range.mpr hj, hx⟩
  have k : σ (.n (308 + 3 * j)) = word (2 ^ 24) 0 0 := h.atom (a := .const _ _) (mem _ (by simp [cst]))
  have m : σ (.n (309 + 3 * j)) = σ (sHi j) * σ (.n (308 + 3 * j)) :=
    h.atom (a := .mul _ _ _) (mem _ (by simp [mulS]))
  have a : σ (sLane j) = σ (sLo j) + σ (.n (309 + 3 * j)) := h.atom (a := .add _ _ _) (mem _ (by simp [addS]))
  rw [a, m, k, h1, h2, word_eq_eOfNat, mul_comm, Value.eOfNat_two_pow_mul (by omega), add_comm,
    Value.eOfNat_add_of_lt hlo, add_comm]

/-- **A message cell's check, sound**: the claim's word at offset `2 + k` is its two lanes'. -/
theorem sMsgCheck_sound {k b : Nat} {l0 l1 : Nat} (hl1 : l1 < 2 ^ 64) (h : AtomsHold rd σ (sMsgCheck k b))
    (h0 : σ (sLane (2 * k)) = eOfNat l0) (h1 : σ (sLane (2 * k + 1)) = eOfNat l1) (hl0 : l0 < 2 ^ 64) :
    LoadHolds rd (σ (.n 0)) (2 + k) (σ (.n (b + 3))) ∧ σ (.n (b + 3)) = eOfNat192 (l0 + 2 ^ 64 * l1) := by
  have c : σ (.n b) = word 0 1 0 := h.atom (a := .const _ _) (by simp [sMsgCheck, cst])
  have m : σ (.n (b + 1)) = σ (sLane (2 * k + 1)) * σ (.n b) := h.atom (a := .mul _ _ _) (by simp [sMsgCheck, mulS])
  have a : σ (.n (b + 2)) = σ (sLane (2 * k)) + σ (.n (b + 1)) :=
    h.atom (a := .add _ _ _) (by simp [sMsgCheck, addS])
  have l : LoadHolds rd (σ (.n 0)) (2 + k) (σ (.n (b + 3))) := h.atom (a := .load _ _ _) (by simp [sMsgCheck, loadS])
  have e : σ (.n (b + 2)) = σ (.n (b + 3)) :=
    e_add_eq_zero_iff.mp (h.atom (a := .assertEq (.n (b + 2)) (.n (b + 3))) (by simp [sMsgCheck]))
  refine ⟨l, ?_⟩
  rw [← e, a, m, c, h0, h1, mul_word_y hl1, eOfNat_eq192 hl0, eOfNat192_add_shift hl0]

/-- `hi + lo · g^40` from `x`. -/
theorem loHi_sound {lo hi : V} {x a b : Nat} (ha : a < 2 ^ 24) (hb : b < 2 ^ 40)
    (h1 : σ lo = eOfNat a) (h2 : σ hi = eOfNat b)
    (h : AtomsHold rd σ [cst x (pw 40), mulS (.n (x + 1)) lo (.n x), addS (.n (x + 2)) hi (.n (x + 1))]) :
    σ (.n (x + 2)) = eOfNat (2 ^ 40 * a + b) := by
  have k : σ (.n x) = pw 40 := h.atom (a := .const _ _) (by simp [cst])
  have m : σ (.n (x + 1)) = σ lo * σ (.n x) := h.atom (a := .mul _ _ _) (by simp [mulS])
  have ad : σ (.n (x + 2)) = σ hi + σ (.n (x + 1)) := h.atom (a := .add _ _ _) (by simp [addS])
  rw [ad, m, k, h1, h2, pw_lo (by norm_num), word_eq_eOfNat, mul_comm (eOfNat a),
    Value.eOfNat_two_pow_mul (by omega), add_comm, Value.eOfNat_add_of_lt hb]

/-- **The message, sound**: the claim's keys and its message `M` (two cells) loaded, and the cells
`M'` puts it in after the framing: `M'`'s first 48 bytes are those of `framing + 2^104 M`. -/
theorem sMsg_sound {κ : Nat} (hκ : κ ≤ 32) {L : MemoryImage κ} (hbb : ByteBits L.read (σ (.n 1)))
    (h : AtomsHold L.read σ sMsg) :
    LoadHolds L.read (σ (.n 0)) 0 (σ sPP) ∧ LoadHolds L.read (σ (.n 0)) 1 (σ sRoot) ∧
      ∃ M < 2 ^ 256, LoadHolds L.read (σ (.n 0)) 2 (eOfNat192 (M % 2 ^ 128)) ∧
        LoadHolds L.read (σ (.n 0)) 3 (eOfNat192 (M / 2 ^ 128)) ∧
        σ sM0 = eOfNat192 ((framingNat + 2 ^ 104 * M) % 2 ^ 128) ∧
        σ sM1 = eOfNat192 ((framingNat + 2 ^ 104 * M) / 2 ^ 128 % 2 ^ 128) ∧
        σ sM2 = eOfNat192 ((framingNat + 2 ^ 104 * M) / 2 ^ 256) := by
  have hC : AtomsHold L.read σ sMCells := h.right
  have hc1 : AtomsHold L.read σ (sMsgCheck 1 324) := h.left.right
  have hc0 : AtomsHold L.read σ (sMsgCheck 0 320) := h.left.left.right
  have hl : AtomsHold L.read σ sLanes := h.left.left.left.right
  have hb : AtomsHold L.read σ ((List.range 4).flatMap sLaneBytes) := h.left.left.left.left.right
  have hpre := h.left.left.left.left.left
  have lP : LoadHolds L.read (σ (.n 0)) 0 (σ sPP) := hpre.atom (a := .load _ _ _) (by simp [loadS])
  have lR : LoadHolds L.read (σ (.n 0)) 1 (σ sRoot) := hpre.atom (a := .load _ _ _) (by simp [loadS])
  have hj : ∀ j < 4, AtomsHold L.read σ (sLaneBytes j) := fun j hj =>
    hb.sub fun x hx => List.mem_flatMap.mpr ⟨j, List.mem_range.mpr hj, hx⟩
  obtain ⟨lo0, hi0, a0, b0, e0, f0⟩ := sLaneBytes_sound hκ hbb (hj 0 (by norm_num))
  obtain ⟨lo1, hi1, a1, b1, e1, f1⟩ := sLaneBytes_sound hκ hbb (hj 1 (by norm_num))
  obtain ⟨lo2, hi2, a2, b2, e2, f2⟩ := sLaneBytes_sound hκ hbb (hj 2 (by norm_num))
  obtain ⟨lo3, hi3, a3, b3, e3, f3⟩ := sLaneBytes_sound hκ hbb (hj 3 (by norm_num))
  have L0 := sLane_sound (by norm_num) a0 hl e0 f0 b0
  have L1 := sLane_sound (by norm_num) a1 hl e1 f1 b1
  have L2 := sLane_sound (by norm_num) a2 hl e2 f2 b2
  have L3 := sLane_sound (by norm_num) a3 hl e3 f3 b3
  obtain ⟨ld2, v2⟩ := sMsgCheck_sound (k := 0) (by omega) hc0 L0 L1 (by omega)
  obtain ⟨ld3, v3⟩ := sMsgCheck_sound (k := 1) (by omega) hc1 L2 L3 (by omega)
  set M := (lo0 + 2 ^ 24 * hi0) + 2 ^ 64 * (lo1 + 2 ^ 24 * hi1) + 2 ^ 128 * (lo2 + 2 ^ 24 * hi2) +
    2 ^ 192 * (lo3 + 2 ^ 24 * hi3) with hM
  refine ⟨lP, lR, M, by omega, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show M % 2 ^ 128 = lo0 + 2 ^ 24 * hi0 + 2 ^ 64 * (lo1 + 2 ^ 24 * hi1) by omega, ← v2]; exact ld2
  · rw [show M / 2 ^ 128 = lo2 + 2 ^ 24 * hi2 + 2 ^ 64 * (lo3 + 2 ^ 24 * hi3) by omega, ← v3]; exact ld3
  · have k8 : σ (.n 328) = spFraming := hC.atom (a := .const _ _) (by simp [sMCells, cst])
    have k9 : σ (.n 329) = pw 104 := hC.atom (a := .const _ _) (by simp [sMCells, cst])
    have m : σ (.n 330) = σ (sLo 0) * σ (.n 329) := hC.atom (a := .mul _ _ _) (by simp [sMCells, mulS])
    have ad : σ sM0 = σ (.n 328) + σ (.n 330) := hC.atom (a := .add sM0 _ _) (by simp [sMCells, addS])
    rw [ad, m, k8, k9, e0, spFraming_eq, pw_mul (by norm_num) (by norm_num; omega),
      eOfNat192_add_shift (by norm_num [framingNat])]
    congr 1
    simp only [framingNat] at *
    omega
  · have hA1 := loHi_sound (x := 332) a1 b0 e1 f0 (hC.sub fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl | rfl <;> simp [sMCells])
    have hA2 := loHi_sound (x := 335) a2 b1 e2 f1 (hC.sub fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl | rfl <;> simp [sMCells])
    have k : σ (.n 338) = word 0 1 0 := hC.atom (a := .const _ _) (by simp [sMCells, cst])
    have m : σ (.n 339) = σ (.n 337) * σ (.n 338) := hC.atom (a := .mul _ _ _) (by simp [sMCells, mulS])
    have ad : σ sM1 = σ (.n 334) + σ (.n 339) := hC.atom (a := .add sM1 _ _) (by simp [sMCells, addS])
    rw [ad, m, k, hA2, hA1, mul_word_y (by omega), eOfNat_eq192 (by omega), eOfNat192_add_shift (by omega)]
    congr 1
    simp only [framingNat] at *
    omega
  · have hA3 := loHi_sound (x := 341) a3 b2 e3 f2 (hC.sub fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl | rfl <;> simp [sMCells])
    have k : σ (.n 344) = word 0 1 0 := hC.atom (a := .const _ _) (by simp [sMCells, cst])
    have m : σ (.n 345) = σ (sHi 3) * σ (.n 344) := hC.atom (a := .mul _ _ _) (by simp [sMCells, mulS])
    have ad : σ sM2 = σ (.n 343) + σ (.n 345) := hC.atom (a := .add sM2 _ _) (by simp [sMCells, addS])
    rw [ad, m, k, hA3, f3, mul_word_y (by omega), eOfNat_eq192 (by omega), eOfNat192_add_shift (by omega)]
    congr 1
    simp only [framingNat] at *
    omega

/-! ## The check -/

theorem bitE_testBit (T k : Nat) : bitE (T.testBit k) = eOfNat (T / 2 ^ k % 2) := by
  rw [bitE_eq, Nat.toNat_testBit]

/-- The top leaf's low byte is the digest's byte 31. -/
theorem layerLeaf2_low (T : Nat) : layerLeafN T 2 % 2 ^ 8 = byteN T 31 := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_mod_two_pow, testBit_layerLeafN, testBit_byteN]
  by_cases hj : j < 8
  · simp [hj, sLeafLen, sLeafOff, leafPos, show j < 10 by omega, show ¬ 16 + j < 8 by omega,
      show ¬ 16 + j < 16 by omega, show 16 + j < 24 by omega]
    congr 1; omega
  · simp [hj]

/-- The top leaf's two high bits are the digest's byte 30's low two. -/
theorem layerLeaf2_high (T : Nat) : layerLeafN T 2 >>> 8 = T / 2 ^ 240 % 2 ^ 2 := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_shiftRight, testBit_layerLeafN, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases hj : j < 2
  · simp [hj, sLeafLen, sLeafOff, leafPos, show 8 + j < 10 by omega, show ¬ 16 + (8 + j) < 8 by omega,
      show ¬ 16 + (8 + j) < 16 by omega, show ¬ 16 + (8 + j) < 24 by omega]
    congr 1; omega
  · simp [hj, sLeafLen, show ¬ 8 + j < 10 by omega]

/-- The middle and bottom leaves are the second call's two low bytes. -/
theorem layerLeaf01 (T : Nat) : 2 ^ 8 * layerLeafN T 0 + layerLeafN T 1 = T / 2 ^ 256 % 2 ^ 16 := by
  have h1 : layerLeafN T 1 < 2 ^ 8 := by simpa [sLeafLen] using layerLeafN_lt T 1
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_two_pow_mul_add _ h1, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases hj : j < 8
  · simp only [hj, ↓reduceIte, testBit_layerLeafN]
    simp [sLeafLen, sLeafOff, leafPos, hj, show j < 16 by omega, show ¬ 8 + j < 8 by omega,
      show 8 + j < 16 by omega]
    congr 1; omega
  · simp only [hj, ↓reduceIte, testBit_layerLeafN]
    by_cases hj16 : j < 16
    · simp [sLeafLen, sLeafOff, leafPos, hj16, show j - 8 < 8 by omega]
      congr 1; omega
    · simp [sLeafLen, hj16, show ¬ j - 8 < 8 by omega]

theorem word_y_inv' : word 1 0 1 = y⁻¹ := by rw [y_inv]; rfl

/-- **The second call's low bytes**: its cell, the bytes `l` and the unused bytes `N` times `g^16`
checked into `K` after `y⁻¹`. -/
theorem high_low_bytes {x : E} {l N : Nat} (hl : l < 2 ^ 16)
    (hK : IsInK ((x + eOfNat l + eOfNat (2 ^ 16 * N)) * word 1 0 1)) : cellNat x % 2 ^ 16 = l := by
  rw [word_y_inv', eq_ofLimbs x, eOfNat_eq_ofLimbs, eOfNat_eq_ofLimbs, ofLimbs_add, ofLimbs_add,
    ofLimbs_mul_y_inv, isInK_ofLimbs_iff] at hK
  simp only [add_zero] at hK
  have h0 : x.limb 0 = K.ofBits l + K.ofBits (2 ^ 16 * N) := by
    have := hK.2
    rw [add_assoc] at this
    exact (add_eq_zero_iff_eq_neg.mp this).trans (CharTwo.neg_eq _)
  rw [cellNat, h0, ← ofBits_xor, Nat.xor_comm, two_pow_mul_xor hl, kToNat_ofBits]
  omega

/-- The tree index's high byte's six unused bits, folded most significant first. -/
def padV (b : Nat) : V := if b = 0 then .n 639 else .n (1621 + 3 * (b - 1) + 2)

theorem sPadBits_sound {T : Nat} (hb : BitsAt σ T) (h : AtomsHold rd σ sPadBits) :
    ∀ b ≤ 5, σ (padV b) = eOfNat (T / 2 ^ (247 - b) % 2 ^ (b + 1))
  | 0, _ => by
      rw [show padV 0 = .n (392 + 247) from rfl, hb 247 (by norm_num), bitE_testBit]
      norm_num
  | b + 1, hb5 => by
      have ih := sPadBits_sound hb h b (by omega)
      have mem : ∀ x ∈ [cst (1621 + 3 * b) (word 2 0 0),
          mulS (.n (1621 + 3 * b + 1)) (.n (if b = 0 then 639 else 1621 + 3 * b - 1)) (.n (1621 + 3 * b)),
          addS (.n (1621 + 3 * b + 2)) (.n (638 - b)) (.n (1621 + 3 * b + 1))], x ∈ sPadBits := fun x hx =>
        List.mem_flatMap.mpr ⟨b, List.mem_range.mpr (by omega), hx⟩
      have k : σ (.n (1621 + 3 * b)) = word 2 0 0 := h.atom (a := .const _ _) (mem _ (by simp [cst]))
      have m : σ (.n (1621 + 3 * b + 1)) = σ (padV b) * σ (.n (1621 + 3 * b)) := by
        have := h.atom (a := .mul _ _ _) (mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
        rw [this]
        congr 2
        unfold padV
        split_ifs <;> first | rfl | (congr 1; omega)
      have a : σ (.n (1621 + 3 * b + 2)) = σ (.n (638 - b)) + σ (.n (1621 + 3 * b + 1)) :=
        h.atom (a := .add _ _ _) (mem _ (by simp [addS]))
      have hP : T / 2 ^ (247 - b) % 2 ^ (b + 1) < 2 ^ 6 :=
        lt_of_lt_of_le (Nat.mod_lt _ (by positivity)) (Nat.pow_le_pow_right (by norm_num) (by omega))
      rw [show padV (b + 1) = .n (1621 + 3 * b + 2) by simp [padV], a, m, k, ih, word_two, mul_comm,
        Value.gen_mul_eOfNat (by omega), show 638 - b = 392 + (246 - b) by omega, hb _ (by omega),
        bitE_testBit, add_comm, show 2 * (T / 2 ^ (247 - b) % 2 ^ (b + 1)) =
          2 ^ 1 * (T / 2 ^ (247 - b) % 2 ^ (b + 1)) by ring,
        Value.eOfNat_add_of_lt (s := 1) (r := T / 2 ^ (246 - b) % 2) (by omega)]
      congr 1
      rw [show 247 - (b + 1) = 246 - b by omega, show b + 1 + 1 = 1 + (b + 1) by ring,
        mod_split (T / 2 ^ (246 - b)) 1 (b + 1), Nat.div_div_eq_div_mul, ← pow_add,
        show 246 - b + 1 = 247 - b by omega, pow_one]

theorem lval_at {T : Nat} (hl : LValsAt σ T) {l z i : Nat} (hl3 : l < 3) (hz : z < sLeafLen l)
    (hi : i = 8 * l + z) : σ (sLVal i) = eOfNat (layerLeafN T l >>> z) := by
  subst hi; exact hl l hl3 z hz

/-- The check's statements before `d0[0] = md0`: the tree's middle byte, the unused bits. -/
def sCheckA : List Stmt :=
  [cst 1618 (word 256 0 0), mulS (.n 1619) (sLVal 24) (.n 1618), addS sTreeMid (sLVal 16) (.n 1619)] ++
    sPadBits

/-- Between `d0[0] = md0` and `d0[1] = …`: the tree index's two high bytes placed. -/
def sCheckB : List Stmt :=
  [cst 1636 (word 4 0 0), mulS (.n 1637) (.n 1635) (.n 1636), addS (.n 1638) (sLVal 24) (.n 1637),
    cst 1639 (pw 112), mulS (.n 1640) (.n 1638) (.n 1639), addS (.n 1641) sMd1.2.2 (.n 1640),
    cst 1642 (pw 120), mulS (.n 1643) sTreeMid (.n 1642)]

/-- After the unused bytes: the second call's high lane. -/
def sCheckC : List Stmt :=
  [addS (.n 1701) sHm1 (sLVal 8), cst 1702 (word 256 0 0), mulS (.n 1703) (sLVal 0) (.n 1702),
    addS (.n 1704) (.n 1701) (.n 1703), cst 1705 (word 65536 0 0),
    mulS (.n 1706) sUnused.2.2 (.n 1705), addS (.n 1707) (.n 1704) (.n 1706),
    cst 1708 (word 1 0 1), mulS (.n 1709) (.n 1707) (.n 1708)]

theorem sCheck_split : sCheck = sCheckA ++ [copyS sHm0 sMd0.2.2] ++ sCheckB ++
    [addS sHm0b (.n 1641) (.n 1643), hintW "sp_unused" (runV 1644 6)] ++ sUnused.1 ++ sCheckC ++
    [.atom (.assertInK (.n 1709) sUnused.2.2)] := by
  simp [sCheck, sCheckA, sCheckB, sCheckC]

theorem lval_16 {T : Nat} (hl : LValsAt σ T) : σ (sLVal 16) = eOfNat (layerLeafN T 2) := by
  simpa using lval_at hl (l := 2) (z := 0) (by norm_num) (by simp [sLeafLen]) rfl

theorem lval_24 {T : Nat} (hl : LValsAt σ T) : σ (sLVal 24) = eOfNat (layerLeafN T 2 >>> 8) :=
  lval_at hl (l := 2) (z := 8) (by norm_num) (by simp [sLeafLen]) rfl

theorem lval_8 {T : Nat} (hl : LValsAt σ T) : σ (sLVal 8) = eOfNat (layerLeafN T 1) := by
  simpa using lval_at hl (l := 1) (z := 0) (by norm_num) (by simp [sLeafLen]) rfl

theorem lval_0 {T : Nat} (hl : LValsAt σ T) : σ (sLVal 0) = eOfNat (layerLeafN T 0) := by
  simpa using lval_at hl (l := 0) (z := 0) (by norm_num) (by simp [sLeafLen]) rfl

/-- **The tree's middle byte and the unused bits.** -/
theorem sCheckA_sound {T : Nat} (hb : BitsAt σ T) (hl : LValsAt σ T) (h : AtomsHold rd σ sCheckA) :
    σ sTreeMid = eOfNat (byteN T 31) ∧ σ (.n 1635) = eOfNat (T / 2 ^ 242 % 2 ^ 6) := by
  have hA := h.left
  have hL2 : layerLeafN T 2 < 2 ^ 10 := by simpa [sLeafLen] using layerLeafN_lt T 2
  refine ⟨?_, ?_⟩
  · have k : σ (.n 1618) = word 256 0 0 := hA.atom (a := .const _ _) (by simp [cst])
    have m : σ (.n 1619) = σ (sLVal 24) * σ (.n 1618) := hA.atom (a := .mul _ _ _) (by simp [mulS])
    have a : σ sTreeMid = σ (sLVal 16) + σ (.n 1619) := hA.atom (a := .add sTreeMid _ _) (by simp [addS])
    rw [a, m, k, lval_16 hl, lval_24 hl, word_eq_eOfNat, show (256 : Nat) = 2 ^ 8 by norm_num, mul_comm,
      Value.eOfNat_two_pow_mul (by rw [Nat.shiftRight_eq_div_pow]; omega), eOfNat_low, layerLeaf2_low]
  · have pad := sPadBits_sound hb h.right 5 le_rfl
    rw [show padV 5 = .n 1635 from rfl] at pad
    simpa using pad

/-- **The tree index's two high bytes placed**: with `md1`, the first call's second cell. -/
theorem sCheckB_sound {T : Nat} (hl : LValsAt σ T) (tm : σ sTreeMid = eOfNat (byteN T 31))
    (pad : σ (.n 1635) = eOfNat (T / 2 ^ 242 % 2 ^ 6))
    (h1 : σ sMd1.2.2 = eOfNat192 (T / 2 ^ 128 % 2 ^ 112)) (hB : AtomsHold rd σ sCheckB) :
    σ (.n 1641) + σ (.n 1643) = eOfNat192 (T / 2 ^ 128 % 2 ^ 128) := by
  have k6 : σ (.n 1636) = word 4 0 0 := hB.atom (a := .const _ _) (by simp [sCheckB, cst])
  have m7 : σ (.n 1637) = σ (.n 1635) * σ (.n 1636) := hB.atom (a := .mul _ _ _) (by simp [sCheckB, mulS])
  have a8 : σ (.n 1638) = σ (sLVal 24) + σ (.n 1637) := hB.atom (a := .add _ _ _) (by simp [sCheckB, addS])
  have k9 : σ (.n 1639) = pw 112 := hB.atom (a := .const _ _) (by simp [sCheckB, cst])
  have m0 : σ (.n 1640) = σ (.n 1638) * σ (.n 1639) := hB.atom (a := .mul _ _ _) (by simp [sCheckB, mulS])
  have a1 : σ (.n 1641) = σ sMd1.2.2 + σ (.n 1640) := hB.atom (a := .add _ _ _) (by simp [sCheckB, addS])
  have k2 : σ (.n 1642) = pw 120 := hB.atom (a := .const _ _) (by simp [sCheckB, cst])
  have m3 : σ (.n 1643) = σ sTreeMid * σ (.n 1642) := hB.atom (a := .mul _ _ _) (by simp [sCheckB, mulS])
  have b30 : σ (.n 1638) = eOfNat (byteN T 30) := by
    rw [a8, m7, k6, pad, lval_24 hl, layerLeaf2_high, word_eq_eOfNat, show (4 : Nat) = 2 ^ 2 by norm_num,
      mul_comm, Value.eOfNat_two_pow_mul (by omega), add_comm,
      Value.eOfNat_add_of_lt (Nat.mod_lt _ (by norm_num))]
    congr 1
    unfold byteN
    have e : T / 2 ^ 242 = T / 2 ^ 240 / 4 := by rw [Nat.div_div_eq_div_mul]; norm_num
    rw [e, show 8 * 30 = 240 by norm_num]
    generalize T / 2 ^ 240 = X
    omega
  have e41 : σ (.n 1641) = eOfNat192 (T / 2 ^ 128 % 2 ^ 120) := by
    rw [a1, m0, b30, k9, h1, pw_mul (by norm_num) (by have := byteN_lt T 30; norm_num; omega),
      eOfNat192_add_shift (Nat.mod_lt _ (by positivity)), show (120 : Nat) = 112 + 8 by norm_num,
      mod_split (T / 2 ^ 128) 112 8, Nat.div_div_eq_div_mul, ← pow_add, byteN, Nat.add_comm]
  rw [e41, m3, k2, tm, pw_mul (by norm_num) (by have := byteN_lt T 31; norm_num; omega),
    eOfNat192_add_shift (Nat.mod_lt _ (by positivity)), show (128 : Nat) = 120 + 8 by norm_num,
    mod_split (T / 2 ^ (120 + 8)) 120 8, Nat.div_div_eq_div_mul, ← pow_add, byteN, Nat.add_comm]

/-- **The second call's high lane**: its cell, the leaves' bytes and the unused bytes `N`, times
`y⁻¹`. -/
theorem sCheckC_sound {T N : Nat} (hl : LValsAt σ T) (hN : σ sUnused.2.2 = eOfNat N) (hN48 : N < 2 ^ 48)
    (hC : AtomsHold rd σ sCheckC) :
    σ (.n 1709) = (σ sHm1 + eOfNat (T / 2 ^ 256 % 2 ^ 16) + eOfNat (2 ^ 16 * N)) * word 1 0 1 := by
  have hL1 : layerLeafN T 1 < 2 ^ 8 := by simpa [sLeafLen] using layerLeafN_lt T 1
  have hL0 : layerLeafN T 0 < 2 ^ 8 := by simpa [sLeafLen] using layerLeafN_lt T 0
  have a01 : σ (.n 1701) = σ sHm1 + σ (sLVal 8) := hC.atom (a := .add _ _ _) (by simp [sCheckC, addS])
  have k02 : σ (.n 1702) = word 256 0 0 := hC.atom (a := .const _ _) (by simp [sCheckC, cst])
  have m03 : σ (.n 1703) = σ (sLVal 0) * σ (.n 1702) := hC.atom (a := .mul _ _ _) (by simp [sCheckC, mulS])
  have a04 : σ (.n 1704) = σ (.n 1701) + σ (.n 1703) := hC.atom (a := .add _ _ _) (by simp [sCheckC, addS])
  have k05 : σ (.n 1705) = word 65536 0 0 := hC.atom (a := .const _ _) (by simp [sCheckC, cst])
  have m06 : σ (.n 1706) = σ sUnused.2.2 * σ (.n 1705) := hC.atom (a := .mul _ _ _) (by simp [sCheckC, mulS])
  have a07 : σ (.n 1707) = σ (.n 1704) + σ (.n 1706) := hC.atom (a := .add _ _ _) (by simp [sCheckC, addS])
  have k08 : σ (.n 1708) = word 1 0 1 := hC.atom (a := .const _ _) (by simp [sCheckC, cst])
  have m09 : σ (.n 1709) = σ (.n 1707) * σ (.n 1708) := hC.atom (a := .mul _ _ _) (by simp [sCheckC, mulS])
  rw [m09, k08, a07, m06, k05, a04, m03, k02, a01, lval_8 hl, lval_0 hl, hN, word_eq_eOfNat, word_eq_eOfNat,
    show (256 : Nat) = 2 ^ 8 by norm_num, show (65536 : Nat) = 2 ^ 16 by norm_num,
    mul_comm (eOfNat (layerLeafN T 0)), Value.eOfNat_two_pow_mul (by omega), mul_comm (eOfNat N),
    Value.eOfNat_two_pow_mul (by omega), add_assoc (σ sHm1), add_comm (eOfNat (layerLeafN T 1)),
    Value.eOfNat_add_of_lt hL1, layerLeaf01]
  rfl

/-- **The check, sound**: the first call's cells are the digest's bytes `0 … 31` the bits spell,
the second call's low two bytes its bytes `32`, `33`. -/
theorem sCheck_sound {κ : Nat} (hκ : κ ≤ 32) {L : MemoryImage κ} (hbb : ByteBits L.read (σ (.n 1)))
    {T : Nat} (hb : BitsAt σ T) (hl : LValsAt σ T) (h0 : σ sMd0.2.2 = eOfNat192 (T % 2 ^ 128))
    (h1 : σ sMd1.2.2 = eOfNat192 (T / 2 ^ 128 % 2 ^ 112)) (h : AtomsHold L.read σ sCheck) :
    σ sTreeMid = eOfNat (byteN T 31) ∧ σ sHm0 = eOfNat192 (T % 2 ^ 128) ∧
      σ sHm0b = eOfNat192 (T / 2 ^ 128 % 2 ^ 128) ∧ cellNat (σ sHm1) % 2 ^ 16 = T / 2 ^ 256 % 2 ^ 16 := by
  rw [sCheck_split] at h
  have hK := h.right
  have hC := h.left.right
  have hU := h.left.left.right
  have hD := h.left.left.left.right
  have hB := h.left.left.left.left.right
  have hc := h.left.left.left.left.left.right
  have hA := h.left.left.left.left.left.left
  obtain ⟨tm, pad⟩ := sCheckA_sound hb hl hA
  refine ⟨tm, ?_, ?_, ?_⟩
  · have c : σ sHm0 = σ sMd0.2.2 := hc.atom (a := .copy sHm0 _) (by simp [copyS])
    rw [c, h0]
  · have a4 : σ sHm0b = σ (.n 1641) + σ (.n 1643) := hD.atom (a := .add sHm0b _ _) (by simp [addS])
    rw [a4, sCheckB_sound hl tm pad h1 hB]
  · obtain ⟨N, hN, hNlt⟩ := sFromMarks_sound hκ hbb (b := 1644) (n := 6) (x := 1650) (by norm_num)
      (by norm_num) hU
    have hk : IsInK (σ (.n 1709)) := (hK.atom (a := .assertInK (.n 1709) sUnused.2.2) (by simp)).1
    rw [sCheckC_sound hl hN (by simpa using hNlt) hC] at hk
    exact high_low_bytes (Nat.mod_lt _ (by norm_num)) hk

/-! ## The block -/

/-- **What the digest block gives**: the digest's number `T` (`< 2^272`) whose bits the bit run
holds, every FORS leaf and layer leaf with their shifts, and the tree index's middle byte. -/
def DigestAt (σ : Val) (T : Nat) : Prop :=
  T < 2 ^ 272 ∧ BitsAt σ T ∧ FValsAt σ T ∧ LValsAt σ T ∧ σ sTreeMid = eOfNat (byteN T 31)

theorem DigestAt.mdBit {T : Nat} (h : DigestAt σ T) {p : Nat} (hp : p < 240) :
    σ (sMdBit p) = bitE (T.testBit (mdPos p)) := by
  rw [sMdBit_eq]; exact h.2.1 _ (by have := mdPos_lt hp; omega)

theorem DigestAt.leafBit {T : Nat} (h : DigestAt σ T) {b : Nat} (hb : b < 26) :
    σ (sLeafBit b) = bitE (T.testBit (leafPos b)) := by
  rw [sLeafBit_eq hb]; exact h.2.1 _ (leafPos_lt hb)

/-- The bytes `H_msg`'s call `i` hashes: `R | PK.seed | PK.root | M' | BE_32(i)`, `M'` the framing then
the message `M` (its number), little endian. -/
def hmsgBytes (R seed root : E) (M i : Nat) : List UInt8 :=
  cellBytes R ++ cellBytes seed ++ cellBytes root ++ leBytes (framingNat + 2 ^ 104 * M) 48 ++
    [UInt8.ofNat i]

/-- The digest's number from `H_msg`'s two calls: the first call's two cells and the second call's
low two bytes. -/
def hmsgNat (d0 d1 : E × E) : Nat := cellNat d0.1 + 2 ^ 128 * cellNat d0.2 + 2 ^ 256 * (cellNat d1.1 % 2 ^ 16)

theorem cells3_bytes {N : Nat} (hN : N < 2 ^ 384) :
    cellBytes (eOfNat192 (N % 2 ^ 128)) ++ cellBytes (eOfNat192 (N / 2 ^ 128 % 2 ^ 128)) ++
      cellBytes (eOfNat192 (N / 2 ^ 256)) = leBytes N 48 := by
  rw [cellBytes_eOfNat192 (Nat.mod_lt _ (by norm_num)), cellBytes_eOfNat192 (Nat.mod_lt _ (by norm_num)),
    cellBytes_eOfNat192 (by omega), show (2 : Nat) ^ 128 = 256 ^ 16 by norm_num, leBytes_mod, leBytes_mod,
    leBytes_append, show (2 : Nat) ^ 256 = 256 ^ 32 by norm_num, leBytes_append]

theorem hmsg_take {R s r : E} {M i : Nat} (hM : M < 2 ^ 256) (hi : i < 256) :
    (cellsBytes [R, s, r, eOfNat192 ((framingNat + 2 ^ 104 * M) % 2 ^ 128),
      eOfNat192 ((framingNat + 2 ^ 104 * M) / 2 ^ 128 % 2 ^ 128),
      eOfNat192 ((framingNat + 2 ^ 104 * M) / 2 ^ 256), word i 0 0]).take 97 = hmsgBytes R s r M i := by
  have hb := cells3_bytes (N := framingNat + 2 ^ 104 * M) (by simp only [framingNat]; omega)
  have e : cellsBytes [R, s, r, eOfNat192 ((framingNat + 2 ^ 104 * M) % 2 ^ 128),
      eOfNat192 ((framingNat + 2 ^ 104 * M) / 2 ^ 128 % 2 ^ 128),
      eOfNat192 ((framingNat + 2 ^ 104 * M) / 2 ^ 256), word i 0 0] =
      (cellBytes R ++ cellBytes s ++ cellBytes r ++ leBytes (framingNat + 2 ^ 104 * M) 48) ++
        cellBytes (word i 0 0) := by
    rw [← hb]; simp [cellsBytes]
  have hl : (cellBytes R ++ cellBytes s ++ cellBytes r ++ leBytes (framingNat + 2 ^ 104 * M) 48).length = 96 := by
    simp [cellBytes_eq_leBytes, leBytes]
  rw [e, show 97 = 96 + 1 from rfl, ← hl, List.take_length_add_append, hmsgBytes,
    cellBytes_eq_leBytes (word i 0 0), word_eq_eOfNat, cellNat_eOfNat (by omega)]
  simp [leBytes]

/-- **The message digest's block, sound**: the padding run; the claim's keys and message `M` loaded;
and a number `T` whose bits and fields the block holds, `T` the digest `H_msg`'s two calls give on
`R | PK.seed | PK.root | M' | BE_32(i)`. -/
theorem sDigestBlock_sound {κ : Nat} (hκ : κ ≤ 32) {L : MemoryImage κ}
    (hbb : ByteBits L.read (σ (.n 1))) (h : AtomsHold L.read σ sDigestBlock) :
    PadOK σ sPad ∧ LoadHolds L.read (σ (.n 0)) 0 (σ sPP) ∧ LoadHolds L.read (σ (.n 0)) 1 (σ sRoot) ∧
      ∃ M < 2 ^ 256, LoadHolds L.read (σ (.n 0)) 2 (eOfNat192 (M % 2 ^ 128)) ∧
        LoadHolds L.read (σ (.n 0)) 3 (eOfNat192 (M / 2 ^ 128)) ∧
        ∃ T, DigestAt σ T ∧
          T = hmsgNat (digestHalves (keccak256 (hmsgBytes (σ sRand) (σ sPP) (σ sRoot) M 0)))
            (digestHalves (keccak256 (hmsgBytes (σ sRand) (σ sPP) (σ sRoot) M 1))) := by
  have hCk : AtomsHold L.read σ sCheck := h.right
  have hMd : AtomsHold L.read σ sMdBytes := h.left.right
  have hLs : AtomsHold L.read σ sLeafShifts := h.left.left.right
  have hFs : AtomsHold L.read σ sForsFields := h.left.left.left.right
  have hBo : AtomsHold L.read σ sBooleans := h.left.left.left.left.right
  have hDg : AtomsHold L.read σ sDigests := h.left.left.left.left.left.left.right
  have hMs : AtomsHold L.read σ sMsg := h.left.left.left.left.left.left.left
  obtain ⟨hp, d0, d1⟩ := sDigests_sound hDg
  obtain ⟨lP, lR, M, hM, l2, l3, e0, e1, e2⟩ := sMsg_sound hκ hbb hMs
  set T := bitsOf σ 392 272 with hTdef
  have hT : T < 2 ^ 272 := bitsOf_lt' σ
  have hb := sBooleans_bitsAt hBo
  have hv := sForsFields_sound hb hFs
  have hl := sLeafShifts_sound hb hLs
  have m0 := sMd0_sound hv (hMd.left.left) hMd.left.right
  have m1 := sMd1_sound hv hMd.right
  obtain ⟨tm, c0, c1, c2⟩ := sCheck_sound hκ hbb hb hl m0 m1 hCk
  refine ⟨hp, lP, lR, M, hM, l2, l3, T, ⟨hT, hb, hv, hl, tm⟩, ?_⟩
  have k0 : hmsgCells σ 0 = [σ sRand, σ sPP, σ sRoot, eOfNat192 ((framingNat + 2 ^ 104 * M) % 2 ^ 128),
      eOfNat192 ((framingNat + 2 ^ 104 * M) / 2 ^ 128 % 2 ^ 128),
      eOfNat192 ((framingNat + 2 ^ 104 * M) / 2 ^ 256), word 0 0 0] := by rw [hmsgCells, e0, e1, e2]
  have k1 : hmsgCells σ 1 = [σ sRand, σ sPP, σ sRoot, eOfNat192 ((framingNat + 2 ^ 104 * M) % 2 ^ 128),
      eOfNat192 ((framingNat + 2 ^ 104 * M) / 2 ^ 128 % 2 ^ 128),
      eOfNat192 ((framingNat + 2 ^ 104 * M) / 2 ^ 256), word 1 0 0] := by rw [hmsgCells, e0, e1, e2]
  rw [hcellLen, k0, hmsg_take hM (by norm_num)] at d0
  rw [hcellLen, k1, hmsg_take hM (by norm_num)] at d1
  rw [← d0, ← d1, hmsgNat]
  dsimp only
  rw [c0, c1, cellNat_eOfNat192 (Nat.mod_lt _ (by norm_num)), cellNat_eOfNat192 (Nat.mod_lt _ (by norm_num)),
    c2]
  omega

/-! ## The statement's message digest -/

theorem framingNat_bytes : leBytes framingNat 13 = [0x00, UInt8.ofNat Sphincs.contextString.length] ++
    Sphincs.contextString := by decide

/-- **`H_msg`'s input is `hmsgBytes`**: `R | PK.seed | PK.root | M' | BE_32(i)` of cells and a
message. -/
theorem hmsgBytes_eq (R seed root : E) (msg : HashSig.Message) (call : Sphincs.DigestCall) :
    HashSig.littleEndianBytes 16 (cellVal R) ++ HashSig.littleEndianBytes 16 (cellVal seed) ++
        HashSig.littleEndianBytes 16 (cellVal root) ++ Sphincs.framedMessage msg ++
        Sphincs.bigEndianBytes 4 (BitVec.ofNat 32 call.val) =
      hmsgBytes R seed root msg.toNat call.val := by
  have hM := msg.isLt
  have hbe : Sphincs.bigEndianBytes 4 (BitVec.ofNat 32 call.val) = [0, 0, 0, UInt8.ofNat call.val] := by
    fin_cases call <;> decide
  have h35 : leBytes msg.toNat 35 = leBytes msg.toNat 32 ++ [0, 0, 0] := by
    rw [← leBytes_append msg.toNat 32 3, Nat.div_eq_of_lt (by norm_num; omega)]
    rfl
  rw [bytesLE_cellVal, bytesLE_cellVal, bytesLE_cellVal, hmsgBytes, Sphincs.framedMessage, hbe,
    show (2 : Nat) ^ 104 = 256 ^ 13 by norm_num, show (48 : Nat) = 13 + 35 from rfl,
    leBytes_add_mul _ _ _ _ (by simp only [framingNat]; norm_num), h35, framingNat_bytes, bytesLE_eq]
  simp only [List.append_assoc, List.cons_append, List.nil_append]

/-- **The statement's message digest, from cells**: `H_msg` of the randomizer, the key and the
message is the number `hmsgNat` of `H_msg`'s two calls on `hmsgBytes`. -/
theorem hmsgDigest_cells (R seed root : E) (msg : HashSig.Message) :
    Id.run (Sphincs.Verification.messageDigest (m := Id) LeanVM.Semantics.keccakF1600
        ⟨cellVal seed, cellVal root⟩ (cellVal R) msg) =
      BitVec.ofNat (8 * Sphincs.digestByteCount)
        (hmsgNat (digestHalves (keccak256 (hmsgBytes R seed root msg.toNat 0)))
          (digestHalves (keccak256 (hmsgBytes R seed root msg.toNat 1)))) := by
  simp only [Sphincs.Verification.messageDigest, Sphincs.Verification.messageDigestCall,
    keccakHash_keccakF1600, Id.run, bind, pure, sequenceFin_id]
  rw [Sphincs.truncateMessageDigest]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, Sphincs.digestValue]
  have k : ∀ c : Sphincs.DigestCall, (Node.keccakBits
      (HashSig.littleEndianBytes 16 (cellVal R) ++ HashSig.littleEndianBytes 16 (cellVal seed) ++
        HashSig.littleEndianBytes 16 (cellVal root) ++ Sphincs.framedMessage msg ++
        Sphincs.bigEndianBytes 4 (BitVec.ofNat 32 c.val))).toNat =
      cellNat (digestHalves (keccak256 (hmsgBytes R seed root msg.toNat c.val))).1 +
        2 ^ 128 * cellNat (digestHalves (keccak256 (hmsgBytes R seed root msg.toNat c.val))).2 :=
    fun c => by rw [hmsgBytes_eq, keccakBits_toNat]
  simp only [k]
  rw [Fin.sum_univ_eq_sum_range (fun c => (cellNat (digestHalves (keccak256 (hmsgBytes R seed root msg.toNat c))).1 +
      2 ^ 128 * cellNat (digestHalves (keccak256 (hmsgBytes R seed root msg.toNat c))).2) * 2 ^ (256 * c))
      Sphincs.digestCallCount, show Sphincs.digestCallCount = 2 from rfl, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_zero, hmsgNat]
  generalize hN : 8 * Sphincs.digestByteCount = N
  have h2N : 2 ^ N = 2 ^ 256 * 2 ^ 16 := by
    rw [← hN, ← pow_add]
    exact congrArg (fun x => 2 ^ x) (show 8 * Sphincs.digestByteCount = 256 + 16 from rfl)
  rw [h2N]
  have a0 := cellNat_lt (digestHalves (keccak256 (hmsgBytes R seed root msg.toNat 0))).1
  have b0 := cellNat_lt (digestHalves (keccak256 (hmsgBytes R seed root msg.toNat 0))).2
  generalize cellNat (digestHalves (keccak256 (hmsgBytes R seed root msg.toNat 0))).1 = A0 at *
  generalize cellNat (digestHalves (keccak256 (hmsgBytes R seed root msg.toNat 0))).2 = B0 at *
  generalize cellNat (digestHalves (keccak256 (hmsgBytes R seed root msg.toNat 1))).1 = A1
  generalize cellNat (digestHalves (keccak256 (hmsgBytes R seed root msg.toNat 1))).2 = B1
  simp only [Nat.mul_zero, pow_zero, mul_one, zero_add]
  omega

/-! ## Algorithm 19: the digest's fields -/

/-- The statement's message digest of the number `T`. -/
abbrev digestOf (T : Nat) : Sphincs.MessageDigest := BitVec.ofNat (8 * Sphincs.digestByteCount) T

theorem two_pow_digestBits : 2 ^ (8 * Sphincs.digestByteCount) = 2 ^ 272 :=
  congrArg (fun x => 2 ^ x) (show 8 * Sphincs.digestByteCount = 272 from rfl)

theorem digestOf_toNat {T : Nat} (hT : T < 2 ^ 272) : (digestOf T).toNat = T := by
  rw [BitVec.toNat_ofNat, two_pow_digestBits, Nat.mod_eq_of_lt hT]

/-- **The statement's byte `p` is `T`'s.** -/
theorem messageDigestByte_eq {T p : Nat} (hT : T < 2 ^ 272) :
    Sphincs.messageDigestByte (digestOf T) p = byteN T p := by
  rw [Sphincs.messageDigestByte, BitVec.extractLsb'_toNat, digestOf_toNat hT, Nat.shiftRight_eq_div_pow,
    byteN]

/-- **The statement's bit `p`, most significant first, is `T`'s bit `mdPos p`.** -/
theorem messageDigestBit_eq {T p : Nat} (hT : T < 2 ^ 272) :
    Sphincs.messageDigestBit (digestOf T) p = (T.testBit (mdPos p)).toNat := by
  rw [Sphincs.messageDigestBit, messageDigestByte_eq hT, ← Nat.toNat_testBit, mdPos, testBit_byteN]
  simp [show 7 - p % 8 < 8 by omega]

/-- **The statement's FORS leaves are `forsLeafN`** (`base_2b`, Algorithm 19). -/
theorem digestForsLeaves_val {T : Nat} (hT : T < 2 ^ 272) (c : Sphincs.ForsTreeIndex) :
    (Sphincs.digestForsLeaves (digestOf T) c).val = forsLeafN T c.val := by
  have hc := c.isLt
  have hb : ∀ j < 10, Sphincs.messageDigestBit (digestOf T) (10 * c.val + j) =
      (T.testBit (mdPos (10 * c.val + j))).toNat := fun j _ => messageDigestBit_eq hT
  have hl := forsLeafN_lt T c.val
  simp only [Sphincs.digestForsLeaves, Sphincs.forsLeafOfNat, Sphincs.forsTreeHeight]
  simp only [List.range_succ, List.range_zero, List.nil_append, List.foldl_append, List.foldl_cons,
    List.foldl_nil]
  rw [hb 0 (by norm_num), hb 1 (by norm_num), hb 2 (by norm_num), hb 3 (by norm_num), hb 4 (by norm_num),
    hb 5 (by norm_num), hb 6 (by norm_num), hb 7 (by norm_num), hb 8 (by norm_num), hb 9 (by norm_num)]
  simp only [forsLeafN, bitsVal, Nat.add_zero] at hl ⊢
  simp (disch := omega) only [Nat.add_sub_assoc, Nat.reduceSub, Nat.add_zero] at hl ⊢
  norm_num at hl ⊢
  omega

/-- The index `idx` the digest picks: its layers' leaves, bottom first, eight bits each below the
top's ten. -/
def indexN (T : Nat) : Nat := layerLeafN T 0 + 2 ^ 8 * layerLeafN T 1 + 2 ^ 16 * layerLeafN T 2

theorem layerLeafN_bytes {T : Nat} :
    layerLeafN T 0 = byteN T 33 ∧ layerLeafN T 1 = byteN T 32 ∧
      layerLeafN T 2 = byteN T 31 + 2 ^ 8 * (byteN T 30 % 4) := by
  have h01 := layerLeaf01 T
  have hlo := layerLeaf2_low T
  have hhi := layerLeaf2_high T
  have l0 : layerLeafN T 0 < 2 ^ 8 := by simpa [sLeafLen] using layerLeafN_lt T 0
  have l1 : layerLeafN T 1 < 2 ^ 8 := by simpa [sLeafLen] using layerLeafN_lt T 1
  have l2 : layerLeafN T 2 < 2 ^ 10 := by simpa [sLeafLen] using layerLeafN_lt T 2
  have e33 : byteN T 33 = T / 2 ^ 256 / 2 ^ 8 % 2 ^ 8 := by
    rw [byteN, Nat.div_div_eq_div_mul, ← pow_add]
  have e31 : byteN T 30 % 4 = T / 2 ^ 240 % 2 ^ 2 := by
    rw [byteN, Nat.mod_mod_of_dvd _ (by norm_num)]; norm_num
  rw [Nat.shiftRight_eq_div_pow] at hhi
  refine ⟨?_, ?_, ?_⟩
  · rw [e33]; omega
  · rw [byteN, show 8 * 32 = 256 by norm_num]; omega
  · omega

/-- **The statement's index is `indexN`** (Algorithm 19: the tree index cut to 18 bits, then the
bottom leaf). -/
theorem digestIndex_val {T : Nat} (hT : T < 2 ^ 272) : (Sphincs.digestIndex (digestOf T)).val = indexN T := by
  obtain ⟨e0, e1, e2⟩ := layerLeafN_bytes (T := T)
  have b30 := byteN_lt T 30
  have b31 := byteN_lt T 31
  have b32 := byteN_lt T 32
  have b33 := byteN_lt T 33
  simp only [Sphincs.digestIndex, Sphincs.messageDigestBigEndian, Sphincs.forsMessageByteCount,
    Sphincs.treeIndexByteCount, Sphincs.leafIndexByteCount, List.range_succ, List.range_zero,
    List.nil_append, List.foldl_append, List.foldl_cons, List.foldl_nil, messageDigestByte_eq hT, indexN,
    e0, e1, e2]
  norm_num at b30 b31 b32 b33 ⊢
  omega

/-- Layer `l`'s tree of the index: the leaves of the layers above it. -/
def layerTreeN (T l : Nat) : Nat :=
  if l = 0 then layerLeafN T 1 + 2 ^ 8 * layerLeafN T 2 else if l = 1 then layerLeafN T 2 else 0

theorem layerLeafN_lt' (T : Nat) : layerLeafN T 0 < 2 ^ 8 ∧ layerLeafN T 1 < 2 ^ 8 ∧ layerLeafN T 2 < 2 ^ 10 :=
  ⟨by simpa [sLeafLen] using layerLeafN_lt T 0, by simpa [sLeafLen] using layerLeafN_lt T 1,
    by simpa [sLeafLen] using layerLeafN_lt T 2⟩

/-- **Each layer's leaf of the digest's index** is the layer's leaf the digest holds. -/
theorem leafOfIndex_digest {T : Nat} (hT : T < 2 ^ 272) (l : Sphincs.Layer) :
    (Sphincs.leafOfIndex l (Sphincs.digestIndex (digestOf T))).val = layerLeafN T l.val := by
  obtain ⟨h0, h1, h2⟩ := layerLeafN_lt' T
  rw [Sphincs.leafOfIndex]
  simp only [digestIndex_val hT, indexN, Sphincs.bitsBelowLayer, Sphincs.layerHeight]
  fin_cases l <;> simp <;> omega

/-- **Each layer's tree of the digest's index.** -/
theorem treeOfIndex_digest {T : Nat} (hT : T < 2 ^ 272) (l : Sphincs.Layer) :
    (Sphincs.treeOfIndex l (Sphincs.digestIndex (digestOf T))).val = layerTreeN T l.val := by
  obtain ⟨h0, h1, h2⟩ := layerLeafN_lt' T
  rw [Sphincs.treeOfIndex]
  simp only [digestIndex_val hT, indexN, Sphincs.bitsBelowLayer, Sphincs.layerHeight, layerTreeN]
  fin_cases l <;> simp <;> omega

/-! ## The block, against the statement -/

theorem canon_eOfNat192 {n : Nat} (h : n < 2 ^ 128) : IsCanonical128 (eOfNat192 n) := by
  rw [eOfNat192, isCanonical128_ofLimbs_iff, Nat.div_eq_of_lt h, Value.ofBits_zero]

theorem cellPairVal_toNat (lo hi : E) : (cellPairVal lo hi).toNat = cellNat lo + 2 ^ 128 * cellNat hi := by
  rw [cellPairVal, BitVec.toNat_append, toNat_cellVal, toNat_cellVal, Nat.shiftLeft_eq, mul_comm,
    two_pow_mul_or (cellNat_lt lo), add_comm]

/-- **The message digest's block, sound, against the statement**: the padding run; the four words at
the claim pointer are the claim of `PK.seed`, `PK.root` and two canonical message cells; and the
statement's `H_msg` of the claim and the randomizer is `digestOf T` for a `T` whose bits and
fields the block holds. -/
theorem sDigestBlock_sound_stmt {κ : Nat} (hκ : κ ≤ 32) {L : MemoryImage κ}
    (hbb : ByteBits L.read (σ (.n 1))) (h : AtomsHold L.read σ sDigestBlock) :
    PadOK σ sPad ∧ ∃ c d, ClaimAt L.read (σ (.n 0)) (σ sPP) (σ sRoot) c d ∧ IsCanonical128 c ∧
      IsCanonical128 d ∧ ∃ T, DigestAt σ T ∧
        Id.run (Sphincs.Verification.messageDigest (m := Id) LeanVM.Semantics.keccakF1600
          (sphincsClaimOf (σ sPP) (σ sRoot) c d).1 (cellVal (σ sRand))
          (sphincsClaimOf (σ sPP) (σ sRoot) c d).2) = digestOf T := by
  obtain ⟨hp, lP, lR, M, hM, l2, l3, T, hD, hT⟩ := sDigestBlock_sound hκ hbb h
  refine ⟨hp, _, _, ⟨lP, lR, l2, l3⟩, canon_eOfNat192 (Nat.mod_lt _ (by norm_num)),
    canon_eOfNat192 (by omega), T, hD, ?_⟩
  have hm : (cellPairVal (eOfNat192 (M % 2 ^ 128)) (eOfNat192 (M / 2 ^ 128))).toNat = M := by
    rw [cellPairVal_toNat, cellNat_eOfNat192 (Nat.mod_lt _ (by norm_num)), cellNat_eOfNat192 (by omega)]
    omega
  simp only [sphincsClaimOf]
  rw [hmsgDigest_cells, hm, ← hT]

end
end LeanVM.Guest.B1.Sig
