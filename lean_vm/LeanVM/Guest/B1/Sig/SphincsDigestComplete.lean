/-
  LeanVM.Guest.B1.Sig.SphincsDigestComplete

  The message and `H_msg` of `verify_sig_lean_sphincs` (`lean_ethereum.py:3972-4023` at leanVM
  834e6614) are complete: the claim's keys loaded, the message's bytes hinted, the lanes rebuilt
  and checked against the claim, `M'`'s cells laid out, the randomizer hinted and both calls hashed.
-/

module

public import LeanVM.Guest.B1.Sig.SphincsBytesComplete
public import LeanVM.Guest.B1.Sig.SphincsSoundDigest
public import LeanVM.Guest.B1.Sig.CwComplete
public import LeanVM.Guest.B1.Sig.KMsgComplete

/-!
# The message and `H_msg`, complete

* `bFold_desc`, `sFromMarks_complete`: `sp_from_bytes` of bytes hinted from a number's;
* `sLaneBytes_complete`, `sLaneBytesAll_complete`: the message's lanes, each as its three low and five
  high bytes;
* `sMsg_complete`: the claim's keys, the message, its check against the claim and `M'`'s cells;
* `sDigests_complete`: the randomizer and `H_msg`'s two calls.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier (eOfNat)

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-! ## `sp_from_bytes` of a number's bytes -/

/-- Folding a number's bytes high first. -/
theorem bFold_desc (X : Nat) :
    ∀ (m acc : Nat), bFold acc ((List.range m).reverse.map fun k => X / 256 ^ k % 256) =
      acc * 256 ^ m + X % 256 ^ m
  | 0, acc => by simp [bFold, Nat.mod_one]
  | m + 1, acc => by
      rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
        List.map_cons, bFold, bFold_desc X m]
      rw [show (256 : Nat) ^ (m + 1) = 256 ^ m * 256 by ring, Nat.mod_mul]
      ring

/-- **`sp_from_bytes` of `n ≤ 8` bytes hinted from `X`'s low bytes completes**: the value `X`'s low
`n` bytes, every byte's pointer the table's. -/
theorem sFromMarks_complete (hm : MemOK rd 256) {bb : E} (hbb : ByteBits rd bb) {b n x X : Nat}
    (hn : 1 ≤ n) (hn8 : n ≤ 8) (σ : Val) (hx : 2 ≤ x) (hbx : b + n ≤ x)
    (hmk : ∀ t < n, σ (.n (b + t)) = ofK (addressOfIndex (X / 256 ^ t % 256))) (h1 : σ (.n 1) = bb) :
    Completes C rd x (x + 6 + 9 * (n - 1)) (sFromMarks b n x).1 σ
      (fun σ' => σ' (sFromMarks b n x).2.2 = eOfNat (X % 256 ^ n) ∧
        ∀ k ≤ n - 1, BytePtr bb (σ' (.n (fbPtr x k)))) := by
  have hl : (sMarks b n).2.length = n - 1 := by simp [sMarks]
  have hc := sFromBytes_complete (C := C) hm hbb (v0 := X / 256 ^ (n - 1) % 256) (Nat.mod_lt _ (by norm_num))
    (sMarks b n).1 (sMarks b n).2 ((List.range (n - 1)).reverse.map fun k => X / 256 ^ k % 256) x σ hx
    ⟨b + n - 1, by omega, rfl⟩ (by rw [show (sMarks b n).1 = .n (b + (n - 1)) by simp [sMarks]; omega,
      hmk _ (by omega)])
    (by
      simp only [sMarks, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
      refine List.forall₂_same.mpr fun k hk => ⟨⟨b + k, by simp at hk; omega, rfl⟩,
        hmk k (by simp at hk; omega), Nat.mod_lt _ (by norm_num)⟩)
    h1 (by
      rw [hl, ← pow_succ']
      exact le_trans (Nat.pow_le_pow_right (by norm_num) (show n - 1 + 1 ≤ 8 by omega)) (by norm_num))
  rw [hl] at hc
  refine hc.mono le_rfl le_rfl fun σ' ⟨h1', h2'⟩ => ⟨?_, h2'⟩
  rw [show sFromMarks b n x = sFromBytes (sMarks b n).1 (sMarks b n).2 x from rfl, h1', bFold_desc,
    show (256 : Nat) ^ n = 256 ^ (n - 1) * 256 by rw [← pow_succ]; congr 1; omega, Nat.mod_mul,
    Nat.add_comm, Nat.mul_comm (X / 256 ^ (n - 1) % 256)]

/-! ## The message's lanes -/

theorem div_256_pow (M a t : Nat) : M / 256 ^ a / 256 ^ t = M / 256 ^ (a + t) := by
  rw [Nat.div_div_eq_div_mul, ← pow_add]

/-- **A lane's bytes complete**: its three low bytes and its five high ones, from the message's bytes
hinted at `n4 …`. -/
theorem sLaneBytes_complete (hm : MemOK rd 256) {bb : E} (hbb : ByteBits rd bb) {M j : Nat} (σ : Val)
    (hmk : ∀ t < 8, σ (.n (4 + 8 * j + t)) = ofK (addressOfIndex (M / 256 ^ (8 * j + t) % 256)))
    (h1 : σ (.n 1) = bb) :
    Completes C rd (sLaneBase j) (sLaneBase j + 68) (sLaneBytes j) σ
      (fun σ' => σ' (sLo j) = eOfNat (M / 256 ^ (8 * j) % 256 ^ 3) ∧
        σ' (sHi j) = eOfNat (M / 256 ^ (8 * j + 3) % 256 ^ 5) ∧
        (∀ k ≤ 2, BytePtr bb (σ' (.n (fbPtr (sLaneBase j) k)))) ∧
        ∀ k ≤ 4, BytePtr bb (σ' (.n (fbPtr (sLaneBase j + 25) k)))) := by
  have hL : sLaneBase j = 36 + 68 * j := rfl
  have shA := sFromBytes_shape (sMarks (4 + 8 * j) 3).1 (sMarks (4 + 8 * j) 3).2 (sLaneBase j)
    ⟨4 + 8 * j + 2, by rw [hL]; omega, by simp [sMarks]⟩
    (fun m hm => by simp [sMarks] at hm; obtain ⟨k, hk, rfl⟩ := hm; exact ⟨4 + 8 * j + k, by rw [hL]; omega, rfl⟩)
  have shB := sFromBytes_shape (sMarks (7 + 8 * j) 5).1 (sMarks (7 + 8 * j) 5).2 (sLaneBase j + 25)
    ⟨7 + 8 * j + 4, by rw [hL]; omega, by simp [sMarks]⟩
    (fun m hm => by simp [sMarks] at hm; obtain ⟨k, hk, rfl⟩ := hm; exact ⟨7 + 8 * j + k, by rw [hL]; omega, rfl⟩)
  have lA : (sMarks (4 + 8 * j) 3).2.length = 2 := by simp [sMarks]
  have lB : (sMarks (7 + 8 * j) 5).2.length = 4 := by simp [sMarks]
  rw [lA] at shA
  rw [lB] at shB
  obtain ⟨-, vA, nA⟩ := shA
  obtain ⟨-, vB, nB⟩ := shB
  have e : sLaneBytes j = (sFromMarks (4 + 8 * j) 3 (sLaneBase j)).1 ++
      ([copyS (sLo j) (sFromMarks (4 + 8 * j) 3 (sLaneBase j)).2.2] ++
        ((sFromMarks (7 + 8 * j) 5 (sLaneBase j + 25)).1 ++
          [copyS (sHi j) (sFromMarks (7 + 8 * j) 5 (sLaneBase j + 25)).2.2])) := by
    simp [sLaneBytes]
  rw [e]
  refine Completes.append (m := sLaneBase j + 24) (by omega) (by omega) nA
    (sFromMarks_complete (b := 4 + 8 * j) (n := 3) (x := sLaneBase j) (X := M / 256 ^ (8 * j)) hm hbb
      (by norm_num) (by norm_num) σ (by rw [hL]; omega) (by rw [hL]; omega)
      (fun t ht => by rw [div_256_pow]; exact hmk t (by omega)) h1)
    (fun σ1 he1 ⟨hv1, hp1⟩ => ?_)
  refine Completes.append (m := sLaneBase j + 25) (by omega) (by omega)
    (nb_copyS (d := sLaneBase j + 24) vA) (copyS_complete σ1 (sLaneBase j + 24) vA)
    (fun σ2 he2 hv2 => ?_)
  have hmk2 : ∀ t < 5, σ2 (.n (7 + 8 * j + t)) = ofK (addressOfIndex (M / 256 ^ (8 * j + 3) / 256 ^ t % 256)) :=
    fun t ht => by
      rw [he2.apply (Or.inl (by rw [hL]; omega)), he1.apply (Or.inl (by rw [hL]; omega)), div_256_pow,
        show 7 + 8 * j + t = 4 + 8 * j + (t + 3) by omega, show 8 * j + 3 + t = 8 * j + (t + 3) by omega]
      exact hmk (t + 3) (by omega)
  refine Completes.append (m := sLaneBase j + 67) (by omega) (by omega) nB
    (sFromMarks_complete (b := 7 + 8 * j) (n := 5) (x := sLaneBase j + 25) (X := M / 256 ^ (8 * j + 3)) hm
      hbb (by norm_num) (by norm_num) σ2 (by omega)
      (by rw [hL]; omega) hmk2
      (by rw [he2.apply (Or.inl (by rw [hL]; omega)), he1.apply (Or.inl (by rw [hL]; omega))]; exact h1))
    (fun σ3 he3 ⟨hv3, hp3⟩ => ?_)
  obtain ⟨σ4, he4, hv4, hh4⟩ := copyS_complete (C := C) (rd := rd) σ3 (sLaneBase j + 67) vB
  refine ⟨σ4, he4, ⟨?_, ?_, fun k hk => ?_, fun k hk => ?_⟩, hh4⟩
  · rw [show sLo j = .n (sLaneBase j + 24) from rfl, he4.apply (Or.inl (by omega)),
      he3.apply (Or.inl (by omega)), hv2]
    exact hv1
  · rw [show sHi j = .n (sLaneBase j + 67) from rfl, hv4]
    exact hv3
  · have hk' : fbPtr (sLaneBase j) k < sLaneBase j + 24 := by simp only [fbPtr]; split <;> omega
    rw [he4.apply (Or.inl (by omega)), he3.apply (Or.inl (by omega)), he2.apply (Or.inl (by omega))]
    exact hp1 k hk
  · have hk' : fbPtr (sLaneBase j + 25) k < sLaneBase j + 67 := by simp only [fbPtr]; split <;> omega
    rw [he4.apply (Or.inl (by omega))]
    exact hp3 k hk

theorem sLaneBytes_nb {j : Nat} (hj : j < 4) : NumBelow (sLaneBase j + 68) (Stmt.valsList (sLaneBytes j)) := by
  interval_cases j <;> exact numBelow_of_all (by decide +kernel)

/-- What a lane's bytes give. -/
def LaneAt (σ : Val) (bb : E) (M j : Nat) : Prop :=
  σ (sLo j) = eOfNat (M / 256 ^ (8 * j) % 256 ^ 3) ∧ σ (sHi j) = eOfNat (M / 256 ^ (8 * j + 3) % 256 ^ 5) ∧
    (∀ k ≤ 2, BytePtr bb (σ (.n (fbPtr (sLaneBase j) k)))) ∧
    ∀ k ≤ 4, BytePtr bb (σ (.n (fbPtr (sLaneBase j + 25) k)))

theorem LaneAt.congr {σ σ' : Val} {bb : E} {M j : Nat} (h : LaneAt σ bb M j)
    (hσ : ∀ k < sLaneBase j + 68, σ' (.n k) = σ (.n k)) : LaneAt σ' bb M j := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨by rw [show sLo j = .n (sLaneBase j + 24) from rfl, hσ _ (by omega)]; exact h1,
    by rw [show sHi j = .n (sLaneBase j + 67) from rfl, hσ _ (by omega)]; exact h2, fun k hk => ?_,
    fun k hk => ?_⟩
  · rw [hσ _ (by simp only [fbPtr]; split <;> omega)]; exact h3 k hk
  · rw [hσ _ (by simp only [fbPtr]; split <;> omega)]; exact h4 k hk

theorem lanes_nb : ∀ n ≤ 4, NumBelow (36 + 68 * n) (Stmt.valsList ((List.range n).flatMap sLaneBytes))
  | 0, _ => fun v hv => by simp at hv
  | n + 1, hn => by
      rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, valsList_append]
      exact ((lanes_nb n (by omega)).mono (by omega)).append
        ((sLaneBytes_nb (j := n) (by omega)).mono (by simp only [sLaneBase]; omega))

/-- **The first `n ≤ 4` lanes complete.** -/
theorem sLanesBytes_complete (hm : MemOK rd 256) {bb : E} (hbb : ByteBits rd bb) {M : Nat} (σ : Val)
    (hmk : ∀ t < 32, σ (.n (4 + t)) = ofK (addressOfIndex (M / 256 ^ t % 256))) (h1 : σ (.n 1) = bb) :
    ∀ n ≤ 4, Completes C rd 36 (36 + 68 * n) ((List.range n).flatMap sLaneBytes) σ
      (fun σ' => ∀ j < n, LaneAt σ' bb M j)
  | 0, _ => Completes.nil' fun j hj => absurd hj (by omega)
  | n + 1, hn => by
      rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
      refine Completes.append (m := 36 + 68 * n) (by omega) (by omega) (lanes_nb n (by omega))
        (sLanesBytes_complete hm hbb σ hmk h1 n (by omega)) (fun σ1 he1 hp1 => ?_)
      have hmk1 : ∀ t < 8, σ1 (.n (4 + 8 * n + t)) = ofK (addressOfIndex (M / 256 ^ (8 * n + t) % 256)) := by
        intro t ht
        rw [he1.apply (Or.inl (by omega)), show 4 + 8 * n + t = 4 + (8 * n + t) by omega]
        exact hmk _ (by omega)
      have h11 : σ1 (.n 1) = bb := by rw [he1.apply (Or.inl (by omega))]; exact h1
      have hc : Completes C rd (36 + 68 * n) (sLaneBase n + 68) (sLaneBytes n) σ1
          (fun σ' => LaneAt σ' bb M n) := sLaneBytes_complete hm hbb σ1 hmk1 h11
      refine ((hc.keep (Q := fun σ' => ∀ j < n, LaneAt σ' bb M j)
        (Q' := fun σ' => ∀ j < n, LaneAt σ' bb M j) hp1 (fun σ' he _ j hj => (hp1 j hj).congr fun k hk =>
          he.apply (Or.inl (by simp only [sLaneBase] at hk ⊢; omega))))).mono le_rfl
          (by simp only [sLaneBase]; omega) ?_
      rintro σ' ⟨hl, hr⟩ j hj
      rcases (show j < n ∨ j = n by omega) with h | rfl
      · exact hr j h
      · exact hl

/-! ## The message -/

/-- A message check's first three statements: `lane[2k] + lane[2k + 1] · y`. -/
def mc3 (k b : Nat) : List Stmt :=
  [cst b (word 0 1 0), mulS (.n (b + 1)) (sLane (2 * k + 1)) (.n b), addS (.n (b + 2)) (sLane (2 * k)) (.n (b + 1))]

theorem sMsg_eq : sMsg = loadS sPP (.n 0) 0 :: loadS sRoot (.n 0) 1 :: hintW "sp_msg" (runV 4 32) ::
    ((List.range 4).flatMap sLaneBytes ++ (sLanes ++ (mc3 0 320 ++ (loadS (.n 323) (.n 0) 2 ::
      (.atom (.assertEq (.n 322) (.n 323)) :: (mc3 1 324 ++ (loadS (.n 327) (.n 0) 3 ::
        (.atom (.assertEq (.n 326) (.n 327)) :: sMCells)))))))) := by
  simp [sMsg, sMsgCheck, mc3]

theorem mc3_val {k b l0 l1 : Nat} {σ : Val} (hl0 : l0 < 2 ^ 64) (hl1 : l1 < 2 ^ 64)
    (h0 : σ (sLane (2 * k)) = eOfNat l0) (h1 : σ (sLane (2 * k + 1)) = eOfNat l1)
    (h : AtomsHold rd σ (mc3 k b)) : σ (.n (b + 2)) = eOfNat192 (l0 + 2 ^ 64 * l1) := by
  have c : σ (.n b) = word 0 1 0 := h.atom (a := .const _ _) (by simp [mc3, cst])
  have m : σ (.n (b + 1)) = σ (sLane (2 * k + 1)) * σ (.n b) := h.atom (a := .mul _ _ _) (by simp [mc3, mulS])
  have a : σ (.n (b + 2)) = σ (sLane (2 * k)) + σ (.n (b + 1)) := h.atom (a := .add _ _ _) (by simp [mc3, addS])
  rw [a, m, c, h0, h1, mul_word_y hl1, eOfNat_eq192 hl0, eOfNat192_add_shift hl0]

/-- `M'`'s cells from the lanes' parts. -/
theorem sMCells_vals {σ : Val} {lo hi : Nat → Nat} (hlo : ∀ j < 4, lo j < 2 ^ 24) (hhi : ∀ j < 4, hi j < 2 ^ 40)
    (el : ∀ j < 4, σ (sLo j) = eOfNat (lo j)) (eh : ∀ j < 4, σ (sHi j) = eOfNat (hi j))
    (hC : AtomsHold rd σ sMCells) :
    σ sM0 = eOfNat192 (framingNat + 2 ^ 104 * lo 0) ∧
      σ sM1 = eOfNat192 (2 ^ 40 * lo 1 + hi 0 + 2 ^ 64 * (2 ^ 40 * lo 2 + hi 1)) ∧
      σ sM2 = eOfNat192 (2 ^ 40 * lo 3 + hi 2 + 2 ^ 64 * hi 3) := by
  have a0 := hlo 0 (by norm_num); have a1 := hlo 1 (by norm_num); have a2 := hlo 2 (by norm_num)
  have a3 := hlo 3 (by norm_num); have b0 := hhi 0 (by norm_num); have b1 := hhi 1 (by norm_num)
  have b2 := hhi 2 (by norm_num); have b3 := hhi 3 (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · have k8 : σ (.n 328) = spFraming := hC.atom (a := .const _ _) (by simp [sMCells, cst])
    have k9 : σ (.n 329) = pw 104 := hC.atom (a := .const _ _) (by simp [sMCells, cst])
    have m : σ (.n 330) = σ (sLo 0) * σ (.n 329) := hC.atom (a := .mul _ _ _) (by simp [sMCells, mulS])
    have ad : σ sM0 = σ (.n 328) + σ (.n 330) := hC.atom (a := .add sM0 _ _) (by simp [sMCells, addS])
    rw [ad, m, k8, k9, el 0 (by norm_num), spFraming_eq, pw_mul (by norm_num) (by norm_num; omega),
      eOfNat192_add_shift (by norm_num [framingNat])]
  · have hA1 := loHi_sound (x := 332) a1 b0 (el 1 (by norm_num)) (eh 0 (by norm_num)) (hC.sub fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl | rfl <;> simp [sMCells])
    have hA2 := loHi_sound (x := 335) a2 b1 (el 2 (by norm_num)) (eh 1 (by norm_num)) (hC.sub fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl | rfl <;> simp [sMCells])
    have k : σ (.n 338) = word 0 1 0 := hC.atom (a := .const _ _) (by simp [sMCells, cst])
    have m : σ (.n 339) = σ (.n 337) * σ (.n 338) := hC.atom (a := .mul _ _ _) (by simp [sMCells, mulS])
    have ad : σ sM1 = σ (.n 334) + σ (.n 339) := hC.atom (a := .add sM1 _ _) (by simp [sMCells, addS])
    rw [ad, m, k, hA2, hA1, mul_word_y (by omega), eOfNat_eq192 (by omega), eOfNat192_add_shift (by omega)]
  · have hA3 := loHi_sound (x := 341) a3 b2 (el 3 (by norm_num)) (eh 2 (by norm_num)) (hC.sub fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl | rfl <;> simp [sMCells])
    have k : σ (.n 344) = word 0 1 0 := hC.atom (a := .const _ _) (by simp [sMCells, cst])
    have m : σ (.n 345) = σ (sHi 3) * σ (.n 344) := hC.atom (a := .mul _ _ _) (by simp [sMCells, mulS])
    have ad : σ sM2 = σ (.n 343) + σ (.n 345) := hC.atom (a := .add sM2 _ _) (by simp [sMCells, addS])
    rw [ad, m, k, hA3, eh 3 (by norm_num), mul_word_y (by omega), eOfNat_eq192 (by omega),
      eOfNat192_add_shift (by omega)]

/-- **The message completes**: the claim's keys loaded, the message's bytes hinted from `M`, its
lanes rebuilt and checked against the claim's message cells, and `M'`'s cells laid out. -/
theorem sMsg_complete (hm : MemOK rd 256) {bb p Pc Rc : E} (hbb : ByteBits rd bb) {M : Nat}
    (hM : M < 2 ^ 256) (hcl : ClaimAt rd p Pc Rc (eOfNat192 (M % 2 ^ 128)) (eOfNat192 (M / 2 ^ 128)))
    (σ : Val) (h0 : σ (.n 0) = p) (h1 : σ (.n 1) = bb) :
    Completes C rd 2 347 sMsg σ (fun σ' => σ' sPP = Pc ∧ σ' sRoot = Rc ∧
      σ' sM0 = eOfNat192 ((framingNat + 2 ^ 104 * M) % 2 ^ 128) ∧
      σ' sM1 = eOfNat192 ((framingNat + 2 ^ 104 * M) / 2 ^ 128 % 2 ^ 128) ∧
      σ' sM2 = eOfNat192 ((framingNat + 2 ^ 104 * M) / 2 ^ 256) ∧ ∀ j < 4, LaneAt σ' bb M j) := by
  obtain ⟨c0, c1, c2, c3⟩ := hcl
  rw [sMsg_eq]
  refine Completes.load ⟨0, by norm_num, rfl⟩ (w := Pc) (by rw [h0]; exact c0) (by norm_num)
    (fun σ1 he1 e1 => ?_)
  refine Completes.load ⟨0, by norm_num, rfl⟩ (w := Rc) (by rw [he1.apply (Or.inl (by norm_num)), h0]; exact c1)
    (by norm_num) (fun σ2 he2 e2 => ?_)
  set f : Nat → E := fun k => ofK (addressOfIndex (M / 256 ^ k % 256)) with hf
  refine Completes.reload ((updRun_ext σ2 4 32 f).mono le_rfl (by norm_num)) ?_
  set σr := updRun σ2 4 32 f with hσr
  have hmk : ∀ t < 32, σr (.n (4 + t)) = f t := fun t ht => updRun_at σ2 4 32 f ht
  have r0 : σr (.n 0) = p := by
    rw [hσr, updRun_below σ2 4 32 f ⟨0, by norm_num, rfl⟩, he2.apply (Or.inl (by norm_num)),
      he1.apply (Or.inl (by norm_num)), h0]
  have r1 : σr (.n 1) = bb := by
    rw [hσr, updRun_below σ2 4 32 f ⟨1, by norm_num, rfl⟩, he2.apply (Or.inl (by norm_num)),
      he1.apply (Or.inl (by norm_num)), h1]
  have r2 : σr (.n 2) = Pc := by
    rw [hσr, updRun_below σ2 4 32 f ⟨2, by norm_num, rfl⟩, he2.apply (Or.inl (by norm_num))]; exact e1
  have r3 : σr (.n 3) = Rc := by rw [hσr, updRun_below σ2 4 32 f ⟨3, by norm_num, rfl⟩]; exact e2
  refine Completes.append (xs := [hintW "sp_msg" (runV 4 32)]) (m := 36) (by norm_num) (by norm_num)
    (by rw [valsList_hint]; exact numBelow_of_all (by decide)) (hintKeep_complete _ _ _ _ _)
    (fun σ3 _ e3 => ?_)
  subst e3
  refine Completes.append (m := 308) (by norm_num) (by norm_num) (lanes_nb 4 le_rfl)
    (sLanesBytes_complete hm hbb σr hmk r1 4 le_rfl) (fun σ4 he4 hp4 => ?_)
  refine Completes.seq (m := 320) (seqB_ok (by decide +kernel)) (by norm_num) (fun σ5 he5 hh5 => ?_)
  have t5 : ∀ k < 308, σ5 (.n k) = σ4 (.n k) := fun k hk => he5.apply (Or.inl hk)
  have t4 : ∀ k < 36, σ4 (.n k) = σr (.n k) := fun k hk => he4.apply (Or.inl hk)
  have lan5 : ∀ j < 4, LaneAt σ5 bb M j := fun j hj => (hp4 j hj).congr fun k hk =>
    t5 k (by simp only [sLaneBase] at hk; omega)
  have hlo : ∀ j < 4, M / 256 ^ (8 * j) % 256 ^ 3 < 2 ^ 24 := fun j _ => by
    have := Nat.mod_lt (M / 256 ^ (8 * j)) (show 256 ^ 3 > 0 by norm_num); norm_num at this ⊢; omega
  have hhi : ∀ j < 4, M / 256 ^ (8 * j + 3) % 256 ^ 5 < 2 ^ 40 := fun j _ => by
    have := Nat.mod_lt (M / 256 ^ (8 * j + 3)) (show 256 ^ 5 > 0 by norm_num); norm_num at this ⊢; omega
  have lane : ∀ j < 4, σ5 (sLane j) = eOfNat (M / 256 ^ (8 * j) % 256 ^ 3 +
      2 ^ 24 * (M / 256 ^ (8 * j + 3) % 256 ^ 5)) := fun j hj =>
    sLane_sound hj (hlo j hj) hh5 (lan5 j hj).1 (lan5 j hj).2.1 (hhi j hj)
  have lnat : ∀ j < 4, M / 256 ^ (8 * j) % 256 ^ 3 + 2 ^ 24 * (M / 256 ^ (8 * j + 3) % 256 ^ 5) =
      M / 2 ^ (64 * j) % 2 ^ 64 := fun j _ => by
    rw [show (256 : Nat) ^ (8 * j + 3) = 256 ^ (8 * j) * 256 ^ 3 by rw [pow_add], ← Nat.div_div_eq_div_mul,
      show (2 : Nat) ^ (64 * j) = 256 ^ (8 * j) by rw [show 64 * j = 8 * (8 * j) by ring, pow_mul]; norm_num]
    generalize M / 256 ^ (8 * j) = X
    norm_num
    omega
  have hl64 : ∀ j < 4, M / 2 ^ (64 * j) % 2 ^ 64 < 2 ^ 64 := fun j _ => Nat.mod_lt _ (by norm_num)
  -- the message's first cell
  refine Completes.seq (m := 323) (xs := mc3 0 320) (seqB_ok (by decide +kernel)) (by norm_num)
    (fun σ6 he6 hh6 => ?_)
  have t65 : ∀ k < 320, σ6 (.n k) = σ5 (.n k) := fun k hk => he6.apply (Or.inl hk)
  have v322 : σ6 (.n 322) = eOfNat192 (M % 2 ^ 128) := by
    rw [mc3_val (hl64 0 (by norm_num)) (hl64 1 (by norm_num))
      (by rw [show sLane (2 * 0) = .n 310 from rfl, t65 _ (by norm_num), ← lnat 0 (by norm_num)]
          exact lane 0 (by norm_num))
      (by rw [show sLane (2 * 0 + 1) = .n 313 from rfl, t65 _ (by norm_num), ← lnat 1 (by norm_num)]
          exact lane 1 (by norm_num)) hh6]
    congr 1; omega
  have p6 : σ6 (.n 0) = p := by
    rw [t65 0 (by norm_num), t5 0 (by norm_num), t4 0 (by norm_num)]; exact r0
  refine Completes.load ⟨0, by norm_num, rfl⟩ (w := eOfNat192 (M % 2 ^ 128)) (by rw [p6]; exact c2)
    (by norm_num) (fun σ7 he7 e7 => ?_)
  refine Completes.checks (xs := [.atom (.assertEq (.n 322) (.n 323))]) rfl (fun a ha => by
      simp only [List.mem_singleton, Stmt.atom.injEq] at ha
      subst ha
      show σ7 (.n 322) + σ7 (.n 323) = 0
      rw [e7, he7.apply (Or.inl (by norm_num)), v322, e_add_self])
    (numBelow_of_all (by decide)) (by norm_num) ?_
  -- the message's second cell
  refine Completes.seq (m := 327) (xs := mc3 1 324) (seqB_ok (by decide +kernel)) (by norm_num)
    (fun σ8 he8 hh8 => ?_)
  have t85 : ∀ k < 320, σ8 (.n k) = σ5 (.n k) := fun k hk => by
    rw [he8.apply (Or.inl (by omega)), he7.apply (Or.inl (by omega)), t65 k hk]
  have v326 : σ8 (.n 326) = eOfNat192 (M / 2 ^ 128) := by
    rw [mc3_val (hl64 2 (by norm_num)) (hl64 3 (by norm_num))
      (by rw [show sLane (2 * 1) = .n 316 from rfl, t85 _ (by norm_num), ← lnat 2 (by norm_num)]
          exact lane 2 (by norm_num))
      (by rw [show sLane (2 * 1 + 1) = .n 319 from rfl, t85 _ (by norm_num), ← lnat 3 (by norm_num)]
          exact lane 3 (by norm_num)) hh8]
    congr 1; omega
  refine Completes.load ⟨0, by norm_num, rfl⟩ (w := eOfNat192 (M / 2 ^ 128))
    (by rw [t85 0 (by norm_num), t5 0 (by norm_num), t4 0 (by norm_num), r0]; exact c3)
    (by norm_num) (fun σ9 he9 e9 => ?_)
  refine Completes.checks (xs := [.atom (.assertEq (.n 326) (.n 327))]) rfl (fun a ha => by
      simp only [List.mem_singleton, Stmt.atom.injEq] at ha
      subst ha
      show σ9 (.n 326) + σ9 (.n 327) = 0
      rw [e9, he9.apply (Or.inl (by norm_num)), v326, e_add_self])
    (numBelow_of_all (by decide)) (by norm_num) ?_
  -- `M'`'s cells
  obtain ⟨σ10, he10, hh10, hk10⟩ := seq_completes (C := C) (rd := rd) (b := 328) (b' := 347)
    (ss := sMCells) (seqB_ok (by decide +kernel)) σ9
  have t10 : ∀ k < 320, σ10 (.n k) = σ5 (.n k) := fun k hk => by
    rw [he10.apply (Or.inl (by omega)), he9.apply (Or.inl (by omega)), t85 k hk]
  have vals := sMCells_vals (σ := σ10) (lo := fun j => M / 256 ^ (8 * j) % 256 ^ 3)
    (hi := fun j => M / 256 ^ (8 * j + 3) % 256 ^ 5) hlo hhi
    (fun j hj => by
      rw [show sLo j = .n (sLaneBase j + 24) from rfl, t10 _ (by simp only [sLaneBase]; omega)]
      exact (lan5 j hj).1)
    (fun j hj => by
      rw [show sHi j = .n (sLaneBase j + 67) from rfl, t10 _ (by simp only [sLaneBase]; omega)]
      exact (lan5 j hj).2.1) hh10
  obtain ⟨m0, m1, m2⟩ := vals
  refine ⟨σ10, he10, ⟨?_, ?_, ?_, ?_, ?_, fun j hj => (lan5 j hj).congr fun k hk => t10 k
    (by simp only [sLaneBase] at hk; omega)⟩, hk10⟩
  · rw [show sPP = .n 2 from rfl, t10 2 (by norm_num), t5 2 (by norm_num), t4 2 (by norm_num)]; exact r2
  · rw [show sRoot = .n 3 from rfl, t10 3 (by norm_num), t5 3 (by norm_num), t4 3 (by norm_num)]; exact r3
  · rw [m0]; congr 1; simp only [framingNat]; omega
  · rw [m1]; congr 1; simp only [framingNat]; omega
  · rw [m2]; congr 1; simp only [framingNat]; omega

end
end LeanVM.Guest.B1.Sig
