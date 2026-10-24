/-
  LeanVM.Guest.B1.KeccakGkr.VkCA

  `verify_keccak`'s head, completely: `y` in the exponent, the copies, the point, the squeezes, the
  committed word.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.VkHead
public import LeanVM.Guest.B1.KeccakGkr.VkCSpec

/-!
# The head, completely

`vkBits_complete`: on a valuation satisfying the equations of `vkBitsT` but its pins, the bits of
`y = τ - 3` hinted, `y` in the exponent (`y_g`, `half_g`, `odd_g`, `y_last`) is computed and the
section holds (its pins and its check).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd

@[expose] public section

variable {C : CallRel} {rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val}

theorem bitE_mul_self (b : Bool) : bitE b * bitE b = bitE b := by cases b <;> simp [bitE]

theorem half_bits {y : ℕ} (hy : y < 32) :
    bitsVal (fun j ↦ y.testBit (j + 1)) 4 = y / 2 := by
  interval_cases y <;> rfl

theorem word3 : word 3 0 0 = gen ^ 2 ^ 0 + 1 := by
  rw [word_eOfNat, show (3 : ℕ) = 2 ^ 1 ^^^ 1 from rfl, eOfNat_xor, eOfNat_one,
    ← word_eOfNat, word_two_pow (by decide)]; simp

theorem word5 : word 5 0 0 = gen ^ 2 ^ 1 + 1 := by
  rw [word_eOfNat, show (5 : ℕ) = 2 ^ 2 ^^^ 1 from rfl, eOfNat_xor, eOfNat_one,
    ← word_eOfNat, word_two_pow (by decide)]; norm_num

theorem word17 : word 17 0 0 = gen ^ 2 ^ 2 + 1 := by
  rw [word_eOfNat, show (17 : ℕ) = 2 ^ 4 ^^^ 1 from rfl, eOfNat_xor, eOfNat_one,
    ← word_eOfNat, word_two_pow (by decide)]; norm_num

theorem word257 : word 257 0 0 = gen ^ 2 ^ 3 + 1 := by
  rw [word_eOfNat, show (257 : ℕ) = 2 ^ 8 ^^^ 1 from rfl, eOfNat_xor, eOfNat_one,
    ← word_eOfNat, word_two_pow (by decide)]; norm_num

theorem mulG {d x y : ℕ} (hx : x < d) (hy : y < d)
    (h : Good rd S w σ (.mul (.n d) (.n x) (.n y))) : σ (.n d) = σ (.n x) * σ (.n y) := by
  simp only [Good] at h
  rwa [ite_pos' ⟨hx, hy⟩] at h

set_option maxRecDepth 20000 in
/-- **`y` in the exponent, completely.** -/
theorem vkBits_complete {τ : ℕ} (hτ1 : 9 ≤ τ) (hτ2 : τ ≤ 28)
    (hg : ∀ s ∈ vkBitsT, pinB s = false → GoodS rd S w σ s) (h6 : σ (.n 6) = gen ^ τ)
    (hbits : ∀ j < 5, σ (.n (20 + j)) = bitE ((τ - 3).testBit j)) :
    σ (.n 17) = gen ^ (τ - 4) ∧ σ (.n 19) = gen ^ (τ - 3) ∧
      σ (.n 43) = gen ^ ((τ - 3) / 2) ∧ σ (.n 47) = gen ^ ((τ - 3) % 2) ∧
      σ (.n 48) = gen ^ ((τ - 3) / 2 + (τ - 3) % 2) ∧
      ∀ {next : Prop} {kret : List E → Prop}, next → Stmt.HoldsList C rd σ vkBitsT next kret := by
  have gd : ∀ a, Stmt.atom a ∈ vkBitsT → pinB (.atom a) = false → Good rd S w σ a :=
    fun a h hp ↦ hg _ h hp
  have c16 := gd (.const (.n 16) (word 8070450532247928836 0 0)) (by simp [vkBitsT]) rfl
  have m17 := mulG (by norm_num) (by norm_num) (gd (.mul (.n 17) (.n 6) (.n 16)) (by simp [vkBitsT]) rfl)
  have c18 := gd (.const (.n 18) (word 2 0 0)) (by simp [vkBitsT]) rfl
  have m19 := mulG (by norm_num) (by norm_num) (gd (.mul (.n 19) (.n 17) (.n 18)) (by simp [vkBitsT]) rfl)
  have c25 := gd (.const (.n 25) (word 1 0 0)) (by simp [vkBitsT]) rfl
  have c26 := gd (.const (.n 26) (word 3 0 0)) (by simp [vkBitsT]) rfl
  have m27 := mulG (by norm_num) (by norm_num) (gd (.mul (.n 27) (.n 21) (.n 26)) (by simp [vkBitsT]) rfl)
  have a28 := gd (.add (.n 28) (.n 25) (.n 27)) (by simp [vkBitsT]) rfl
  have c29 := gd (.const (.n 29) (word 1 0 0)) (by simp [vkBitsT]) rfl
  have c30 := gd (.const (.n 30) (word 5 0 0)) (by simp [vkBitsT]) rfl
  have m31 := mulG (by norm_num) (by norm_num) (gd (.mul (.n 31) (.n 22) (.n 30)) (by simp [vkBitsT]) rfl)
  have a32 := gd (.add (.n 32) (.n 29) (.n 31)) (by simp [vkBitsT]) rfl
  have m33 := mulG (by norm_num) (by norm_num) (gd (.mul (.n 33) (.n 28) (.n 32)) (by simp [vkBitsT]) rfl)
  have c34 := gd (.const (.n 34) (word 1 0 0)) (by simp [vkBitsT]) rfl
  have c35 := gd (.const (.n 35) (word 17 0 0)) (by simp [vkBitsT]) rfl
  have m36 := mulG (by norm_num) (by norm_num) (gd (.mul (.n 36) (.n 23) (.n 35)) (by simp [vkBitsT]) rfl)
  have a37 := gd (.add (.n 37) (.n 34) (.n 36)) (by simp [vkBitsT]) rfl
  have m38 := mulG (by norm_num) (by norm_num) (gd (.mul (.n 38) (.n 33) (.n 37)) (by simp [vkBitsT]) rfl)
  have c39 := gd (.const (.n 39) (word 1 0 0)) (by simp [vkBitsT]) rfl
  have c40 := gd (.const (.n 40) (word 257 0 0)) (by simp [vkBitsT]) rfl
  have m41 := mulG (by norm_num) (by norm_num) (gd (.mul (.n 41) (.n 24) (.n 40)) (by simp [vkBitsT]) rfl)
  have a42 := gd (.add (.n 42) (.n 39) (.n 41)) (by simp [vkBitsT]) rfl
  have m43 := mulG (by norm_num) (by norm_num) (gd (.mul (.n 43) (.n 38) (.n 42)) (by simp [vkBitsT]) rfl)
  have c44 := gd (.const (.n 44) (word 1 0 0)) (by simp [vkBitsT]) rfl
  have c45 := gd (.const (.n 45) (word 3 0 0)) (by simp [vkBitsT]) rfl
  have m46 := mulG (by norm_num) (by norm_num) (gd (.mul (.n 46) (.n 20) (.n 45)) (by simp [vkBitsT]) rfl)
  have a47 := gd (.add (.n 47) (.n 44) (.n 46)) (by simp [vkBitsT]) rfl
  have m48 := mulG (by norm_num) (by norm_num) (gd (.mul (.n 48) (.n 43) (.n 47)) (by simp [vkBitsT]) rfl)
  have m49 := mulG (by norm_num) (by norm_num) (gd (.mul (.n 49) (.n 43) (.n 48)) (by simp [vkBitsT]) rfl)
  have c50 := gd (.const (.n 50) (word 2 0 0)) (by simp [vkBitsT]) rfl
  have m51 := mulG (by norm_num) (by norm_num) (gd (.mul (.n 51) (.n 17) (.n 50)) (by simp [vkBitsT]) rfl)
  simp only [Good] at c16 c18 c25 c26 a28 c29 c30 a32 c34 c35 a37 c39 c40 a42 c44 c45 a47 c50
  set y := τ - 3 with hy
  have hy32 : y < 32 := by omega
  have b0 := hbits 0 (by norm_num)
  have b1 := hbits 1 (by norm_num)
  have b2 := hbits 2 (by norm_num)
  have b3 := hbits 3 (by norm_num)
  have b4 := hbits 4 (by norm_num)
  simp only [Nat.add_zero, Nat.reduceAdd] at b0 b1 b2 b3 b4
  have h17 : σ (.n 17) = gen ^ (τ - 4) := by
    rw [m17, h6, c16, show τ = τ - 4 + 4 by omega, pow_add, mul_assoc, mul_comm (gen ^ 4),
      word_ginv4_mul, mul_one]
    congr 1
  have h19 : σ (.n 19) = gen ^ (τ - 3) := by
    rw [m19, h17, c18, word_gen, ← pow_succ]; congr 1; omega
  have h43 : σ (.n 43) = gen ^ (y / 2) := by
    rw [m43, a42, m41, c40, c39, m38, a37, m36, c35, c34, m33, a32, m31, c30, c29, a28, m27, c26, c25,
      b1, b2, b3, b4, word_one, word3, word5, word17, word257, ← half_bits hy32,
      ← prod_bitE_gen_pow]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
  have h47 : σ (.n 47) = gen ^ (y % 2) := by
    rw [a47, m46, c45, c44, b0, word_one, word3]
    rcases Nat.mod_two_eq_zero_or_one y with h0 | h1
    · rw [h0, show y.testBit 0 = false by simp [Nat.testBit_zero, h0]]; simp [bitE]
    · rw [h1, show y.testBit 0 = true by simp [Nat.testBit_zero, h1]]
      simp only [bitE, ↓reduceIte, one_mul, pow_zero, pow_one]
      rw [add_comm gen 1, ← add_assoc, e_add_self, zero_add]
  have h48 : σ (.n 48) = gen ^ (y / 2 + y % 2) := by rw [m48, h43, h47, ← pow_add]
  refine ⟨h17, h19, h43, h47, h48, fun {next kret} hn ↦ ?_⟩
  simp only [vkBitsT, Stmt.HoldsList, Stmt.Holds, Atom.Holds]
  refine ⟨c16, m17, c18, m19, trivial, ?_, ?_, c25, c26, m27, a28, ?_, c29, c30, m31, a32, m33, ?_,
    c34, c35, m36, a37, m38, ?_, c39, c40, m41, a42, m43, c44, c45, m46, a47, m48, m49, c50, m51,
    ?_, hn⟩
  · rw [b0, bitE_mul_self]
  · rw [b1, bitE_mul_self]
  · rw [b2, bitE_mul_self]
  · rw [b3, bitE_mul_self]
  · rw [b4, bitE_mul_self]
  · rw [m49, m51, h43, h48, h17, c50, word_gen, ← pow_add, ← pow_succ,
      show y / 2 + (y / 2 + y % 2) = τ - 4 + 1 by omega]
    exact e_add_self _

/-- **A squeeze with nothing waiting, completely.** -/
theorem sqZero_complete {capb o : ℕ} (hσ : ∀ v, σ v = σ (.n v.idx))
    (hk : canonChk [capb, capb + 1, capb + 2, capb + 3, capb + 4, 66, 67, 68, 69]
      (atomsL ([] ++ sqZeroT capb o)) = true)
    (hr : resid (atomsL (sqZeroT capb o)) = [.assertInK (.n (o + 13)) (.n (o + 16))])
    (hg : ∀ s ∈ sqZeroT capb o, GoodS rd S w σ s) (hcap : AllCanonical ((cap5 capb).map σ))
    (hz : ∀ k < 4, σ (.n (66 + k)) = 0) :
    σ (.n (o + 19)) = (⟨(cap5 capb).map σ, []⟩ : Fs).squeeze.1 ∧
      (cap5 (o + 8)).map σ = (⟨(cap5 capb).map σ, []⟩ : Fs).squeeze.2.cap ∧
      ∀ {next : Prop} {kret : List E → Prop}, next →
        Stmt.HoldsList C rd σ (sqZeroT capb o) next kret := by
  have hall : (sqZeroT capb o).all isAtom = true := by simp [sqZeroT, challengeT, keccakA, isAtom]
  have gk : Good rd S w σ (.keccak ([.n 66, .n 66, .n 66, .n 66, .n 66, .n 67, .n 68, .n 69] ++
      cap5 capb) ((List.range 13).map fun k ↦ .n (o + k)) false false) :=
    hg (.atom (.keccak _ _ false false)) (by simp [sqZeroT, keccakA])
  have hzc : IsCanonical128 (0 : E) := by unfold IsCanonical128; exact limb_zero 2
  have hcanI : AllCanonical (([V.n 66, .n 66, .n 66, .n 66, .n 66, .n 67, .n 68, .n 69] ++
      cap5 capb).map σ) := by
    intro c hc
    rw [List.map_append] at hc
    rcases List.mem_append.mp hc with hc | hc
    · simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first
        | (rw [hz 0 (by norm_num)]; exact hzc)
        | (rw [hz 1 (by norm_num)]; exact hzc)
        | (rw [hz 2 (by norm_num)]; exact hzc)
        | (rw [hz 3 (by norm_num)]; exact hzc)
    · exact hcap c hc
  have kc := keccakA_complete gk hcanI
  obtain ⟨-, -, -, hout⟩ := keccak_outs kc
  have c1 : IsCanonical128 (σ (.n (o + 1))) := by
    have := hout 1 (by norm_num)
    simp only [range13_map, List.getD_cons_succ, List.getD_cons_zero] at this
    rw [this]; exact cellsOfState_canonical _ _ _
  have gc : ∀ s ∈ challengeT (.n o) (.n (o + 1)) (o + 13), GoodS rd S w σ s :=
    fun s hs ↦ hg s (by simp [sqZeroT, hs])
  obtain ⟨ch, -⟩ := challenge_complete (C := C) gc c1
  have hA : ∀ i ∈ [capb, capb + 1, capb + 2, capb + 3, capb + 4, 66, 67, 68, 69],
      IsCanonical128 (σ (.n i)) := by
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hcap _ (by simp [cap5])
    · exact hcap _ (by simp [cap5])
    · exact hcap _ (by simp [cap5])
    · exact hcap _ (by simp [cap5])
    · exact hcap _ (by simp [cap5])
    · rw [hz 0 (by norm_num)]; exact hzc
    · rw [hz 1 (by norm_num)]; exact hzc
    · rw [hz 2 (by norm_num)]; exact hzc
    · rw [hz 3 (by norm_num)]; exact hzc
  have H : ∀ {next : Prop} {kret : List E → Prop}, next →
      Stmt.HoldsList C rd σ (sqZeroT capb o) next kret :=
    fun hn ↦ block_holdsP (P := []) hall hσ hk (by simpa using hg) hA
      (by rw [hr]; simp only [List.mem_singleton, forall_eq]; exact Or.inl ⟨ch.2.2.2.1, ch.2.2.2.2.1⟩)
      hn
  obtain ⟨q1, q2, -⟩ := sqZeroT_holds rfl hz (H (next := True) (kret := fun _ ↦ True) trivial)
  exact ⟨q1, q2, H⟩

theorem sq_kernel0 :
    canonChk [11, 12, 13, 14, 15, 66, 67, 68, 69] (atomsL ([] ++ sqZeroT 11 70)) = true ∧
      resid (atomsL (sqZeroT 11 70)) = [.assertInK (.n (70 + 13)) (.n (70 + 16))] := by
  decide +kernel

theorem sq_kernelL : ∀ i < 5,
    canonChk [if i = 0 then 78 else 79 + 20 * i, (if i = 0 then 78 else 79 + 20 * i) + 1,
        (if i = 0 then 78 else 79 + 20 * i) + 2, (if i = 0 then 78 else 79 + 20 * i) + 3,
        (if i = 0 then 78 else 79 + 20 * i) + 4, 66, 67, 68, 69]
      (atomsL ([] ++ sqZeroT (if i = 0 then 78 else 79 + 20 * i) (91 + 20 * i))) = true ∧
    resid (atomsL (sqZeroT (if i = 0 then 78 else 79 + 20 * i) (91 + 20 * i))) =
      [.assertInK (.n (91 + 20 * i + 13)) (.n (91 + 20 * i + 16))] := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
/-- **`verify_keccak`'s head, completely.** -/
theorem vkHead_complete (hσ : ∀ v, σ v = σ (.n v.idx))
    (hg : ∀ s ∈ vkHeadT, pinB s = false → GoodS rd S w σ s)
    (hS7 : ∀ d off, Atom.load d (.n 7) off ∉ S) (hS5 : ∀ d off, Atom.load d (.n 5) off ∉ S)
    {τ : ℕ} (hτ1 : 9 ≤ τ) (hτ2 : τ ≤ 28) (h6 : σ (.n 6) = gen ^ τ)
    (hbits : ∀ j < 5, σ (.n (20 + j)) = bitE ((τ - 3).testBit j)) {chis : List E}
    (hchi : ReadsAt rd (σ (.n 7)) chis) (h4 : 4 ≤ chis.length) {committed : E}
    (hcur : LoadHolds rd (σ (.n 5)) 0 committed)
    (hcapf : AllCanonical [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)]) :
    σ (.n 17) = gen ^ (τ - 4) ∧ σ (.n 19) = gen ^ (τ - 3) ∧
    σ (.n 43) = gen ^ ((τ - 3) / 2) ∧ σ (.n 47) = gen ^ ((τ - 3) % 2) ∧
    σ (.n 48) = gen ^ ((τ - 3) / 2 + (τ - 3) % 2) ∧
    (∀ i < 4, σ (.n (52 + i)) = chis.getD i 0) ∧
    σ (.n 60) = 1 + σ (.n 17) ∧ σ (.n 61) = 1 ∧ σ (.n 63) = σ (.n 7) * gen ^ 4 ∧
    σ (.n 64) = σ (.n 58) * σ (.n 17) ∧
    (⟨[σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)], []⟩ : Fs).squeezeN 1 =
      ([σ (.n 89)], ⟨(cap5 78).map σ, []⟩) ∧
    (⟨(cap5 78).map σ, []⟩ : Fs).squeezeN 5 =
      ((List.range 5).map (fun i ↦ σ (.n (110 + 20 * i))), ⟨(cap5 179).map σ, []⟩) ∧
    σ (.n 191) = committed ∧ FsPackOk σ (.n 191) (191 + 1) dsObserve ∧
    ∀ {next : Prop} {kret : List E → Prop},
      (∀ i < 4, LoadHolds rd (σ (.n 9)) i (σ (.n (52 + i)))) →
      LoadHolds rd (σ (.n 64)) 0 (σ (.n 89)) →
      (∀ i < 5, LoadHolds rd (σ (.n 90)) i (σ (.n (110 + 20 * i)))) → next →
      Stmt.HoldsList (fun _ _ _ ↦ True) rd σ vkHeadT next kret := by
  have hnp2 : (copyWordsT (.n 7) (.n 9) 0 0 52 4 ++ vkPointT ++ vkSqueezesT ++
      fsNextT (.n 5) 0 191).all (fun s ↦ !pinB s) = true := by decide +kernel
  have gx : ∀ s, s ∈ copyWordsT (.n 7) (.n 9) 0 0 52 4 ++ vkPointT ++ vkSqueezesT ++
      fsNextT (.n 5) 0 191 → GoodS rd S w σ s := fun s hs ↦
    hg s (by simp only [vkHeadT, List.mem_append] at hs ⊢; tauto)
      (by have := List.all_eq_true.mp hnp2 s hs; simpa using this)
  -- the copies
  have gcp : ∀ i < 5, σ (.n (11 + i)) = σ (.n i) := fun i hi ↦
    hg (.atom (.copy (.n (11 + i)) (.n i))) (by
      simp only [vkHeadT, List.mem_append, List.mem_map, List.mem_range]
      exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨i, hi, rfl⟩))))) rfl
  -- the bits
  obtain ⟨h17, h19, h43, h47, h48, HB⟩ := vkBits_complete (C := fun _ _ _ ↦ True) hτ1 hτ2
    (fun s hs hp ↦ hg s (by simp only [vkHeadT, List.mem_append]; tauto) hp) h6 hbits
  -- the copied words
  have gcw : ∀ s ∈ copyWordsT (.n 7) (.n 9) 0 0 52 4, GoodS rd S w σ s := fun s hs ↦
    gx s (by simp only [List.mem_append]; tauto)
  have e52 : ∀ i < 4, σ (.n (52 + i)) = chis.getD i 0 := by
    intro i hi
    have g := gcw (.atom (.load (.n (52 + i)) (.n 7) (0 + i))) (by
      simp only [copyWordsT, List.mem_flatten, List.mem_map, List.mem_range]
      exact ⟨_, ⟨i, hi, rfl⟩, by simp⟩)
    exact load_val (w := w) g (hS7 _ _)
      (by rw [zero_add, List.getD_eq_getElem _ _ (by omega)]; exact hchi i (by omega))
  -- the point
  have gp : ∀ s ∈ vkPointT, GoodS rd S w σ s := fun s hs ↦
    gx s (by simp only [List.mem_append]; tauto)
  have gp' := gp
  simp only [vkPointT, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
    and_true, GoodS] at gp'
  obtain ⟨c56, m57, -, c59, a60, c61, c62, m63, -, m64, c65, z66, z67, z68, z69⟩ := gp'
  have m57' := mulG (by norm_num) (by norm_num) m57
  have m63' := mulG (by norm_num) (by norm_num) m63
  have m64' := mulG (by norm_num) (by norm_num) m64
  simp only [Good] at c56 c59 a60 c61 c62 c65 z66 z67 z68 z69
  have hz : ∀ k < 4, σ (.n (66 + k)) = 0 := by
    intro k hk
    interval_cases k
    · rw [z66, word_zero]
    · rw [z67, word_zero]
    · rw [z68, word_zero]
    · rw [z69, word_zero]
  have e60 : σ (.n 60) = 1 + σ (.n 17) := by rw [a60, c59, word_one]
  have e63 : σ (.n 63) = σ (.n 7) * gen ^ 4 := by rw [m63', c62, word_16]
  -- the squeezes
  have gsq : ∀ s ∈ vkSqueezesT, GoodS rd S w σ s := fun s hs ↦
    gx s (by simp only [List.mem_append]; tauto)
  -- the segment's squeeze
  have hcap11 : (cap5 11).map σ = [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)] := by
    simp only [cap5, List.map_cons, List.map_nil]
    rw [gcp 0 (by omega), gcp 1 (by omega), gcp 2 (by omega), gcp 3 (by omega), gcp 4 (by omega)]
  have gs0 : ∀ s ∈ sqZeroT 11 70, GoodS rd S w σ s := fun s hs ↦
    gsq s (List.mem_append_left _ (List.mem_append_left _ hs))
  obtain ⟨q0c, q0p, H0⟩ := sqZero_complete (C := fun _ _ _ ↦ True) hσ sq_kernel0.1 sq_kernel0.2
    gs0 (by rw [hcap11]; exact hcapf) hz
  rw [hcap11] at q0c q0p
  -- the lanes' squeezes
  have step : ∀ i < 5, AllCanonical ((cap5 (if i = 0 then 78 else 79 + 20 * i)).map σ) →
      σ (.n (91 + 20 * i + 19)) =
          (⟨(cap5 (if i = 0 then 78 else 79 + 20 * i)).map σ, []⟩ : Fs).squeeze.1 ∧
        (cap5 (91 + 20 * i + 8)).map σ =
          (⟨(cap5 (if i = 0 then 78 else 79 + 20 * i)).map σ, []⟩ : Fs).squeeze.2.cap ∧
        ∀ {next : Prop} {kret : List E → Prop}, next →
          Stmt.HoldsList (fun _ _ _ ↦ True) rd σ
            (sqZeroT (if i = 0 then 78 else 79 + 20 * i) (91 + 20 * i)) next kret := by
    intro i hi hc
    exact sqZero_complete hσ (sq_kernelL i hi).1 (sq_kernelL i hi).2
      (fun s hs ↦ gsq s (List.mem_append_right _ (List.mem_flatten.mpr
        ⟨_, List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩, List.mem_append_left _ hs⟩))) hc hz
  have canc : ∀ i < 5, AllCanonical ((cap5 (if i = 0 then 78 else 79 + 20 * i)).map σ) := by
    intro i
    induction i with
    | zero =>
      intro _
      show AllCanonical ((cap5 (70 + 8)).map σ)
      rw [q0p]; exact squeeze_cap_canonical _
    | succ i ih =>
      intro hi
      have := (step i (by omega) (ih (by omega))).2.1
      simp only [Nat.add_one_ne_zero, ↓reduceIte]
      rw [show 79 + 20 * (i + 1) = 91 + 20 * i + 8 by ring, this]
      exact squeeze_cap_canonical _
  have q1 : (⟨[σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)], []⟩ : Fs).squeezeN 1 =
      ([σ (.n 89)], ⟨(cap5 78).map σ, []⟩) := by
    simp only [Fs.squeezeN]
    rw [← q0c]
    have : (⟨[σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)], []⟩ : Fs).squeeze.2 =
        ⟨(cap5 78).map σ, []⟩ := by
      rw [show ((⟨[σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)], []⟩ : Fs).squeeze.2) =
        ⟨(⟨[σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)], []⟩ : Fs).squeeze.2.cap, []⟩ from rfl,
        ← q0p]
    rw [this]
  have q5 : (⟨(cap5 78).map σ, []⟩ : Fs).squeezeN 5 =
      ((List.range 5).map (fun i ↦ σ (.n (110 + 20 * i))), ⟨(cap5 179).map σ, []⟩) := by
    have st : ∀ i < 5, σ (.n (110 + 20 * i)) =
          (⟨(cap5 (if i = 0 then 78 else 79 + 20 * i)).map σ, []⟩ : Fs).squeeze.1 ∧
        (cap5 (99 + 20 * i)).map σ =
          (⟨(cap5 (if i = 0 then 78 else 79 + 20 * i)).map σ, []⟩ : Fs).squeeze.2.cap := by
      intro i hi
      obtain ⟨a, b, -⟩ := step i hi (canc i hi)
      exact ⟨by rw [show 110 + 20 * i = 91 + 20 * i + 19 by omega]; exact a,
        by rw [← b]; congr 2; omega⟩
    have hs : ∀ i < 5, (⟨(cap5 (if i = 0 then 78 else 79 + 20 * i)).map σ, []⟩ : Fs).squeeze.2 =
        ⟨(cap5 (99 + 20 * i)).map σ, []⟩ := by
      intro i hi
      rw [show (⟨(cap5 (if i = 0 then 78 else 79 + 20 * i)).map σ, []⟩ : Fs).squeeze.2 =
        ⟨(⟨(cap5 (if i = 0 then 78 else 79 + 20 * i)).map σ, []⟩ : Fs).squeeze.2.cap, []⟩ from rfl,
        ← (st i hi).2]
    have s0 := st 0 (by omega); have s1 := st 1 (by omega); have s2 := st 2 (by omega)
    have s3 := st 3 (by omega); have s4 := st 4 (by omega)
    have h0 := hs 0 (by omega); have h1 := hs 1 (by omega); have h2 := hs 2 (by omega)
    have h3 := hs 3 (by omega); have h4 := hs 4 (by omega)
    simp only [↓reduceIte, Nat.reduceMul, Nat.reduceAdd, Nat.one_ne_zero,
      OfNat.ofNat_ne_zero] at s0 s1 s2 s3 s4 h0 h1 h2 h3 h4
    simp only [Fs.squeezeN, List.range_succ, List.range_zero, List.nil_append, List.map_cons,
      List.map_nil, List.cons_append, Nat.reduceMul, Nat.reduceAdd]
    rw [h0, h1, h2, h3, h4, ← s0.1, ← s1.1, ← s2.1, ← s3.1, ← s4.1]
  -- the committed word
  have gfs : ∀ s ∈ fsNextT (.n 5) 0 191, GoodS rd S w σ s := fun s hs ↦
    gx s (List.mem_append_right _ hs)
  obtain ⟨fv, -, -, -, FN⟩ := fsNext_complete (C := fun _ _ _ ↦ True) gfs (hS5 _ _) hcur
  have fpk : FsPackOk σ (.n 191) (191 + 1) dsObserve :=
    ((holds_fsNextT _ _ _ _ _).1 (FN (next := True) (kret := fun _ ↦ True) trivial)).1.2
  refine ⟨h17, h19, h43, h47, h48, e52, e60, by rw [c61, word_one], e63, m64', q1, q5, fv, fpk,
    fun {next kret} lw l89 lr hn ↦ ?_⟩
  rw [vkHeadT, holdsList_append, holdsList_append, holdsList_append, holdsList_append,
    holdsList_append, holdsList_map_atoms]
  refine ⟨fun i hi ↦ by simp only [Atom.Holds]; exact gcp i hi, HB ?_⟩
  -- the copied words
  rw [copyWordsT, holdsList_range_flatten _ _ (fun _ ↦ rfl)]
  refine ⟨fun i hi ↦ ?_, ?_⟩
  · simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
    refine ⟨?_, by rw [zero_add]; exact lw i hi⟩
    rw [zero_add, e52 i hi, List.getD_eq_getElem _ _ (by omega)]
    exact hchi i (by omega)
  -- the point
  simp only [vkPointT, Stmt.HoldsList, Stmt.Holds, Atom.Holds]
  refine ⟨c56, m57', trivial, c59, a60, c61, c62, m63', ?_, fun _ ↦ trivial, m64', c65, z66, z67,
    z68, z69, ?_⟩
  · rw [e60, h17]
    exact isInK_add ((isInK_iff _).mpr ⟨1, ofK_one.symm⟩) ((isInK_iff _).mpr ⟨_, gen_pow_eq_ofK _⟩)
  -- the squeezes
  rw [vkSqueezesT, holdsList_append, holdsList_append, holdsList_range_flatten _ _ (fun _ ↦ rfl)]
  refine H0 ?_
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds]
  refine ⟨l89, trivial, fun i hi ↦ ?_, ?_⟩
  · rw [holdsList_append]
    refine (step i hi (canc i hi)).2.2 ?_
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
    exact lr i hi
  -- the committed word
  exact FN hn

end
end LeanVM.Guest.B1.VerifySub
