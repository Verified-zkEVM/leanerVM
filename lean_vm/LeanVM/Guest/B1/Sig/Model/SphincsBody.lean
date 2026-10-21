/-
  LeanVM.Guest.B1.Sig.Model.SphincsBody

  The pieces of `verify_sig_lean_sphincs` around the forest under a hash model (`SphincsBody` over
  `M.sem`): the prologue's message digest and the counter's encoding hash, answered.
-/

module

public import LeanVM.Guest.B1.Sig.SphincsBody
public import LeanVM.Guest.B1.Sig.Model.Merkle

/-!
# The prologue and the counter under a hash model

* `sPrologue_model` (`sPrologue_sound`): the message digest is the answered hash of
  `P | A | m | ρ` (two blocks: `compress_two_model`), the rest of the prologue hash-free;
* `sLanes_model` (`sLanes_sound`, by `holdsListB_free`);
* `sCounter_model` (`sCounter_sound`): the encoding digest is the answered hash of the forest key and
  the counter's bytes.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

variable {M : HashModel} {C : CallRel} {rd : Reader}

theorem sPrologue_tail_free : Stmt.freeInList [] (.atom (.hint (.bits (.n 18) 0 26 (.stack ((List.range 26).map
    fun j => .n (19 + j))))) :: (booleans 19 26 ++ (.atom (.hint (.bits (.n 18) 106 22 (.stack ((List.range 22).map
      fun j => .n (45 + j))))) :: (booleans 45 22 ++ (shifts 19 26 67 ++ (shifts 45 22 143 ++
        [cst 207 (word 0 (2 ^ 42) 0), mulS (.n 208) (.n 206) (.n 207), addS (.n 209) (.n 142) (.n 208)])))))) = true := by
  decide

/-- **The prologue under a model** (`sPrologue_sound`): the message digest is the answered hash of
the claim's message under some randomizer. -/
theorem sPrologue_model {σ : Val} {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsListB M.sem C rd σ sPrologue next kret) :
    LoadHolds rd (σ (.n 0)) 1 (σ (.n 1)) ∧ LoadHolds rd (σ (.n 0)) 2 (σ (.n 5)) ∧
      LoadHolds rd (σ (.n 0)) 3 (σ (.n 6)) ∧ IsCanonical128 (σ (.n 1)) ∧ IsCanonical128 (σ (.n 5)) ∧
      IsCanonical128 (σ (.n 6)) ∧
      hcellWith M.H [σ (.n 1), word (tw 12) 0 0, σ (.n 5), σ (.n 6), σ (.n 12)] = some (σ (.n 17), σ (.n 18)) ∧
      (∃ N U, SPre σ N U) ∧ next := by
  rw [sPrologue_eq] at h
  simp only [List.cons_append, List.nil_append] at h
  obtain ⟨hl1, h2, h3, h4, hl5, hl6, h7, h8, h9, hc1, -, h13, h14, h15, h16, hc2, h⟩ := h
  have h2 : σ (.n 2) = mdw 48 true := h2
  have h3 : σ (.n 3) = mdw 64 true := h3
  have h4 : σ (.n 4) = word (tw 12) 0 0 := h4
  have h7 : σ (.n 7) = iv0 := h7
  have h8 : σ (.n 8) = iv1 := h8
  have h9 : σ (.n 9) = mdw 64 false := h9
  have h13 : σ (.n 13) = word 0 0 0 := h13
  have h14 : σ (.n 14) = word 0 0 0 := h14
  have h15 : σ (.n 15) = word 0 0 0 := h15
  have h16 : σ (.n 16) = mdw 80 true := h16
  have hc1 : M.sem.check ![σ (.n 1), σ (.n 4), σ (.n 5), σ (.n 6)] (σ (.n 7)) (σ (.n 8)) (σ (.n 10)) (σ (.n 11))
    (σ (.n 9)) := hc1
  have hc2 : M.sem.check ![σ (.n 12), σ (.n 13), σ (.n 14), σ (.n 15)] (σ (.n 10)) (σ (.n 11)) (σ (.n 17))
    (σ (.n 18)) (σ (.n 16)) := hc2
  have h := (holdsListB_free sPrologue_tail_free σ _ _).mp h
  simp only [holdsList_cons_atom, holdsList_append, Atom.Holds, true_and] at h
  rw [booleans_iff] at h
  obtain ⟨hbN, h⟩ := h
  rw [booleans_iff] at h
  obtain ⟨hbU, h⟩ := h
  set fN : Nat → Bool := fun j => decide (σ (.n (19 + j)) = 1)
  set fU : Nat → Bool := fun j => decide (σ (.n (45 + j)) = 1)
  have hN : bitsVal fN 26 < 2 ^ 26 := bitsVal_lt fN 26
  have hU : bitsVal fU 22 < 2 ^ 22 := bitsVal_lt fU 22
  have hbitsN : ∀ j < 26, σ (.n (19 + j)) = bitE ((bitsVal fN 26).testBit j) := fun j hj => by
    rw [testBit_bitsVal, decide_eq_true hj, Bool.true_and]
    exact bitE_of_mul_self (hbN j hj)
  have hbitsU : ∀ j < 22, σ (.n (45 + j)) = bitE ((bitsVal fU 22).testBit j) := fun j hj => by
    rw [testBit_bitsVal, decide_eq_true hj, Bool.true_and]
    exact bitE_of_mul_self (hbU j hj)
  obtain ⟨hshN, h⟩ := shifts_sound (by omega) (by omega) hN hbitsN h
  obtain ⟨hshU, h⟩ := shifts_sound (by omega) (by omega) hU hbitsU h
  simp only [cst, mulS, addS, holdsList_cons_atom, holdsList_nil, Atom.Holds] at h
  obtain ⟨h207, h208, h209, hn⟩ := h
  -- the digest
  rw [h4, h7, h8, h9] at hc1
  rw [h13, h14, h15, h16, word_zero] at hc2
  have hr : ([σ (.n 12)].flatMap cellBytes).length = 16 := by rw [length_flatMap_cellBytes']; rfl
  have hc2' : M.sem.check ![σ (.n 12), 0, 0, 0] (σ (.n 10)) (σ (.n 11)) (σ (.n 17)) (σ (.n 18))
      (mdw (64 + ([σ (.n 12)].flatMap cellBytes).length) true) := by rw [hr]; exact hc2
  obtain ⟨hb0, -, -, ho⟩ := compress_two_model (M := M) (blockBytes_one (σ (.n 12))) (by rw [hr]; omega)
    (by rw [hr]; omega) hc1 hc2'
  rw [fin4_canonical] at hb0
  refine ⟨hl1, hl5, hl6, hb0.1, hb0.2.2.1, hb0.2.2.2, ?_, ⟨bitsVal fN 26, bitsVal fU 22, h2, h3, hN, hU, hbitsN,
    fun l hl => ?_, ?_⟩, hn⟩
  · rw [hcellWith, ← ho, blockBytes_four, ← List.flatMap_append]
    rfl
  · have := hshN (25 - l) (by omega)
    rwa [show 67 + 3 * (25 - l) = 142 - 3 * l by omega, show 26 - 1 - (25 - l) = l by omega] at this
  · have hN0 := hshN 25 (by omega)
    have hU0 := hshU 21 (by omega)
    simp only [show 67 + 3 * 25 = 142 from rfl, show 26 - 1 - 25 = 0 from rfl, pow_zero, Nat.div_one] at hN0
    simp only [show 143 + 3 * 21 = 206 from rfl, show 22 - 1 - 21 = 0 from rfl, pow_zero, Nat.div_one] at hU0
    rw [h209, h208, h207, hN0, hU0, eOfNat_mul_unused hU]

theorem sLanes_free (wd : Nat → V) (bound : V) (b : Nat) : Stmt.freeInList [] (sLanes wd bound b) = true := rfl

/-- **The lanes under a model** (`sLanes_sound`; no `BLAKE2S`). -/
theorem sLanes_model {σ : Val} {wd : Nat → V} {bound : V} {b : Nat} {t : Nat → Nat} (ht : ∀ k < 16, t k < 2 ^ 8)
    (hwd : ∀ k < 16, σ (wd k) = eOfNat (t k)) {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsListB M.sem C rd σ (sLanes wd bound b) next kret) :
    σ (.n 17) = lit (∑ k ∈ Finset.range 16, t k * 2 ^ (8 * k)) ∧ σ bound = σ (.n 18) ∧ next :=
  sLanes_sound ht hwd ((holdsListB_free (sLanes_free wd bound b) σ _ _).mp h)

/-- **The counter under a model** (`sCounter_sound`): a counter below `2^32`, and the encoding
digest the answered hash of the forest key `fk` and the counter's four bytes. -/
theorem sCounter_model {σ : Val} {fk : V} {b : Nat} {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsListB M.sem C rd σ (sCounter fk b) next kret) :
    ∃ Cn < 2 ^ 32, σ (.n b) = eOfNat Cn ∧ σ (.n (b + 126 + 1)) = σ (.n 142) + word (tw 4) 0 0 ∧
      (∃ o, hbWith M.H (cellBytes (σ (.n 1)) ++ cellBytes (σ (.n (b + 126 + 1))) ++ cellBytes (σ fk) ++
        leBytes Cn 4) = some o ∧ σ (.n (b + 126 + 5)) = o.1) ∧ next := by
  simp only [sCounter, holdsListB_append, hintW, mulS, holdsListB_cons_atom, Atom.HoldsB, true_and,
    holdsListB_nil] at h
  obtain ⟨hb0, h⟩ := h
  rw [holdsListB_flatMap_range _ (fun _ => rfl)] at h
  obtain ⟨hblk, h⟩ := h
  simp only [cst, addS, ivs, b2s, holdsListB_cons_atom, holdsListB_nil, Atom.HoldsB] at h hblk
  obtain ⟨heq, he, he1, hiv0, hiv1, hmd, hc, hn⟩ := h
  have hbool : ∀ j < 32, σ (.n (b + 1 + j)) * σ (.n (b + 1 + j)) = σ (.n (b + 1 + j)) := fun j hj => by
    rcases j with _ | j
    · exact hb0.symm
    · exact (hblk j (by omega)).1.symm
  set f : Nat → Bool := fun j => decide (σ (.n (b + 1 + j)) = 1)
  set Cn := bitsVal f 32
  have hCn : Cn < 2 ^ 32 := bitsVal_lt f 32
  have hbits : ∀ j < 32, σ (.n (b + 1 + j)) = bitE (Cn.testBit j) := fun j hj => by
    rw [testBit_bitsVal, decide_eq_true hj, Bool.true_and]
    exact bitE_of_mul_self (hbool j hj)
  have hh : ∀ i' ≤ 30, σ (.n (b + 33 + 3 * i' + 2)) = eOfNat (Cn / 2 ^ (30 - i')) := by
    intro i' hi'
    induction i' with
    | zero =>
        obtain ⟨-, h1, h2, h3, -⟩ := hblk 0 (by omega)
        simp only [↓reduceIte] at h2
        rw [h3, h2, h1, word_two, show b + 32 = b + 1 + 31 by omega, hbits 31 (by omega),
          top_bit (show Cn < 2 ^ (31 + 1) from hCn), show b + 32 - (0 + 1) = b + 1 + 30 by omega,
          hbits 30 (by omega), add_comm, shift_step (by omega)]
    | succ i' ih =>
        obtain ⟨-, h1, h2, h3, -⟩ := hblk (i' + 1) (by omega)
        simp only [Nat.add_one_ne_zero, ↓reduceIte] at h2
        rw [h3, h2, h1, word_two, show b + 33 + 3 * (i' + 1) - 1 = b + 33 + 3 * i' + 2 by omega, ih (by omega),
          show b + 32 - (i' + 1 + 1) = b + 1 + (30 - (i' + 1)) by omega, hbits _ (by omega), add_comm,
          show 30 - i' = 30 - (i' + 1) + 1 by omega, shift_step (by omega)]
  have hC : σ (.n b) = eOfNat Cn := by
    have := hh 30 le_rfl
    rw [show b + 33 + 3 * 30 + 2 = b + 125 by omega, Nat.sub_self, pow_zero, Nat.div_one] at this
    exact (e_add_eq_zero_iff.mp heq).symm.trans this
  refine ⟨Cn, hCn, hC, by rw [he1, he], ?_, hn⟩
  rw [hiv0, hiv1, hmd, hC] at hc
  have hr : (cellBytes (σ (.n 1)) ++ cellBytes (σ (.n (b + 126 + 1))) ++ cellBytes (σ fk) ++ leBytes Cn 4).length = 52 := by
    simp [length_cellBytes]
  have hc' : M.sem.check ![σ (.n 1), σ (.n (b + 126 + 1)), σ fk, eOfNat Cn] iv0 iv1 (σ (.n (b + 126 + 5)))
      (σ (.n (b + 126 + 6)))
      (mdw (cellBytes (σ (.n 1)) ++ cellBytes (σ (.n (b + 126 + 1))) ++ cellBytes (σ fk) ++ leBytes Cn 4).length
        true) := by rw [hr]; exact hc
  obtain ⟨-, ho⟩ := compress_final_model (M := M) (by rw [blockBytes_four, hr]; simp [cellBytes_counter hCn])
    (by rw [hr]; omega) hc'
  exact ⟨_, ho, rfl⟩

end
end LeanVM.Guest.B1.Sig
