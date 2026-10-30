/-
  LeanVM.Guest.B1.Bits.Grind

  B1 for `grind_check`: the low bits of a challenge's first limb are zero.
-/

module

public import LeanVM.Guest.B1.Bits.Meaning
public import LeanVM.Guest.B1.Bits.Templates

/-!
# `grind_check` (G:779-801, TRIAGE #21)

`grind_check(word, 17)` splits the word (`canonicalLimbsT (.n 0) 1`: canonical, its low limb at
`1`), hints the low limb's 64 bits into frame cells `5 .. 68`, pins bits `17 .. 63` by booleanity,
reconstructs them over `COORD_BASIS` (`gcBlk`, the running sum at `gcAcc`) and asserts the sum is
the low limb: its low 17 bits are zero.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The running sum after bit `17 + j`. -/
def gcAcc : ℕ → ℕ
  | 0 => 70
  | j + 1 => 73 + 3 * j

/-- Bit `17 + j`: booleanity, its term, added (the first folded). -/
def gcBlk : ℕ → List Stmt
  | 0 => [.atom (.mul (.n 22) (.n 22) (.n 22)), .atom (.const (.n 69) (word (2 ^ 17) 0 0)),
      .atom (.mul (.n 70) (.n 22) (.n 69))]
  | j + 1 => [.atom (.mul (.n (23 + j)) (.n (23 + j)) (.n (23 + j))),
      .atom (.const (.n (71 + 3 * j)) (word (2 ^ (18 + j)) 0 0)),
      .atom (.mul (.n (72 + 3 * j)) (.n (23 + j)) (.n (71 + 3 * j))),
      .atom (.add (.n (73 + 3 * j)) (.n (gcAcc j)) (.n (72 + 3 * j)))]

/-- The 64 frame cells of the lane's bits. -/
def gcRun : List V := (List.range 64).map fun i => .n (5 + i)

/-- The expansion of `grind_check__L17`. -/
def gcBody : List Stmt :=
  canonicalLimbsT (.n 0) 1 ++ [.atom (.hint (.bits (.n 1) 0 64 (.stack gcRun)))] ++
  ((List.range 47).map gcBlk).flatten ++ [.atom (.assertEq (.n 208) (.n 1)), .ret []]

theorem core388_body : Fn.body Data.core388 = gcBody := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem find_grind_check : coreProgram.find? "grind_check__L17" = some Data.core388 :=
  Program.find?_of_indexOf? (j := 388) (by decide +kernel) rfl

/-- What bit `17 + j` asks of a valuation. -/
def GcOk (σ : Val) : ℕ → Prop
  | 0 => σ (.n 22) = σ (.n 22) * σ (.n 22) ∧ σ (.n 69) = word (2 ^ 17) 0 0 ∧
      σ (.n 70) = σ (.n 22) * σ (.n 69)
  | j + 1 => σ (.n (23 + j)) = σ (.n (23 + j)) * σ (.n (23 + j)) ∧
      σ (.n (71 + 3 * j)) = word (2 ^ (18 + j)) 0 0 ∧
      σ (.n (72 + 3 * j)) = σ (.n (23 + j)) * σ (.n (71 + 3 * j)) ∧
      σ (.n (73 + 3 * j)) = σ (.n (gcAcc j)) + σ (.n (72 + 3 * j))

theorem holds_gcBlk {C : CallRel} {rd : Reader} {σ : Val} (j : ℕ) (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (gcBlk j) True kret ↔ GcOk σ j := by
  cases j <;> simp only [gcBlk, GcOk, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]

theorem word_coordBasis {i : ℕ} (h : i < 64) : word (2 ^ i) 0 0 = coordBasis i := by
  rw [word_eOfNat, coordBasis_of_lt h]

theorem gc_acc {σ : Val} : ∀ n, n < 47 → (∀ j < n + 1, GcOk σ j) →
    σ (.n (gcAcc n)) = ∑ j ∈ Finset.range (n + 1), σ (.n (22 + j)) * coordBasis (17 + j)
  | 0, _, h => by
    obtain ⟨-, e69, e70⟩ := h 0 (by omega)
    rw [Finset.sum_range_one, gcAcc, e70, e69, word_coordBasis (by norm_num)]
  | n + 1, hn, h => by
    obtain ⟨-, e71, e72, e73⟩ := h (n + 1) (by omega)
    rw [gcAcc, e73, gc_acc n (by omega) (fun j hj => h j (by omega)), e72, e71,
      word_coordBasis (by omega), Finset.sum_range_succ (n := n + 1),
      show 22 + (n + 1) = 23 + n by omega, show 17 + (n + 1) = 18 + n by omega]

/-- The honest values of `grind_check__L17` on the word `w`, `L` its low limb's integer. -/
def gcVals (w : E) (k : ℕ) : E :=
  let L := kToNat (w.limb 0)
  let b := fun i => bitE (L.testBit i)
  let acc := fun m => ∑ j ∈ Finset.range m, b (17 + j) * coordBasis (17 + j)
  if k = 0 then w else if k = 1 then ofK (w.limb 0) else if k = 2 then w + ofK (w.limb 0)
  else if k = 3 then word 1 0 1 else if k = 4 then ofK (w.limb 1)
  else if k < 69 then b (k - 5)
  else if k = 69 then word (2 ^ 17) 0 0 else if k = 70 then b 17 * word (2 ^ 17) 0 0
  else if (k - 71) % 3 = 0 then word (2 ^ (18 + (k - 71) / 3)) 0 0
  else if (k - 71) % 3 = 1 then b (18 + (k - 71) / 3) * word (2 ^ (18 + (k - 71) / 3)) 0 0
  else acc ((k - 71) / 3 + 2)

/-- The honest running sum. -/
def gcSum (w : E) (m : ℕ) : E :=
  ∑ j ∈ Finset.range m, bitE ((kToNat (w.limb 0)).testBit (17 + j)) * coordBasis (17 + j)

theorem gv_bit (w : E) {k : ℕ} (h1 : 5 ≤ k) (h2 : k < 69) :
    gcVals w k = bitE ((kToNat (w.limb 0)).testBit (k - 5)) := by
  unfold gcVals; split_ifs <;> first | omega | rfl

theorem gv_c (w : E) (j : ℕ) : gcVals w (71 + 3 * j) = word (2 ^ (18 + j)) 0 0 := by
  unfold gcVals
  split_ifs <;> first | omega | (rw [show (71 + 3 * j - 71) / 3 = j by omega])

theorem gv_m (w : E) (j : ℕ) : gcVals w (72 + 3 * j) =
    bitE ((kToNat (w.limb 0)).testBit (18 + j)) * word (2 ^ (18 + j)) 0 0 := by
  unfold gcVals
  split_ifs <;> first | omega | (rw [show (72 + 3 * j - 71) / 3 = j by omega])

theorem gv_a (w : E) (j : ℕ) : gcVals w (73 + 3 * j) = gcSum w (j + 2) := by
  unfold gcVals
  split_ifs <;> first | omega | (rw [show (73 + 3 * j - 71) / 3 = j by omega]; rfl)

theorem gv_acc (w : E) (j : ℕ) : gcVals w (gcAcc j) = gcSum w (j + 1) := by
  cases j with
  | zero =>
    have h70 : gcVals w 70 = bitE ((kToNat (w.limb 0)).testBit 17) * word (2 ^ 17) 0 0 := by
      rfl
    rw [show gcAcc 0 = 70 from rfl, h70, gcSum, Finset.sum_range_one, word_coordBasis (by norm_num)]
  | succ j => exact gv_a w j

/-- **`grind_check`'s core IR is its meaning.** -/
theorem grind_check_holds : grind_check_Spec := by
  intro rd args rets
  rw [rel_iff_sem find_grind_check, core388_body, show Fn.params Data.core388 = [.n 0] from rfl,
    gcBody]
  simp only [holdsList_append, holds_canonicalLimbsT,
    holdsList_range_flatten 47 gcBlk (fun j => by cases j <;> rfl), holds_gcBlk, Stmt.HoldsList,
    Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, true_and]
  constructor
  · rintro ⟨σ, hp, ⟨hc, h1, -⟩, hbits, ha, hret⟩
    subst hp
    refine ⟨hret.symm, hc, ?_⟩
    have hsum := gc_acc 46 (by omega) hbits
    rw [show gcAcc 46 = 208 from rfl, e_add_eq_zero_iff.mp ha, h1] at hsum
    have hb : ∀ i < 47, σ (.n (22 + i)) * σ (.n (22 + i)) = σ (.n (22 + i)) := by
      intro i hi
      cases i with
      | zero => exact (hbits 0 (by omega)).1.symm
      | succ i =>
        rw [show 22 + (i + 1) = 23 + i by omega]
        exact (hbits (i + 1) hi).1.symm
    obtain ⟨N, hN, hx, -⟩ := bits_of_reconstruct (s := 17) hb hsum.symm
    have hm : 2 ^ 17 * N < 2 ^ 64 := by
      calc 2 ^ 17 * N < 2 ^ 17 * 2 ^ 47 := Nat.mul_lt_mul_of_pos_left hN (by positivity)
        _ = 2 ^ 64 := by norm_num
    rw [eOfNat192_of_lt hm, eOfNat] at hx
    have hl := ofK_injective hx
    show kToNat ((σ (.n 0)).limb 0) % 2 ^ 17 = 0
    rw [hl, kToNat_ofBits, Nat.mod_eq_of_lt hm, Nat.mul_mod_right]
  · intro hm
    obtain ⟨w, rfl⟩ : ∃ w, args = [w] := by
      match args, hm with
      | [a], _ => exact ⟨a, rfl⟩
    obtain ⟨rfl, hc, hlow⟩ := hm
    change kToNat (w.limb 0) % 2 ^ 17 = 0 at hlow
    let σ : Val := fun x => gcVals w x.idx
    have ev : ∀ k, σ (.n k) = gcVals w k := fun _ => rfl
    have hL : kToNat (w.limb 0) < 2 ^ 64 := by
      have := (w.limb 0).toBitVec.isLt; exact this
    set L := kToNat (w.limb 0) with hLdef
    have hLN : L = 2 ^ 17 * (L / 2 ^ 17) := (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hlow)).symm
    have hN : L / 2 ^ 17 < 2 ^ 47 := by omega
    refine ⟨σ, rfl, ⟨by simpa [ev, gcVals] using hc, by simp [ev, gcVals], by simp [ev, gcVals],
      by simp [ev, gcVals], by simp [ev, gcVals]⟩, fun j hj => ?_, ?_, rfl⟩
    · cases j with
      | zero =>
        refine ⟨?_, by simp [ev, gcVals], ?_⟩
        · rw [ev, gv_bit w (by omega) (by omega)]; exact (bitE_mul_self _).symm
        · show gcVals w 70 = gcVals w 22 * gcVals w 69
          rw [gv_bit w (k := 22) (by omega) (by omega)]
          simp [gcVals]
      | succ j =>
        refine ⟨?_, by rw [ev, gv_c], ?_, ?_⟩
        · rw [ev, gv_bit w (by omega) (by omega)]; exact (bitE_mul_self _).symm
        · rw [ev, ev, ev, gv_m, gv_c, gv_bit w (by omega) (by omega),
            show 23 + j - 5 = 18 + j by omega]
        · rw [ev, ev, ev, gv_a, gv_acc, gv_m, gcSum, gcSum, Finset.sum_range_succ (n := j + 1),
            word_coordBasis (by omega), show 17 + (j + 1) = 18 + j by omega]
    · rw [ev, ev, show (208 : ℕ) = gcAcc 46 from rfl, gv_acc, e_add_eq_zero_iff, gcSum]
      have hrec := reconstruct_bits 17 hN
      simp only [Nat.testBit_div_two_pow] at hrec
      rw [← hLN, eOfNat192_of_lt hL] at hrec
      simp only [show ∀ i, i + 17 = 17 + i from fun i => by omega] at hrec
      rw [show gcVals w 1 = ofK (w.limb 0) by simp [gcVals], hrec, eOfNat, hLdef, ofBits_kToNat]

end
end LeanVM.Guest.B1
