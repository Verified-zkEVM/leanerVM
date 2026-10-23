/-
  LeanVM.Guest.B1.Digest.ChildListCRec

  A child claim record, completely: on an evaluated valuation, its atoms hold at honest slots.
-/

module

public import LeanVM.Guest.B1.Digest.ChildListCChk
public import LeanVM.Guest.B1.Digest.ClaimListCLast

/-!
# A claim record, completely

On a valuation evaluated (`Fwd.Good`) with the pure atoms holding, a record evaluated by
`recC`/`recSide` holds once its slot is `g^e` (the oracle `slotW`), its mark, cells and the
coverage table's slot are the honest ones (`RecMem`), and the words the range check reads are
defined (`g^i`, `i` below the log `L` of the bound): `wit_val`, `markC_val`, `cellRead_val` give
the values, `recSide_holds` the side atoms.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd

@[expose] public section

variable {rd : Reader} {A S : List Atom} {w : ℕ → E} {σ : Val} {P : ClaimVs} {o0 K : ℕ}

/-- The claim of a slot value's number (`ccOV o0 j ↦ j`). -/
def slotOf (o0 i : ℕ) : ℕ := if i = o0 then 0 else (i - o0 - 15) / 17 + 1

theorem slotOf_ccOV (o0 j : ℕ) : slotOf o0 (ccOV o0 j).idx = j := by
  unfold slotOf ccOV
  split
  · subst_vars; simp
  · simp only
    rw [ite_neg' (by omega)]
    omega

/-- The oracle of the slots `os`: `g^(os j)` at claim `j`'s slot value. -/
noncomputable def slotW (o0 : ℕ) (os : ℕ → ℕ) (i : ℕ) : E := gen ^ os (slotOf o0 i)

/-- **The honest records**: claim `j < K`'s slot `os j` below the bound's log, its mark at the
coverage table's slot, its four cells at the table. -/
def RecMem (rd : Reader) (cover origin limit entries marks : E) (K : ℕ) (os : ℕ → ℕ)
    (cells : List E) : Prop :=
  ∀ j < K, BelowLog limit (os j) ∧ LoadHolds rd (cover * (origin * gen ^ os j)) 0 (marks * gen ^ j) ∧
    ∀ c < 4, LoadHolds rd entries (4 * os j + c) (cells.getD (4 * j + c) 0)

/-- The words a range check against `g^L` reads are defined. -/
def BoundMem (rd : Reader) (L : ℕ) : Prop := ∀ i < L, ∃ t, LoadHolds rd (gen ^ i) 0 t

theorem isWitO_eq {o : V} {a : Atom} (h : isWitO o a = true) :
    ∃ s, a = .hint (.witness s (.stack [o])) := by
  unfold isWitO at h
  split at h
  · rename_i s v
    simp only [decide_eq_true_eq] at h
    exact ⟨s, by rw [h]⟩
  · exact absurd h (by simp)

theorem wit_val {o : V} (h : A.any (isWitO o) = true) (hg : ∀ a ∈ A, Good rd S w σ a) :
    σ o = w o.idx := by
  obtain ⟨a, ha, hp⟩ := List.any_eq_true.mp h
  obtain ⟨s, rfl⟩ := isWitO_eq hp
  exact hg _ ha o (by simp)

theorem limK_val {k : V} (h : isLimK (A.filter pureB) P k = true)
    (hF : ∀ a ∈ A.filter pureB, a.Holds rd σ) : σ k = σ P.limit * ginvW := by
  unfold isLimK at h
  split at h
  · rename_i l gi hlg
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨rfl, hgi⟩ := h
    rw [mulOf_sound hlg hF, const_sound hgi hF]
  · exact absurd h (by simp)

theorem markC_val {j : ℕ} (hj : j < 64) {mark : V} (h : markC (A.filter pureB) P j mark = true)
    (hF : ∀ a ∈ A.filter pureB, a.Holds rd σ) : σ mark = σ P.marks * gen ^ j := by
  unfold markC at h
  by_cases h0 : j = 0
  · subst h0
    simp only [↓reduceIte, decide_eq_true_eq] at h
    rw [h, pow_zero, mul_one]
  · rw [ite_neg' h0] at h
    split at h
    · rename_i m c hmc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨rfl, hc⟩ := h
      rw [mulOf_sound hmc hF, const_sound hc hF, word_two_pow hj]
    · exact absurd h (by simp)

theorem cells_ptr {p o : V} {e : ℕ} (hperm : (monoOf (A.filter pureB) 40 p).isPerm
      (P.entries :: List.replicate 4 o) = true)
    (hF : ∀ a ∈ A.filter pureB, a.Holds rd σ) (ho : σ o = gen ^ e) :
    σ p = σ P.entries * gen ^ (4 * e) := by
  rw [monoPerm_sound hperm hF]
  simp only [List.map_cons, List.map_replicate, List.prod_cons, List.prod_replicate]
  rw [ho, ← pow_mul, mul_comm e 4]

theorem cellRead_val {j c e : ℕ} {v : E} (h : A.any (isCellRead (A.filter pureB) S P o0 j c) = true)
    (hF : ∀ a ∈ A.filter pureB, a.Holds rd σ) (hg : ∀ a ∈ A, Good rd S w σ a)
    (ho : σ (ccOV o0 j) = gen ^ e) (hv : LoadHolds rd (σ P.entries) (4 * e + c) v) :
    σ (.n (ccCell o0 j c)) = v := by
  obtain ⟨a, ha, hp⟩ := List.any_eq_true.mp h
  cases a <;> simp only [isCellRead, Bool.false_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    Bool.not_eq_true', decide_eq_false_iff_not] at hp
  rename_i d p off
  obtain ⟨⟨⟨rfl, rfl⟩, hperm⟩, hnS⟩ := hp
  rw [load_val (by simp [isLoadAt]) (fun b hb => hg b (List.mem_singleton.mp hb ▸ ha)) hnS,
    cells_ptr hperm hF ho, rdAt_of_load ((loadHolds_mul_gen_pow rd _ _ _ _).mpr hv)]

theorem gen_mul_ginvW : gen * ginvW = 1 := by rw [mul_comm]; exact ginvW_mul_gen

set_option maxHeartbeats 1000000 in
/-- **A record's side atom holds**: a range check, a mark's store, a cell's read. -/
theorem recSide_holds {os : ℕ → ℕ} {cells : List E} {L : ℕ}
    (hF : ∀ a ∈ A.filter pureB, a.Holds rd σ) (hg : ∀ a ∈ A, Good rd S w σ a)
    (hwit : ∀ j < K, σ (ccOV o0 j) = gen ^ os j)
    (hmark : ∀ j < K, σ (ccMark o0 P.marks j) = σ P.marks * gen ^ j)
    (hrec : RecMem rd (σ P.cover) (σ P.origin) (σ P.limit) (σ P.entries) (σ P.marks) K os cells)
    (hL : σ P.limit = gen ^ L) (hL33 : L < 2 ^ 33) (hdef : BoundMem rd L)
    {a : Atom} (ha : a ∈ A) (hs : recSide (A.filter pureB) P o0 K S a = true) : a.Holds rd σ := by
  cases a with
  | rangeCheck x y t1 t2 k =>
    simp only [recSide, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true,
      List.mem_range] at hs
    obtain ⟨⟨hky, hlk⟩, j, hj, rfl⟩ := hs
    have hk := limK_val hlk hF
    obtain ⟨he32, e', he', hlim⟩ := (hrec j hj).1
    have hLe : L = os j + e' + 1 := gen_pow_inj' (by omega) (by omega) (hL.symm.trans hlim)
    have hg' := hg _ ha
    simp only [Good] at hg'
    rw [ite_pos' hky] at hg'
    obtain ⟨h1, h2, h3⟩ := hg'
    have hx := hwit j hj
    have hgen : gen ^ os j ≠ 0 := pow_ne_zero _ gen_ne_zero
    have hkv : σ k = gen ^ os j * gen ^ e' := by
      rw [hk, hL, hLe, pow_succ, ← pow_add, mul_assoc, gen_mul_ginvW, mul_one]
    have hyv : σ y = gen ^ e' := by
      rw [h3, hkv, hx, mul_comm (gen ^ os j), mul_assoc, mul_inv_cancel₀ hgen, mul_one]
    obtain ⟨t1', ht1⟩ := hdef (os j) (by omega)
    obtain ⟨t2', ht2⟩ := hdef e' (by omega)
    refine ⟨?_, ?_, ?_⟩
    · rw [h1, hx, rdAt_of_load ht1]; exact ht1
    · rw [hkv, hx, hyv]
    · rw [h2, hyv, rdAt_of_load ht2]; exact ht2
  | load d p off =>
    by_cases hS : Atom.load d p off ∈ S
    · simp only [recSide, hS, decide_true, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq,
        List.any_eq_true, List.mem_range] at hs
      obtain ⟨rfl, j, hj, rfl, hperm⟩ := hs
      show LoadHolds rd (σ p) 0 (σ (ccMark o0 P.marks j))
      rw [monoPerm_sound hperm hF, hmark j hj]
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      rw [hwit j hj]
      exact (hrec j hj).2.1
    · simp only [recSide, hS, decide_false, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true,
        decide_eq_true_eq, List.any_eq_true, List.mem_range] at hs
      obtain ⟨hoff, j, hj, hperm⟩ := hs
      have hv := (loadHolds_mul_gen_pow rd _ _ _ _).mpr ((hrec j hj).2.2 off hoff)
      rw [← cells_ptr hperm hF (hwit j hj)] at hv
      exact load_holds_of hS (hg _ ha) hv
  | _ => simp [recSide] at hs

end
end LeanVM.Guest.B1.Digest
