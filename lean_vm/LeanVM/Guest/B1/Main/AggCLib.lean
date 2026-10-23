/-
  LeanVM.Guest.B1.Main.AggCLib

  What an evaluated valuation (`Fwd.ev`) gives of `fs_pack`s, loads and challenges, for the
  completeness of `aggregate_claims` and its loops.
-/

module

public import LeanVM.Guest.B1.Main.AggCDefs
public import LeanVM.Guest.B1.Digest.PairComplete
public import LeanVM.Guest.B1.Da.ColumnComplete

/-!
# Evaluated templates

`pack_vals`: an `fs_pack(x)` from `b` whose atoms are in a block, evaluated, has the honest values
`fsPackVals (σ x) 1`; so its `assert_in_k` holds (`pack_inK`, for the atoms `isPackInK` names) and
its cells are canonical (`pack_canon`), the scalar's rate cells (`pack_cells`). `side_load`: a
load (not a store) reading a word in memory has its side condition; `good_load_val`: its value is
the memory's.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Fwd

@[expose] public section

variable {rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val}

/-- An `assert_in_k` of an `fs_pack`'s top limb and tag constant, of one of the packs `ps`. -/
def isPackInK (ps : List (V × ℕ)) : Atom → Bool
  | .assertInK x y => ps.any fun p => decide (x = .n (p.2 + 2)) && decide (y = .n (p.2 + 3))
  | _ => false

theorem good_of_any {A : List Atom} (hg : ∀ a ∈ A, Good rd S w σ a) {a : Atom}
    (h : A.any (atomEqb a) = true) : Good rd S w σ a := by
  obtain ⟨a', ha', he⟩ := List.any_eq_true.mp h
  rw [atomEqb_sound he]
  exact hg a' ha'

/-- **An evaluated `fs_pack`** has its honest values. -/
theorem pack_vals {A : List Atom} {x : V} {b : ℕ} (h : packIn A x b = true)
    (hg : ∀ a ∈ A, Good rd S w σ a) : ∀ i < 9, σ (.n (b + i)) = fsPackVals (σ x) dsObserve i := by
  have hall := List.all_eq_true.mp h
  have h0 := hall (.hint (.limbs x [.n b, .n (b + 1), .n (b + 2)])) (by simp [fsPackA])
  have h3 := hall (.const (.n (b + 3)) (word dsObserve 0 0)) (by simp [fsPackA])
  have h4 := hall (.const (.n (b + 4)) (word 0 0 1)) (by simp [fsPackA])
  have h5 := hall (.mul (.n (b + 5)) (.n (b + 4)) (.n (b + 2))) (by simp [fsPackA])
  have h6 := hall (.add (.n (b + 6)) x (.n (b + 5))) (by simp [fsPackA])
  have h7 := hall (.const (.n (b + 7)) (word 0 dsObserve 0)) (by simp [fsPackA])
  have h8 := hall (.add (.n (b + 8)) (.n (b + 2)) (.n (b + 7))) (by simp [fsPackA])
  have g0 := good_of_any hg h0
  have g3 : σ (.n (b + 3)) = word dsObserve 0 0 := good_of_any hg h3
  have g4 : σ (.n (b + 4)) = word 0 0 1 := good_of_any hg h4
  have g5 := good_of_any hg h5
  have g6 : σ (.n (b + 6)) = σ x + σ (.n (b + 5)) := good_of_any hg h6
  have g7 : σ (.n (b + 7)) = word 0 dsObserve 0 := good_of_any hg h7
  have g8 : σ (.n (b + 8)) = σ (.n (b + 2)) + σ (.n (b + 7)) := good_of_any hg h8
  simp only [Good] at g0 g5
  have l0 : σ (.n b) = ofK ((σ x).limb 0) := g0 0 (by simp)
  have l1 : σ (.n (b + 1)) = ofK ((σ x).limb 1) := g0 1 (by simp)
  have l2 : σ (.n (b + 2)) = ofK ((σ x).limb 2) := g0 2 (by simp)
  rw [ite_pos' (by simp)] at g5
  intro i hi
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact l0
  · exact l1
  · exact l2
  · exact g3
  · exact g4
  · show σ (.n (b + 5)) = word 0 0 1 * ofK ((σ x).limb 2)
    rw [g5, g4, l2]
  · show σ (.n (b + 6)) = σ x + word 0 0 1 * ofK ((σ x).limb 2)
    rw [g6, g5, g4, l2]
  · exact g7
  · show σ (.n (b + 8)) = ofK ((σ x).limb 2) + word 0 dsObserve 0
    rw [g8, l2, g7]

theorem pack_ok {A : List Atom} {x : V} {b : ℕ} (h : packIn A x b = true)
    (hg : ∀ a ∈ A, Good rd S w σ a) : FsPackOk σ x b dsObserve :=
  fsPackOk_of_vals (pack_vals h hg)

/-- An evaluated `fs_pack`'s cells are canonical. -/
theorem pack_canon {A : List Atom} {x : V} {b : ℕ} (h : packIn A x b = true)
    (hg : ∀ a ∈ A, Good rd S w σ a) :
    IsCanonical128 (σ (.n (b + 6))) ∧ IsCanonical128 (σ (.n (b + 8))) := by
  rw [pack_vals h hg 6 (by omega), pack_vals h hg 8 (by omega)]
  exact fsPackVals_canonical _ _

/-- An evaluated `fs_pack`'s cells are its scalar's rate cells. -/
theorem pack_cells {A : List Atom} {x : V} {b : ℕ} (h : packIn A x b = true)
    (hg : ∀ a ∈ A, Good rd S w σ a) :
    (σ (.n (b + 6)), σ (.n (b + 8))) = Keccak.scalarCells (σ x) dsObserve := by
  rw [pack_vals h hg 6 (by omega), pack_vals h hg 8 (by omega)]
  exact fsPackVals_cells _ _

/-- An evaluated `fs_pack`'s `assert_in_k` holds. -/
theorem pack_inK {A : List Atom} {ps : List (V × ℕ)} (hps : ps.all (fun p => packIn A p.1 p.2) = true)
    (hg : ∀ a ∈ A, Good rd S w σ a) {a : Atom} (ha : isPackInK ps a = true) : a.Holds rd σ := by
  cases a <;> simp only [isPackInK, Bool.false_eq_true] at ha
  rename_i x y
  obtain ⟨p, hp, hxy⟩ := List.any_eq_true.mp ha
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hxy
  obtain ⟨rfl, rfl⟩ := hxy
  obtain ⟨-, h2, h3, -⟩ := pack_ok (List.all_eq_true.mp hps p hp) hg
  exact ⟨h2, h3⟩

/-- A load (not a store) reading a word in memory has its side condition. -/
theorem side_load {d p : V} {o : ℕ} {v : E} (hS : Atom.load d p o ∉ S)
    (h : LoadHolds rd (σ p) o v) : Side rd S σ (.load d p o) := by
  simp only [Side]
  rw [ite_neg' hS]
  exact ⟨h.1, by rw [h.2]; rfl⟩

/-- A load (not a store), evaluated, reads the memory. -/
theorem good_load_val {d p : V} {o : ℕ} (hS : Atom.load d p o ∉ S)
    (h : Good rd S w σ (.load d p o)) : σ d = rdAt rd (σ p) o := by
  rcases h with h | h
  · exact absurd h hS
  · exact h

/-- A load (not a store) of a word in memory, evaluated, holds and reads it. -/
theorem load_of_good {d p : V} {o : ℕ} {v : E} (hS : Atom.load d p o ∉ S)
    (hg : Good rd S w σ (.load d p o)) (h : LoadHolds rd (σ p) o v) :
    σ d = v ∧ (Atom.load d p o).Holds rd σ := by
  have e : σ d = v := by rw [good_load_val hS hg, rdAt_of_load h]
  refine ⟨e, ?_⟩
  show LoadHolds rd (σ p) o (σ d)
  rw [e]; exact h

end
end LeanVM.Guest.B1.Main
