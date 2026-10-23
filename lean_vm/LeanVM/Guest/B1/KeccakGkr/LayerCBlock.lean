/-
  LeanVM.Guest.B1.KeccakGkr.LayerCBlock

  A block of atoms on an evaluated valuation holds: its canonical `KECCAK` inputs and its `K`
  assertions checked by kernel evaluation, the remaining atoms (`resid`) given.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.FsComplete
public import LeanVM.Guest.B1.Fwd.Canon

/-!
# Blocks, completely

On a valuation satisfying every atom's equations (`Fwd.Good`), an atom holds by them alone unless
it needs a side condition (`needsSide`): a load, an assertion, a quotient. Of those, an
`assertInK` of two values known in `K` (`inKVals`: a hinted limb, a constant without `y` limbs)
holds by the equations too. `resid as`: the atoms left, which `block_holds` takes as given, with
the canonical `KECCAK` inputs checked by `canonChk`.

`side_loadVia`: a load that is not a store, through a pointer whose words the memory holds, has
its side condition.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.B1.Fwd

@[expose] public section

variable {C : CallRel} {rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val}

/-- The atoms of a list of statements. -/
def atomsL (B : List Stmt) : List Atom := B.filterMap fun s ↦ match s with
  | .atom a => some a
  | _ => none

theorem mem_atomsL {B : List Stmt} {a : Atom} : a ∈ atomsL B ↔ Stmt.atom a ∈ B := by
  simp only [atomsL, List.mem_filterMap]
  constructor
  · rintro ⟨s, hs, h⟩
    cases s <;> simp_all
  · intro h
    exact ⟨_, h, rfl⟩

/-- The values known in `K` by their equations: hinted limbs, constants without `y` limbs. -/
def inKVals (as : List Atom) : List ℕ := as.flatMap fun a ↦ match a with
  | .hint (.limbs _ ds) => ds.map V.idx
  | .const d e => if e.limb 1 = 0 ∧ e.limb 2 = 0 then [d.idx] else []
  | _ => []

/-- An `assertInK` of two values known in `K`. -/
def inkB (K : List ℕ) : Atom → Bool
  | .assertInK x y => K.contains x.idx && K.contains y.idx
  | _ => false

/-- The atoms whose relation the equations do not give. -/
def resid (as : List Atom) : List Atom :=
  as.filter fun a ↦ needsSide a && !inkB (inKVals as) a

theorem inK_of_inKVals (hσ : ∀ v, σ v = σ (.n v.idx)) {as : List Atom}
    (hg : ∀ a ∈ as, Good rd S w σ a) {i : ℕ} (hi : i ∈ inKVals as) : IsInK (σ (.n i)) := by
  simp only [inKVals, List.mem_flatMap] at hi
  obtain ⟨a, ha, hi⟩ := hi
  have hga := hg a ha
  cases a with
  | hint h =>
    cases h with
    | limbs v ds =>
      simp only [List.mem_map] at hi
      obtain ⟨u, hu, rfl⟩ := hi
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hu
      rw [← hσ, hga j hj, limbAt]
      split
      · exact (isInK_iff _).mpr ⟨_, rfl⟩
      · exact (isInK_iff _).mpr ⟨0, by rw [ofK_zero]⟩
    | _ => simp at hi
  | const d e =>
    simp only at hi
    split at hi
    · rename_i he
      simp only [List.mem_singleton] at hi
      subst hi
      rw [← hσ, hga]
      exact he
    · simp at hi
  | _ => simp at hi

/-- **A block of atoms holds** on an evaluated valuation: its canonical `KECCAK` inputs checked
from the canonical values `A`, the atoms `resid` leaves holding or with their side conditions. -/
theorem block_holds {B : List Stmt} (hall : B.all isAtom = true) (hσ : ∀ v, σ v = σ (.n v.idx))
    {A : List ℕ} (hk : canonChk A (atomsL B) = true) (hg : ∀ s ∈ B, GoodS rd S w σ s)
    (hA : ∀ i ∈ A, IsCanonical128 (σ (.n i)))
    (hR : ∀ a ∈ resid (atomsL B), a.Holds rd σ ∨ Side rd S σ a) :
    ∀ {next : Prop} {kret : List E → Prop}, next → Stmt.HoldsList C rd σ B next kret := by
  intro next kret hn
  have hg' : ∀ a ∈ atomsL B, Good rd S w σ a := fun a ha ↦ hg _ (mem_atomsL.mp ha)
  have H := atoms_holds hσ hk hg' hA fun a ha hns ↦ by
    cases hik : inkB (inKVals (atomsL B)) a
    · exact hR a (List.mem_filter.mpr ⟨ha, by simp [hns, hik]⟩)
    · left
      cases a with
      | assertInK x y =>
        simp only [inkB, Bool.and_eq_true, List.contains_iff_mem] at hik
        show IsInK (σ x) ∧ IsInK (σ y)
        rw [hσ x, hσ y]
        exact ⟨inK_of_inKVals hσ hg' hik.1, inK_of_inKVals hσ hg' hik.2⟩
      | _ => simp [inkB] at hik
  exact (holdsList_atoms (allAtoms_of_all hall) next kret).2
    ⟨fun a ha ↦ H a (mem_atomsL.mpr ha), hn⟩

/-- A load that is not a store, through a pointer whose word the memory holds: its side
condition. -/
theorem side_load {d p : V} {off : ℕ} (hS : Atom.load d p off ∉ S) {v : E}
    (h : LoadHolds rd (σ p) off v) : Side rd S σ (.load d p off) := by
  simp only [Side, hS, ↓reduceIte]
  exact ⟨h.1, by rw [h.2]; rfl⟩

/-- `side_load` through a pointer whose words `W` the memory holds. -/
theorem side_loadVia {d p : V} {off : ℕ} (hS : Atom.load d p off ∉ S) {W : List E}
    (hW : ReadsAt rd (σ p) W) (hoff : off < W.length) : Side rd S σ (.load d p off) :=
  side_load hS (hW off hoff)

/-- A store of the word the memory holds: its side condition. -/
theorem side_store {d p : V} {off : ℕ} (hS : Atom.load d p off ∈ S) {v : E}
    (h : LoadHolds rd (σ p) off v) (hv : σ d = v) : Side rd S σ (.load d p off) := by
  simp only [Side, hS, ↓reduceIte]
  rw [hv]; exact h

/-- A load that is not a store reads the memory's word. -/
theorem load_val {d p : V} {off : ℕ} (hg : Good rd S w σ (.load d p off))
    (hS : Atom.load d p off ∉ S) {v : E} (h : LoadHolds rd (σ p) off v) : σ d = v := by
  rcases hg with h' | h'
  · exact absurd h' hS
  · rw [h', rdAt_load h]

/-- A load that is not a store holds and reads the memory's word. -/
theorem load_holds {d p : V} {off : ℕ} (hg : Good rd S w σ (.load d p off))
    (hS : Atom.load d p off ∉ S) {v : E} (h : LoadHolds rd (σ p) off v) :
    σ d = v ∧ (Atom.load d p off).Holds rd σ := by
  have e := load_val hg hS h
  refine ⟨e, ?_⟩
  show LoadHolds rd _ _ _
  rw [e]; exact h

end
end LeanVM.Guest.B1.VerifySub
