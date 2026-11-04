/-
  LeanVM.Guest.B1.Sig.SphincsFold

  The folds of `verify_sig_lean_sphincs` (`sp_fold`, `sp_subtree_arm`, `sp_tree_arm`,
  `lean_ethereum.py:3590-3629`) are sound: arm `index` of a fold's dispatch folds its leaf up the
  hinted path into the top it reaches, and sets the mark and the weight of `index`.
-/

module

public import LeanVM.Guest.B1.Sig.SphincsFk

/-!
# The folds, sound

* `flAdr`, `flNext`, `flBase`: a level's address (`at` plus a cell or a constant) and the bases;
* `foldLevel_sound`, `foldLevels_sound`: the levels are the forward fold `mFold` of the hinted
  siblings;
* `foldArm_sound`: the reached node into the top of the index's top bit, the mark and the weight;
* `foldArmsRest_getElem`, `foldArms_sound`: arm `index` of the `2^height` is `foldArm index`, from
  the base `foAB`, writing into the dispatch's three cells.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier (eOfNat)

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}

/-- A level's address: `at` plus the cell, or plus the constant's word. -/
def flAdr (σ : Val) (atV : V) (adr : Nat → Sum V Nat) (l : Nat) : E :=
  σ atV + match adr l with
    | .inl a => σ a
    | .inr c => word c 0 0

/-- The base after a level at base `b`. -/
def flNext (adr : Nat → Sum V Nat) (l b : Nat) : Nat :=
  match adr l with
  | .inl _ => b + 16
  | .inr _ => b + 17

/-- The base of level `l + j` of a fold from level `l` at base `b`. -/
def flBase (adr : Nat → Sum V Nat) : Nat → Nat → Nat → Nat
  | _, 0, b => b
  | l, j + 1, b => flBase adr (l + 1) j (flNext adr l b)

theorem foldLevel_sound (hp : PadOK σ sPad) {atV : V} {adr : Nat → Sum V Nat} {l : Nat} {bit : Bool}
    {cur : V} {b : Nat} (h : AtomsHold rd σ (foldLevel atV (adr l) bit cur b).1) :
    σ (foldLevel atV (adr l) bit cur b).2.2 = (hcell [σ sPP, flAdr σ atV adr l,
      if bit then σ (.n b) else σ cur, if bit then σ cur else σ (.n b)]).1 ∧
      (foldLevel atV (adr l) bit cur b).2.1 = flNext adr l b := by
  unfold flAdr flNext
  cases ha : adr l with
  | inl a =>
      simp only [ha, foldLevel] at h ⊢
      have hs : σ (.n (b + 1)) = σ atV + σ a := h.atom (a := .add (.n (b + 1)) atV a) (by simp [addS])
      have hk := k64_sound hp (h.sub fun x hx => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx))
      refine ⟨?_, trivial⟩
      have hk1 := congrArg Prod.fst hk
      simp only at hk1
      rw [hk1, hs]
      cases bit <;> rfl
  | inr c =>
      simp only [ha, foldLevel] at h ⊢
      have hc : σ (.n (b + 1)) = word c 0 0 := h.atom (a := .const (.n (b + 1)) _) (by simp [cst])
      have hs : σ (.n (b + 2)) = σ atV + σ (.n (b + 1)) :=
        h.atom (a := .add (.n (b + 2)) atV (.n (b + 1))) (by simp [addS])
      have hk := k64_sound hp (h.sub fun x hx =>
        List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx)))
      refine ⟨?_, trivial⟩
      have hk1 := congrArg Prod.fst hk
      simp only at hk1
      rw [hk1, hs, hc]
      cases bit <;> rfl

/-- **The levels of a fold**: the forward fold of the hinted siblings, and the base after. -/
theorem foldLevels_sound (hp : PadOK σ sPad) {atV : V} {adr : Nat → Sum V Nat} {index : Nat} :
    ∀ (m l : Nat) (cur : V) (b : Nat), AtomsHold rd σ (foldLevels atV adr index m l cur b).1 →
      σ (foldLevels atV adr index m l cur b).2.2 =
          mFold (σ sPP) (flAdr σ atV adr) index.testBit (fun l' => σ (.n (flBase adr l (l' - l) b)))
            m l (σ cur) ∧
        (foldLevels atV adr index m l cur b).2.1 = flBase adr l m b
  | 0, _, _, _, _ => ⟨rfl, rfl⟩
  | m + 1, l, cur, b, h => by
      have h' : AtomsHold rd σ ((foldLevel atV (adr l) (index.testBit l) cur b).1 ++
          (foldLevels atV adr index m (l + 1) (foldLevel atV (adr l) (index.testBit l) cur b).2.2
            (foldLevel atV (adr l) (index.testBit l) cur b).2.1).1) := h
      obtain ⟨e1, e2⟩ := foldLevel_sound hp h'.left
      obtain ⟨r1, r2⟩ := foldLevels_sound hp m (l + 1) _ _ h'.right
      have hb : ∀ l', l + 1 ≤ l' → flBase adr (l + 1) (l' - (l + 1))
          (foldLevel atV (adr l) (index.testBit l) cur b).2.1 = flBase adr l (l' - l) b := by
        intro l' hl'
        rw [e2, show l' - l = l' - (l + 1) + 1 by omega, flBase]
      refine ⟨?_, ?_⟩
      swap
      · show (foldLevels atV adr index m (l + 1) (foldLevel atV (adr l) (index.testBit l) cur b).2.2
          (foldLevel atV (adr l) (index.testBit l) cur b).2.1).2.1 = _
        rw [r2, e2]
        rfl
      show σ (foldLevels atV adr index m (l + 1) (foldLevel atV (adr l) (index.testBit l) cur b).2.2
        (foldLevel atV (adr l) (index.testBit l) cur b).2.1).2.2 = _
      rw [r1, e1, mFold, Nat.sub_self, flBase]
      apply mFold_congr
      intro l' hl'
      exact ⟨rfl, rfl, by rw [hb l' hl']⟩

/-- **A fold's arm**: the leaf folded `height - 1` levels into the top of the index's top bit; the
mark and the weight. -/
theorem foldArm_sound (hp : PadOK σ sPad) {atV : V} {adr : Nat → Sum V Nat} {height index : Nat}
    {node0 : V} {outs : V × V × V} {markV : V} {markC wC : E} {fresh : Bool} {b : Nat}
    (h : AtomsHold rd σ (foldArm atV adr height index node0 outs markV markC wC fresh b).1) :
    σ (if index / 2 ^ (height - 1) = 0 then
        (if fresh then (V.n (flBase adr 0 (height - 1) b)) else outs.1)
      else (if fresh then (V.n (flBase adr 0 (height - 1) b + 1)) else outs.2.1)) =
        mFold (σ sPP) (flAdr σ atV adr) index.testBit (fun l' => σ (.n (flBase adr 0 l' b)))
          (height - 1) 0 (σ node0) ∧
      σ markV = markC ∧
      σ (if fresh then (V.n (flBase adr 0 (height - 1) b + 2)) else outs.2.2) = wC := by
  unfold foldArm at h
  simp only at h
  obtain ⟨r1, r2⟩ := foldLevels_sound hp (index := index) (atV := atV) (adr := adr) (height - 1) 0
    node0 b h.left
  rw [r2] at h
  simp only [Nat.sub_zero] at r1
  have hc := h.right.atom (a := .copy (if index / 2 ^ (height - 1) = 0 then
      (if fresh then (V.n (flBase adr 0 (height - 1) b), V.n (flBase adr 0 (height - 1) b + 1),
        V.n (flBase adr 0 (height - 1) b + 2)) else outs).1
      else (if fresh then (V.n (flBase adr 0 (height - 1) b), V.n (flBase adr 0 (height - 1) b + 1),
        V.n (flBase adr 0 (height - 1) b + 2)) else outs).2.1)
      (foldLevels atV adr index (height - 1) 0 node0 b).2.2) (by simp [copyS])
  have hm : σ markV = markC := h.right.atom (a := .const markV markC) (by simp)
  have hw := h.right.atom (a := .const (if fresh then (V.n (flBase adr 0 (height - 1) b),
      V.n (flBase adr 0 (height - 1) b + 1), V.n (flBase adr 0 (height - 1) b + 2)) else outs).2.2 wC)
    (by simp)
  simp only [Atom.Holds] at hc hw
  refine ⟨?_, hm, ?_⟩
  · rw [← r1, ← hc]
    cases fresh <;> rfl
  · rw [← hw]
    cases fresh <;> rfl

/-! ## The arms -/

theorem foldArmsRest_length (atV : V) (adr : Nat → Nat → Sum V Nat) (height : Nat) (node0 : V)
    (outs : V × V × V) (markV : V) (markC wC : Nat → E) :
    ∀ (m index b : Nat), (foldArmsRest atV adr height node0 outs markV markC wC m index b).1.length = m
  | 0, _, _ => rfl
  | m + 1, index, b => by
      simp only [foldArmsRest, List.length_cons,
        foldArmsRest_length atV adr height node0 outs markV markC wC m]

theorem foldArmsRest_getElem (atV : V) (adr : Nat → Nat → Sum V Nat) (height : Nat) (node0 : V)
    (outs : V × V × V) (markV : V) (markC wC : Nat → E) :
    ∀ (m index b k : Nat)
      (hk : k < (foldArmsRest atV adr height node0 outs markV markC wC m index b).1.length),
      (foldArmsRest atV adr height node0 outs markV markC wC m index b).1[k] =
        (foldArm atV (adr (index + k)) height (index + k) node0 outs markV (markC (index + k))
          (wC (index + k)) false (foldArmsRest atV adr height node0 outs markV markC wC k index b).2).1
  | 0, _, _, k, hk => absurd hk (by simp [foldArmsRest])
  | m + 1, index, b, k, hk => by
      rcases k with _ | k
      · rfl
      · have := foldArmsRest_getElem atV adr height node0 outs markV markC wC m (index + 1)
          (foldArm atV (adr index) height index node0 outs markV (markC index) (wC index) false b).2 k
          (by simp only [foldArmsRest, List.length_cons, foldArmsRest_length] at hk ⊢; omega)
        rw [show index + 1 + k = index + (k + 1) by omega] at this
        exact this

theorem foldArms_length (atV : V) (adr : Nat → Nat → Sum V Nat) (height : Nat) (node0 markV : V)
    (markC wC : Nat → E) (b : Nat) :
    (foldArms atV adr height node0 markV markC wC b).1.length = 2 ^ height := by
  simp only [foldArms, List.length_cons, foldArmsRest_length]
  have : 1 ≤ 2 ^ height := Nat.one_le_two_pow
  omega

/-- The base of arm `index` of a fold. -/
def foAB (atV : V) (adr : Nat → Nat → Sum V Nat) (height : Nat) (node0 markV : V)
    (markC wC : Nat → E) (b index : Nat) : Nat :=
  if index = 0 then b else
    (foldArmsRest atV adr height node0 (foldArms atV adr height node0 markV markC wC b).2.2 markV
      markC wC (index - 1) 1
      (foldArm atV (adr 0) height 0 node0 (.n 0, .n 0, .n 0) markV (markC 0) (wC 0) true b).2).2

theorem foldLevels_atoms (atV : V) (adr : Nat → Sum V Nat) (index : Nat) :
    ∀ (m l : Nat) (cur : V) (b : Nat), atomsOnly (foldLevels atV adr index m l cur b).1 = true
  | 0, _, _, _ => rfl
  | m + 1, l, cur, b => by
      simp only [foldLevels, atomsOnly_append, foldLevels_atoms atV adr index m, Bool.and_true]
      unfold foldLevel
      split <;> rfl

theorem foldArm_atoms (atV : V) (adr : Nat → Sum V Nat) (height index : Nat) (node0 : V)
    (outs : V × V × V) (markV : V) (markC wC : E) (fresh : Bool) (b : Nat) :
    atomsOnly (foldArm atV adr height index node0 outs markV markC wC fresh b).1 = true := by
  simp only [foldArm, atomsOnly_append, foldLevels_atoms]
  rfl

theorem foldArms_atoms (atV : V) (adr : Nat → Nat → Sum V Nat) (height : Nat) (node0 markV : V)
    (markC wC : Nat → E) (b : Nat) :
    ∀ a ∈ (foldArms atV adr height node0 markV markC wC b).1, atomsOnly a = true := by
  have hr : ∀ m index b' (outs : V × V × V),
      ∀ a ∈ (foldArmsRest atV adr height node0 outs markV markC wC m index b').1, atomsOnly a = true := by
    intro m
    induction m with
    | zero => intro _ _ _ a ha; simp [foldArmsRest] at ha
    | succ m ih =>
        intro index b' outs a ha
        simp only [foldArmsRest, List.mem_cons] at ha
        rcases ha with rfl | ha
        · exact foldArm_atoms _ _ _ _ _ _ _ _ _ _ _
        · exact ih _ _ _ a ha
  intro a ha
  simp only [foldArms, List.mem_cons] at ha
  rcases ha with rfl | ha
  · exact foldArm_atoms _ _ _ _ _ _ _ _ _ _ _
  · exact hr _ _ _ _ a ha

/-- **Arm `index` of a fold, sound**: the leaf folded into the top cell of the index's top bit,
the mark and the weight of `index`. -/
theorem foldArms_sound (hp : PadOK σ sPad) {atV : V} {adr : Nat → Nat → Sum V Nat} {height : Nat}
    {node0 markV : V} {markC wC : Nat → E} {b index : Nat}
    (hidx : index < (foldArms atV adr height node0 markV markC wC b).1.length)
    (h : AtomsHold rd σ (foldArms atV adr height node0 markV markC wC b).1[index]) :
    σ (if index / 2 ^ (height - 1) = 0 then (foldArms atV adr height node0 markV markC wC b).2.2.1
        else (foldArms atV adr height node0 markV markC wC b).2.2.2.1) =
        mFold (σ sPP) (flAdr σ atV (adr index)) index.testBit
          (fun l' => σ (.n (flBase (adr index) 0 l'
            (foAB atV adr height node0 markV markC wC b index))))
          (height - 1) 0 (σ node0) ∧
      σ markV = markC index ∧
      σ (foldArms atV adr height node0 markV markC wC b).2.2.2.2 = wC index := by
  rcases index with _ | index
  · have e : (foldArms atV adr height node0 markV markC wC b).1[0] =
        (foldArm atV (adr 0) height 0 node0 (.n 0, .n 0, .n 0) markV (markC 0) (wC 0) true b).1 := rfl
    rw [e] at h
    have := foldArm_sound hp h
    have hb : (foldArm atV (adr 0) height 0 node0 (.n 0, .n 0, .n 0) markV (markC 0) (wC 0) true b).2 =
        flBase (adr 0) 0 (height - 1) b + 3 := by
      simp only [foldArm, ↓reduceIte]
      rw [(foldLevels_sound (σ := σ) (rd := rd) hp (height - 1) 0 node0 b
        (h.sub fun x hx => by unfold foldArm; simp only; exact List.mem_append_left _ hx)).2]
    simp only [Nat.zero_div, ↓reduceIte] at this ⊢
    have e1 : (foldArms atV adr height node0 markV markC wC b).2.2.1 =
        .n (flBase (adr 0) 0 (height - 1) b) := by
      simp only [foldArms]
      rw [hb]
      rfl
    have e2 : (foldArms atV adr height node0 markV markC wC b).2.2.2.2 =
        .n (flBase (adr 0) 0 (height - 1) b + 2) := by
      simp only [foldArms]
      rw [hb]
      rfl
    rw [e1, e2]
    exact ⟨this.1, this.2.1, this.2.2⟩
  · have e : (foldArms atV adr height node0 markV markC wC b).1[index + 1] =
        (foldArm atV (adr (index + 1)) height (index + 1) node0
          (foldArms atV adr height node0 markV markC wC b).2.2 markV (markC (index + 1))
          (wC (index + 1)) false (foAB atV adr height node0 markV markC wC b (index + 1))).1 := by
      have := foldArmsRest_getElem atV adr height node0
        (foldArms atV adr height node0 markV markC wC b).2.2 markV markC wC (2 ^ height - 1) 1
        (foldArm atV (adr 0) height 0 node0 (.n 0, .n 0, .n 0) markV (markC 0) (wC 0) true b).2 index
        (by
          rw [foldArmsRest_length]
          simp only [foldArms, List.length_cons, foldArmsRest_length] at hidx
          omega)
      rw [show 1 + index = index + 1 by omega] at this
      exact this
    rw [e] at h
    have := foldArm_sound hp h
    simp only [Bool.false_eq_true, ↓reduceIte] at this
    exact this

end
end LeanVM.Guest.B1.Sig
