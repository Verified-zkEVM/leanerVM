/-
  LeanVM.Guest.B1.Sig.SpWotsLayout

  Where `sp_wots`'s template (`SpWotsT`) puts its groups, its arms and its chains' starts: the
  groups' running product, encoding and base, the arms' bases, the renaming each arm's padding run
  makes, and the value each chain's start is hinted into, for given digit words.
-/

module

public import LeanVM.Guest.B1.Sig.SpWotsT
public import LeanVM.Guest.B1.Sig.WotsSound

/-!
# `sp_wots`'s layout

* `padRenOf X sel L`: the renaming `withPad X sel L` makes (`padShift X P` at its padding base `P`,
  the identity when nothing is selected); `withPad_eq`: `withPad` is that renaming with the run
  inserted;
* `spSlots`, `spPo`, `spEo`, `spArmV`: arm `k`'s slots, product and encoding outputs, and the shared
  arm (`armT spW`, its padding run virtual) whose moved form `spArmT` is;
* `spArmB`, `spArmsT_getElem`: the base of arm `k` and the arm the dispatch takes;
* `spState`, `spGroupsT_eq`: group `p`'s running product, encoding and base (`cwState` for `sp_wots`);
* `spN`, `spStartAt K i`: group `p`'s digits and the value chain `i`'s start is hinted into when
  group `p` takes arm `K p`.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Parameters

@[expose] public section

/-! ## The padding run's renaming -/

/-- The renaming `withPad X sel L` makes: the virtual run at `X` to the padding base, every value
from it five up; the identity when `sel` picks nothing. -/
def padRenOf (X : Nat) (sel : Stmt → Bool) (L : List Stmt) : V → V :=
  match L.findIdx? sel with
  | none => id
  | some i => padShift X (firstDef (L.getD i default))

/-! ## The arms -/

/-- Arm `k`'s slots: arm `0`'s as the shared template lays them out, the others' the real ones. -/
def spSlots (fold : Bool) (B k : Nat) : Nat → Nat → Nat :=
  if k = 0 then slotsT spW fold B else spSlot fold B

/-- Arm `k`'s product output. -/
def spPo (fold : Bool) (n B k : Nat) : V :=
  if k = 0 then prodT spW fold n B else .n (spProd fold n B)

/-- Arm `k`'s encoding output. -/
def spEo (fold : Bool) (n B k : Nat) : V :=
  if k = 0 then encT spW fold n B else .n (spEnc fold n B)

/-- Arm `k` of the group from `B`, from base `b`, its padding run virtual. -/
def spArmV (first n : Nat) (fold : Bool) (B : Nat) (prodIn encIn : V) (k b : Nat) : List Stmt × Nat :=
  armT spW (spSlots fold B k) first n fold prodIn encIn (spPo fold n B k) (spEo fold n B k) k b

theorem spArmK_eq (first n : Nat) (fold : Bool) (B : Nat) (prodIn encIn : V) (k b : Nat) :
    spArmK first n fold B prodIn encIn k b =
      ((withPad spVPad isTopConst (spArmV first n fold B prodIn encIn k b).1).1,
        (spArmV first n fold B prodIn encIn k b).2 +
          (withPad spVPad isTopConst (spArmV first n fold B prodIn encIn k b).1).2) := by
  by_cases hk : k = 0
  · subst hk; rfl
  · simp only [spArmK, hk, ↓reduceIte, spArmT, spArmV, spSlots, spPo, spEo]

/-- The base of arm `k` of the group from `B`. -/
def spArmB (first n : Nat) (fold : Bool) (B : Nat) (prodIn encIn : V) : Nat → Nat
  | 0 => B + 5
  | k + 1 =>
      let a := spArmK first n fold B prodIn encIn k (spArmB first n fold B prodIn encIn k)
      if k = 0 then a.2 + 2 else a.2

theorem spArmsT_cons (first n : Nat) (fold : Bool) (B : Nat) (prodIn encIn : V) (m k b : Nat) :
    spArmsT first n fold B prodIn encIn (m + 1) k b =
      ((spArmK first n fold B prodIn encIn k b).1 ::
        (spArmsT first n fold B prodIn encIn m (k + 1)
          (if k = 0 then (spArmK first n fold B prodIn encIn k b).2 + 2
            else (spArmK first n fold B prodIn encIn k b).2)).1,
        (spArmsT first n fold B prodIn encIn m (k + 1)
          (if k = 0 then (spArmK first n fold B prodIn encIn k b).2 + 2
            else (spArmK first n fold B prodIn encIn k b).2)).2) := by
  rfl

theorem spArmsT_length (first n : Nat) (fold : Bool) (B : Nat) (prodIn encIn : V) :
    ∀ m k b, (spArmsT first n fold B prodIn encIn m k b).1.length = m
  | 0, _, _ => rfl
  | m + 1, k, b => by
      rw [spArmsT_cons]
      simp [spArmsT_length first n fold B prodIn encIn m]

/-- The base arm `k + j` of `spArmsT` from arm `k` at `b` starts from. -/
def spArmBase (first n : Nat) (fold : Bool) (B : Nat) (prodIn encIn : V) : Nat → Nat → Nat → Nat
  | _, 0, b => b
  | k, j + 1, b => spArmBase first n fold B prodIn encIn (k + 1) j
      (if k = 0 then (spArmK first n fold B prodIn encIn k b).2 + 2
        else (spArmK first n fold B prodIn encIn k b).2)

theorem spArmsT_getElem (first n : Nat) (fold : Bool) (B : Nat) (prodIn encIn : V) :
    ∀ m k b j (hj : j < (spArmsT first n fold B prodIn encIn m k b).1.length),
      (spArmsT first n fold B prodIn encIn m k b).1[j] =
        (spArmK first n fold B prodIn encIn (k + j) (spArmBase first n fold B prodIn encIn k j b)).1
  | 0, _, _, j, hj => absurd hj (by simp [spArmsT])
  | m + 1, k, b, 0, _ => by simp [spArmsT_cons, spArmBase]
  | m + 1, k, b, j + 1, hj => by
      have hj' : j < (spArmsT first n fold B prodIn encIn m (k + 1)
          (if k = 0 then (spArmK first n fold B prodIn encIn k b).2 + 2
            else (spArmK first n fold B prodIn encIn k b).2)).1.length := by
        rw [spArmsT_length]; rw [spArmsT_length] at hj; omega
      simp only [spArmsT_cons, List.getElem_cons_succ]
      rw [spArmsT_getElem first n fold B prodIn encIn m (k + 1) _ j hj']
      simp only [spArmBase, show k + 1 + j = k + (j + 1) by omega]

theorem spArmBase_eq (first n : Nat) (fold : Bool) (B : Nat) (prodIn encIn : V) :
    ∀ k, spArmBase first n fold B prodIn encIn 0 k (B + 5) = spArmB first n fold B prodIn encIn k := by
  suffices h : ∀ j k, spArmBase first n fold B prodIn encIn k j (spArmB first n fold B prodIn encIn k) =
      spArmB first n fold B prodIn encIn (k + j) by
    intro k; simpa [spArmB] using h k 0
  intro j
  induction j with
  | zero => intro k; rfl
  | succ j ih =>
      intro k
      simp only [spArmBase]
      rw [show k + (j + 1) = k + 1 + j by omega, ← ih (k + 1)]
      rfl

theorem spArmsT_end (first n : Nat) (fold : Bool) (B : Nat) (prodIn encIn : V) :
    ∀ m k, (spArmsT first n fold B prodIn encIn m k (spArmB first n fold B prodIn encIn k)).2 =
      spArmB first n fold B prodIn encIn (k + m)
  | 0, k => rfl
  | m + 1, k => by
      rw [spArmsT_cons, show k + (m + 1) = k + 1 + m by omega, ← spArmsT_end first n fold B prodIn encIn m (k + 1)]
      rfl

/-- **The arm the dispatch of a group takes**, its `k`-th. -/
theorem spGroupArm (first n : Nat) (fold : Bool) (B : Nat) (prodIn encIn : V) (k : Nat)
    (hk : k < (spArmsT first n fold B prodIn encIn (4 ^ n) 0 (B + 5)).1.length) :
    (spArmsT first n fold B prodIn encIn (4 ^ n) 0 (B + 5)).1[k] =
      (spArmK first n fold B prodIn encIn k (spArmB first n fold B prodIn encIn k)).1 := by
  rw [spArmsT_getElem, spArmBase_eq, Nat.zero_add]

theorem spGroupT_end (first n : Nat) (fold : Bool) (prodIn encIn : V) (B : Nat) :
    (spGroupT first n fold prodIn encIn B).2 = spArmB first n fold B prodIn encIn (4 ^ n) := by
  have := spArmsT_end first n fold B prodIn encIn (4 ^ n) 0
  rw [Nat.zero_add] at this
  exact this

/-! ## The groups -/

/-- Group `p`'s running product's and encoding's cells and its base. -/
def spState : Nat → V × V × Nat
  | 0 => (.n 0, .n 0, 13)
  | p + 1 =>
      let st := spState p
      (.n (spProd (p == 0) 3 st.2.2), .n (spEnc (p == 0) 3 st.2.2),
        (spGroupT (3 * p) 3 (p == 0) st.1 st.2.1 st.2.2).2)

theorem spState_zero : spState 0 = (.n 0, .n 0, 13) := by rw [spState]

theorem spState_succ (p : Nat) : spState (p + 1) =
    (.n (spProd (p == 0) 3 (spState p).2.2), .n (spEnc (p == 0) 3 (spState p).2.2),
      (spGroupT (3 * p) 3 (p == 0) (spState p).1 (spState p).2.1 (spState p).2.2).2) := by
  rw [spState]

theorem spGroupsT_succ (m p : Nat) (prod enc : V) (B : Nat) : spGroupsT (m + 1) p prod enc B =
    ((spGroupT (3 * p) 3 (p == 0) prod enc B).1 ++
        (spGroupsT m (p + 1) (.n (spProd (p == 0) 3 B)) (.n (spEnc (p == 0) 3 B))
          (spGroupT (3 * p) 3 (p == 0) prod enc B).2).1,
      (spGroupsT m (p + 1) (.n (spProd (p == 0) 3 B)) (.n (spEnc (p == 0) 3 B))
          (spGroupT (3 * p) 3 (p == 0) prod enc B).2).2.1,
      (List.range 3).map (fun r => V.n (spSlot (p == 0) B r 2)) ++
        (spGroupsT m (p + 1) (.n (spProd (p == 0) 3 B)) (.n (spEnc (p == 0) 3 B))
          (spGroupT (3 * p) 3 (p == 0) prod enc B).2).2.2.1,
      (spGroupsT m (p + 1) (.n (spProd (p == 0) 3 B)) (.n (spEnc (p == 0) 3 B))
          (spGroupT (3 * p) 3 (p == 0) prod enc B).2).2.2.2) := by
  rw [spGroupsT]

theorem spGroupsT_eq : ∀ (m p : Nat),
    (spGroupsT m p (spState p).1 (spState p).2.1 (spState p).2.2).2 =
      ((spState (p + m)).2.2, (List.range m).flatMap (fun j => (List.range 3).map fun r =>
        V.n (spSlot (p + j == 0) (spState (p + j)).2.2 r 2)),
        (spState (p + m)).1, (spState (p + m)).2.1)
  | 0, p => by rw [spGroupsT]; simp
  | m + 1, p => by
      have ih := spGroupsT_eq m (p + 1)
      rw [spState_succ p] at ih
      rw [spGroupsT_succ, ih, show p + 1 + m = p + (m + 1) by omega]
      simp only [Prod.mk.injEq, true_and, and_true]
      rw [List.range_succ_eq_map (n := m), List.flatMap_cons, List.flatMap_map]
      simp only [Nat.add_zero]
      congr 1
      apply List.flatMap_congr
      intro j _
      simp only [show p + 1 + j = p + (j + 1) by omega]

theorem spGroupsT_fst (m p : Nat) :
    (spGroupsT (m + 1) p (spState p).1 (spState p).2.1 (spState p).2.2).1 =
      (spGroupT (3 * p) 3 (p == 0) (spState p).1 (spState p).2.1 (spState p).2.2).1 ++
        (spGroupsT m (p + 1) (spState (p + 1)).1 (spState (p + 1)).2.1 (spState (p + 1)).2.2).1 := by
  rw [spGroupsT_succ, spState_succ p]

/-- `spGs` from the states: the codeword's base after its 21 groups, the tips, product and encoding. -/
theorem spGs_eq : spGs.2 = ((spState 21).2.2, (List.range 21).flatMap (fun j => (List.range 3).map
    fun r => V.n (spSlot (j == 0) (spState j).2.2 r 2)), (spState 21).1, (spState 21).2.1) := by
  have h := spGroupsT_eq 21 0
  rw [spState_zero] at h
  simp only [Nat.zero_add] at h
  unfold spGs
  rw [h]

theorem spGs_fst : spGs.1 = (spGroupsT 21 0 (spState 0).1 (spState 0).2.1 (spState 0).2.2).1 := by
  rw [spState_zero]; rfl

/-- The digits of group `p`: three, the last chain's one. -/
def spN (p : Nat) : Nat := if p < 21 then 3 else 1

/-- **Where chain `i`'s start is hinted** when group `p = i / 3` takes arm `K p`: arm `K p`'s start of
chain `i % 3` (`armStart`), moved by the arm's padding run. -/
def spStartAt (K : Nat → Nat) (i : Nat) : V :=
  let p := i / 3
  let st := spState p
  let k := K p
  let b := spArmB (3 * p) (spN p) (p == 0) st.2.2 st.1 st.2.1 k
  padRenOf spVPad isTopConst (spArmV (3 * p) (spN p) (p == 0) st.2.2 st.1 st.2.1 k b).1
    (armStart spW (spSlots (p == 0) st.2.2 k) (p == 0) k b (i % 3))

end
end LeanVM.Guest.B1.Sig
