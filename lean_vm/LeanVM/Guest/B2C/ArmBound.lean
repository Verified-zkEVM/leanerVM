/-
  LeanVM.Guest.B2C.ArmBound

  `verify_lean_xmss`'s separately counted arms, bounded for every valuation: `costW` within the sum
  over its counted `match`es of their largest arm (`costMaxW`), `xmssArmC` per opcode, the
  hypothesis `hC` of `cnt_le_weight_arm` (`xmssArmC_spec`).
-/

module

public import LeanVM.Guest.B2C.CntWeight

/-!
# `verify_lean_xmss`'s arms, bounded

`costW acs σ ss op` adds, along the path `σ` takes through `ss`, the count of each separately
counted arm it passes. Whatever the path, it is at most `costMaxW acs op ss`: an `ite` its larger
side, a `match` its table's largest arm and its larger arm's own (`costMaxArms`). On
`verify_lean_xmss`'s body this is `xmssArmC op` (by `decide +kernel`), so `cnt_le_weight_arm`
holds at `C := xmssArmC` (`cnt_le_weight_xmss`).
-/

namespace LeanVM.Guest.B2C

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-- A counted `match`'s largest arm at `op`, `0` if not counted. -/
def keyMax (key : Option (List (List ℕ))) (op : Opcode) : ℕ :=
  match key with
  | some cs => (cs.map fun l => l.getD (opIdx op) 0).foldr max 0
  | none => 0

mutual
/-- The separately counted arms a statement can pass, at most. -/
def costMax1 (acs : List (ℕ × List (List ℕ))) (op : Opcode) : Stmt → ℕ
  | .ite _ z n => max (costMaxW acs op z) (costMaxW acs op n)
  | .match_ x arms => keyMax (armRaw acs x.idx) op + costMaxArms acs op arms
  | _ => 0

/-- The separately counted arms a block can pass, at most. -/
def costMaxW (acs : List (ℕ × List (List ℕ))) (op : Opcode) : List Stmt → ℕ
  | [] => 0
  | s :: ss => costMax1 acs op s + costMaxW acs op ss

/-- The separately counted arms an arm of a `match` can pass, at most. -/
def costMaxArms (acs : List (ℕ × List (List ℕ))) (op : Opcode) : List (List Stmt) → ℕ
  | [] => 0
  | a :: as => max (costMaxW acs op a) (costMaxArms acs op as)
end

theorem nth_getD_le_foldr (i : ℕ) : ∀ (cs : List (List ℕ)) (k : ℕ),
    (nth cs k []).getD i 0 ≤ (cs.map fun l => l.getD i 0).foldr max 0
  | [], _ => by simp [nth]
  | c :: cs, 0 => by simp [nth]
  | c :: cs, k + 1 => by
    simp only [nth, List.map_cons, List.foldr_cons]
    exact (nth_getD_le_foldr i cs k).trans (le_max_right _ _)

section Le

variable (acs : List (ℕ × List (List ℕ))) (σ : Val) (op : Opcode)

mutual
theorem cost1_le_max : ∀ s : Stmt, cost1 acs σ s op ≤ costMax1 acs op s
  | .atom _ => Nat.zero_le _
  | .ite c z n => by
    rw [cost1, costMax1]
    split
    · exact (costW_le_max z).trans (le_max_left _ _)
    · exact (costW_le_max n).trans (le_max_right _ _)
  | .match_ x arms => by
    rw [cost1, costMax1]
    exact costArms_le_max x arms 0 (armRaw acs x.idx)
  | .call .. => Nat.zero_le _
  | .callIf .. => Nat.zero_le _
  | .dispatch .. => Nat.zero_le _
  | .ret _ => Nat.zero_le _

theorem costW_le_max : ∀ ss : List Stmt, costW acs σ ss op ≤ costMaxW acs op ss
  | [] => by rw [costW, costMaxW]; exact Nat.zero_le _
  | s :: ss => by
    rw [costW, costMaxW, Pi.add_apply]
    exact Nat.add_le_add (cost1_le_max s) (costW_le_max ss)

theorem costArms_le_max (x : V) : ∀ (arms : List (List Stmt)) (k : ℕ) (key : Option (List (List ℕ))),
    costArms acs σ x key k arms op ≤ keyMax key op + costMaxArms acs op arms
  | [], _, _ => by rw [costArms]; exact Nat.zero_le _
  | a :: as, k, key => by
    rw [costArms, costMaxArms]
    split
    · rw [Pi.add_apply]
      refine Nat.add_le_add ?_ ((costW_le_max a).trans (le_max_left _ _))
      cases key with
      | none => exact Nat.zero_le _
      | some cs => exact nth_getD_le_foldr _ cs k
    · exact (costArms_le_max x as (k + 1) key).trans
        (Nat.add_le_add_left (le_max_right _ _) _)
end

end Le

/-- **`verify_lean_xmss`'s separately counted arms, per opcode**: the sum of its counted
`match`es' largest arms. -/
def xmssArmC (op : Opcode) : ℕ := [40, 80, 40, 0, 40, 348].getD (opIdx op) 0

set_option maxRecDepth 100000 in
theorem costMaxW_xmss (op : Opcode) :
    costMaxW (nth Data.cplArms 20 []) op (coreOf 20).body = xmssArmC op := by
  cases op <;> decide +kernel

/-- **`cnt_le_weight_arm`'s `hC` at `xmssArmC`**: `verify_lean_xmss`'s arms within `xmssArmC`, on
every valuation. -/
theorem xmssArmC_spec : ∀ op σ bufs kids rd args rets,
    (Memory.Tree.node "verify_lean_xmss" σ bufs kids).Valid coreProgram rd args rets →
      costW (nth Data.cplArms 20 []) σ (coreOf 20).body op ≤ xmssArmC op :=
  fun op σ _ _ _ _ _ _ => (costW_le_max _ σ op _).trans (costMaxW_xmss op).le

end
end LeanVM.Guest.B2C
