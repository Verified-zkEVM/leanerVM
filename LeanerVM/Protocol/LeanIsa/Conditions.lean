/-
  LeanerVM.Protocol.LeanIsa.Conditions

  The leanISA instance meets the bus phase's side conditions, at every size.
-/

module

public import LeanerVM.Protocol.LeanIsa
public import LeanerVM.Protocol.Bus

/-!
# The bus phase's conditions at the leanISA instance

`leanIsa_conditions`: at every size the instance meets `Bus.Conditions`, so leanVM's master
theorems apply to it: the pull side has as many leaves as the push side (each table pulls as
often as it pushes, and the boundary blocks pair up), the count side has no more (each count is
a pull's), and `JUMP`, the one table with constraints, pushes. A module of its own, so that the
instance and the adaptor import no module of the oracle protocol.
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Arithmetization CompPoly CPoly
open CMlPolynomialEval

@[expose] public section

namespace LeanIsa

/-- Summing over a list with repetitions. -/
private theorem sum_flatMap_replicate {α : Type} (l : List α) (a : α → ℕ) (f : α → ℕ)
    (g : ℕ → ℕ) :
    ((l.flatMap fun x ↦ List.replicate (a x) (f x)).map g).sum =
      (l.map fun x ↦ a x * g (f x)).sum := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.flatMap_cons, List.map_append, List.sum_append, ih, List.map_replicate,
      List.sum_replicate, smul_eq_mul, List.map_cons, List.sum_cons]

/-- Every table has at most as many count columns as push flushes. -/
private theorem counts_le_pushes : ∀ j : Fin 9,
    (counts j).length ≤ ((flushes j).filter fun f ↦ decide (f.1 = Side.push)).length := by
  decide +kernel

/-- A table with a constraint has a push flush. -/
private theorem constrained_pushes : ∀ j : Fin 9, 0 < (LeanIsa.constraints j).length →
    0 < ((LeanIsa.flushes j).filter fun f ↦ decide (f.1 = Side.push)).length := by
  decide +kernel

variable (F : FlockSpec) (prog : Program) (s : Sizes)

/-- A side's leaf count, from its blocks' log-heights. -/
private theorem leafCount_eq (I : M3Instance) (k : Fin 3) :
    Bus.leafCount I k = (((Bus.sources I k).map Bus.Source.κ).map (2 ^ ·)).sum := by
  rw [Bus.leafCount, List.map_map]
  rfl

/-- The leaves of the push side, by table. -/
private theorem leafCount_push :
    Bus.leafCount (leanIsaInstance F prog s) 0 =
      (((boundary prog s).filter fun b ↦ decide (b.side = .push)).map fun b ↦ 2 ^ b.κ).sum +
      ((List.finRange 9).map fun j ↦
        ((LeanIsa.flushes j).filter fun f ↦ decide (f.1 = Side.push)).length *
          2 ^ height prog s j).sum := by
  rw [leafCount_eq]
  change ((((Bus.sideSources _ .push).map Bus.Source.κ).map (2 ^ ·))).sum = _
  rw [Bus.sideSources_map_κ, List.map_append, List.sum_append, sum_flatMap_replicate,
    List.map_map]
  rfl

/-- The pull side has as many leaves as the push side: a table pulls as often as it pushes, and the
boundary blocks pair up. -/
private theorem leafCount_pull :
    Bus.leafCount (leanIsaInstance F prog s) 1 = Bus.leafCount (leanIsaInstance F prog s) 0 := by
  rw [leafCount_push, leafCount_eq]
  change ((((Bus.sideSources _ .pull).map Bus.Source.κ).map (2 ^ ·))).sum = _
  rw [Bus.sideSources_map_κ, List.map_append, List.sum_append, sum_flatMap_replicate,
    List.map_map]
  congr 1

/-- The count side has at most as many leaves as the push side. -/
private theorem leafCount_count_le :
    Bus.leafCount (leanIsaInstance F prog s) 2 ≤ Bus.leafCount (leanIsaInstance F prog s) 0 := by
  rw [leafCount_push, leafCount_eq]
  change ((((Bus.countSources _).map Bus.Source.κ).map (2 ^ ·))).sum ≤ _
  rw [Bus.countSources_map_κ, sum_flatMap_replicate]
  refine le_add_left (List.sum_le_sum fun j _ ↦ ?_)
  exact Nat.mul_le_mul_right _ (counts_le_pushes j)

/-- The leanISA instance meets the bus phase's side conditions, at every size. -/
theorem leanIsa_conditions : Bus.Conditions (leanIsaInstance F prog s) where
  one_le_d := by norm_num
  constrained j hj := by
    have hfit : Bus.leafCount (leanIsaInstance F prog s) 0 ≤ 2 ^ (leanIsaInstance F prog s).μBus :=
      (Bus.blocks_total _ 0).symm.trans_le (Bus.push_fits _)
    have hpos := constrained_pushes j (List.length_pos_iff.mpr hj)
    refine (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp (le_trans ?_ hfit)
    rw [leafCount_push]
    refine le_add_left ((Nat.le_mul_of_pos_left _ hpos).trans ?_)
    exact List.le_sum_of_mem (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩)
  pull_fits := by
    rw [leafCount_pull, ← Bus.blocks_total]
    exact Bus.push_fits _
  count_fits := (leafCount_count_le F prog s).trans
    ((Bus.blocks_total _ 0).symm.trans_le (Bus.push_fits _))

end LeanIsa

end
end LeanerVM.Protocol
