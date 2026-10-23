/-
  LeanVM.Guest.B1.Sig.SphincsForest

  The forest key `verify_sig_lean_sphincs` reaches is leanSPHINCS's `forestRecover` of the opening
  its frame holds: a sub-tree's two level-2 nodes, then a coordinate's two level-3 nodes.
-/

module

public import LeanVM.Guest.B1.Sig.SphincsTail

/-!
# The forest, as the Spec's

* `subVal`, `subSib`, `subOpening`: a sub-tree's opening, read off the frame (the chain values
  the forest key's dispatch hints, the fold's siblings, the other level-2 node);
* `subTops_eq`: the ordered level-2 nodes of the Spec's sub-tree are the guest's two cells;
* `topSib`, `coordOpening`, `coordKey_eq`: a coordinate's opening and its two level-3 nodes.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier (eOfNat)
open Sphincs Sphincs.Concrete

@[expose] public section

attribute [local irreducible] fkArms foldArms

/-- The hinted value of chain `i` of sub-tree `j` of coordinate `c` at base `b`. -/
noncomputable def subVal (σ : Val) (c j b i : Nat) : E :=
  σ (.n (fkCB (subT σ b) (.n (b + 11)) 0 (fkAB (2 * c + j) (.n (b + 11)) (b + 12) (subT σ b)) i))

/-- The fold's sibling at level `l` of sub-tree `j` of coordinate `c` at base `b`, the other
level-2 node at `l = 2`. -/
noncomputable def subSib (σ : Val) (c j : Nat) (enc : Option V) (b l : Nat) : E :=
  if l < 2 then σ (.n (flBase (subAdr (subA σ b)) 0 l
    (foAB (.n (b + 11)) subAdr 3 (subFk c j b).2.2.1 (.n (b + 1))
      (fun a => word (j * 2 ^ 39 + a * 2 ^ 40) 0 0) (fun a => cbMul a (58 + 3 * (2 * c + j)))
      (subE c j enc b).2.2 (subA σ b))))
  else σ (if subA σ b / 2 ^ 2 = 0 then (subFd c j enc b).2.2.2.1 else (subFd c j enc b).2.2.1)

/-- A sub-tree's opening, read off the frame. -/
noncomputable def subOpening (σ : Val) (c j : Nat) (enc : Option V) (b : Nat) : SubOpening :=
  ⟨fun i => sv (subVal σ c j b i.val), fun l => sv (subSib σ c j enc b l.val)⟩

theorem testBit_top {a n : Nat} (ha : a < 2 ^ (n + 1)) : a.testBit n = !(a / 2 ^ n == 0) := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have hlt : a / 2 ^ n < 2 := Nat.div_lt_of_lt_mul (by rw [pow_succ] at ha; exact ha)
  have h01 : a / 2 ^ n = 0 ∨ a / 2 ^ n = 1 := by
    generalize a / 2 ^ n = q at hlt ⊢
    omega
  rcases h01 with h | h <;> simp [h]

theorem sNode0_eq {rd : Reader} {σ : Val} (hpre : SPre rd σ) : σ (sNode 0) = eOfNat (sIdx σ) := by
  rw [hpre.nodes 0 (by norm_num), Nat.shiftRight_zero]

variable {rd : Reader} {σ : Val}

/-- **A sub-tree's two level-2 nodes**, as the Spec orders them. -/
theorem subTops_eq (hpre : SPre rd σ) {c : Coord} {s : SuperIdx} {j : SubIdx} {a : ChildIdx}
    {t : LutIdx} {leafAt : V} {enc : Option V} {bound : V} {b : Nat}
    (f : SubFacts σ c.val j.val leafAt enc bound b) (ha : a.val = subA σ b) (ht : t.val = subT σ b)
    (hleaf : σ leafAt = eOfNat (sIdx σ) + word (c.val * hiMul + s.val * 2 ^ 35) 0 0)
    {index : Index} (hidx : index.val = sIdx σ) :
    orderTops (a.val.testBit (subHeight - 1))
        (@subFold Id _ ⟨Node.keccakBits⟩ (spp (σ sPP)) index c s j a
          (subOpening σ c.val j.val enc b).path (subHeight - 1)
          (@childRecover Id _ ⟨Node.keccakBits⟩ (spp (σ sPP)) index c s j a (lut t)
            (subOpening σ c.val j.val enc b).values))
        ((subOpening σ c.val j.val enc b).path subTopLevel) =
      (sv (σ (subFd c.val j.val enc b).2.2.1), sv (σ (subFd c.val j.val enc b).2.2.2.1)) := by
  have hidx26 := sIdx_lt σ
  have hc8 : c.val < 8 := c.isLt
  have hs16 : s.val < 16 := s.isLt
  have hj2 : j.val < 2 := j.isLt
  have ha8 : a.val < 8 := a.isLt
  have hka : σ (.n (b + 11)) = eOfNat (sIdx σ) + word (c.val * hiMul + s.val * 2 ^ 35) 0 0 +
      word (j.val * 2 ^ 39 + a.val * 2 ^ 40) 0 0 := by
    rw [f.keyOK, hleaf, ha]
  -- the child leaf
  have hcr : @childRecover Id _ ⟨Node.keccakBits⟩ (spp (σ sPP)) index c s j a (lut t)
      (subOpening σ c.val j.val enc b).values = sv (σ (subFk c.val j.val b).2.2.1) := by
    show @childRecover Id _ ⟨Node.keccakBits⟩ (spp (σ sPP)) index c s j a (lut t)
      (fun i => sv (subVal σ c.val j.val b i.val)) = _
    rw [sChildRecover_cells sq_keccak (ka := σ (.n (b + 11)))
      (aL := σ (.n (b + 11)) + word (tw 16) 0 0) (lut t) (subVal σ c.val j.val b)
      (fun i t' => by
        rw [hka]
        show _ = Sphincs.fieldBytes (Sphincs.tweakFields 15 t'.val (chainSlot c s j a i) index.val)
        rw [hidx, show chainSlot c s j a i = c.val + 8 * s.val + 128 * j.val + 256 * a.val +
          2048 * i.val by simp [chainSlot, childSlot, subSlot]]
        exact fchainAdr_bytes hidx26 c.isLt s.isLt j.isLt a.isLt i.isLt t'.isLt)
      (by
        rw [hka]
        show _ = Sphincs.fieldBytes (Sphincs.tweakFields 16 0 (childSlot c s j a) index.val)
        rw [hidx, show childSlot c s j a = c.val + 8 * s.val + 128 * j.val + 256 * a.val by
          simp [childSlot, subSlot]]
        exact childLeafAdr_bytes hidx26 c.isLt s.isLt j.isLt a.isLt), f.leaf]
    refine congrArg sv (congrArg Prod.fst (congrArg hcell (congrArg _ (congrArg _ ?_))))
    apply List.map_congr_left
    intro i hi
    have hi6 : i < 6 := List.mem_range.mp hi
    have hl := spCode_lut t ⟨i, hi6⟩
    rw [ht] at hl
    simp only [fEnds, Nat.mod_eq_of_lt hi6, ← hl]
    rfl
  -- the fold
  set A : Nat → E := fun l => if l < 2 then flAdr σ (.n (b + 11)) (subAdr a.val) l else
    eOfNat (sIdx σ + 2 ^ 32 * (c.val + 8 * s.val + 128 * j.val + 256 * (l + 1) +
      1024 * (a.val / 2 ^ (l + 1))) + 2 ^ 56 * (17 + 32 * 0)) with hA
  have hAb : ∀ (l : Fin subHeight) (node : ChildIdx), node.val = a.val / 2 ^ (l.val + 1) →
      cellBytes (A l.val) = tweakBytes (.subNode index c s j l node) := by
    intro l node hn
    show _ = Sphincs.fieldBytes (Sphincs.tweakFields 17 0
      (subSlot c s j + 256 * (l.val + 1) + 1024 * node.val) index.val)
    rw [hn, hidx, subSlot]
    have hl3 : l.val < 3 := l.isLt
    have hn8 : node.val < 8 := node.isLt
    by_cases hl : l.val < 2
    · simp only [hA, hl, ↓reduceIte, flAdr, subAdr]
      rw [hka, hpre.subTws a.val a.isLt l.val hl]
      exact subNodeAdr_bytes hidx26 c.isLt s.isLt j.isLt a.isLt hl
    · simp only [hA, hl, ↓reduceIte]
      have hq : a.val / 2 ^ (l.val + 1) < 2 ^ 2 := div_two_pow_lt (n := 2) (show a.val < 2 ^ (2 + 1) from a.isLt)
      exact sAdr_bytes (by omega) (by omega) (by omega) (by omega)
  have hsf := sSubFold_cells sq_keccak (pp := σ sPP) (A := A) (index := index) (c := c) (s := s)
    (j := j) (a := a) hAb (subSib σ c.val j.val enc b) (subHeight - 1) (by decide)
    (σ (subFk c.val j.val b).2.2.1)
  have hreach : xFold (σ sPP) A (fun l => a.val.testBit l) (subSib σ c.val j.val enc b)
      (subHeight - 1) (σ (subFk c.val j.val b).2.2.1) =
      σ (if a.val / 2 ^ 2 = 0 then (subFd c.val j.val enc b).2.2.1
        else (subFd c.val j.val enc b).2.2.2.1) := by
    rw [ha, f.node, mFold_eq_xFold]
    apply xFold_congr
    intro l hl
    have hl2 : l < 2 := by simpa [subHeight] using hl
    refine ⟨?_, rfl, ?_⟩
    · simp only [hA, hl2, ↓reduceIte, ha]
    · simp only [subSib, hl2, ↓reduceIte]
  show orderTops (a.val.testBit (subHeight - 1))
      (@subFold Id _ ⟨Node.keccakBits⟩ (spp (σ sPP)) index c s j a
        (fun l => sv (subSib σ c.val j.val enc b l.val)) (subHeight - 1) _)
      (sv (subSib σ c.val j.val enc b (subHeight - 1))) = _
  rw [hcr, hsf, hreach]
  have hb2 : (a.val).testBit 2 = !(a.val / 2 ^ 2 == 0) := testBit_top (show a.val < 2 ^ (2 + 1) from a.isLt)
  rw [show subHeight - 1 = 2 from rfl, hb2]
  unfold subSib
  simp only [lt_irrefl, ↓reduceIte, ← ha]
  by_cases h0 : a.val / 2 ^ 2 = 0
  · simp only [h0, ↓reduceIte]
    rfl
  · simp only [h0, ↓reduceIte]
    have : (a.val / 2 ^ 2 == 0) = false := by simpa using h0
    rw [this]
    rfl

end
end LeanVM.Guest.B1.Sig
