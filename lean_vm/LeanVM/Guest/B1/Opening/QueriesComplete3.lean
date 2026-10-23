/-
  LeanVM.Guest.B1.Opening.QueriesComplete3

  The completeness of a query's Merkle path and cap leaf.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesComplete2

/-!
# A query's path and cap leaf, completeness

The honest nodes are the climb's (`node_eq`: the leaf's digest, then each level's pair hash,
`climbD_snoc`); with the memory holding the path's frame run, the nodes stored at their bits'
sides, the cap leaf and the parent's flag (what `QueryOpens` says), every atom of the path
(`oqPath_complete`) and of the cap leaf (`oqCap_complete`) holds at the honest values.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

namespace QD

variable (d : QD) {rd : Reader} {σ : Val}

/-! ## The values of the path and of the cap -/

theorem capQ_eq : ∀ j, j < 7 → d.capQ j = gen ^ (d.q / 2 ^ (d.s.pd + 1) % 2 ^ (j + 1))
  | 0, _ => by
    rw [capQ, QD.bit, word_capFac (by decide), word_one, bit_factor,
      Nat.testBit_eq_decide_div_mod_eq]
    congr 1
    by_cases h : d.q / 2 ^ (d.s.pd + 1) % 2 = 1 <;> simp [h]
    omega
  | j + 1, hj => by
    rw [capQ, QD.bit, capQ_eq j (by omega), word_capFac (by omega), word_one,
      bit_factor, ← pow_add,
      show d.q / 2 ^ (d.s.pd + 1) % 2 ^ (j + 1 + 1) = d.q / 2 ^ (d.s.pd + 1) % 2 ^ (j + 1) +
        2 ^ (j + 1) * (d.q / 2 ^ (d.s.pd + 1) / 2 ^ (j + 1) % 2) from Nat.mod_pow_succ,
      Nat.testBit_eq_decide_div_mod_eq, Nat.div_div_eq_div_mul, ← pow_add,
      show d.s.pd + 2 + j = d.s.pd + 1 + (j + 1) by omega]
    congr 1
    by_cases h : d.q / 2 ^ (d.s.pd + 1 + (j + 1)) % 2 = 1
    · simp [h]
    · simp [show d.q / 2 ^ (d.s.pd + 1 + (j + 1)) % 2 = 0 by omega]

theorem pc_canonical (k : ℕ) : IsCanonical128 (d.pc k) := by
  unfold pc pathCell
  dsimp only
  split <;> exact canonical_ofLimbs _ _

/-- A level's pair hash is the climb's step. -/
theorem level_out {l : ℕ} (hl : l < d.sibs.length) {o0 o1 : E}
    (h : HashesPair (d.pc (4 * l)) (d.pc (4 * l + 1)) (d.pc (4 * l + 2)) (d.pc (4 * l + 3)) o0 o1) :
    (o0, o1) = digestScalars (climbNode d.leaf d.q d.sibs (l + 1)) := by
  obtain ⟨dl, dr, hl', hr', hp⟩ := hashesPair_digests h
  have hcs : climbNode d.leaf d.q d.sibs (l + 1) =
      if d.q / 2 ^ l % 2 = 0 then hashPair (climbNode d.leaf d.q d.sibs l) (d.sibs.getD l (Vector.replicate 4 0))
      else hashPair (d.sibs.getD l (Vector.replicate 4 0)) (climbNode d.leaf d.q d.sibs l) := by
    rw [climbNode, List.take_add_one, List.getElem?_eq_getElem hl, Option.toList_some, climbD_snoc,
      List.length_take, min_eq_left (by omega)]
    simp [climbNode, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl]
  have i0 : (4 * l) / 4 = l ∧ (4 * l) % 4 = 0 ∧ (4 * l) % 2 = 0 := by omega
  have i1 : (4 * l + 1) / 4 = l ∧ (4 * l + 1) % 4 = 1 ∧ (4 * l + 1) % 2 = 1 := by omega
  have i2 : (4 * l + 2) / 4 = l ∧ (4 * l + 2) % 4 = 2 ∧ (4 * l + 2) % 2 = 0 := by omega
  have i3 : (4 * l + 3) / 4 = l ∧ (4 * l + 3) % 4 = 3 ∧ (4 * l + 3) % 2 = 1 := by omega
  rw [hp, hcs]
  by_cases hb : d.q.testBit l
  · have hb' : d.q / 2 ^ l % 2 = 1 := by
      rw [Nat.testBit_eq_decide_div_mod_eq] at hb; simpa using hb
    have c0 : d.pc (4 * l) = (digestScalars (d.sibs.getD l (Vector.replicate 4 0))).1 := by
      unfold pc pathCell; simp [i0, hb]
    have c1 : d.pc (4 * l + 1) = (digestScalars (d.sibs.getD l (Vector.replicate 4 0))).2 := by
      unfold pc pathCell; simp [i1, hb]
    have c2 : d.pc (4 * l + 2) = (digestScalars (climbNode d.leaf d.q d.sibs l)).1 := by
      unfold pc pathCell; simp [i2, hb]
    have c3 : d.pc (4 * l + 3) = (digestScalars (climbNode d.leaf d.q d.sibs l)).2 := by
      unfold pc pathCell; simp [i3, hb]
    have edl : dl = d.sibs.getD l (Vector.replicate 4 0) :=
      capDigestScalars_injective (by rw [← hl', c0, c1])
    have edr : dr = climbNode d.leaf d.q d.sibs l :=
      capDigestScalars_injective (by rw [← hr', c2, c3])
    rw [edl, edr]
    simp [hb']
  · have hb' : d.q / 2 ^ l % 2 = 0 := by
      rw [Nat.testBit_eq_decide_div_mod_eq] at hb; simp at hb; omega
    have c0 : d.pc (4 * l) = (digestScalars (climbNode d.leaf d.q d.sibs l)).1 := by
      unfold pc pathCell; simp [i0, hb]
    have c1 : d.pc (4 * l + 1) = (digestScalars (climbNode d.leaf d.q d.sibs l)).2 := by
      unfold pc pathCell; simp [i1, hb]
    have c2 : d.pc (4 * l + 2) = (digestScalars (d.sibs.getD l (Vector.replicate 4 0))).1 := by
      unfold pc pathCell; simp [i2, hb]
    have c3 : d.pc (4 * l + 3) = (digestScalars (d.sibs.getD l (Vector.replicate 4 0))).2 := by
      unfold pc pathCell; simp [i3, hb]
    have edl : dl = climbNode d.leaf d.q d.sibs l :=
      capDigestScalars_injective (by rw [← hl', c0, c1])
    have edr : dr = d.sibs.getD l (Vector.replicate 4 0) :=
      capDigestScalars_injective (by rw [← hr', c2, c3])
    rw [edl, edr]
    simp [hb']

end QD

end
end LeanVM.Guest.B1
