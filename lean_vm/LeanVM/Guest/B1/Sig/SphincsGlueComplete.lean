/-
  LeanVM.Guest.B1.Sig.SphincsGlueComplete

  Glue for `verify_sig_lean_sphincs`'s completeness: where the blocks' values lie, the forest key's
  nodes canonical, and the encoding's digest the literal of its digits.
-/

module

public import LeanVM.Guest.B1.Sig.SphincsKeyComplete

/-!
# Glue

* `sCs_nb`, `sMid_nb`, `sEnd_bounds`: the forest's and the middle's values lie below their ends,
  and the bases increase;
* `sT_canon`: the forest key's nodes are canonical;
* `enc_lit`: a digest decoding to an encoding is the literal of its digits, which sum to `123`.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier (eOfNat gen)
open Sphincs Sphincs.Concrete

@[expose] public section

attribute [local irreducible] sCoords kMsg codewordT merkleT fkArms foldArms sCoord

/-- The values of coordinates `c ..< c + m` lie below their end. -/
theorem sCoords_nb : ∀ (m c : Nat), NumBelow (cSt (c + m)).2.2
    (Stmt.valsList (sCoords m c (cSt c).1 (cSt c).2.1 (cSt c).2.2).1)
  | 0, c => by simp only [sCoords]; exact NumBelow.nil _
  | m + 1, c => by
      obtain ⟨b1, b2, b3, -⟩ := cSt_shape c
      obtain ⟨-, -, -, snb⟩ := sCoord_shape c b1 b2 b3
      rw [sCoords_cons, valsList_append, show c + (m + 1) = c + 1 + m by omega]
      exact (snb.mono (cSt_mono (c + 1) m)).append (sCoords_nb m (c + 1))

theorem sCs_nb : NumBelow sB (Stmt.valsList sCs.1) := by
  have := sCoords_nb 8 0
  rw [Nat.zero_add] at this
  rw [sB_eq]
  exact this

theorem sEnc_cells_nb : ∀ c ∈ sTops.map KC.cell, KCb (sFb.2.1 + 1) c := by
  have hB := sB_ge
  obtain ⟨f1, -, -⟩ := sFb_shape
  intro c hc
  simp only [sTops, List.map_append, List.map_cons, List.map_nil, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false, List.mem_map] at hc
  rcases hc with ((rfl | rfl) | ⟨v, hv, rfl⟩) | rfl
  · exact ⟨162, by omega, rfl⟩
  · exact ⟨164, by omega, rfl⟩
  · obtain ⟨k, hk, e⟩ := List.getElem_of_mem hv
    have hk16 : k < 16 := by rw [sTops_count] at hk; exact hk
    have := sT_nb hk16
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some, e] at this
    exact this.mono' (by omega)
  · exact ⟨_, by omega, rfl⟩

/-- The middle's values lie below the powers' end. -/
theorem sMid_nb : NumBelow (sEnc.2.1 + 10) (Stmt.valsList sMid) := by
  have hB := sB_ge
  obtain ⟨f1, f2, f3⟩ := sFb_shape
  obtain ⟨hE1, -⟩ := sEnc_ge
  rw [sMid_split, valsList_append, valsList_append, valsList_append, valsList_append]
  refine NumBelow.append ?_ (NumBelow.append ?_ (NumBelow.append ?_ (NumBelow.append ?_ ?_)))
  · rw [valsList_hint]; exact fun v hv => runV_mem_nb (by omega) hv
  · exact f3.mono (by omega)
  · have f2' : NBv sFb.2.1 sFb.2.2 := by rw [f1]; exact f2
    exact (nb_copyS f2').mono (by omega)
  · exact (kMsg_numBelow (by simp only [sPad]; omega) sEnc_cells_nb).mono
      (show sEnc.2.1 ≤ sEnc.2.1 + 10 by omega)
  · exact (csts_seq sEnc.2.1 (fun s => word (2 ^ s) 0 0) 10).numBelow

/-- The bases after the powers increase. -/
theorem sEnd_bounds : sEnc.2.1 + 10 < sCw.2.1 ∧ sCw.2.1 + 2 ≤ sLeaf.2.1 ∧ sLeaf.2.1 ≤ sMk.2.1 := by
  have hB := sB_ge
  obtain ⟨hE1, hE2⟩ := sEnc_ge
  have b1 : sEnc.2.1 + 10 < sCw.2.1 := by
    rw [sCw_eq]
    exact cwBase_lt (sWc sEnc.2.1) (q := 0) (G := 21) _ _ _ (by norm_num)
  have htips : sCw.2.2 = (List.range 64).map (cwTip sW (sEnc.2.1 + 10)) :=
    codewordT_tips sW (G := 21) (by norm_num) _ _ _
  have hcellNB : ∀ c ∈ (sPP :: V.n (sCw.2.1 + 1) :: sCw.2.2).map KC.cell, KCb (sCw.2.1 + 2) c := by
    intro c hc
    simp only [List.map_cons, List.mem_cons, htips, List.map_map, List.mem_map,
      List.mem_range, Function.comp_apply] at hc
    rcases hc with rfl | rfl | ⟨i, hi, rfl⟩
    · exact ⟨2, by omega, rfl⟩
    · exact ⟨_, by omega, rfl⟩
    · obtain ⟨j, ej, hj⟩ := cwTip_lt sW (G := 21) sTarget (.n sEnc.2.2) (sEnc.2.1 + 10)
        (by norm_num) (show i < 3 * 21 + 1 by omega)
      have hj' : j < sCw.2.1 := hj
      exact ⟨j, by omega, ej⟩
  exact ⟨b1, kMsg_le (show sPad + 5 ≤ sCw.2.1 + 2 by simp only [sPad]; omega) hcellNB, merkleT_snd_ge ..⟩

/-- **The forest key's nodes are canonical**, its coordinates' facts holding. -/
theorem sT_canon {σ : Val} {H : Nat → CoordH} {E1 E2 : Nat → E}
    (hpost : ∀ k < 8, CoordPost (E1 k) (E2 k) k (cSt k).1 (cSt k).2.1 (cSt k).2.2 (H k) σ) :
    ∀ k < 16, IsCanonical128 (sT σ k) := by
  intro k hk
  have hc8 : k / 2 < 8 := by omega
  obtain ⟨-, -, -, -, -, -, c1, c2, -⟩ := hpost (k / 2) hc8
  have hp := getD_pairs (fun k => (cCoord (0 + k)).2.2.2.2.1) (fun k => (cCoord (0 + k)).2.2.2.2.2)
    (.n 0) 8 (k / 2) hc8
  have e := sCoords_tops 8 0
  have ht : (cCoord (k / 2)).2.2.2.2 = ((coordFd (k / 2) (cSt (k / 2)).2.2
      (coordS1 (k / 2) (cSt (k / 2)).1 (cSt (k / 2)).2.1 (cSt (k / 2)).2.2).2.1).2.2.1,
      (coordFd (k / 2) (cSt (k / 2)).2.2
      (coordS1 (k / 2) (cSt (k / 2)).1 (cSt (k / 2)).2.1 (cSt (k / 2)).2.2).2.1).2.2.2.1) := by
    unfold cCoord; rw [sCoord_eq]
  unfold sT
  rw [show sCs = sCoords 8 0 (cSt 0).1 (cSt 0).2.1 (cSt 0).2.2 from rfl, e]
  rcases Nat.mod_two_eq_zero_or_one k with h0 | h1
  · rw [show k = 2 * (k / 2) by omega, hp.1, Nat.zero_add, ht]; exact c1
  · rw [show k = 2 * (k / 2) + 1 by omega, hp.2, Nat.zero_add, ht]; exact c2

/-- The base-`4` digits of `n` sum to `n mod 4^k`. -/
theorem digits4 (n : Nat) : ∀ k, ∑ i ∈ Finset.range k, n / 4 ^ i % 4 * 4 ^ i = n % 4 ^ k
  | 0 => by simp [Nat.mod_one]
  | k + 1 => by
      rw [Finset.sum_range_succ, digits4 n k, pow_succ, Nat.mod_mul]
      ring

/-- **A digest that decodes** is the literal of its 64 digits, which sum to `123`. -/
theorem enc_lit {x : E} (hx : IsCanonical128 x) {enc : Encoding}
    (hd : TargetSum.decodeDigest (sv x) = some enc) :
    x = lit (∑ i ∈ Finset.range 64, cellNat x / 4 ^ i % 4 * 4 ^ i) ∧
      ∑ i ∈ Finset.range 64, cellNat x / 4 ^ i % 4 = 123 := by
  obtain ⟨hs, -⟩ := sDecode_iff.mp hd
  have ht : (sv x).toNat = cellNat x := toNat_cellVal x
  rw [ht] at hs
  refine ⟨?_, hs⟩
  have hsum : ∑ i ∈ Finset.range 64, cellNat x / 4 ^ i % 4 * 4 ^ i = cellNat x := by
    rw [digits4, Nat.mod_eq_of_lt (by have := cellNat_lt x; norm_num at this ⊢; omega)]
  rw [hsum]
  refine cellVal_inj hx (canon_word _ _) ?_
  rw [cellVal_lit, ← toNat_cellVal, BitVec.ofNat_toNat, BitVec.setWidth_eq]

end
end LeanVM.Guest.B1.Sig
