/-
  LeanVM.Guest.B1.Digest.Statement

  B1 for `statement_digest` (G:3766-3797; TRIAGE #86): the statement's digest, byte for byte.
-/

module

public import LeanVM.Guest.B1.Digest.Basic

/-!
# `statement_digest`

`statement_digest(seed_0, seed_1, signers_hash, da_0, da_1, defer)` hashes 42 cells: the seed's
two cells, the signer-set digest's two (read at `signers_hash`), the DA list digest's two, then
the 24 deferred cells (read at `defer`) two at a time as three canonical cells each
(`pack_pair`), `672` bytes in five `KECCAK` blocks, the last padded by the constant cell
`0x01 … 0x80`. Its core IR (`Data.core21`) is the template `sdAtoms` (`core21_body`, by kernel
evaluation); `keccak_final_digest` makes the chain Keccak-256 of the cells' bytes, which are the
header cells' and the deferred cells' limbs (`pair_bytes`).
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The template -/

/-- The value of hashed cell `m < 42`: the six header cells, then the three cells of each pair. -/
def sdCell (m : ℕ) : ℕ :=
  if m < 6 then 6 + m else 12 + 27 * ((m - 6) / 3) + (8 + 9 * ((m - 6) % 3))

/-- The value of output cell `c` of block `k < 5`. -/
def sdOut (k c : ℕ) : ℕ := if k < 4 then 341 + 22 * k + c else 430 + c

/-- The value of input cell `c` of block `k < 5`. -/
def sdIn (k c : ℕ) : ℕ :=
  if c < 9 then
    (if k = 0 then sdCell c else if k < 4 then 354 + 22 * (k - 1) + c else if c < 8 then 420 + c
      else 429)
  else (if k = 0 then 337 + (c - 9) else sdOut (k - 1) c)

/-- The `KECCAK` of block `k`. -/
def sdKeccak (k : ℕ) : Atom :=
  .keccak ((List.range 13).map fun c => .n (sdIn k c)) ((List.range 13).map fun c => .n (sdOut k c))
    (inLayout k) (outLayout 5 k)

/-- The header cells. -/
def sdHdr : List Atom :=
  [.copy (.n 6) (.n 0), .copy (.n 7) (.n 1), .load (.n 8) (.n 2) 0, .load (.n 9) (.n 2) 1,
   .copy (.n 10) (.n 3), .copy (.n 11) (.n 4)]

/-- The padding constants: the unused `0x01` cell and the zero capacity of the first block. -/
def sdConsts : List Atom :=
  [.const (.n 336) (word 1 0 0), .const (.n 337) (word 0 0 0), .const (.n 338) (word 0 0 0),
   .const (.n 339) (word 0 0 0), .const (.n 340) (word 0 0 0)]

/-- Block `k ∈ {1, 2, 3}`: nine message cells XORed into the previous output, then its `KECCAK`. -/
def sdBlk (k : ℕ) : List Atom :=
  (List.range 9).map (fun c => .add (.n (354 + 22 * (k - 1) + c)) (.n (sdOut (k - 1) c))
    (.n (sdCell (17 * k / 2 + c)))) ++ [sdKeccak k]

/-- The padding cell of the last block (`0x01` at byte `672`, `0x80` at byte `679`). -/
abbrev padWord : E := word 9223372036854775809 0 0

/-- The last block: eight message cells, the padding cell, its `KECCAK`. -/
def sdBlk4 : List Atom :=
  (List.range 8).map (fun c => .add (.n (420 + c)) (.n (sdOut 3 c)) (.n (sdCell (34 + c)))) ++
    [.const (.n 428) padWord, .add (.n 429) (.n (sdOut 3 8)) (.n 428), sdKeccak 4]

/-- `statement_digest`'s atoms. -/
def sdAtoms : List Atom :=
  sdHdr ++ (List.range 12).flatMap (fun p => pairAtoms (.n 5) (2 * p) (12 + 27 * p)) ++ sdConsts ++
    [sdKeccak 0] ++ (List.range 3).flatMap (fun j => sdBlk (j + 1)) ++ sdBlk4 ++
    [.copy (.n 443) (.n 430), .copy (.n 444) (.n 431)]

set_option maxRecDepth 100000 in
theorem core21_body : Fn.body Data.core21 = sdAtoms.map Stmt.atom ++ [.ret [.n 443, .n 444]] :=
  stmtsEqb_sound (by decide +kernel)

theorem core21_params : Fn.params Data.core21 = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5] := rfl

/-! ## The cells -/

theorem sdCell_A (p : ℕ) : sdCell (6 + 3 * p) = 12 + 27 * p + 8 := by
  unfold sdCell
  rw [ite_neg' (by omega), show (6 + 3 * p - 6) / 3 = p by omega, show (6 + 3 * p - 6) % 3 = 0 by omega]

theorem sdCell_B (p : ℕ) : sdCell (6 + 3 * p + 1) = 12 + 27 * p + 17 := by
  unfold sdCell
  rw [ite_neg' (by omega), show (6 + 3 * p + 1 - 6) / 3 = p by omega,
    show (6 + 3 * p + 1 - 6) % 3 = 1 by omega]

theorem sdCell_C (p : ℕ) : sdCell (6 + 3 * p + 2) = 12 + 27 * p + 26 := by
  unfold sdCell
  rw [ite_neg' (by omega), show (6 + 3 * p + 2 - 6) / 3 = p by omega,
    show (6 + 3 * p + 2 - 6) % 3 = 2 by omega]

theorem range42_split (f : ℕ → E) :
    (List.range 42).map f = (List.range 6).map f ++
      (List.range 12).flatMap (fun p => [f (6 + 3 * p), f (6 + 3 * p + 1), f (6 + 3 * p + 2)]) :=
  rfl

theorem range24_split (g : ℕ → E) :
    (List.range 24).map g = (List.range 12).flatMap (fun p => [g (2 * p), g (2 * p + 1)]) := rfl

theorem cells13_map_range (σ : Val) (f : ℕ → ℕ) (c : Fin 13) :
    cells13 (((List.range 13).map fun c => V.n (f c)).map σ) c = σ (.n (f c)) := by
  simp [cells13, List.getD_eq_getElem?_getD, c.isLt]

theorem keccak_holds {rd : Reader} {σ : Val} {k : ℕ} (h : (sdKeccak k).Holds rd σ) :
    KeccakCells (fun c : Fin 13 => σ (.n (sdIn k c))) (inLayout k)
      (fun c : Fin 13 => σ (.n (sdOut k c))) (outLayout 5 k) := by
  obtain ⟨-, -, hK⟩ := h
  have e1 : cells13 (((List.range 13).map fun c => V.n (sdIn k c)).map σ) =
      fun c : Fin 13 => σ (.n (sdIn k c)) := funext (cells13_map_range σ _)
  have e2 : cells13 (((List.range 13).map fun c => V.n (sdOut k c)).map σ) =
      fun c : Fin 13 => σ (.n (sdOut k c)) := funext (cells13_map_range σ _)
  rw [e1, e2] at hK
  exact hK

/-- The padding cell of the 42-cell message, at its byte `672`. -/
theorem padCells_42 (cells : List E) (hl : cells.length = 42) :
    (padCells cells 672).getD 42 0 = padWord := by
  have hr : padRead 672 - cells.length = 1 := by rw [hl]; rfl
  have hlen : (cells ++ List.replicate (padRead 672 - cells.length) 0).length = 43 := by
    rw [List.length_append, List.length_replicate, hr, hl]
  unfold padCells xorByte
  rw [show rate * (672 / rate + 1) - 1 = 679 from rfl, show (679 : ℕ) / 16 = 42 from rfl,
    getD_modify _ _ _ _ (by rw [List.length_modify, hlen]; omega),
    getD_modify _ _ _ _ (by rw [hlen]; omega), hr,
    List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hl]
  simp only [Nat.sub_self, List.replicate_one, List.getElem?_cons_zero, Option.getD_some, zero_add]
  unfold byteCell
  simp only [show (672 : ℕ) % 16 = 0 from rfl, show (679 : ℕ) % 16 = 7 from rfl]
  rw [ite_pos' (by omega), ite_pos' (by omega), word_eOfNat, word_eOfNat, ← eOfNat_xor, padWord,
    word_eOfNat, show (1 * 2 ^ (8 * 0)) ^^^ (128 * 2 ^ (8 * 7)) = 9223372036854775809 by decide]

/-! ## Soundness -/

set_option maxRecDepth 100000 in
/-- **`statement_digest` computes the statement's digest.** -/
theorem statement_digest_sound : statement_digest_sound_Spec := by
  intro rd args rets h
  obtain ⟨σ, hp, hb⟩ := (rel_iff_sem find_statement_digest args rets).mp h
  rw [core21_body, holdsList_atoms_ret] at hb
  obtain ⟨hat, hr⟩ := hb
  simp only [sdAtoms, List.forall_mem_append, List.forall_mem_cons, List.not_mem_nil,
    IsEmpty.forall_iff, implies_true, and_true] at hat
  obtain ⟨⟨⟨⟨⟨⟨hH, hP⟩, hC⟩, hK0⟩, hB⟩, hB4⟩, h443, h444⟩ := hat
  rw [forall_mem_flatMap_range] at hP hB
  -- the header
  simp only [sdHdr, List.forall_mem_cons, Atom.Holds, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true, and_true] at hH
  obtain ⟨h6, h7, l8, l9, h10, h11⟩ := hH
  -- the constants
  simp only [sdConsts, List.forall_mem_cons, Atom.Holds, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true, and_true] at hC
  obtain ⟨-, c337, c338, c339, c340⟩ := hC
  -- the pairs
  have hpair := fun p hp => pair_fwd (hP p hp)
  -- the blocks
  have hadd : ∀ k, 1 ≤ k → k ≤ 3 → ∀ c < 9, σ (.n (354 + 22 * (k - 1) + c)) =
      σ (.n (sdOut (k - 1) c)) + σ (.n (sdCell (17 * k / 2 + c))) := by
    intro k hk1 hk3 c hc
    have := hB (k - 1) (by omega) _ (List.mem_append_left _ (List.mem_map.mpr ⟨c, List.mem_range.mpr hc, rfl⟩))
    rwa [show k - 1 + 1 = k by omega] at this
  have hkk : ∀ k, 1 ≤ k → k ≤ 3 → (sdKeccak k).Holds rd σ := by
    intro k hk1 hk3
    have := hB (k - 1) (by omega) (sdKeccak (k - 1 + 1)) (List.mem_append_right _ (List.mem_singleton_self _))
    rwa [show k - 1 + 1 = k by omega] at this
  simp only [sdBlk4, List.forall_mem_append, List.forall_mem_cons, List.not_mem_nil,
    IsEmpty.forall_iff, implies_true, and_true] at hB4
  obtain ⟨hB4a, c428, a429, hk4⟩ := hB4
  have hadd4 : ∀ c < 8, σ (.n (420 + c)) = σ (.n (sdOut 3 c)) + σ (.n (sdCell (34 + c))) :=
    fun c hc => hB4a _ (List.mem_map.mpr ⟨c, List.mem_range.mpr hc, rfl⟩)
  -- the chain
  let C42 : List E := (List.range 42).map fun m => σ (.n (sdCell m))
  have hC42 : C42.length = 42 := by simp [C42]
  have hC42get : ∀ m < 42, C42.getD m 0 = σ (.n (sdCell m)) := fun m hm => by
    simp [C42, List.getD_eq_getElem?_getD, hm]
  let I : ℕ → Fin 13 → E := fun k c => σ (.n (sdIn k c))
  let O : ℕ → Fin 13 → E := fun k c => if k = 0 then 0 else σ (.n (sdOut (k - 1) c))
  have hP42 : ∀ m < 42, (padCells C42 672).getD m 0 = σ (.n (sdCell m)) := fun m hm => by
    rw [padCells_getD_lt _ _ (by omega) (by rw [show (672 : ℕ) / 16 = 42 from rfl]; omega)
      (by rw [show rate * (672 / rate + 1) - 1 = 679 from rfl]; omega), hC42get m hm]
  have hB5 : 672 / rate + 1 = 5 := rfl
  have hrate : ∀ k < 672 / rate + 1, ∀ c : Fin 13, c.val < 9 →
      I k c = O k c + (padCells C42 672).getD (17 * k / 2 + c) 0 := by
    intro k hk c hc
    rw [hB5] at hk
    rcases (show k = 0 ∨ (1 ≤ k ∧ k ≤ 3) ∨ k = 4 by omega) with rfl | ⟨hk1, hk3⟩ | rfl
    · simp only [I, O, sdIn, hc, ↓reduceIte, Nat.mul_zero, Nat.zero_div, zero_add]
      rw [hP42 _ (by omega)]
    · simp only [I, O, sdIn, hc, ↓reduceIte, show k ≠ 0 by omega, show k < 4 by omega]
      rw [hadd k hk1 hk3 c hc, hP42 _ (by omega)]
    · by_cases h8 : c.val < 8
      · simp (config := {decide := true}) only [I, O, sdIn, hc, h8, ↓reduceIte]
        rw [show 17 * 4 / 2 + c.val = 34 + c.val by omega, hadd4 c h8, hP42 _ (by omega)]
      · have hc8 : c.val = 8 := by omega
        simp (config := {decide := true}) only [I, O, sdIn, hc8, ↓reduceIte]
        rw [show 17 * 4 / 2 + 8 = 42 from rfl, a429, c428, padCells_42 C42 hC42]
  have hcap : ∀ k < 672 / rate + 1, ∀ c : Fin 13, 9 ≤ c.val → I k c = O k c := by
    intro k hk c hc
    rw [hB5] at hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp only [I, O, sdIn, show ¬ c.val < 9 by omega, ↓reduceIte]
      rcases (show c.val - 9 = 0 ∨ c.val - 9 = 1 ∨ c.val - 9 = 2 ∨ c.val - 9 = 3 by omega) with
        h | h | h | h <;> simp only [h, Nat.reduceAdd] <;>
        first | rw [c337, word_zero] | rw [c338, word_zero] | rw [c339, word_zero] |
          rw [c340, word_zero]
    · simp only [I, O, sdIn, show ¬ c.val < 9 by omega, ↓reduceIte, show k ≠ 0 by omega]
  have hK : ∀ k < 672 / rate + 1,
      KeccakCells (I k) (inLayout k) (O (k + 1)) (outLayout (672 / rate + 1) k) := by
    intro k hk
    rw [hB5] at hk ⊢
    have hO : O (k + 1) = fun c : Fin 13 => σ (.n (sdOut k c)) := by
      funext c; simp [O]
    rw [hO]
    rcases (show k = 0 ∨ (1 ≤ k ∧ k ≤ 3) ∨ k = 4 by omega) with rfl | ⟨hk1, hk3⟩ | rfl
    · exact keccak_holds hK0
    · exact keccak_holds (hkk k hk1 hk3)
    · exact keccak_holds hk4
  have h0 : O 0 = cellsOfState (absorbChunks 0 zeroState []) false := by
    funext c
    simp only [O, ↓reduceIte]
    exact (cellsOfState_zero false c).symm
  have hz : ∀ j, 672 ≤ j → (cellsBytes C42).getD j 0 = 0 := fun j hj =>
    getD_of_length_le (by rw [length_cellsBytes, hC42]; omega)
  have hdig := keccak_final_digest (pre := []) (n := 0) rfl (by rw [hC42]) hz h0 hrate hcap hK
  rw [hB5, List.nil_append, List.take_of_length_le (by rw [length_cellsBytes, hC42])] at hdig
  -- the canonical header
  have hcan := (hK 0 (by rw [hB5]; omega)).1
  have can : ∀ m < 6, IsCanonical128 (σ (.n (6 + m))) := fun m hm => by
    have := hcan ⟨m, by omega⟩
    simpa [I, sdIn, sdCell, show m < 9 by omega, hm] using this
  -- the deferred cells
  let cells : List E := (List.range 24).map fun q => σ (.n (12 + 27 * (q / 2) + q % 2))
  have hcells : cells = (List.range 12).flatMap
      (fun p => [σ (.n (12 + 27 * p)), σ (.n (12 + 27 * p + 1))]) := by
    simp only [cells, range24_split]
    refine List.flatMap_congr fun p _ => ?_
    rw [show 2 * p / 2 = p by omega, show 2 * p % 2 = 0 by omega,
      show (2 * p + 1) / 2 = p by omega, show (2 * p + 1) % 2 = 1 by omega, Nat.add_zero]
  have e1 : (List.range 6).map (fun m => σ (.n (sdCell m))) =
      [σ (.n 0), σ (.n 1), σ (.n 8), σ (.n 9), σ (.n 3), σ (.n 4)] := by
    rw [← h6, ← h7, ← h10, ← h11]; rfl
  have e2 : (List.range 12).flatMap (fun p => [σ (.n (sdCell (6 + 3 * p))),
      σ (.n (sdCell (6 + 3 * p + 1))), σ (.n (sdCell (6 + 3 * p + 2)))]) =
      (List.range 12).flatMap (fun p => pairCells (σ (.n (12 + 27 * p))) (σ (.n (12 + 27 * p + 1)))) := by
    refine List.flatMap_congr fun p hp => ?_
    obtain ⟨-, -, hc3⟩ := hpair p (List.mem_range.mp hp)
    rw [sdCell_A, sdCell_B, sdCell_C]
    exact hc3
  have hbytes : cellsBytes C42 =
      stmtBytes [σ (.n 0), σ (.n 1), σ (.n 8), σ (.n 9), σ (.n 3), σ (.n 4)] cells := by
    show cellsBytes ((List.range 42).map fun m => σ (.n (sdCell m))) = _
    rw [range42_split, e1, e2, cellsBytes_append, stmtBytes, hcells, List.flatMap_assoc]
    congr 1
  -- the meaning
  simp only [core21_params, List.map_cons, List.map_nil] at hp
  subst hp
  refine ⟨σ (.n 8), σ (.n 9), cells, l8, l9, by simp [cells], fun k hk => ?_, ?_, ?_⟩
  · have hk' : k < 24 := by simpa [cells] using hk
    obtain ⟨la, lb, -⟩ := hpair (k / 2) (by omega)
    simp only [cells, List.getElem_map, List.getElem_range]
    rcases Nat.mod_two_eq_zero_or_one k with h2 | h2
    · rw [h2, Nat.add_zero, show k = 2 * (k / 2) by omega]
      rw [show 2 * (k / 2) / 2 = k / 2 by omega]
      exact la
    · rw [h2, show k = 2 * (k / 2) + 1 by omega, show (2 * (k / 2) + 1) / 2 = k / 2 by omega]
      exact lb
  · intro c hc
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [← h6]; exact can 0 (by omega)
    · rw [← h7]; exact can 1 (by omega)
    · exact can 2 (by omega)
    · exact can 3 (by omega)
    · rw [← h10]; exact can 4 (by omega)
    · rw [← h11]; exact can 5 (by omega)
  · simp only [Atom.Holds] at h443 h444
    rw [← hbytes, digestCells, ← hdig, ← hr]
    simp only [List.map_cons, List.map_nil, h443, h444]
    rfl

end
end LeanVM.Guest.B1.Digest
