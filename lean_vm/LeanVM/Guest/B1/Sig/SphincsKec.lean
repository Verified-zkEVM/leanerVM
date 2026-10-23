/-
  LeanVM.Guest.B1.Sig.SphincsKec

  The one-block `keccak` calls of `verify_sig_lean_sphincs`: a chain step (48 bytes), a super-child
  (96 bytes) and a child leaf (128 bytes).
-/

module

public import LeanVM.Guest.B1.Sig.SphincsT
public import LeanVM.Guest.B1.Sig.Digest80
public import LeanVM.Guest.B1.Sig.Shifts

/-!
# One-block `keccak` calls

`kecOne_sound`: a `KECCAK` atom whose nine rate cells are the padded cells of a message of whole
cells shorter than a block, and whose capacity cells are zero, writes their `hcell`. Its instances:
`k48_sound` (`keccak([P, a], [v, 0], len=48)`), `kec96_sound` (the super-child) and
`kec128_sound` (a forest key's child leaf).
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Protocol.KeccakHash

@[expose] public section

variable {rd : Reader} {σ : Val}

/-- **A one-block `keccak` of whole cells.** -/
theorem kecOne_sound {ins : List V} {o len : Nat} {cs : List E} (hlen : 16 * cs.length = len)
    (hn : len < 136) (hK : AtomsHold rd σ [kecS ins (runV o 13) false false])
    (hrate : ∀ c < 9, σ (ins.getD c (.n 0)) = (padCells cs len).getD c 0)
    (hcap : ∀ c, 9 ≤ c → c < 13 → σ (ins.getD c (.n 0)) = 0) :
    (σ (.n o), σ (.n (o + 1))) = hcell cs := by
  have hk := hK.atom (List.mem_singleton_self _)
  obtain ⟨hl, -, hk⟩ := hk
  have hget : ∀ c : Fin 13, cells13 (ins.map σ) c = σ (ins.getD c.val (.n 0)) := fun c => by
    simp only [cells13, List.getD_eq_getElem?_getD, List.getElem?_map]
    rw [List.getElem?_eq_getElem (by omega)]
    rfl
  subst hlen
  have := keccak_one (cells := cs) (len := 16 * cs.length) (le_refl _) (by simpa [rate] using hn)
    (fun j hj => by
      simp only [List.getD_eq_getElem?_getD]
      rw [List.getElem?_eq_none (by simp [cellsBytes, mul_comm]; omega)]
      rfl)
    (fun c hc => by rw [hget]; exact hrate c hc)
    (fun c hc => by rw [hget]; exact hcap c hc c.isLt) hk
  rw [hcell, ← cellsBytes_eq_flatMap]
  have hfull : (cellsBytes cs).take (16 * cs.length) = cellsBytes cs := by
    rw [List.take_of_length_le (by simp [cellsBytes, mul_comm])]
  rw [← hfull, ← this.2]
  simp [cells13, runV]

theorem padCells_three (a b c : E) :
    padCells [a, b, c] 48 = [a, b, c, word 1 0 0, 0, 0, 0, 0, word (2 ^ 63) 0 0] := by
  simp [padCells, xorByte, padRead, rate, byteCell]

theorem padCells_six (a b c d e f : E) :
    padCells [a, b, c, d, e, f] 96 = [a, b, c, d, e, f, word 1 0 0, 0, word (2 ^ 63) 0 0] := by
  simp [padCells, xorByte, padRead, rate, byteCell]

theorem padCells_eight (a b c d e f g h : E) :
    padCells [a, b, c, d, e, f, g, h] 128 = [a, b, c, d, e, f, g, h, word (2 ^ 63 + 1) 0 0] := by
  have e : word 1 0 0 + word 9223372036854775808 0 0 = word 9223372036854775809 0 0 := by
    rw [word_eq_eOfNat, word_eq_eOfNat, word_eq_eOfNat, ← Value.eOfNat_xor]
    rfl
  simp [padCells, xorByte, padRead, rate, byteCell]
  exact e

theorem k48_atoms (a v : V) (c o : Nat) : atomsOnly (k48 a v c o) = true := rfl

/-- **A chain step's `keccak([P, a], [v, 0], len=48)`.** -/
theorem k48_sound (hp : PadOK σ sPad) {a v : V} {c o : Nat} (h : AtomsHold rd σ (k48 a v c o)) :
    (σ (.n o), σ (.n (o + 1))) = hcell [σ sPP, σ a, σ v] := by
  have hc : σ (.n c) = word (2 ^ 63) 0 0 := h.atom (a := .const (.n c) _) (by simp [k48, cst])
  obtain ⟨p0, p1, p2, p3, p4⟩ := hp
  refine kecOne_sound (ins := [sPP, a, v, .n sPad, .n (sPad + 1), .n (sPad + 2), .n (sPad + 3),
    .n (sPad + 4), .n c, .n (sPad + 1), .n (sPad + 2), .n (sPad + 3), .n (sPad + 4)]) (len := 48)
    rfl (by norm_num) (h.sub fun x hx => by
    simp only [List.mem_singleton] at hx; subst hx; simp [k48]) (fun c' hc' => ?_) (fun c' h1 h2 => ?_)
  · rw [padCells_three]
    interval_cases c' <;> simp_all [sPad]
  · interval_cases c' <;> simp_all [sPad]

/-- **The super-child's `keccak` of six cells**, its padding cells `p1`, `p2`, `p3`. -/
theorem kec96_sound (hp : PadOK σ sPad) {m0 m1 m2 m3 m4 m5 p1 p2 p3 : V} {o : Nat}
    (hK : AtomsHold rd σ [kecS [m0, m1, m2, m3, m4, m5, p1, p2, p3, .n (sPad + 1), .n (sPad + 2),
      .n (sPad + 3), .n (sPad + 4)] (runV o 13) false false])
    (h1 : σ p1 = word 1 0 0) (h2 : σ p2 = 0) (h3 : σ p3 = word (2 ^ 63) 0 0) :
    (σ (.n o), σ (.n (o + 1))) = hcell [σ m0, σ m1, σ m2, σ m3, σ m4, σ m5] := by
  obtain ⟨-, q1, q2, q3, q4⟩ := hp
  refine kecOne_sound (len := 96) rfl (by norm_num) hK (fun c' hc' => ?_) (fun c' h1 h2 => ?_)
  · rw [padCells_six]
    interval_cases c' <;> simp_all
  · interval_cases c' <;> simp_all

/-- **A child leaf's `keccak` of eight cells**, its padding cell `p`. -/
theorem kec128_sound (hp : PadOK σ sPad) {m0 m1 m2 m3 m4 m5 m6 m7 p : V} {o : Nat}
    (hK : AtomsHold rd σ [kecS [m0, m1, m2, m3, m4, m5, m6, m7, p, .n (sPad + 1), .n (sPad + 2),
      .n (sPad + 3), .n (sPad + 4)] (runV o 13) false false])
    (h : σ p = word (2 ^ 63 + 1) 0 0) :
    (σ (.n o), σ (.n (o + 1))) = hcell [σ m0, σ m1, σ m2, σ m3, σ m4, σ m5, σ m6, σ m7] := by
  obtain ⟨-, q1, q2, q3, q4⟩ := hp
  refine kecOne_sound (len := 128) rfl (by norm_num) hK (fun c' hc' => ?_) (fun c' h1 h2 => ?_)
  · rw [padCells_eight]
    interval_cases c' <;> simp_all
  · interval_cases c' <;> simp_all

end
end LeanVM.Guest.B1.Sig
