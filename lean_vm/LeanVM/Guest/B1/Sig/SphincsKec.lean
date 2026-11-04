/-
  LeanVM.Guest.B1.Sig.SphincsKec

  The one-block `keccak` calls of leanSPHINCS's guest functions: a message of whole cells shorter
  than a block, and its instance of 48 bytes (a chain step, a FORS leaf).
-/

module

public import LeanVM.Guest.B1.Sig.SphincsT
public import LeanVM.Guest.B1.Sig.Digest80
public import LeanVM.Guest.B1.Sig.Shifts

/-!
# One-block `keccak` calls

`kecOne_sound`: a `KECCAK` atom whose nine rate cells are the padded cells of a message of whole
cells shorter than a block, and whose capacity cells are zero, writes their `hcell`. Its instance
`k48At_sound` (`keccak([pp, a], [v, 0], len=48)` at any padding run; `k48_sound` at
`verify_sig_lean_sphincs`'s).
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

/-- **A 48-byte `keccak([pp, a], [v, 0], len=48)`** at the padding run `pad`. -/
theorem k48At_sound {pad : Nat} (hp : PadOK σ pad) {pp a v : V} {c o : Nat}
    (h : AtomsHold rd σ (k48At pp pad a v c o)) :
    (σ (.n o), σ (.n (o + 1))) = hcell [σ pp, σ a, σ v] := by
  have hc : σ (.n c) = word (2 ^ 63) 0 0 := h.atom (a := .const (.n c) _) (by simp [k48At, cst])
  obtain ⟨p0, p1, p2, p3, p4⟩ := hp
  refine kecOne_sound (ins := [pp, a, v, .n pad, .n (pad + 1), .n (pad + 2), .n (pad + 3),
    .n (pad + 4), .n c, .n (pad + 1), .n (pad + 2), .n (pad + 3), .n (pad + 4)]) (len := 48)
    rfl (by norm_num) (h.sub fun x hx => by
    simp only [List.mem_singleton] at hx; subst hx; simp [k48At]) (fun c' hc' => ?_) (fun c' h1 h2 => ?_)
  · rw [padCells_three]
    interval_cases c' <;> simp_all
  · interval_cases c' <;> simp_all

/-- **A chain step's or a FORS leaf's `keccak([P, a], [v, 0], len=48)`** in
`verify_sig_lean_sphincs`. -/
theorem k48_sound (hp : PadOK σ sPad) {a v : V} {c o : Nat} (h : AtomsHold rd σ (k48 a v c o)) :
    (σ (.n o), σ (.n (o + 1))) = hcell [σ sPP, σ a, σ v] :=
  k48At_sound hp h

end
end LeanVM.Guest.B1.Sig
