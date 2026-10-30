/-
  LeanVM.Guest.B1.Whir.QueryBits

  The positions and bit runs a level's decodes leave, position by position.
-/

module

public import LeanVM.Guest.B1.Whir.Squeezes

/-!
# The positions table (G:1429-1433, 729-773)

`decode_query_bits` of challenge `jj` writes positions `jj·per .. jj·per + per - 1` and their
bit runs (`per = 192 / depth`). `positions_of_decodes`: for every `k < q`, the position
`queriesOf … [k]` (the Spec's, `Whir/Positions.lean`) is at `qpos·g^(po + k)`, and the pointer at
`qbp·g^(po + k)` points to its `depth` bits.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader}

theorem testBit_chunk (W t d l : ℕ) (hl : l < d) :
    ((W >>> (t * d)) % 2 ^ d).testBit l = W.testBit (t * d + l) := by
  rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  simp [hl, Nat.add_comm]

/-- **The positions table**: position `k < q` at `qpos·g^(po + k)` and its bit run's pointer at
`qbp·g^(po + k)`. -/
theorem positions_of_decodes {d po q nsq : ℕ} (hd : 1 ≤ 192 / d) (hq : q ≤ nsq * (192 / d))
    {qpos qbp : E} (ws : List E)
    (hdec : ∀ jj < nsq, MeaningDecodeQueryBits d rd [ws.getD jj 0,
      qpos * gen ^ (po + jj * (192 / d)), qbp * gen ^ (po + jj * (192 / d))] []) :
    ∀ k < q, LoadHolds rd qpos (po + k) (eOfNat ((queriesOf (192 / d) d ws q).getD k 0)) ∧
      ∃ bp, LoadHolds rd qbp (po + k) bp ∧ ∀ l < d, ∀ w, LoadHolds rd bp l w →
        w = bitE (((queriesOf (192 / d) d ws q).getD k 0).testBit l) := by
  intro k hk
  set per := 192 / d
  have hjj : k / per < nsq := by
    rw [Nat.div_lt_iff_lt_mul (by omega)]; exact lt_of_lt_of_le hk hq
  have ht : k % per < per := Nat.mod_lt _ (by omega)
  have hk' : po + k = po + k / per * per + k % per := by
    have := Nat.div_add_mod k per; rw [Nat.mul_comm] at this; omega
  obtain ⟨-, p, hfb, hall⟩ := hdec (k / per) hjj
  obtain ⟨hpos, hptr⟩ := hall (k % per) ht
  have hg : (queriesOf per d ws q).getD k 0 = (eToNat (ws.getD (k / per) 0) >>> (k % per * d)) % 2 ^ d := by
    simp [queriesOf, List.getD_eq_getElem?_getD, hk]
  rw [hg]
  refine ⟨?_, p * gen ^ (k % per * d), ?_, ?_⟩
  · rw [hk', ← loadHolds_mul_gen_pow]; exact hpos
  · rw [hk', ← loadHolds_mul_gen_pow]; exact hptr
  · intro l hl w hw
    rw [loadHolds_mul_gen_pow] at hw
    rw [testBit_chunk _ _ _ _ hl]
    refine hfb.2 _ ?_ w hw.2
    have : k % per * d + l < per * d := by
      have : k % per * d + d ≤ per * d := by
        rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ ht
      omega
    have h192 : per * d ≤ 192 := Nat.div_mul_le_self 192 d
    omega

end
end LeanVM.Guest.B1.Whir
