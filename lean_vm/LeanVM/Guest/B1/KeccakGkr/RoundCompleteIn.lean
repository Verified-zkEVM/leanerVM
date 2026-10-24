/-
  LeanVM.Guest.B1.KeccakGkr.RoundCompleteIn

  `keccak_round`, completely and with its loads placed: its relation by a tree loading only the
  record, the coordinate, the challenge's slot and the two stream words.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.RoundComplete
public import LeanVM.Guest.Memory.LiftPure

/-!
# `keccak_round`'s loads

`keccak_round` is a leaf body (atoms, then `ret`; `round_leafOk`), so its relation loads from a
region `R` when every walk that holds does (`Lift.relIn_of_leaf'`). Its loads read the record at
`rec` (offsets `roundRecOffs`), the coordinate at `pp`, the challenge's slot at `pt`, and the two
stream words at the record's cursor, which every holding walk reads off the record
(`keccak_round_relIn`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.Memory LeanVM.Guest.Lift
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The word at `p·g^k` lies in the region `R`. -/
def InR (R : ℕ → Prop) (p : E) (k : ℕ) : Prop :=
  ∃ i, p.limb 0 * Parameters.gpow k = Parameters.gpow i ∧ R i

/-- The record's offsets `keccak_round` reads and writes. -/
def roundRecOffs : List ℕ := [0, 16, 32, 48, 64, 80, 96, 112, 1, 17, 33, 49, 65, 81, 97, 113]

theorem round_leafOk : Stmt.leafOkList anyAtom Data.core11.body = true := by decide +kernel

/-- The body's statements before its `ret`. -/
noncomputable def roundPre : List Stmt := Data.core11.body.dropLast

theorem round_split : Data.core11.body = roundPre ++ [.ret []] := by rfl

theorem round_straight : roundPre.all Stmt.straight = true := by decide +kernel

theorem round_loads : roundPre.filterMap Stmt.loadS =
    [(.n 0, 0), (.n 0, 16), (.n 0, 32), (.n 0, 48), (.n 0, 64), (.n 0, 80), (.n 1, 0), (.n 8, 0),
      (.n 8, 1), (.n 2, 0), (.n 0, 1), (.n 0, 17), (.n 0, 33), (.n 0, 49), (.n 0, 65), (.n 0, 81),
      (.n 0, 96), (.n 0, 97), (.n 0, 112), (.n 0, 113)] := by decide +kernel

theorem round_cur_mem : Stmt.atom (.load (.n 8) (.n 0) 80) ∈ roundPre := by
  have h := List.getElem_mem (l := roundPre) (n := 5) (by decide +kernel)
  exact h

/-- **`keccak_round` is complete, loading the record, the coordinate, the challenge's slot and the
two stream words.** -/
theorem keccak_round_relIn {rd : Reader} {R : ℕ → Prop} {rec pp pt : E} {rets : List E}
    (hm : MeaningKeccakRound rd [rec, pp, pt] rets)
    (hrec : ∀ k ∈ roundRecOffs, InR R rec k) (hpp : InR R pp 0) (hpt : InR R pt 0)
    (hcur : ∀ cur, LoadHolds rd rec 80 cur → InR R cur 0 ∧ InR R cur 1) :
    coreProgram.RelIn rd R "keccak_round" [rec, pp, pt] rets := by
  have hrel := keccak_round_complete rd _ _ hm
  obtain ⟨-, cap, cur, claim, scale, r, g1, g2, ⟨-, lcur, -⟩, -⟩ := hm
  obtain ⟨c0, c1⟩ := hcur cur lcur
  refine relIn_of_leaf' find_keccak_round round_leafOk (fun σ es vs hp hw hes A hA ↦ ?_) hrel
  rw [show Data.core11.params = [.n 0, .n 1, .n 2] from rfl] at hp
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hp
  obtain ⟨h0, h1, h2⟩ := hp
  rw [show Fn.body Data.core11 = roundPre ++ [.ret []] from round_split,
    walk_straight σ [] roundPre round_straight] at hw
  cases hw
  have h8 : σ (.n 8) = cur := by
    have := hes (.atom (.load (.n 8) (.n 0) 80))
      (List.mem_flatMap.2 ⟨_, round_cur_mem, List.mem_singleton_self _⟩)
    exact loadHolds_unique (show LoadHolds rd (σ (.n 0)) 80 (σ (.n 8)) from this)
      (h0 ▸ lcur)
  rw [loadAddrs_straight σ roundPre round_straight, round_loads] at hA
  simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hA
  rw [h0, h1, h2, h8] at hA
  have hr : ∀ k ∈ roundRecOffs, ∃ i, rec.limb 0 * Parameters.gpow k = Parameters.gpow i ∧ R i :=
    hrec
  simp only [roundRecOffs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at hr
  obtain ⟨r0, r16, r32, r48, r64, r80, r96, r112, r1, r17, r33, r49, r65, r81, r97, r113⟩ := hr
  rcases hA with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact r0
  · exact r16
  · exact r32
  · exact r48
  · exact r64
  · exact r80
  · exact hpp
  · exact c0
  · exact c1
  · exact hpt
  · exact r1
  · exact r17
  · exact r33
  · exact r49
  · exact r65
  · exact r81
  · exact r96
  · exact r97
  · exact r112
  · exact r113

end
end LeanVM.Guest.B1.VerifySub
