/-
  LeanVM.Guest.B1.KeccakGkr.Lib

  The vocabulary of B1-d's proofs: functions found by index, a `KECCAK` atom in the even layouts
  as a squeeze of the carried sponge, the rate cells of waiting scalars, and `fs_next`'s cells.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.Interface
public import LeanVM.Guest.B1.Fs.Templates

/-!
# B1-d: shared lemmas

* `keccak_outs`: a `KECCAK` atom in the even layouts reads canonical cells and writes the cells
  of their permutation (`permOf`), output `k` its cell `k`;
* `rateOf_nil` … `rateOf_four`: the rate cells of `k ≤ 4` waiting scalars (`Keccak.scalarCells`);
* `squeeze_atom`: the atom on the rate cells of `s.pend` and the capacity `s.cap`, followed by
  `challenge_from_state` on its outputs `0`, `1`, is `s.squeeze`: the challenge, and the
  capacity cells `8..12` of its outputs;
* `fsPack_scalar`: `fs_pack`'s two cells, once read canonical, are the scalar's rate cells.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-! ## A `KECCAK` atom -/

/-- **A `KECCAK` atom in the even layouts**: it reads thirteen canonical cells and writes, as
output `k`, cell `k` of their permutation. -/
theorem keccak_outs {ins outs : List V} (h : (Atom.keccak ins outs false false).Holds rd σ) :
    ins.length = 13 ∧ outs.length = 13 ∧ AllCanonical (ins.map σ) ∧
      ∀ k (hk : k < 13), σ (outs.getD k default) = cellsOfState (permOf (ins.map σ)) false ⟨k, hk⟩ := by
  obtain ⟨hi, ho, hc, hout⟩ := keccakA_perm h
  refine ⟨hi, ho, hc, fun k hk => ?_⟩
  have := congrFun hout ⟨k, hk⟩
  simp only [cells13, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem (show k < outs.length by omega), Option.map_some,
    Option.getD_some] at this ⊢
  exact this

/-! ## Rate cells -/

theorem range8 : List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] := rfl

theorem rateCell_fst (ps : List (E × ℕ)) (k : ℕ) (hk : k < ps.length) :
    Keccak.rateCell ps (2 * k) = (Keccak.scalarCells ps[k].1 ps[k].2).1 :=
  congrArg Prod.fst (Keccak.rateCell_scalar ps k hk)

theorem rateCell_snd (ps : List (E × ℕ)) (k : ℕ) (hk : k < ps.length) :
    Keccak.rateCell ps (2 * k + 1) = (Keccak.scalarCells ps[k].1 ps[k].2).2 :=
  congrArg Prod.snd (Keccak.rateCell_scalar ps k hk)

theorem rateOf_nil : rateOf [] = [0, 0, 0, 0, 0, 0, 0, 0] := by
  simp only [rateOf, range8, List.map_cons, List.map_nil,
    Keccak.rateCell_past [] (Nat.zero_le _)]

theorem rateOf_one (a : E × ℕ) :
    rateOf [a] = [(Keccak.scalarCells a.1 a.2).1,
      (Keccak.scalarCells a.1 a.2).2, 0, 0, 0, 0, 0, 0] := by
  have h0 : Keccak.rateCell [a] 0 = (Keccak.scalarCells a.1 a.2).1 :=
    rateCell_fst [a] 0 (by simp)
  have h1 : Keccak.rateCell [a] 1 = (Keccak.scalarCells a.1 a.2).2 :=
    rateCell_snd [a] 0 (by simp)
  have h2 : Keccak.rateCell [a] 2 = 0 := Keccak.rateCell_past [a] (by simp)
  have h3 : Keccak.rateCell [a] 3 = 0 := Keccak.rateCell_past [a] (by simp)
  have h4 : Keccak.rateCell [a] 4 = 0 := Keccak.rateCell_past [a] (by simp)
  have h5 : Keccak.rateCell [a] 5 = 0 := Keccak.rateCell_past [a] (by simp)
  have h6 : Keccak.rateCell [a] 6 = 0 := Keccak.rateCell_past [a] (by simp)
  have h7 : Keccak.rateCell [a] 7 = 0 := Keccak.rateCell_past [a] (by simp)
  simp only [rateOf, range8, List.map_cons, List.map_nil, h0, h1, h2, h3, h4, h5, h6, h7]

theorem rateOf_two (a b : E × ℕ) :
    rateOf [a, b] = [(Keccak.scalarCells a.1 a.2).1, (Keccak.scalarCells a.1 a.2).2,
      (Keccak.scalarCells b.1 b.2).1, (Keccak.scalarCells b.1 b.2).2, 0, 0, 0, 0] := by
  have h0 : Keccak.rateCell [a, b] 0 = (Keccak.scalarCells a.1 a.2).1 :=
    rateCell_fst [a, b] 0 (by simp)
  have h1 : Keccak.rateCell [a, b] 1 = (Keccak.scalarCells a.1 a.2).2 :=
    rateCell_snd [a, b] 0 (by simp)
  have h2 : Keccak.rateCell [a, b] 2 = (Keccak.scalarCells b.1 b.2).1 :=
    rateCell_fst [a, b] 1 (by simp)
  have h3 : Keccak.rateCell [a, b] 3 = (Keccak.scalarCells b.1 b.2).2 :=
    rateCell_snd [a, b] 1 (by simp)
  have h4 : Keccak.rateCell [a, b] 4 = 0 := Keccak.rateCell_past [a, b] (by simp)
  have h5 : Keccak.rateCell [a, b] 5 = 0 := Keccak.rateCell_past [a, b] (by simp)
  have h6 : Keccak.rateCell [a, b] 6 = 0 := Keccak.rateCell_past [a, b] (by simp)
  have h7 : Keccak.rateCell [a, b] 7 = 0 := Keccak.rateCell_past [a, b] (by simp)
  simp only [rateOf, range8, List.map_cons, List.map_nil, h0, h1, h2, h3, h4, h5, h6, h7]

theorem rateOf_three (a b c : E × ℕ) :
    rateOf [a, b, c] = [(Keccak.scalarCells a.1 a.2).1, (Keccak.scalarCells a.1 a.2).2,
      (Keccak.scalarCells b.1 b.2).1, (Keccak.scalarCells b.1 b.2).2,
      (Keccak.scalarCells c.1 c.2).1, (Keccak.scalarCells c.1 c.2).2, 0, 0] := by
  have h0 : Keccak.rateCell [a, b, c] 0 = (Keccak.scalarCells a.1 a.2).1 :=
    rateCell_fst [a, b, c] 0 (by simp)
  have h1 : Keccak.rateCell [a, b, c] 1 = (Keccak.scalarCells a.1 a.2).2 :=
    rateCell_snd [a, b, c] 0 (by simp)
  have h2 : Keccak.rateCell [a, b, c] 2 = (Keccak.scalarCells b.1 b.2).1 :=
    rateCell_fst [a, b, c] 1 (by simp)
  have h3 : Keccak.rateCell [a, b, c] 3 = (Keccak.scalarCells b.1 b.2).2 :=
    rateCell_snd [a, b, c] 1 (by simp)
  have h4 : Keccak.rateCell [a, b, c] 4 = (Keccak.scalarCells c.1 c.2).1 :=
    rateCell_fst [a, b, c] 2 (by simp)
  have h5 : Keccak.rateCell [a, b, c] 5 = (Keccak.scalarCells c.1 c.2).2 :=
    rateCell_snd [a, b, c] 2 (by simp)
  have h6 : Keccak.rateCell [a, b, c] 6 = 0 := Keccak.rateCell_past [a, b, c] (by simp)
  have h7 : Keccak.rateCell [a, b, c] 7 = 0 := Keccak.rateCell_past [a, b, c] (by simp)
  simp only [rateOf, range8, List.map_cons, List.map_nil, h0, h1, h2, h3, h4, h5, h6, h7]

theorem rateOf_four (a b c d : E × ℕ) :
    rateOf [a, b, c, d] = [(Keccak.scalarCells a.1 a.2).1, (Keccak.scalarCells a.1 a.2).2,
      (Keccak.scalarCells b.1 b.2).1, (Keccak.scalarCells b.1 b.2).2,
      (Keccak.scalarCells c.1 c.2).1, (Keccak.scalarCells c.1 c.2).2,
      (Keccak.scalarCells d.1 d.2).1, (Keccak.scalarCells d.1 d.2).2] := by
  have h0 : Keccak.rateCell [a, b, c, d] 0 = (Keccak.scalarCells a.1 a.2).1 :=
    rateCell_fst [a, b, c, d] 0 (by simp)
  have h1 : Keccak.rateCell [a, b, c, d] 1 = (Keccak.scalarCells a.1 a.2).2 :=
    rateCell_snd [a, b, c, d] 0 (by simp)
  have h2 : Keccak.rateCell [a, b, c, d] 2 = (Keccak.scalarCells b.1 b.2).1 :=
    rateCell_fst [a, b, c, d] 1 (by simp)
  have h3 : Keccak.rateCell [a, b, c, d] 3 = (Keccak.scalarCells b.1 b.2).2 :=
    rateCell_snd [a, b, c, d] 1 (by simp)
  have h4 : Keccak.rateCell [a, b, c, d] 4 = (Keccak.scalarCells c.1 c.2).1 :=
    rateCell_fst [a, b, c, d] 2 (by simp)
  have h5 : Keccak.rateCell [a, b, c, d] 5 = (Keccak.scalarCells c.1 c.2).2 :=
    rateCell_snd [a, b, c, d] 2 (by simp)
  have h6 : Keccak.rateCell [a, b, c, d] 6 = (Keccak.scalarCells d.1 d.2).1 :=
    rateCell_fst [a, b, c, d] 3 (by simp)
  have h7 : Keccak.rateCell [a, b, c, d] 7 = (Keccak.scalarCells d.1 d.2).2 :=
    rateCell_snd [a, b, c, d] 3 (by simp)
  simp only [rateOf, range8, List.map_cons, List.map_nil, h0, h1, h2, h3, h4, h5, h6, h7]

/-! ## A squeeze -/

/-- **A squeeze as atoms**: a `KECCAK` atom in the even layouts on the rate cells of the waiting
scalars and the capacity, then `challenge_from_state` on its outputs `0`, `1` from the value `b`:
the challenge is `s.squeeze`'s, and the outputs `8..12` its capacity. -/
theorem squeeze_atom {ins outs : List V} {b : ℕ} {s : Fs}
    (hk : (Atom.keccak ins outs false false).Holds rd σ) (hin : ins.map σ = rateOf s.pend ++ s.cap)
    (hch : ChallengeOk σ (outs.getD 0 default) (outs.getD 1 default) b) :
    σ (.n (b + 6)) = s.squeeze.1 ∧ (outs.drop 8).map σ = s.squeeze.2.cap := by
  obtain ⟨-, ho, -, hout⟩ := keccak_outs hk
  rw [hin] at hout
  refine ⟨challengeT_value hch (hout 0 (by omega)) (hout 1 (by omega)), ?_⟩
  apply List.ext_getElem
  · simp [ho, Fs.squeeze, capOf]
  · intro i h1 h2
    simp only [List.length_map, List.length_drop, ho] at h1
    simp only [List.getElem_map, List.getElem_drop]
    have e := hout (8 + i) (by omega)
    rw [List.getD_eq_getElem _ _ (by omega)] at e
    rw [e]
    simp only [Fs.squeeze, Fs.perm]
    interval_cases i <;> rfl

/-- A state's cells are canonical. -/
theorem cellsOfState_canonical (S : KState) (odd : Bool) (c : Fin 13) :
    IsCanonical128 (cellsOfState S odd c) := rfl

/-- A squeeze's capacity cells are canonical. -/
theorem squeeze_cap_canonical (s : Fs) : AllCanonical s.squeeze.2.cap := by
  intro c hc
  simp only [Fs.squeeze, capOf, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> exact cellsOfState_canonical _ _ _

/-! ## Words -/

theorem word_four : word 4 0 0 = gen ^ 2 := by
  rw [show (4 : ℕ) = 2 ^ 2 from rfl]; exact word_two_pow (by decide)

/-! ## Records and runs -/

/-- Five capacity cells `16` words apart. -/
theorem capAt_five {rec : E} {k : ℕ} {c0 c1 c2 c3 c4 : E} (h0 : LoadHolds rd rec k c0)
    (h1 : LoadHolds rd rec (k + 16) c1) (h2 : LoadHolds rd rec (k + 32) c2)
    (h3 : LoadHolds rd rec (k + 48) c3) (h4 : LoadHolds rd rec (k + 64) c4) :
    CapAt rd rec k krCap [c0, c1, c2, c3, c4] := by
  refine ⟨rfl, fun j hj => ?_⟩
  simp only [List.length_cons, List.length_nil] at hj
  interval_cases j
  · simpa [krCap] using h0
  · simpa [krCap] using h1
  · simpa [krCap] using h2
  · simpa [krCap] using h3
  · simpa [krCap] using h4

/-- A run of words, read one at a time. -/
theorem readsAt_of_forall {p : E} {xs : List E} (h : ∀ k (hk : k < xs.length), LoadHolds rd p k xs[k]) :
    ReadsAt rd p xs := h

theorem readsAt_two {p a b : E} (ha : LoadHolds rd p 0 a) (hb : LoadHolds rd p 1 b) :
    ReadsAt rd p [a, b] := by
  intro k hk
  simp only [List.length_cons, List.length_nil] at hk
  interval_cases k
  · exact ha
  · exact hb

/-! ## `fs_pack`'s cells -/

/-- **`fs_next`'s cells** (`fsNextT cur off b`): once its first cell `b + 7` is read canonical,
the cells `b + 7`, `b + 9` are the read word's rate cells with the tag `DS_OBSERVE`. -/
theorem fsNext_scalar {b : ℕ} (h : FsPackOk σ (.n b) (b + 1) dsObserve)
    (hcan : IsCanonical128 (σ (.n (b + 7)))) :
    (σ (.n (b + 7)), σ (.n (b + 9))) = Keccak.scalarCells (σ (.n b)) dsObserve :=
  fsPackT_cells h hcan

end
end LeanVM.Guest.B1.VerifySub
