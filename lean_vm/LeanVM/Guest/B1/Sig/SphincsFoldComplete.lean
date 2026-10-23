/-
  LeanVM.Guest.B1.Sig.SphincsFoldComplete

  The folds of `verify_sig_lean_sphincs` are sequential: a fold's levels read its anchor, its first
  node, `P`, the address constants and the padding run.
-/

module

public import LeanVM.Guest.B1.Sig.SphincsFkArms

/-!
# The folds, sequential

* `k64_kseqS`: a 64-byte `keccak` of `P` and three values is sequential;
* `foldLevel_kseq`, `foldLevels_kseq`: a fold's levels are sequential, from bases `flBase`;
* `foldLevels_hints`, `foldLevels_hint_mem`, `flBase_lt`: their only hints are the siblings, at the
  levels' increasing bases.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

variable {lo : Nat} {a1 a2 : V}

/-- A 64-byte `keccak` of `P` and three values is sequential. -/
theorem k64_kseqS {m1 m2 m3 : V} {c : Nat} (hlo : 206 ≤ lo) (hc : lo ≤ c)
    (h1 : KRd lo (SX a1 a2) c m1) (h2 : KRd lo (SX a1 a2) c m2) (h3 : KRd lo (SX a1 a2) c m3) :
    KSeq lo (SX a1 a2) c (k64 sPad sPP m1 m2 m3 c (c + 1)) (c + 14) :=
  ⟨c + 1, ⟨rfl, canon_word _ _, rfl⟩, c + 14, ⟨rfl, rfl, fun x hx => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact sx_pp (by omega)
    · exact h1.mono (by omega)
    · exact h2.mono (by omega)
    · exact h3.mono (by omega)
    · exact sx_pad (k := 0) (by omega) (by norm_num)
    · exact sx_pad (k := 1) (by omega) (by norm_num)
    · exact sx_pad (k := 2) (by omega) (by norm_num)
    · exact sx_pad (k := 3) (by omega) (by norm_num)
    · exact krd_in hc (by omega)
    · exact sx_pad (k := 1) (by omega) (by norm_num)
    · exact sx_pad (k := 2) (by omega) (by norm_num)
    · exact sx_pad (k := 3) (by omega) (by norm_num)
    · exact sx_pad (k := 4) (by omega) (by norm_num), rfl⟩, rfl⟩

/-- A fold's addresses read the address constants, or are constants. -/
def AdrOK (adr : Nat → Sum V Nat) : Prop := ∀ l a, adr l = .inl a → ∃ k < 41, a = .n (165 + k)

theorem foldLevel_snd (atV : V) (adr : Nat → Sum V Nat) (l : Nat) (bit : Bool) (cur : V) (b : Nat) :
    (foldLevel atV (adr l) bit cur b).2.1 = flNext adr l b := by
  unfold foldLevel flNext; cases adr l <;> rfl

/-- **A fold's level is sequential**, its node below its end. -/
theorem foldLevel_kseq {atV : V} {adr : Nat → Sum V Nat} {l : Nat} {bit : Bool} {cur : V} {b : Nat}
    (hlo : 206 ≤ lo) (hb : lo ≤ b) (hadr : AdrOK adr) (hat : NBv lo atV)
    (hcur : KRd lo (SX atV a2) b cur) :
    KSeq lo (SX atV a2) b (foldLevel atV (adr l) bit cur b).1 (flNext adr l b) ∧
      (foldLevel atV (adr l) bit cur b).2.1 = flNext adr l b ∧
      (∃ j, b ≤ j ∧ j < flNext adr l b ∧ (foldLevel atV (adr l) bit cur b).2.2 = .n j) ∧
      b + 16 ≤ flNext adr l b := by
  refine ⟨?_, foldLevel_snd atV adr l bit cur b, ?_, ?_⟩
  · cases ha : adr l with
    | inl a =>
        obtain ⟨k, hk, rfl⟩ := hadr l a ha
        have hn : flNext adr l b = b + 16 := by simp [flNext, ha]
        rw [hn]
        refine ⟨b + 1, hint1_kseqA _ b, b + 2, ⟨rfl, sx_a1 hat, sx_cst hlo hk, rfl⟩,
          k64_kseqS hlo (by omega) (krd_in (by omega) (by omega)) ?_ ?_⟩ <;>
          cases bit <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
          first | exact hcur.mono (by omega) | exact krd_in (by omega) (by omega)
    | inr c =>
        have hn : flNext adr l b = b + 17 := by simp [flNext, ha]
        rw [hn]
        refine ⟨b + 1, hint1_kseqA _ b, b + 2, ⟨rfl, canon_word _ _, rfl⟩, b + 3,
          ⟨rfl, sx_a1 hat, krd_in (by omega) (by omega), rfl⟩,
          k64_kseqS hlo (by omega) (krd_in (by omega) (by omega)) ?_ ?_⟩ <;>
          cases bit <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
          first | exact hcur.mono (by omega) | exact krd_in (by omega) (by omega)
  · cases ha : adr l with
    | inl a => exact ⟨b + 3, by omega, by simp [flNext, ha], by simp [foldLevel]⟩
    | inr c => exact ⟨b + 4, by omega, by simp [flNext, ha], by simp [foldLevel]⟩
  · unfold flNext; split <;> omega

theorem flNext_ge (adr : Nat → Sum V Nat) (l b : Nat) : b + 16 ≤ flNext adr l b := by
  unfold flNext; split <;> omega

theorem flBase_ge (adr : Nat → Sum V Nat) : ∀ (l j b : Nat), b + 16 * j ≤ flBase adr l j b
  | _, 0, _ => by simp [flBase]
  | l, j + 1, b => by
      have := flBase_ge adr (l + 1) j (flNext adr l b)
      have := flNext_ge adr l b
      simp only [flBase]
      omega

theorem flBase_lt (adr : Nat → Sum V Nat) : ∀ (l j j' b : Nat), j < j' →
    flBase adr l j b + 16 ≤ flBase adr l j' b
  | _, _, 0, _, h => absurd h (by omega)
  | l, 0, j' + 1, b, _ => by
      have := flBase_ge adr (l + 1) j' (flNext adr l b)
      have := flNext_ge adr l b
      simp only [flBase]
      omega
  | l, j + 1, j' + 1, b, h => by
      have := flBase_lt adr (l + 1) j j' (flNext adr l b) (by omega)
      simp only [flBase]
      exact this

/-- **A fold's levels are sequential**, the node reached below their end. -/
theorem foldLevels_kseq {atV : V} {adr : Nat → Sum V Nat} {index : Nat} (hlo : 206 ≤ lo)
    (hadr : AdrOK adr) (hat : NBv lo atV) :
    ∀ (m l : Nat) (cur : V) (b : Nat), lo ≤ b → KRd lo (SX atV a2) b cur →
      KSeq lo (SX atV a2) b (foldLevels atV adr index m l cur b).1 (flBase adr l m b) ∧
        (foldLevels atV adr index m l cur b).2.1 = flBase adr l m b ∧
        KRd lo (SX atV a2) (flBase adr l m b) (foldLevels atV adr index m l cur b).2.2
  | 0, _, cur, b, _, hcur => ⟨rfl, rfl, hcur⟩
  | m + 1, l, cur, b, hb, hcur => by
      obtain ⟨k1, k2, ⟨j, hj1, hj2, ej⟩, k4⟩ := foldLevel_kseq (l := l) (bit := index.testBit l) hlo hb
        hadr hat hcur
      obtain ⟨r1, r2, r3⟩ := foldLevels_kseq hlo hadr hat m (l + 1)
        (foldLevel atV (adr l) (index.testBit l) cur b).2.2 (flNext adr l b) (by omega)
        (by rw [ej]; exact krd_in (by omega) hj2)
      simp only [foldLevels]
      rw [k2]
      exact ⟨KSeq.append k1 r1, r2, r3⟩

/-- A fold's levels' only hints are the siblings, at the levels' bases. -/
theorem foldLevels_hints {atV : V} {adr : Nat → Sum V Nat} {index : Nat} : ∀ (m l : Nat) (cur : V)
    (b : Nat) s vs, Stmt.atom (.hint (.witness s (.stack vs))) ∈ (foldLevels atV adr index m l cur b).1 →
      ∃ j < m, vs = [.n (flBase adr l j b)]
  | 0, _, _, _, _, _, h => absurd h (by simp [foldLevels])
  | m + 1, l, cur, b, s, vs, h => by
      simp only [foldLevels, List.mem_append] at h
      rcases h with h | h
      · refine ⟨0, by omega, ?_⟩
        unfold foldLevel at h
        split at h <;>
          simp only [hintW, List.mem_cons, Stmt.atom.injEq, Atom.hint.injEq, Hint.witness.injEq,
            Dest.stack.injEq, k64, cst, kecS, addS, reduceCtorEq, List.not_mem_nil, or_false] at h <;>
          obtain ⟨-, rfl⟩ := h <;> rfl
      · obtain ⟨j, hj, e⟩ := foldLevels_hints m (l + 1) _ _ s vs h
        refine ⟨j + 1, by omega, ?_⟩
        rw [e, foldLevel_snd]
        rfl

theorem foldLevel_hint_mem (atV : V) (a : Sum V Nat) (bit : Bool) (cur : V) (b : Nat) :
    hintW "sp_forest_nodes" [.n b] ∈ (foldLevel atV a bit cur b).1 := by
  unfold foldLevel; split <;> simp

theorem foldLevels_hint_mem {atV : V} {adr : Nat → Sum V Nat} {index : Nat} : ∀ (m l : Nat) (cur : V)
    (b j : Nat), j < m → hintW "sp_forest_nodes" [.n (flBase adr l j b)] ∈ (foldLevels atV adr index m l cur b).1
  | 0, _, _, _, _, h => absurd h (by omega)
  | m + 1, l, cur, b, 0, _ => List.mem_append_left _ (foldLevel_hint_mem ..)
  | m + 1, l, cur, b, j + 1, h => by
      have := foldLevels_hint_mem (atV := atV) (adr := adr) (index := index) m (l + 1)
        (foldLevel atV (adr l) (index.testBit l) cur b).2.2 (foldLevel atV (adr l) (index.testBit l) cur b).2.1 j
        (by omega)
      refine List.mem_append_right _ ?_
      have e : flBase adr (l + 1) j (foldLevel atV (adr l) (index.testBit l) cur b).2.1 = flBase adr l (j + 1) b := by
        rw [foldLevel_snd]; rfl
      rw [e] at this
      exact this

end
end LeanVM.Guest.B1.Sig
