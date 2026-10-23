/-
  LeanVM.Guest.B1.Sig.SphincsCoords

  The eight coordinates of `verify_sig_lean_sphincs`'s forest, in a row, are sound: each
  coordinate's facts, the sixteen top nodes, and the running encoding's and bound's sums.
-/

module

public import LeanVM.Guest.B1.Sig.SphincsSub

/-!
# The coordinates, sound

* `cSt`: the running encoding, bound and base before coordinate `c`;
* `sCoords_cons`, `sCoords_sound`: the coordinates' statements hold, then the rest; each
  coordinate's `CoordFacts`; the tops (`sCoords_tops`) and the end state (`sCoords_end`);
* `cT`, `cA`, `cS`: the codeword index, the child and the super-child each dispatch takes;
* `cSt_acc`: the running encoding is the sum of the weights so far, the bound `n161` plus the
  marks' terms so far.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier (eOfNat)

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}

/-- The running encoding, bound and base before coordinate `c`. -/
def cSt : Nat → Option V × V × Nat
  | 0 => (none, .n 161, 206)
  | c + 1 =>
      (some (sCoord c (cSt c).1 (cSt c).2.1 (cSt c).2.2).2.2.1,
        (sCoord c (cSt c).1 (cSt c).2.1 (cSt c).2.2).2.2.2.1,
        (sCoord c (cSt c).1 (cSt c).2.1 (cSt c).2.2).2.1)

/-- Coordinate `c`, from its state. -/
def cCoord (c : Nat) : List Stmt × Nat × V × V × (V × V) := sCoord c (cSt c).1 (cSt c).2.1 (cSt c).2.2

theorem sCoords_cons (m c : Nat) :
    sCoords (m + 1) c (cSt c).1 (cSt c).2.1 (cSt c).2.2 =
      ((cCoord c).1 ++ (sCoords m (c + 1) (cSt (c + 1)).1 (cSt (c + 1)).2.1 (cSt (c + 1)).2.2).1,
        (sCoords m (c + 1) (cSt (c + 1)).1 (cSt (c + 1)).2.1 (cSt (c + 1)).2.2).2.1,
        (sCoords m (c + 1) (cSt (c + 1)).1 (cSt (c + 1)).2.1 (cSt (c + 1)).2.2).2.2.1,
        (sCoords m (c + 1) (cSt (c + 1)).1 (cSt (c + 1)).2.1 (cSt (c + 1)).2.2).2.2.2.1,
        (cCoord c).2.2.2.2.1 :: (cCoord c).2.2.2.2.2 ::
          (sCoords m (c + 1) (cSt (c + 1)).1 (cSt (c + 1)).2.1 (cSt (c + 1)).2.2).2.2.2.2) := rfl

/-- The end state of `m` coordinates from `c`. -/
theorem sCoords_end : ∀ (m c : Nat),
    (sCoords m c (cSt c).1 (cSt c).2.1 (cSt c).2.2).2.1 = (cSt (c + m)).2.2 ∧
      (sCoords m c (cSt c).1 (cSt c).2.1 (cSt c).2.2).2.2.2.1 = (cSt (c + m)).2.1
  | 0, c => ⟨rfl, rfl⟩
  | m + 1, c => by
      rw [sCoords_cons, show c + (m + 1) = c + 1 + m by omega]
      exact sCoords_end m (c + 1)

/-- The top nodes of `m` coordinates from `c`. -/
theorem sCoords_tops : ∀ (m c : Nat),
    (sCoords m c (cSt c).1 (cSt c).2.1 (cSt c).2.2).2.2.2.2 =
      (List.range m).flatMap fun k => [(cCoord (c + k)).2.2.2.2.1, (cCoord (c + k)).2.2.2.2.2]
  | 0, c => rfl
  | m + 1, c => by
      rw [sCoords_cons, sCoords_tops m (c + 1), List.range_succ_eq_map, List.flatMap_cons,
        List.flatMap_map]
      simp only [Nat.add_zero, List.cons_append, List.nil_append, show ∀ k, c + 1 + k = c + (k + 1)
        from fun k => by omega]

/-- **The coordinates, sound.** -/
theorem sCoords_sound (hp : PadOK σ sPad) (htws : TwsOK σ) {rest : List Stmt} {next : Prop} :
    ∀ (m c : Nat), Stmt.HoldsList C rd σ
      ((sCoords m c (cSt c).1 (cSt c).2.1 (cSt c).2.2).1 ++ rest) next kret →
      Stmt.HoldsList C rd σ rest next kret ∧
        ∀ k < m, CoordFacts σ (c + k) (cSt (c + k)).1 (cSt (c + k)).2.1 (cSt (c + k)).2.2
  | 0, _, h => ⟨h, fun k hk => absurd hk (by omega)⟩
  | m + 1, c, h => by
      rw [sCoords_cons, List.append_assoc] at h
      obtain ⟨h1, f⟩ := sCoord_sound hp htws h
      obtain ⟨h2, fs⟩ := sCoords_sound hp htws m (c + 1) h1
      refine ⟨h2, fun k hk => ?_⟩
      rcases k with _ | k
      · exact f
      · have := fs k (by omega)
        rwa [show c + 1 + k = c + (k + 1) by omega] at this

/-! ## The sums -/

/-- The base of sub-tree `j` of coordinate `c`. -/
def subBase (c j : Nat) : Nat :=
  if j = 0 then (cSt c).2.2 + 10 else (coordS0 c (cSt c).1 (cSt c).2.1 (cSt c).2.2).2.1

/-- The codeword index of sub-tree `j` of coordinate `c`. -/
noncomputable def cT (σ : Val) (c j : Nat) : Nat := subT σ (subBase c j)

/-- The child of sub-tree `j` of coordinate `c`. -/
noncomputable def cA (σ : Val) (c j : Nat) : Nat := subA σ (subBase c j)

/-- The super-child of coordinate `c`. -/
noncomputable def cS (σ : Val) (c : Nat) : Nat := coordS σ (cSt c).2.2

/-- The encoding's terms of coordinate `c`. -/
noncomputable def encTerm (σ : Val) (c : Nat) : E :=
  fkWeight (cT σ c 0) (2 * c) + fkWeight (cT σ c 1) (2 * c + 1)

/-- The bound's terms of coordinate `c`. -/
noncomputable def boundTerm (σ : Val) (c : Nat) : E :=
  cbMul (cA σ c 0) (58 + 3 * (2 * c)) + cbMul (cA σ c 1) (58 + 3 * (2 * c + 1)) +
    cbMul (cS σ c) (26 + 4 * c)

/-- **The running sums**: before coordinate `c`, the encoding is the sum of the weights so far and
the bound is `n161` plus the marks' terms so far. -/
theorem cSt_acc (hf : ∀ c < 8, CoordFacts σ c (cSt c).1 (cSt c).2.1 (cSt c).2.2) :
    ∀ c ≤ 8, encVal σ (cSt c).1 = ∑ k ∈ Finset.range c, encTerm σ k ∧
      σ (cSt c).2.1 = σ (.n 161) + ∑ k ∈ Finset.range c, boundTerm σ k
  | 0, _ => ⟨rfl, by simp [cSt]⟩
  | c + 1, hc => by
      obtain ⟨ih1, ih2⟩ := cSt_acc hf c (by omega)
      have f := hf c (by omega)
      have e0 := f.sub0.encOK
      have e1 := f.sub1.encOK
      have b0 := f.sub0.boundOK
      have b1 := f.sub1.boundOK
      have bc := f.boundOK
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ← ih1, ← add_assoc, ← ih2]
      refine ⟨?_, ?_⟩
      · show σ (sCoord c (cSt c).1 (cSt c).2.1 (cSt c).2.2).2.2.1 = _
        rw [sCoord_eq]
        show σ (coordS1 c (cSt c).1 (cSt c).2.1 (cSt c).2.2).2.2.1 = _
        rw [coordS1, sSubtree_eq, e1]
        show encVal σ (some (coordS0 c (cSt c).1 (cSt c).2.1 (cSt c).2.2).2.2.1) + _ = _
        simp only [encVal]
        rw [coordS0, sSubtree_eq, e0, encTerm, cT, cT, subBase, subBase]
        simp only [↓reduceIte, one_ne_zero, Nat.add_zero]
        rw [add_assoc]
        rfl
      · show σ (sCoord c (cSt c).1 (cSt c).2.1 (cSt c).2.2).2.2.2.1 = _
        rw [bc]
        have e1' : σ (coordS1 c (cSt c).1 (cSt c).2.1 (cSt c).2.2).2.2.2.1 =
            σ (coordS0 c (cSt c).1 (cSt c).2.1 (cSt c).2.2).2.2.2.1 +
              cbMul (cA σ c 1) (58 + 3 * (2 * c + 1)) := b1
        have e0' : σ (coordS0 c (cSt c).1 (cSt c).2.1 (cSt c).2.2).2.2.2.1 =
            σ (cSt c).2.1 + cbMul (cA σ c 0) (58 + 3 * (2 * c)) := b0
        rw [e1', e0', boundTerm, cS]
        abel

end
end LeanVM.Guest.B1.Sig
