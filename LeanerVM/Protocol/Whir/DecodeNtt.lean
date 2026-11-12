/-
  LeanerVM.Protocol.Whir.DecodeNtt

  The exact path of list decoding by the additive transform: a codeword's messages by the inverse
  transform on the first coset, checked by the transform on every coset, in front of a decoder.
-/

module

public import LeanerVM.Protocol.Whir.Decode
public import LeanerVM.Protocol.Whir.WordFast

/-!
# The exact path by the transform

Category A: the list relation of `LeanerVM.Protocol.Whir.Lanes` and the encoder are the
specification; nothing here transcribes a source.

`exactNtt` is the path an honest word takes, at the cost of the deployed prover's encoder: per
lane, one inverse transform on the first `2 ^ κ` positions and one transform per coset of `U_κ`,
`(2 ^ R + 1) · κ · 2 ^ (κ - 1)` products in `E`, against `exactFast`'s elimination. When it
succeeds, its candidate is a codeword equal to the word (`exactNtt_spec`), so every decoder's
list is that candidate at every threshold `2 ^ κ ≤ a ≤ 2 ^ (κ + R)`
(`ListDecoder.decode_eq_of_codeword`); it succeeds on every codeword (`exactNtt_of_codeword`).
`ListDecoder.nttFirst` takes it before another decoder.
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters CompPoly

@[expose] public section

namespace Whir

variable {κ R a ℓ : ℕ}

/-! ## The exact path by the transform -/

/-- The first `2 ^ κ` positions are positions of the word. -/
theorem lt_two_pow_add (i : Fin (2 ^ κ)) : i.val < 2 ^ (κ + R) :=
  lt_of_lt_of_le i.isLt (Nat.pow_le_pow_right (by norm_num) (Nat.le_add_right κ R))

/-- **The exact path by the transform**: each lane's messages interpolated on the first `2 ^ κ`
positions (`inv`), kept when their encoding (`encodeFast`) is the whole lane. -/
def exactNtt (κ R ℓ : ℕ) (F : LW (κ + R)) : Option (Msgs ℓ κ) :=
  let cols : Vector (Vector E (2 ^ (κ + R))) (2 ^ ℓ) :=
    Vector.ofFn fun u ↦ Vector.ofFn fun y ↦ F y u
  let ms : Vector (Vector E (2 ^ κ)) (2 ^ ℓ) := Vector.ofFn fun u ↦
    inv (algebraMap K E) κ (Vector.ofFn fun i ↦ cols[u][i.val]'(lt_two_pow_add i)) 0
  if ∀ u : Fin (2 ^ ℓ), encodeFast (algebraMap K E) κ R ms[u] = cols[u] then
    some fun u ↦ (ms[u] : CMlPolynomialEval E κ)
  else none

/-- What the transform's exact path returns is a codeword equal to the word. -/
theorem exactNtt_spec (hb : κ + R ≤ 64) {F : LW (κ + R)} {V : Msgs ℓ κ}
    (h : exactNtt κ R ℓ F = some V) :
    ∀ y (u : Fin (2 ^ ℓ)), encode (algebraMap K E) κ R (V u) y = F y u := by
  unfold exactNtt at h
  dsimp only at h
  split at h
  · rename_i hall
    cases h
    intro y u
    beta_reduce
    rw [← encodeFast_getElem _ hb, hall u]
    simp
  · exact absurd h (by simp)

/-- The transform's exact path succeeds on every codeword. -/
theorem exactNtt_of_codeword (hb : κ + R ≤ 64) {F : LW (κ + R)} {V : Msgs ℓ κ}
    (hV : ∀ y (u : Fin (2 ^ ℓ)), encode (algebraMap K E) κ R (V u) y = F y u) :
    exactNtt κ R ℓ F = some V := by
  have hcols : ∀ u : Fin (2 ^ ℓ), (Vector.ofFn fun y : Fin (2 ^ (κ + R)) ↦ F y u) =
      encodeFast (algebraMap K E) κ R (V u) := fun u ↦ by
    apply Vector.ext
    intro y hy
    rw [Vector.getElem_ofFn, ← hV ⟨y, hy⟩ u, ← encodeFast_getElem _ hb]
    rfl
  have hms : ∀ u : Fin (2 ^ ℓ), inv (algebraMap K E) κ
      (Vector.ofFn fun i : Fin (2 ^ κ) ↦ F ⟨i.val, lt_two_pow_add i⟩ u) 0 = V u := fun u ↦ by
    have hfirst : (Vector.ofFn fun i : Fin (2 ^ κ) ↦ F ⟨i.val, lt_two_pow_add i⟩ u) =
        fwd (algebraMap K E) κ (V u) 0 := by
      apply Vector.ext
      intro i hi
      rw [Vector.getElem_ofFn, ← hV _ u, encode_eq_novelEval, fwd_getElem _ κ (by omega) _ _ _ hi,
        add_zero]
    rw [hfirst, inv_fwd]
  unfold exactNtt
  simp only [Fin.getElem_fin, Vector.getElem_ofFn]
  simp only [hms, hcols, implies_true, ↓reduceIte]

/-- A decoder that takes the transform's exact path first and falls back to `D`. -/
def ListDecoder.nttFirst (D : ListDecoder κ R a ℓ) (hdist : 2 ^ κ ≤ a)
    (hle : a ≤ 2 ^ (κ + R)) (hb : κ + R ≤ 64) : ListDecoder κ R a ℓ where
  decode := fun F ↦ match exactNtt κ R ℓ F with
    | some V => [V]
    | none => D.decode F
  mem_iff := fun F V ↦ by
    split
    · rename_i V₀ h
      rw [List.mem_singleton, ← D.mem_iff]
      exact (D.decode_eq_of_codeword hdist hle hb (exactNtt_spec hb h) V).symm
    · exact D.mem_iff F V
  nodup := fun F ↦ by
    split
    · exact List.nodup_singleton _
    · exact D.nodup F

end Whir

end

end LeanerVM.Protocol
