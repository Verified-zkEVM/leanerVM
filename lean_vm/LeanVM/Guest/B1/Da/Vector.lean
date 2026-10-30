/-
  LeanVM.Guest.B1.Da.Vector

  `da_vector_cell`'s template and check (TRIAGE G #93).
-/

module

public import LeanVM.Guest.B1.Da.Cell
public import LeanVM.Guest.B1.Da.ChainSplit

/-!
# `da_vector_cell` (G:4043-4053)

`da_vector_cell(digest)` (`core28`): `256` hinted weights `.n 1 … .n 256`; pair `p`'s atoms
(`vpairA`, `pack_pair` of `w[2p]`, `w[2p + 1]` without loads, the template `tmplV`) split the two
weights into three canonical cells (`vpair_fwd`, as `pair_fwd`); the `384` cells are hashed
(`keccak_cells`, a `ChainSpec` checked on the block after the template), the digest's two cells
written at `digest`, and the function returns the frame address of the weights (`frameAddr`).
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Main

@[expose] public section

variable {rd : Reader} {σ : Val}

/-- `pack_pair` of the stack words `s`, `t` from the value `b + 2`: 26 atoms, its three cells
`.n (b + 8)`, `.n (b + 17)`, `.n (b + 26)`. -/
def vpairA (s t : V) (b : ℕ) : List Atom :=
  let v := fun r => V.n (b + r)
  [.hint (.limbs s [v 2, v 3]), .hint (.limbs t [v 4, v 5]),
   .assertInK (v 2) (v 3), .const (v 6) wY, .mul (v 7) (v 6) (v 3),
   .add (v 8) (v 2) (v 7), .add (v 9) s (v 2), .const (v 10) wYi,
   .mul (v 11) (v 9) (v 10), .add (v 12) (v 11) (v 3), .const (v 13) wYi,
   .mul (v 14) (v 12) (v 13), .assertInK (v 14) (v 4), .const (v 15) wY,
   .mul (v 16) (v 15) (v 4), .add (v 17) (v 14) (v 16),
   .add (v 18) t (v 4), .const (v 19) wYi, .mul (v 20) (v 18) (v 19),
   .add (v 21) (v 20) (v 5), .const (v 22) wYi, .mul (v 23) (v 21) (v 22),
   .assertInK (v 5) (v 23), .const (v 24) wY, .mul (v 25) (v 24) (v 23),
   .add (v 26) (v 5) (v 25)]

/-- **`pack_pair` of stack words**: the three cells. -/
theorem vpair_fwd {s t : V} {b : ℕ} (h : ∀ a ∈ vpairA s t b, a.Holds rd σ) :
    [σ (.n (b + 8)), σ (.n (b + 17)), σ (.n (b + 26))] = Digest.pairCells (σ s) (σ t) := by
  simp only [vpairA, List.forall_mem_cons, Atom.Holds, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true, and_true] at h
  obtain ⟨-, -, k1, c6, m7, a8, a9, c10, m11, a12, c13, m14, k2, c15, m16, a17, a18, c19,
    m20, a21, c22, m23, k3, c24, m25, a26⟩ := h
  have e14 : σ (.n (b + 14)) = ((σ s + σ (.n (b + 2))) * wYi + σ (.n (b + 3))) * wYi := by
    rw [m14, a12, m11, a9, c10, c13]
  have e23 : σ (.n (b + 23)) = ((σ t + σ (.n (b + 4))) * wYi + σ (.n (b + 5))) * wYi := by
    rw [m23, a21, m20, a18, c19, c22]
  rw [e14] at k2
  rw [e23] at k3
  obtain ⟨hs0, hs1, ht0, ht1⟩ := pair_spec k1 k2 k3
  obtain ⟨p1, p2, p3⟩ := pair_cells (σ s) (σ t)
  simp only [Digest.pairCells, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_⟩
  · rw [a8, m7, c6, hs0, hs1, p1]
  · rw [a17, m16, c15, e14, hs0, hs1, ht0, p2]
  · rw [a26, m25, c24, e23, ht0, ht1, p3]

/-- The `128` pairs' atoms. -/
def tmplV : List Atom :=
  (List.range 128).flatMap fun p => vpairA (.n (2 * p + 1)) (.n (2 * p + 2)) (255 + 25 * p)

/-- Pair `p`'s three cells. -/
def vcells (p : ℕ) : List (Option V) :=
  [some (.n (255 + 25 * p + 8)), some (.n (255 + 25 * p + 17)), some (.n (255 + 25 * p + 26))]

/-- The digest's chain: the `384` cells, `6144` bytes, from the zero state. -/
def vecSpec (atoms : List Atom) : ChainSpec :=
  ⟨(List.range 128).flatMap vcells, 6144, true, none, keccakBlocks atoms⟩

/-- The weights' run. -/
def wRun : List V := (List.range 256).map fun k => .n (k + 1)

/-- `frameAddr p run`. -/
def isFrameAt (p : V) (run : List V) : Atom → Bool
  | .frameAddr q r => decide (q = p) && decide (r = run)
  | _ => false

theorem frame_sound {atoms : List Atom} {p : V} {run : List V}
    (h : atoms.any (isFrameAt p run) = true) (hat : ∀ x ∈ atoms, x.Holds rd σ) :
    IsInK (σ p) ∧ ∀ (k : ℕ) (hk : k < run.length) (w : E),
      rd ((σ p).limb 0 * Parameters.gpow k) = some w → w = σ run[k] := by
  obtain ⟨x, hp, hx⟩ := any_holds h hat
  cases x <;> simp only [isFrameAt, Bool.false_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hp
  obtain ⟨rfl, rfl⟩ := hp
  exact hx

/-- **`da_vector_cell`'s template, checked**: the hint, then the template's atoms. -/
def vecTmplOk (fn : Fn) : Bool :=
  decide (fn.params = [.n 0]) &&
  match splitBody fn.body with
  | some (A, vs) =>
    decide (vs = [.n 4462]) && decide (3329 ≤ A.length) && atomsEqb ((A.drop 1).take 3328) tmplV
  | none => false

/-- The tail of the body: the chain, the stores, the frame address. -/
noncomputable def vecTail : List Atom := (((splitBody (Fn.body Data.core28)).map (·.1)).getD []).drop 3329

/-- **`da_vector_cell`'s tail, checked**: the chain's shape, the digest's stores, the frame
address and its copy. -/
noncomputable def vecTailOk : Bool :=
  (vecSpec vecTail).shapeOk && decide ((vecSpec vecTail).nb = 46) &&
    vecTail.any (isLoadAt ((vecSpec vecTail).outV ((vecSpec vecTail).nb - 1) 0) (.n 0) 0) &&
    vecTail.any (isLoadAt ((vecSpec vecTail).outV ((vecSpec vecTail).nb - 1) 1) (.n 0) 1) &&
    vecTail.any (isFrameAt (.n 4461) wRun) && vecTail.any (isCopyAt (.n 4462) (.n 4461))

end
end LeanVM.Guest.B1.Da
