/-
  LeanVM.Guest.B1.Sig.XmssLayer

  A layer of `verify_lean_xmss` is the layer's root of leanXMSS: from its message digest, its
  codeword, its one-time leaf and its path.
-/

module

public import LeanVM.Guest.B1.Sig.Codeword
public import LeanVM.Guest.B1.Sig.Shifts
public import LeanVM.Guest.B1.Sig.Digest80
public import LeanVM.Guest.B1.Sig.XmssT

/-!
# A layer of `verify_lean_xmss`

`xLayer layer b root` is the layer's message digest, its three step addresses, the
codeword (`xCw`), the one-time leaf (`xLeafK`) and the path (`xMk`). `xLayerCore_sound`: when its
statements after the digest hold, the prologue's facts given (`XPre`), the digest's first cell
`hcell` of `P`, the message's address and cells and the randomizer, `layerRoot` of the signature
part the frame holds (`xPart`) is the cell the path reaches.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The signature a layer's frame holds -/

/-- **The layer signature `verify_lean_xmss` checks**: the randomizer, the chain values (each
chain's hinted start, in the arm its group's dispatch takes), the path (each level's sibling). -/
noncomputable def xPart (layer b : Nat) (σ : Val) : LeanXmss.LayerSignature :=
  ⟨xv (σ (xRho layer b)), fun i => xv (σ (cwStart (xW layer b) 19 (xA layer b + 6) σ i.val)),
    fun l => xv (mSib σ (xBitOf layer) l.val (mBase (xNodeOf layer) 0 l.val (xLeafK layer b).2.1))⟩

/-! ## The prologue -/

/-- The leaf index the frame's bits spell. -/
noncomputable def xLeaf (σ : Val) : Nat := bitsOf σ 2 32

/-- What the prologue establishes. -/
structure XPre (σ : Val) : Prop where
  bits : ∀ j < 32, IsBit (σ (xBit j))
  nodes : ∀ l < 32, σ (xNode l) = eOfNat (xLeaf σ >>> l)
  powers : ∀ s < 10, σ (xPower s) = gen ^ s
  tags : ∀ i < 58, σ (xTag i) = eOfNat i

theorem xLeaf_lt (σ : Val) : xLeaf σ < 2 ^ 32 := bitsVal_lt _ _

theorem atomsOnly_map_cst (base : Nat) (ws : List E) :
    atomsOnly (ws.zipIdx.map fun (w, k) => cst (base + k) w) = true := by
  induction ws.zipIdx with
  | nil => rfl
  | cons x xs ih => exact ih

theorem xPrologue_atoms : atomsOnly xPrologue = true := by
  decide

theorem xPrologue_sound {rd : Reader} {σ : Val} (h : AtomsHold rd σ xPrologue) :
    LoadHolds rd (σ (.n 0)) 1 (σ (.n 1)) ∧ XPre σ := by
  have hb : ∀ j < 32, IsBit (σ (xBit j)) := by
    intro j hj
    have := h.atom (a := .mul (.n (2 + j)) (.n (2 + j)) (.n (2 + j))) (by
      simp only [xPrologue, List.mem_append, booleans, List.mem_map, List.mem_range]
      exact Or.inl (Or.inl (Or.inl (Or.inr ⟨j, hj, rfl⟩))))
    exact this.symm
  refine ⟨h.atom (a := .load (.n 1) (.n 0) 1) (by simp [xPrologue, loadS]), hb, fun l hl => ?_,
    fun s hs => ?_, fun i hi => ?_⟩
  · have hs := shifts_sound (σ := σ) (rd := rd) (bitBase := 2) (n := 32) (outBase := 34) (by norm_num)
      (by norm_num) hb (h.sub fun x hx => by
        simp only [xPrologue, List.mem_append]; exact Or.inl (Or.inl (Or.inr hx))) (31 - l) (by omega)
    rw [xNode, hs]
    congr 2
    omega
  · have e := h.atom (a := .const (.n (128 + s)) (word (2 ^ s) 0 0)) (by
      simp only [xPrologue, List.mem_append, List.mem_map, List.mem_range]
      exact Or.inl (Or.inr ⟨s, hs, rfl⟩))
    simp only [Atom.Holds] at e
    rw [xPower, e, word_eq_eOfNat, Value.gen_pow_eq_eOfNat (by omega)]
  · have e := h.atom (a := .const (.n (138 + i)) (word i 0 0)) (by
      simp only [xPrologue, List.mem_append, List.mem_map, List.mem_range]
      exact Or.inr ⟨i, hi, rfl⟩)
    simp only [Atom.Holds] at e
    rw [xTag, e, word_eq_eOfNat]

end
end LeanVM.Guest.B1.Sig
