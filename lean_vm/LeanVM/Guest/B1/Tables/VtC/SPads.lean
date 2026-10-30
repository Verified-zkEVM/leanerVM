/-
  LeanVM.Guest.B1.Tables.VtC.SPads

  The tables' height statements (`vtPadT`, `vtPad5T`) hold on the honest valuation: each height
  `g^τ` read from `dims_g`, the rows from `table_rows`, `padding_weight` dispatched on `τ`, and its
  `lead`, `rest` checked when `τ` is not the floor.
-/

module

public import LeanVM.Guest.B1.Tables.VtC.SBase

/-!
# The tables' heights (G:1997-2011)

`pad_ok` (`t < 5`, floor `0`) and `pad5_ok` (`KECCAK`, floor `9`): from the template's equations,
its two reads not stores, a memory holding `g^τ` and the rows `n` with `τ = max (log2Ceil n)
floor < 29`, the bus point's first `τ` coordinates `zs` at `zeta`, and the oracle's returns of
`padding_weight` (`paddingWeight zs n`, `lead`, `rest`), every statement holds and the padding
weight is `paddingWeight zs n`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd

@[expose] public section

variable {rd : Reader} {w : ℕ → E} {σ : Val}

/-- The dispatch on `g^τ` to `padding_weight__L{τ}`. -/
theorem pad_dispatch {v τ n : ℕ} {zs : List E} (hτ : τ < 29) (hv : σ (.n v) = gen ^ τ)
    (hrow : σ (.n (v + 5)) = eOfNat n) (hz : TbReadsAt rd (σ (.n 8)) zs) (hzl : zs.length = τ)
    (hn : n ≤ 2 ^ τ) (h6 : σ (.n (v + 6)) = paddingWeight zs n) (h7 : σ (.n (v + 7)) = PadLead τ n)
    (h8 : σ (.n (v + 8)) = PadRest τ n) :
    VSH (coreProgram.Rel rd) rd σ
      (.dispatch (.n v) vtPadNames [.n (v + 5), .n 8] [.n (v + 6), .n (v + 7), .n (v + 8)]) := by
  rw [vsh_dispatch]
  refine ⟨τ, by simp [vtPadNames]; exact hτ, by rw [hv, gen_pow_eq_ofK], ?_⟩
  simp only [vtPadNames, List.getElem_map, List.getElem_range, List.map_cons, List.map_nil]
  exact padding_weight_complete_holds τ hτ rd _ _ ⟨n, zs, hn, hrow, hzl, hz, h6, h7, h8⟩

set_option maxHeartbeats 1000000 in
/-- **Table `t < 5`'s height.** -/
theorem pad_ok {v t τ n : ℕ} {zs : List E} (hlow : LowDefB 8 rd)
    (hg : GoodL rd w σ (vtPadT v t))
    (hS : ∀ a ∈ [Atom.load (.n v) (.n 10) (t + 1), .load (.n (v + 5)) (.n 11) t], a ∉ vtSL)
    (hdim : LoadHolds rd (σ (.n 10)) (t + 1) (gen ^ τ))
    (hrow : LoadHolds rd (σ (.n 11)) t (eOfNat n))
    (hz : TbReadsAt rd (σ (.n 8)) zs) (hzl : zs.length = τ) (hτ : τ < 29) (hlog : log2Ceil n = τ)
    (hw6 : w (v + 6) = paddingWeight zs n) (hw7 : w (v + 7) = PadLead τ n)
    (hw8 : w (v + 8) = PadRest τ n) :
    (∀ st ∈ vtPadT v t, VSH (coreProgram.Rel rd) rd σ st) ∧
      σ (.n (v + 6)) = paddingWeight zs n := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hS
  obtain ⟨s0, s5⟩ := hS
  simp only [vtPadT, GoodL, GoodS, fixNe, Good, and_true, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp, forall_eq] at hg
  obtain ⟨g0, g1, g2, g3, ⟨g6, g7, g8⟩, g9, -, g10, g11, g12, g13⟩ := hg
  simp only [show v + 1 < v + 2 by omega, show v + 11 < v + 13 ∧ v + 12 < v + 13 from
    ⟨by omega, by omega⟩, ↓reduceIte] at g2 g13
  have hn : n ≤ 2 ^ τ := log2Ceil_le_iff.mp (le_of_eq hlog)
  obtain ⟨hlr1, hlr2⟩ := (lead_rest_iff (by omega) hn).mpr hlog
  obtain ⟨r1, r2, r3⟩ := g2
  obtain ⟨ev, l0⟩ := read_of (g0.resolve_left s0) hdim
  obtain ⟨hrc, -⟩ := rc_holds (κ := 8) hlow r1 r2 r3 ev (by rw [g1, vtW28_gen]) (by omega)
    (by norm_num)
  obtain ⟨e5, l3⟩ := read_of (g3.resolve_left s5) hrow
  have e6 : σ (.n (v + 6)) = paddingWeight zs n := by rw [g6, hw6]
  have e7 : σ (.n (v + 7)) = PadLead τ n := by rw [g7, hw7]
  have e8 : σ (.n (v + 8)) = PadRest τ n := by rw [g8, hw8]
  have e11 : σ (.n (v + 11)) = PadRest τ n := by rw [g11, e8, g10, tb_word_zero, add_zero]
  refine ⟨?_, e6⟩
  simp only [vtPadT, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true, and_true, vsh_atom]
  refine ⟨l0, g1, hrc, l3, pad_dispatch hτ ev e5 hz hzl hn e6 e7 e8, g9, ?_, g10, g11, trivial, ?_⟩
  · show σ _ + σ _ = 0
    rw [e7, g9, tb_word_one, ← pwLead, hlr1, e_add_self]
  · show σ _ = σ _ * σ _ ∧ σ _ = 1
    refine ⟨g13, ?_⟩
    rw [g13, g12, mul_inv_cancel₀ (by rw [e11]; exact hlr2)]

set_option maxHeartbeats 1000000 in
/-- **The `KECCAK` table's height**, its floor `9`. -/
theorem pad5_ok {v τ n : ℕ} {zs : List E} (hlow : LowDefB 8 rd)
    (hg : GoodL rd w σ (vtPad5T v))
    (hgb : GoodL rd w σ [.atom (.const (.n (v + 17)) (word 1 0 0)),
      .atom (.assertEq (.n (v + 7)) (.n (v + 17))), .atom (.const (.n (v + 18)) (word 0 0 0)),
      .atom (.add (.n (v + 19)) (.n (v + 8)) (.n (v + 18))),
      .atom (.hint (.inverse (.n (v + 19)) (.n (v + 20)))),
      .atom (.assertNe (.n (v + 19)) (.n (v + 20)) (.n (v + 21)))])
    (hS : ∀ a ∈ [Atom.load (.n v) (.n 10) 6, .load (.n (v + 5)) (.n 11) 5], a ∉ vtSL)
    (hdim : LoadHolds rd (σ (.n 10)) 6 (gen ^ τ))
    (hrow : LoadHolds rd (σ (.n 11)) 5 (eOfNat n))
    (hz : TbReadsAt rd (σ (.n 8)) zs) (hzl : zs.length = τ) (hτ : τ < 29)
    (hlog : τ = max (log2Ceil n) 9)
    (hw6 : w (v + 6) = paddingWeight zs n) (hw7 : w (v + 7) = PadLead τ n)
    (hw8 : w (v + 8) = PadRest τ n) :
    (∀ st ∈ vtPad5T v, VSH (coreProgram.Rel rd) rd σ st) ∧
      σ (.n (v + 6)) = paddingWeight zs n := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hS
  obtain ⟨s0, s5⟩ := hS
  simp only [vtPad5T, GoodL, GoodS, fixNe, Good, and_true, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp, forall_eq] at hg
  obtain ⟨g0, g1, g2, g3, ⟨g6, g7, g8⟩, g9, g10, g11, g12, g15, g16⟩ := hg
  simp only [GoodL, GoodS, fixNe, Good, and_true] at hgb
  obtain ⟨b17, -, b18, b19, b20, b21⟩ := hgb
  simp only [show v + 1 < v + 2 by omega, show v + 9 < v + 12 by omega,
    show ¬ (v + 11 < v ∧ v + 10 < v) from fun h => by omega,
    show v + 19 < v + 21 ∧ v + 20 < v + 21 from ⟨by omega, by omega⟩, ↓reduceIte] at g2 g11 g12 b21
  have hn : n ≤ 2 ^ τ := by
    have := log2Ceil_le_iff.mp (show log2Ceil n ≤ τ by omega)
    exact this
  obtain ⟨r1, r2, r3⟩ := g2
  obtain ⟨ev, l0⟩ := read_of (g0.resolve_left s0) hdim
  obtain ⟨hrc, -⟩ := rc_holds (κ := 8) hlow r1 r2 r3 ev (by rw [g1, vtW28_gen]) (by omega)
    (by norm_num)
  obtain ⟨e5, l3⟩ := read_of (g3.resolve_left s5) hrow
  have e6 : σ (.n (v + 6)) = paddingWeight zs n := by rw [g6, hw6]
  have e7 : σ (.n (v + 7)) = PadLead τ n := by rw [g7, hw7]
  have e8 : σ (.n (v + 8)) = PadRest τ n := by rw [g8, hw8]
  have w512 : word 512 0 0 = gen ^ 9 := by
    rw [show (512 : ℕ) = 2 ^ 9 by norm_num, tb_word_two_pow (by norm_num)]
  have e10 : σ (.n (v + 10)) = gen ^ 9 := by rw [g10, w512]
  have e11 : σ (.n (v + 11)) = gen ^ (τ - 9) := by rw [g11, ev, e10, gen_pow_div (by omega)]
  obtain ⟨q1, q2, q3⟩ := g12
  obtain ⟨hrc11, -⟩ := rc_holds (κ := 8) hlow q1 q2 q3 e11 (by rw [g9, vtW28_gen]) (by omega)
    (by norm_num)
  refine ⟨?_, e6⟩
  simp only [vtPad5T, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true, and_true, vsh_atom, vsh_ite]
  refine ⟨l0, g1, hrc, l3, pad_dispatch hτ ev e5 hz hzl hn e6 e7 e8, g9, g10,
    mulDiv_holds g11 (by rw [e10]; exact gen_pow_ne_zero _), hrc11, g15, g16,
    by rw [g16, ev, g15, w512]; exact tb_isInK_add (isInK_gpow' _) (isInK_gpow' _), trivial, fun h0 => ?_⟩
  -- not at the floor: τ = log2Ceil n
  have h9 : τ ≠ 9 := fun h => h0 (by rw [g16, ev, g15, w512, h, e_add_self])
  have hlog' : log2Ceil n = τ := by omega
  obtain ⟨hlr1, hlr2⟩ := (lead_rest_iff (by omega) hn).mpr hlog'
  have e19 : σ (.n (v + 19)) = PadRest τ n := by rw [b19, e8, b18, tb_word_zero, add_zero]
  refine ⟨b17, ?_, b18, b19, trivial, ?_⟩
  · show σ _ + σ _ = 0
    rw [e7, b17, tb_word_one, ← pwLead, hlr1, e_add_self]
  · show σ _ = σ _ * σ _ ∧ σ _ = 1
    refine ⟨b21, ?_⟩
    rw [b21, b20, mul_inv_cancel₀ (by rw [e19]; exact hlr2)]

end
end LeanVM.Guest.B1.Tables
