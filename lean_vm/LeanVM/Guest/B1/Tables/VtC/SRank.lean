/-
  LeanVM.Guest.B1.Tables.VtC.SRank

  A rank of the certified block order (`vtRank0T`, `vtRankT`) holds on the honest valuation: its
  block read from `sort_order`, of the side, of log-size `κ`, its offset cell holding the running
  offset.
-/

module

public import LeanVM.Guest.B1.Tables.VtC.SBase

/-!
# A rank (G:1967-1986)

`rank0_ok`, `rank_ok`: from the template's equations (`GoodL`), its reads not stores, a memory
holding the rank's block `g^e` in `sort_order`, its side, `g^κ` in `block_kappa`, the running
offset `g^P` in its `block_off_g` cell and `g^(2^κ)` in `g_squares`, the previous rank's `g^κp`
(`κ ≤ κp`) and `g^ep` (`ep < e` on a tie), every statement holds, the rank's values are `g^e`,
`g^κ` and the next running offset `g^(P + 2^κ)`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd

@[expose] public section

variable {C : CallRel} {rd : Reader} {w : ℕ → E} {σ : Val}

/-- The tie branch of a later rank. -/
def vtTieB (v pc : ℕ) : List Stmt :=
  [.atom (.const (.n (v + 16)) vtW152), .atom (.mul (.n v) (.n (v + 17)) (.n pc)),
    .atom (.rangeCheck (.n (v + 17)) (.n (v + 18)) (.n (v + 19)) (.n (v + 20)) (.n (v + 16)))]

/-- A rank's reads. -/
def vtRankReads (v R : ℕ) : List Atom :=
  [.load (.n v) (.n 30) R, .load (.n (v + 6)) (.n (v + 5)) 0, .load (.n (v + 9)) (.n (v + 8)) 0]

theorem gen_pow_add_ne {a b : ℕ} (ha : a < 34) (hb : b < 34) (h : a ≠ b) : gen ^ a + gen ^ b ≠ 0 :=
  fun h0 => h (gen_pow_inj (by omega) (by omega) (e_add_eq_zero_iff.mp h0))

set_option maxHeartbeats 1000000 in
/-- **The side's first rank.** -/
theorem rank0_ok (hlow : LowDefB 8 rd) {v R s e κ : ℕ} (hv : 186 ≤ v)
    (hg : GoodL rd w σ (vtRank0T v R s))
    (hS : ∀ a ∈ vtRankReads v R ++ [.load (.n (v + 13)) (.n (v + 12)) 0], a ∉ vtSL)
    (hso : LoadHolds rd (σ (.n 30)) R (gen ^ e))
    (hside : LoadHolds rd (σ (.n 31) * gen ^ e) 0 (word s 0 0))
    (hkap : LoadHolds rd (σ (.n 12) * gen ^ e) 0 (gen ^ κ))
    (hoff : LoadHolds rd (σ (.n 185) * gen ^ e) 0 1)
    (hsq : LoadHolds rd (σ (.n 13) * gen ^ κ) 0 (gen ^ 2 ^ κ)) (he : e < 153) :
    (∀ st ∈ vtRank0T v R s, VSH C rd σ st) ∧ σ (.n v) = gen ^ e ∧ σ (.n (v + 9)) = gen ^ κ ∧
      σ (.n (v + 13)) = gen ^ 2 ^ κ := by
  simp only [vtRankReads, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp, forall_eq] at hS
  obtain ⟨s0, s6, s9, s13⟩ := hS
  simp only [vtRank0T, GoodL, GoodS, fixNe, Good, and_true] at hg
  obtain ⟨g0, g1, g2, g3, g4, g5, -, g7, g8, g9, g10, -, g12, g13⟩ := hg
  simp only [show (31 : ℕ) < v + 5 ∧ v < v + 5 from ⟨by omega, by omega⟩,
    show (12 : ℕ) < v + 8 ∧ v < v + 8 from ⟨by omega, by omega⟩,
    show (185 : ℕ) < v + 11 ∧ v < v + 11 from ⟨by omega, by omega⟩,
    show (13 : ℕ) < v + 12 ∧ v + 9 < v + 12 from ⟨by omega, by omega⟩,
    show v + 1 < v + 2 by omega, ↓reduceIte] at g3 g7 g10 g12 g2
  obtain ⟨r1, r2, r3⟩ := g2
  obtain ⟨ev, l0⟩ := read_of (g0.resolve_left s0) hso
  obtain ⟨hrc, -⟩ := rc_holds (κ := 8) hlow r1 r2 r3 ev (by rw [g1, vtW152_gen]) (by omega)
    (by norm_num)
  have m5 : σ (.n (v + 5)) = σ (.n 31) * gen ^ e := by rw [g3, ev]
  obtain ⟨e6, l4⟩ := read_of (g4.resolve_left s6) (by rw [m5]; exact hside)
  have m8 : σ (.n (v + 8)) = σ (.n 12) * gen ^ e := by rw [g7, ev]
  obtain ⟨e9, l8⟩ := read_of (g8.resolve_left s9) (by rw [m8]; exact hkap)
  have m11 : σ (.n (v + 11)) = σ (.n 185) * gen ^ e := by rw [g10, ev]
  have m12 : σ (.n (v + 12)) = σ (.n 13) * gen ^ κ := by rw [g12, e9]
  obtain ⟨e13, l13⟩ := read_of (g13.resolve_left s13) (by rw [m12]; exact hsq)
  refine ⟨?_, ev, e9, e13⟩
  simp only [vtRank0T, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true, and_true, vsh_atom]
  refine ⟨l0, g1, hrc, g3, l4, g5, ?_, g7, l8, g9, g10, ?_, g12, l13⟩
  · show σ _ + σ _ = 0
    rw [e6, g5, e_add_self]
  · show LoadHolds rd _ _ _
    rw [m11, g9, tb_word_one]; exact hoff

set_option maxHeartbeats 1000000 in
/-- **A later rank.** -/
theorem rank_ok (hlow : LowDefB 8 rd) {v R s pk pc gin e κ κp ep P : ℕ} (hv : 186 ≤ v)
    (hpk : pk < v) (hgin : gin < v)
    (hg : GoodL rd w σ (vtRankT v R s pk pc gin)) (hgb : GoodL rd w σ (vtTieB v pc))
    (hS : ∀ a ∈ vtRankReads v R ++ [.load (.n (v + 23)) (.n (v + 22)) 0], a ∉ vtSL)
    (hso : LoadHolds rd (σ (.n 30)) R (gen ^ e))
    (hside : LoadHolds rd (σ (.n 31) * gen ^ e) 0 (word s 0 0))
    (hkap : LoadHolds rd (σ (.n 12) * gen ^ e) 0 (gen ^ κ))
    (hoff : LoadHolds rd (σ (.n 185) * gen ^ e) 0 (gen ^ P))
    (hsq : LoadHolds rd (σ (.n 13) * gen ^ κ) 0 (gen ^ 2 ^ κ))
    (hpkv : σ (.n pk) = gen ^ κp) (hpcv : σ (.n pc) = gen ^ ep) (hginv : σ (.n gin) = gen ^ P)
    (he : e < 153) (hκ : κ < 34) (hκp : κp < 34) (hle : κ ≤ κp) (htie : κ = κp → ep < e) :
    (∀ st ∈ vtRankT v R s pk pc gin, VSH C rd σ st) ∧ σ (.n v) = gen ^ e ∧
      σ (.n (v + 9)) = gen ^ κ ∧ σ (.n (v + 24)) = gen ^ (P + 2 ^ κ) := by
  simp only [vtRankReads, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp, forall_eq] at hS
  obtain ⟨s0, s6, s9, s23⟩ := hS
  simp only [vtRankT, GoodL, GoodS, fixNe, Good, and_true] at hg
  obtain ⟨g0, g1, g2, g3, g4, g5, -, g7, g8, g9, g10, g11, g12, -, g14, -, g16, g17, g18⟩ := hg
  simp only [vtTieB, GoodL, GoodS, fixNe, Good, and_true] at hgb
  obtain ⟨b0, b1, b2⟩ := hgb
  simp only [show (31 : ℕ) < v + 5 ∧ v < v + 5 from ⟨by omega, by omega⟩,
    show (12 : ℕ) < v + 8 ∧ v < v + 8 from ⟨by omega, by omega⟩,
    show ¬ (v + 11 < pk ∧ v + 9 < pk) from fun h => by omega,
    show (185 : ℕ) < v + 21 ∧ v < v + 21 from ⟨by omega, by omega⟩,
    show (13 : ℕ) < v + 22 ∧ v + 9 < v + 22 from ⟨by omega, by omega⟩,
    show gin < v + 24 ∧ v + 23 < v + 24 from ⟨by omega, by omega⟩,
    show ¬ (v + 17 < v ∧ pc < v) from fun h => by omega,
    show v + 1 < v + 2 by omega, show v + 10 < v + 12 by omega, show v + 16 < v + 18 by omega,
    ↓reduceIte] at g3 g7 g10 g14 g16 g18 b1 g2 g11 b2
  obtain ⟨r1, r2, r3⟩ := g2
  obtain ⟨ev, l0⟩ := read_of (g0.resolve_left s0) hso
  obtain ⟨hrc, -⟩ := rc_holds (κ := 8) hlow r1 r2 r3 ev (by rw [g1, vtW152_gen]) (by omega)
    (by norm_num)
  have m5 : σ (.n (v + 5)) = σ (.n 31) * gen ^ e := by rw [g3, ev]
  obtain ⟨e6, l4⟩ := read_of (g4.resolve_left s6) (by rw [m5]; exact hside)
  have m8 : σ (.n (v + 8)) = σ (.n 12) * gen ^ e := by rw [g7, ev]
  obtain ⟨e9, l8⟩ := read_of (g8.resolve_left s9) (by rw [m8]; exact hkap)
  have e11 : σ (.n (v + 11)) = gen ^ (κp - κ) := by rw [g10, hpkv, e9, gen_pow_div hle]
  obtain ⟨q1, q2, q3⟩ := g11
  obtain ⟨hrc11, -⟩ := rc_holds (κ := 8) hlow q1 q2 q3 e11 (by rw [g9, vtW33_gen]) (by omega)
    (by norm_num)
  have m21 : σ (.n (v + 21)) = σ (.n 185) * gen ^ e := by rw [g14, ev]
  have m22 : σ (.n (v + 22)) = σ (.n 13) * gen ^ κ := by rw [g16, e9]
  obtain ⟨e23, l17⟩ := read_of (g17.resolve_left s23) (by rw [m22]; exact hsq)
  refine ⟨?_, ev, e9, by rw [g18, hginv, e23, ← pow_add]⟩
  simp only [vtRankT, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true, and_true, vsh_atom, vsh_ite]
  refine ⟨l0, g1, hrc, g3, l4, g5, ?_, g7, l8, g9, ?_, hrc11, g12, ⟨?_, fun h0 => ?_⟩, g14,
    ?_, g16, l17, g18⟩
  · show σ _ + σ _ = 0
    rw [e6, g5, e_add_self]
  · exact mulDiv_holds g10 (by rw [e9]; exact gen_pow_ne_zero _)
  · rw [g12, hpkv, e9]; exact tb_isInK_add (isInK_gpow' _) (isInK_gpow' _)
  · have hk : κp = κ := by
      rw [g12, hpkv, e9] at h0
      exact gen_pow_inj (by omega) (by omega) (e_add_eq_zero_iff.mp h0)
    have hlt := htie hk.symm
    have e17 : σ (.n (v + 17)) = gen ^ (e - ep) := by rw [b1, ev, hpcv, gen_pow_div hlt.le]
    obtain ⟨r1', r2', r3'⟩ := b2
    obtain ⟨hrc17, -⟩ := rc_holds (κ := 8) hlow r1' r2' r3' e17 (by rw [b0, vtW152_gen])
      (by omega) (by norm_num)
    exact ⟨b0, mulDiv_holds (rd := rd) b1 (by rw [hpcv]; exact gen_pow_ne_zero _), hrc17⟩
  · show LoadHolds rd _ _ _
    rw [m21, hginv]; exact hoff

end
end LeanVM.Guest.B1.Tables
