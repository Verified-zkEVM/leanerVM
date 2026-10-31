/-
  LeanVM.Guest.B1.Terminal.TermEval

  `check_opening_terminal`'s head, selectors and tail on their evaluated valuation: every
  statement holds, every load lies in a region, and the values the terminal's check uses.
-/

module

public import LeanVM.Guest.B1.Terminal.ClaimsComplete
public import LeanVM.Guest.B1.Terminal.TermKids

/-!
# The head, the selectors and the tail, evaluated

The oracle `termW b0 outs`: the buffers at `b0`, `b0 + 35`, `b0 + 70`, `b0 + 105`, and the callees'
results `outs` (`selector_tables`' at `34`, `35`, column `c`'s selector at `selV c`, the ring
switch's weight at `2001`). On a valuation satisfying the evaluator's equations (`GoodS`):
`head_complete`, `sel_complete`, `tail_complete`, as `zrT_complete` for the claims.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol.Verifier hiding gpow
open LeanVM.Guest.Memory LeanVM.Guest.B1.Fwd
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

/-- The trivial call relation (the callees' relations come from their placement). -/
abbrev TrivC : CallRel := fun _ _ _ => True

/-- **The oracle of `check_opening_terminal`'s evaluation**: its buffers, its callees' results. -/
noncomputable def termW (b0 : ℕ) (outs : List (List E × Main.Layout)) : ℕ → E := fun i =>
  if i = 19 then ofK (gpow b0) else if i = 21 then ofK (gpow (b0 + 35)) else
  if i = 25 then ofK (gpow (b0 + 70)) else if i = 1993 then ofK (gpow (b0 + 105)) else
  if i = 34 then (stRes outs).1.getD 0 0 else if i = 35 then (stRes outs).1.getD 1 0 else
  if i = 2001 then (outs.getD 104 ([], [])).1.getD 0 0 else
  (outs.getD (4 + (i - 38) / 3) ([], [])).1.getD 0 0

theorem termW_sel (b0 : ℕ) (outs : List (List E × Main.Layout)) {c : ℕ} (hc : c < 99) :
    termW b0 outs (selV c) = (outs.getD (4 + c) ([], [])).1.getD 0 0 := by
  have e : (38 + 3 * c - 38) / 3 = c := by omega
  simp only [termW, selV, e]
  rw [ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega),
    ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega)]

variable {rd : Reader} {S : List Atom} {σ : Val} {R : ℕ → Prop}

theorem good_hint_alloc {w : ℕ → E} {d n : ℕ} (h : GoodS rd S w σ (.atom (.hint (.alloc (.n d) n)))) :
    σ (.n d) = w d := h

theorem good_rets {w : ℕ → E} {s : Stmt} (h : GoodS rd S w σ s) :
    match s with
    | .call _ _ rets | .dispatch _ _ _ rets => ∀ v ∈ rets, σ v = w v.idx
    | _ => True := by
  cases s <;> first | exact h | trivial

/-! ## The head -/

/-- **The head, completely**: the chains' buffers, the slot points, the public input's chain (its
first two words stored, its loop, its value at `g^m`), the selector tables. -/
theorem head_complete (hS : StoresAt25 S) {b0 : ℕ} {outs : List (List E × Main.Layout)}
    (hg : ∀ s ∈ termHeadT, GoodS rd S (termW b0 outs) σ s) {m : ℕ} {rm : E} {ps : List E}
    (hm1 : 1 ≤ m) (e5 : σ (.n 5) = gen ^ m) (e2 : σ (.n 2) = rm)
    (h15 : LoadHolds rd (σ (.n 15)) 0 (ps.getD 0 0)) (a15 : AddrIn R (σ (.n 15)) 0)
    (hpi : ReadsAt rd (ofK (gpow (b0 + 70))) (piW rm ps m)) (api : ∀ k ≤ m, R (b0 + 70 + k)) :
    (∀ s ∈ termHeadT, Fwd.SHolds TrivC rd σ s) ∧
      (∀ q ∈ termHeadT.filterMap Stmt.loadS, AddrIn R (σ q.1) q.2) ∧
      σ (.n 19) = ofK (gpow b0) ∧ σ (.n 20) = word 1 0 0 ∧ σ (.n 21) = ofK (gpow (b0 + 35)) ∧
      σ (.n 22) = word 1 0 0 ∧ σ (.n 23) = σ (.n 14) * σ (.n 6) ∧
      σ (.n 24) = σ (.n 15) * σ (.n 6) ∧ σ (.n 25) = ofK (gpow (b0 + 70)) ∧
      σ (.n 30) = word 2 0 0 + gen ^ m ∧ σ (.n 31) = word 2 0 0 ∧
      σ (.n 33) = (piW rm ps m).getD m 0 ∧ σ (.n 34) = (stRes outs).1.getD 0 0 ∧
      σ (.n 35) = (stRes outs).1.getD 1 0 := by
  have mm : ∀ s, s ∈ termHeadT → GoodS rd S (termW b0 outs) σ s := hg
  simp only [termHeadT, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at mm
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18,
    g19, g20⟩ := mm
  have e19 : σ (.n 19) = ofK (gpow b0) := by rw [good_hint_alloc g0]; simp [termW]
  have e20 := good_const g1
  have e21 : σ (.n 21) = ofK (gpow (b0 + 35)) := by rw [good_hint_alloc g3]; simp [termW]
  have e22 := good_const g4
  have e23 := good_mul g6 (by omega) (by omega)
  have e24 := good_mul g7 (by omega) (by omega)
  have e25 : σ (.n 25) = ofK (gpow (b0 + 70)) := by rw [good_hint_alloc g8]; simp [termW]
  have e26 := good_const g9
  obtain ⟨e27, l27⟩ := good_load_eq hS (n_ne_25 (by decide)) g11 h15
  have e28 := good_add g12
  have e29 := good_const g14
  have e30 := good_add g15
  have e31 := good_const g16
  have e32 := good_mul g18 (by omega) (by omega)
  have hpk : ∀ k ≤ m, LoadHolds rd (ofK (gpow (b0 + 70))) k ((piW rm ps m).getD k 0) := fun k hk => by
    rw [List.getD_eq_getElem _ _ (by rw [piW_length]; omega)]
    exact hpi k (by rw [piW_length]; omega)
  have h32 : LoadHolds rd (σ (.n 32)) 0 ((piW rm ps m).getD m 0) := by
    rw [e32, e25, e5, loadHolds_mul_gen_pow, Nat.add_zero]; exact hpk m le_rfl
  obtain ⟨e33, l33⟩ := good_load_eq hS (n_ne_25 (by decide)) g19 h32
  have r20 := good_rets g20
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at r20
  have e34 : σ (.n 34) = (stRes outs).1.getD 0 0 := by rw [r20.1]; simp [termW]
  have e35 : σ (.n 35) = (stRes outs).1.getD 1 0 := by rw [r20.2]; simp [termW]
  have s0 : LoadHolds rd (σ (.n 25)) 0 (σ (.n 26)) := by
    rw [e25, e26, word_one]
    have := hpk 0 (by omega)
    rwa [piW_getD (by omega), ite_pos' rfl] at this
  have s1 : LoadHolds rd (σ (.n 25)) 1 (σ (.n 28)) := by
    rw [e25, e28, e27, e2]
    have := hpk 1 hm1
    rwa [piW_getD hm1, ite_neg' (by omega), Finset.Ico_self, Finset.prod_empty, mul_one] at this
  have a25 : ∀ k ≤ m, AddrIn R (σ (.n 25)) k := fun k hk =>
    ⟨b0 + 70 + k, by rw [e25, Main.addr_ofK], api k hk⟩
  have hw2 : word 2 0 0 = gen := word_gen
  refine ⟨fun s hs => ?_, fun q hq => ?_, e19, e20, e21, e22, e23, e24, e25,
    by rw [e30, e29, e5], e31, e33, e34, e35⟩
  · simp only [termHeadT, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · trivial
    · exact e20
    · trivial
    · trivial
    · exact e22
    · trivial
    · exact e23
    · exact e24
    · trivial
    · exact e26
    · exact s0
    · exact l27
    · exact e28
    · exact s1
    · exact e29
    · exact e30
    · exact e31
    · refine ⟨?_, fun _ => trivial⟩
      rw [e30, e29, e5, hw2]
      exact isInK_add (by simpa using gen_pow_isInK 1) (gen_pow_isInK m)
    · exact e32
    · exact l33
    · trivial
  · simp only [termHeadT, List.filterMap_cons, Stmt.loadS, List.filterMap_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact a25 0 (by omega)
    · exact a15
    · exact a25 1 hm1
    · refine ⟨b0 + 70 + m, ?_, api m le_rfl⟩
      show (σ (.n 32)).limb 0 * gpow 0 = _
      rw [e32, e25, e5, ofK_gpow_mul_gen, Main.addr_ofK, Nat.add_zero]

/-! ## The selectors -/

/-- **Committed column `c`'s selector block, completely.** -/
theorem sel_complete (hS : StoresAt25 S) {b0 : ℕ} {outs : List (List E × Main.Layout)} {c : ℕ}
    (hc : c < 99) (hg : ∀ s ∈ selBlockT c, GoodS rd S (termW b0 outs) σ s) {o κ : ℕ} (hκ : κ < 29)
    (hoff : LoadHolds rd (σ (.n 10)) c (gen ^ o)) (aoff : AddrIn R (σ (.n 10)) c)
    (hkap : LoadHolds rd (σ (.n 11)) c (gen ^ κ)) (akap : AddrIn R (σ (.n 11)) c) :
    (∀ s ∈ selBlockT c, Fwd.SHolds TrivC rd σ s) ∧ (∀ s ∈ selBlockT c, DispOk σ s) ∧
      (∀ q ∈ (selBlockT c).filterMap Stmt.loadS, AddrIn R (σ q.1) q.2) ∧
      σ (.n (36 + 3 * c)) = gen ^ o ∧ σ (.n (37 + 3 * c)) = gen ^ κ ∧
      σ (.n (selV c)) = (outs.getD (4 + c) ([], [])).1.getD 0 0 := by
  have mm : ∀ s, s ∈ selBlockT c → GoodS rd S (termW b0 outs) σ s := hg
  simp only [selBlockT, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at mm
  obtain ⟨g0, g1, g2⟩ := mm
  obtain ⟨e0, l0⟩ := good_load_eq hS (n_ne_25 (by decide)) g0 hoff
  obtain ⟨e1, l1⟩ := good_load_eq hS (n_ne_25 (by decide)) g1 hkap
  have r2 := good_rets g2
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq] at r2
  have e2 : σ (.n (selV c)) = (outs.getD (4 + c) ([], [])).1.getD 0 0 := by
    rw [r2]; exact termW_sel b0 outs hc
  have hl : colSelNames.length = 29 := by simp [colSelNames]
  have hd : σ (.n (37 + 3 * c)) = ofK (gpow κ) := by rw [e1, gen_pow_eq_ofK]
  refine ⟨fun s hs => ?_, fun s hs => ?_, fun q hq => ?_, e0, e1, e2⟩
  · simp only [selBlockT, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl
    · exact l0
    · exact l1
    · exact ⟨κ, by omega, hd, trivial⟩
  · simp only [selBlockT, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl
    · trivial
    · trivial
    · exact ⟨κ, by omega, by omega, hd⟩
  · simp only [selBlockT, List.filterMap_cons, Stmt.loadS, List.filterMap_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact aoff
    · exact akap

/-! ## The tail -/

theorem termTailPre_eq : termTailPre =
    [.atom (.const (.n 1990) (word 64 0 0)), .atom (.mul (.n 1991) (.n 6) (.n 1990)),
      .atom (.load (.n 1992) (.n 11) 5), .atom (.assertEq (.n 1991) (.n 1992)),
      .atom (.hint (.alloc (.n 1993) 41)), .atom (.const (.n 1994) (word 1 0 0)),
      .atom (.const (.n 1995) (word 64 0 0)), .atom (.mul (.n 1996) (.n 6) (.n 1995)),
      .call "eq_prefix_chain" [.n 1993, .n 1994, .n 12, .n 15, .n 1996] [],
      .atom (.const (.n 1997) (word 549755813888 0 0)), .atom (.mul (.n 1998) (.n 12) (.n 1997)),
      .atom (.const (.n 1999) (word 64 0 0)), .atom (.mul (.n 2000) (.n 6) (.n 1999)),
      .call "ring_switch_weight" [.n 1998, .n 15, .n 13, .n 2000] [.n 2001],
      .atom (.mul (.n 2002) (.n 1993) (.n 6)), .atom (.load (.n 2003) (.n 2002) 6),
      .atom (.mul (.n 2004) (.n 8) (.n 2003)), .atom (.add (.n 2005) (.n 2001) (.n 2004)),
      .atom (.mul (.n 2006) (.n 2005) (.n 53)), .atom (.add (.n 2007) (.n 1989) (.n 2006)),
      .atom (.mul (.n 2008) (.n 2007) (.n 17)), .atom (.assertEq (.n 2008) (.n 18))] := rfl

/-- **The tail, completely**: the outputs' chain, the ring switch's weight, the terminal's
check (given its value). -/
theorem tail_complete (hS : StoresAt25 S) {b0 : ℕ} {outs : List (List E × Main.Layout)}
    (hg : ∀ s ∈ termTailPre, GoodS rd S (termW b0 outs) σ s) {τ : ℕ} {v : E}
    (e6 : σ (.n 6) = gen ^ τ) (hkap : LoadHolds rd (σ (.n 11)) 5 (gen ^ (τ + 6)))
    (akap : AddrIn R (σ (.n 11)) 5)
    (hch : LoadHolds rd (ofK (gpow (b0 + 105))) (τ + 6) v) (ach : R (b0 + 105 + (τ + 6))) :
    (σ (.n 2008) = σ (.n 18) → ∀ s ∈ termTailPre, Fwd.SHolds TrivC rd σ s) ∧
      (∀ q ∈ termTailPre.filterMap Stmt.loadS, AddrIn R (σ q.1) q.2) ∧
      σ (.n 1993) = ofK (gpow (b0 + 105)) ∧ σ (.n 1994) = word 1 0 0 ∧
      σ (.n 1996) = gen ^ τ * word 64 0 0 ∧ σ (.n 1998) = σ (.n 12) * word 549755813888 0 0 ∧
      σ (.n 2000) = gen ^ τ * word 64 0 0 ∧ σ (.n 2001) = (outs.getD 104 ([], [])).1.getD 0 0 ∧
      σ (.n 2003) = v ∧
      σ (.n 2008) = (σ (.n 1989) + (σ (.n 2001) + σ (.n 8) * σ (.n 2003)) * σ (.n 53)) *
        σ (.n 17) := by
  have mm : ∀ s, s ∈ termTailPre → GoodS rd S (termW b0 outs) σ s := hg
  simp only [termTailPre_eq, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at mm
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18,
    g19, g20, g21⟩ := mm
  have hw64 : word 64 0 0 = gen ^ 6 := word_two_pow (a := 6) (by decide)
  have e0 := good_const g0
  have e1 := good_mul g1 (by omega) (by omega)
  obtain ⟨e2, l2⟩ := good_load_eq hS (n_ne_25 (by decide)) g2 hkap
  have e4 : σ (.n 1993) = ofK (gpow (b0 + 105)) := by rw [good_hint_alloc g4]; simp [termW]
  have e5 := good_const g5
  have e6' := good_const g6
  have e7 := good_mul g7 (by omega) (by omega)
  have e9 := good_const g9
  have e10 := good_mul g10 (by omega) (by omega)
  have e11 := good_const g11
  have e12 := good_mul g12 (by omega) (by omega)
  have r13 := good_rets g13
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq] at r13
  have e13 : σ (.n 2001) = (outs.getD 104 ([], [])).1.getD 0 0 := by rw [r13]; simp [termW]
  have e14 := good_mul g14 (by omega) (by omega)
  have h14 : LoadHolds rd (σ (.n 2002)) 6 v := by
    rw [e14, e4, e6, loadHolds_mul_gen_pow]; exact hch
  obtain ⟨e15, l15⟩ := good_load_eq hS (n_ne_25 (by decide)) g15 h14
  have e16 := good_mul g16 (by omega) (by omega)
  have e17 := good_add g17
  have e18 := good_mul g18 (by omega) (by omega)
  have e19 := good_add g19
  have e20 := good_mul g20 (by omega) (by omega)
  refine ⟨fun hfin s hs => ?_, fun q hq => ?_, e4, e5, by rw [e7, e6', e6], by rw [e10, e9],
    by rw [e12, e11, e6], e13, e15, by rw [e20, e19, e18, e17, e16]⟩
  · simp only [termTailPre_eq, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact e0
    · exact e1
    · exact l2
    · show σ (.n 1991) + σ (.n 1992) = 0
      rw [e1, e0, e6, e2, hw64, ← pow_add]; exact e_add_self _
    · trivial
    · exact e5
    · exact e6'
    · exact e7
    · trivial
    · exact e9
    · exact e10
    · exact e11
    · exact e12
    · trivial
    · exact e14
    · exact l15
    · exact e16
    · exact e17
    · exact e18
    · exact e19
    · exact e20
    · show σ (.n 2008) + σ (.n 18) = 0
      rw [hfin]; exact e_add_self _
  · simp only [termTailPre_eq, List.filterMap_cons, Stmt.loadS, List.filterMap_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact akap
    · refine ⟨b0 + 105 + (τ + 6), ?_, ach⟩
      show (σ (.n 2002)).limb 0 * gpow 6 = _
      rw [e14, e4, e6, ofK_gpow_mul_gen, Main.addr_ofK, Nat.add_assoc]

end
end LeanVM.Guest.B1.VerifySub
