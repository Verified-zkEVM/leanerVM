/-
  LeanVM.Guest.B1.Terminal.Holds

  **`check_opening_terminal` is sound** (G:3078-3144; TRIAGE #70).
-/

module

public import LeanVM.Guest.B1.Terminal.Support
public import LeanVM.Guest.B1.Ring.Weight
public import LeanVM.Guest.B1.Eq.EqPrefix
public import LeanVM.Guest.B1.Eq.RsEqRun

/-!
# `check_opening_terminal`, assembled

The body is the template (`term_body`); its head gives the chains, the slot points, the public
input's chain and the selectors (`Terminal/Support`), its claims' blocks the sum of the claims'
terms (`claimsT_sound`), each its batched weight (`claimTerm_eq`), and its tail the outputs' claim
and the ring switch's; with `stackWeight_eq` the last check is the WHIR terminal.

The selectors' functions are B1-c's: `column_selector_Spec` and `selector_tables_Spec` are
hypotheses.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Verifier Finset

@[expose] public section

theorem claimsT_noRet : ∀ (js : List ℕ) (r acc : ℕ), Stmt.noRetList (claimsT js r acc).1 = true
  | [], _, _ => rfl
  | j :: js, r, acc => by
    simp only [claimsT, noRetList_append, claimsT_noRet js, Bool.and_true]
    unfold claimT
    split <;> rfl

theorem list_sum_range (f : ℕ → E) : ∀ n, ((List.range n).map f).sum = ∑ j ∈ range n, f j
  | 0 => rfl
  | n + 1 => by rw [List.range_succ, List.map_append, List.sum_append, list_sum_range f n,
      sum_range_succ]; simp

theorem getD_take_nat {l : List ℕ} {n k : ℕ} (h : k < n) : (l.take n).getD k 0 = l.getD k 0 := by
  simp [List.getD_eq_getElem?_getD, h]

/-- **`check_opening_terminal` is sound**, given B1-c's selectors. -/
theorem check_opening_terminal_holds (hcs : Tables.column_selector_Spec)
    (hst : Tables.selector_tables_Spec) (rd : Reader) : check_opening_terminal_Spec rd := by
  intro args rets h
  obtain ⟨σ, hpar, hb⟩ := (rel_iff_sem find_term args rets).mp h
  rw [show Data.core17.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9,
    .n 10, .n 11, .n 12, .n 13, .n 14, .n 15, .n 16, .n 17, .n 18] from rfl] at hpar
  simp only [List.map_cons, List.map_nil] at hpar
  subst hpar
  rw [show Fn.body Data.core17 = termT from term_body, termT, holdsList_append, holdsList_append,
    holdsList_append] at hb
  simp only [termHeadT, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil] at hb
  obtain ⟨-, e20, hcz, -, e22, hcr, e23, e24, -, -, -, l27, e28, l28, e29, e30, e31, -, hloop, e32,
    l33, hstc, hb⟩ := hb
  change Stmt.HoldsList _ rd σ ((List.range 113).map selBlockT).flatten _ _ at hb
  rw [holdsList_range_flatten 113 selBlockT (fun _ ↦ rfl)] at hb
  obtain ⟨hsels, hb⟩ := hb
  rw [holdsList_noRet _ (claimsT_noRet _ _ _)] at hb
  obtain ⟨hcl, hb⟩ := hb
  simp only [termTailT, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil] at hb
  obtain ⟨e1836, e1837, -, -, -, e1840, e1841, e1842, hco, e1843, e1844, e1845, e1846, hrw, e1848,
    l1849, e1850, e1851, e1852, e1853, e1854, afin, hret⟩ := hb
  refine ⟨hret.symm, ?_⟩
  intro layout bus claims out lam ringPoint coeffs x hpre
  simp only [TermPre] at hpre
  obtain ⟨hT, hPC, -, hP, hSL, hSL28, hlm1, -, hbus40, hHL, -, hglm, hgtau, hlamP, hlamO, hoc,
    hopl, hoz, hrpl, hrp, hcfl, hct, hxl, hpt, hpt1⟩ := hpre
  obtain ⟨chis, hzR, hgmu, hchR, hgzc, hchL, -, hcols, hpts⟩ := hT
  obtain ⟨hkap, hKr, hOr⟩ := hPC
  simp only [List.getD_cons_succ, List.getD_cons_zero]
  -- names
  set kappas := columnKappas layout.logMemory layout.logBytecode layout.tableLogHeights with hkdef
  set KC := Tables.committedKappas kappas with hKCdef
  set τ := layout.tableLogHeights.getD opKeccak 0 with hτ
  have hKClen : KC.length = 113 := Tables.committedKappas_length _ hkap
  have hLdef : layout.stackLog = max minStackedLog (stackOffsets KC).2 := by
    rw [hSL, placementsOf_snd]
  have hK : ∀ c < 113, KC.getD c 0 ≤ layout.stackLog := fun c hc ↦ by
    have := size_le_stackOffsets KC (i := c) (by omega); rw [hLdef]; omega
  have hO : ∀ c, (stackOffsets KC).1.getD c 0 < 2 ^ layout.stackLog := fun c ↦
    lt_of_lt_of_le (stackOffsets_lt KC c) (Nat.pow_le_pow_right (by decide) (by rw [hLdef]; omega))
  have hkv' : ∀ c < 113, LoadHolds rd (σ (.n 11)) c (gen ^ KC.getD c 0) := fun c hc ↦ by
    have := hKr c (by simp; omega)
    rw [List.getElem_map] at this
    rw [List.getD_eq_getElem _ _ (by omega)]; exact this
  have hoff' : ∀ c < 113, LoadHolds rd (σ (.n 10)) c (gen ^ (stackOffsets KC).1.getD c 0) :=
    fun c hc ↦ by
      have hl : c < (stackOffsets KC).1.length := by rw [stackOffsets_length]; omega
      have := hOr c (by simpa using hl)
      rw [List.getElem_map] at this
      rw [List.getD_eq_getElem _ _ hl]; exact this
  have hselc := fun c (hc : c < 113) ↦ sel_value hcs hst (hsels c hc) hstc (hoff' c hc) (hkv' c hc)
    (hK c hc) hSL28 (hO c) hxl hpt hpt1
  -- sizes
  have hk6 : kappas.take 6 = [layout.logMemory, layout.logMemory, layout.logMemory,
      layout.logMemory, layout.logBytecode, τ + 6] := kappas_small hHL
  have hksmall : ∀ c < 6, kappas.getD c 0 =
      [layout.logMemory, layout.logMemory, layout.logMemory, layout.logMemory, layout.logBytecode,
        τ + 6].getD c 0 := fun c hc ↦ by
    rw [← hk6, getD_take_nat hc]
  have hK5 : KC.getD 5 0 = τ + 6 := by
    rw [committedKappas_small hkap (by decide), hksmall 5 (by decide)]; rfl
  have hmem : ∀ c < 3, KC.getD c 0 = layout.logMemory := fun c hc ↦ by
    rw [committedKappas_small hkap (by omega), hksmall c (by omega)]
    interval_cases c <;> rfl
  have hK5L := hK 5 (by decide)
  rw [hK5] at hK5L
  have hxl40 : x.length ≤ termPointCap := by simp only [termPointCap]; omega
  have hpl40 : ((padPoint x).map (1 + ·)).length = termPointCap := by
    simp [padPoint_length hxl40]
  -- the chains
  rw [e20, word_one] at hcz
  rw [e22, word_one] at hcr
  have hzc := chain_value ((eq_prefix_chain_holds rd _ _).mp hcz) hgmu hbus40 hzR hxl40 hpt1
  have hrc := chain_value ((eq_prefix_chain_holds rd _ _).mp hcr) hgzc (by omega) hchR hxl40 hpt1
  -- the slot points
  have hs1 : ∀ k < 6, valOf rd (σ (.n 23)) k = x.getD (τ + k) 0 := fun k hk ↦ by
    have l := readsAt_getD hpt (k := τ + k) (by rw [padPoint_length hxl40]; simp only [termPointCap]; omega)
    rw [← loadHolds_mul_gen_pow, ← hgtau, ← e23] at l
    rw [valOf_eq l, padPoint_getD]
  have hs0 : ∀ k < 6, valOf rd (σ (.n 24)) k = 1 + x.getD (τ + k) 0 := fun k hk ↦ by
    have l := readsAt_getD hpt1 (k := τ + k) (by rw [hpl40]; simp only [termPointCap]; omega)
    rw [← loadHolds_mul_gen_pow, ← hgtau, ← e24] at l
    rw [valOf_eq l, x1_getD hxl40 (by simp only [termPointCap]; omega)]
  -- the public input's chain
  have hlmL : layout.logMemory ≤ layout.stackLog := by have := hK 0 (by decide); rw [hmem 0 (by decide)] at this; exact this
  have hstep : ∀ k, 1 ≤ k → k < layout.logMemory → PiStep rd (σ (.n 25)) (σ (.n 15)) (gen ^ k) := by
    intro k hk1 hk2
    have hne : σ (.n 30) ≠ 0 := by
      rw [e30, e29, word_gen, hglm]
      intro h0
      have := gen_pow_inj_le (a := 1) (b := layout.logMemory) (by omega) (by omega)
        (by rw [pow_one]; exact e_add_eq_zero_iff.mp h0)
      omega
    have hc : coreProgram.Rel rd "__loop15" (gen ^ 1 :: [σ (.n 5), σ (.n 25), σ (.n 15)]) [] := by
      rw [pow_one, ← word_gen, ← e31]; exact hloop hne
    exact loop_sound (P := coreProgram) (f := "__loop15") (ps := [σ (.n 5), σ (.n 25), σ (.n 15)])
      (N := σ (.n 5)) (B := PiStep rd (σ (.n 25)) (σ (.n 15))) (m := layout.logMemory)
      (fun d y h ↦ loop15_step d y _ _ _ h) hglm (by unfold ordG; omega) 1 hc k hk1 hk2
  have hx1_0 := loadHolds_unique l27 (readsAt_getD hpt1 (k := 0) (by rw [hpl40]; decide))
  have h1 : LoadHolds rd (σ (.n 25)) 1 (σ (.n 2) + ((padPoint x).map (1 + ·)).getD 0 0) := by
    rw [← hx1_0, ← e28]; exact l28
  have hpi := piChain_value hpt1 (m := layout.logMemory) (by rw [hpl40]; simp only [termPointCap]; omega)
    h1 hstep layout.logMemory hlm1 le_rfl
  rw [e32, hglm, loadHolds_mul_gen_pow, Nat.add_zero] at l33
  have h33 : σ (.n 33) = eqEval (σ (.n 2) :: List.replicate (layout.logMemory - 1) 0)
      (x.take layout.logMemory) := by
    rw [loadHolds_unique l33 hpi, x1_getD hxl40 (by decide), ← piChain_eq hlm1 (by omega)]
    refine congrArg (_ * ·) (prod_congr rfl fun i hi ↦ ?_)
    rw [x1_getD hxl40 (by have := (mem_Ico.mp hi).2; simp only [termPointCap]; omega)]
  -- the batching powers and the claims' points
  have hclen : claims.length = 165 := by
    rw [← List.length_map (f := (·.column)), hcols, claimColumns_eq]; simp
  have hlam : ∀ j < 165, termKind j ≠ 4 → valOf rd (σ (.n 9)) j = lam ^ (1 + poolRank j) :=
    fun j hj hk ↦ valOf_eq (hlamP j hj (fun hm ↦ hk (by
      have := (claimCol_out hj).mp hm; unfold termKind; split_ifs <;> omega)))
  have hptj : ∀ j < 165, (claims.map (·.point))[j]? = some (claims.getD j default).point :=
    fun j hj ↦ by
      rw [List.getElem?_map, List.getElem?_eq_getElem (by omega), List.getD_eq_getElem _ _ (by omega)]
      rfl
  let cp : ℕ → ℕ := fun j ↦ (claims.getD j default).point.length
  have hCp : ∀ j ∈ List.range 165, CpAt rd σ cp j := fun j hj hk v hv ↦ by
    have hj' := List.mem_range.mp hj
    have hj2 : j < 162 := by unfold termKind at hk; split_ifs at hk <;> omega
    exact loadHolds_unique hv ((hpts j _ (hptj j hj')).1 hj2)
  obtain ⟨hsum, hoks, -⟩ := claimsT_sound (C := coreProgram.Rel rd) (cp := cp) (List.range 165) 375 16
    hCp hcl
  rw [show (claimsT (List.range 165) 375 16).2.2 = 1835 by rw [claimsT_end]] at hsum
  have hmem0 : (layout.placement memory0).vars = layout.logMemory := by
    have := placement_committed hkap hP (cc := 0) (by decide)
    rw [committedCols_getD (by decide)] at this
    rw [show memory0 = 0 from rfl, show (if 0 < 86 then 0 else 0 + 50) = 0 from rfl] at *
    rw [this, hmem 0 (by decide)]
  have T : TermCtx rd σ layout kappas claims bus.point chis x lam (σ (.n 2)) cp :=
    { hkap := hkap, hP := hP, hx := hxl, hL := hSL28, hK := hK, hq := (hselc 5 (by decide)).2,
      hK5 := hK5, hlane := fun g h1 h2 ↦ kappas_keccak hHL (by omega) (by omega), hmem := hmem,
      hlm := hlm1, hmem0 := hmem0, hcols := hcols, hzs := hbus40, hchis := hchL,
      hpz := fun j hj ↦ (hpts j _ (hptj j (by omega))).2.1 hj,
      hpc := fun j h1 h2 ↦ (hpts j _ (hptj j (by omega))).2.2.1 h1 h2,
      hpp := fun j h1 h2 ↦ (hpts j _ (hptj j h2)).2.2.2 h1,
      hcp := fun _ _ ↦ rfl, hlam := hlam, hsel := fun c hc ↦ (hselc c hc).1,
      hzc := fun n h1 h2 ↦ hzc n h1 (by rw [hxl]; exact h2),
      hrc := fun n h1 h2 ↦ hrc n h1 (by rw [hxl]; exact h2),
      hs1 := hs1, hs0 := hs0, h33 := h33, hok := fun j hj ↦ hoks j (List.mem_range.mpr hj),
      hkv := fun c hc ↦ valOf_eq (hkv' c hc) }
  -- the tail: the outputs' claim and the ring switch's
  have hq5 := placement_committed hkap hP (cc := 5) (by decide)
  rw [committedCols_getD (by decide), show (if 5 < 86 then 5 else 5 + 50) = 5 from rfl] at hq5
  have hw64 : word 64 0 0 = gen ^ 6 := word_two_pow (a := 6) (by decide)
  have h1842 : σ (.n 1842) = gen ^ out.point.length := by
    rw [e1842, e1841, hw64, hgtau, ← pow_add, hopl, Tables.qkeccakSlotBits_eq]
  rw [e1840, word_one, h1842] at hco
  have hoL : out.point.length = τ + 6 := by rw [hopl, Tables.qkeccakSlotBits_eq]
  have hoc' := chain_value ((eq_prefix_chain_holds rd _ _).mp hco) rfl (by omega) hoz hxl40 hpt1
  rw [e1848, hgtau, loadHolds_mul_gen_pow] at l1849
  have h1849 : σ (.n 1849) = eqEval out.point (x.take (τ + 6)) := by
    rw [eq_valOf l1849, show τ + 6 = out.point.length from hoL.symm, hoc' _ le_rfl (by omega),
      List.take_of_length_le le_rfl]
  obtain ⟨n, hn, hng, rs, ps, cs, hrsl, hpsl, hcsl, hrsR, hpsR, hcsR, hret'⟩ :=
    ring_switch_weight_holds rs_eq_run_holds rd _ _ hrw
  have hn6 : n = τ + 6 := by
    rw [e1846, e1845, hw64, hgtau, ← pow_add] at hng
    exact gen_pow_inj_le (by omega) (by omega) hng.symm
  subst hn6
  rw [e1844, e1843, show (549755813888 : ℕ) = 2 ^ 39 from rfl, word_two_pow (by decide)] at hrsR
  have hrs : rs = ringPoint :=
    readsAt_unique hrsR hrp (by rw [hrsl, hrpl, Tables.qkeccakSlotBits_eq])
  have hps : ps = ((padPoint x).map (1 + ·)).take (τ + 6) :=
    readsAt_unique hpsR (readsAt_take hpt1 _) (by rw [hpsl, List.length_take, hpl40]; simp only [termPointCap]; omega)
  have hcs : cs = coeffs := readsAt_unique hcsR hct (by rw [hcsl, hcfl])
  simp only [List.cons.injEq, and_true] at hret'
  rw [hrs, hps, hcs, map_one_take (by omega)] at hret'
  -- the terminal check
  have hfin : σ (.n 1854) = σ (.n 18) := e_add_eq_zero_iff.mp afin
  rw [stackWeight_eq layout out ringPoint coeffs lam x hcols, ← hfin, e1854, e1853, hsum, e1852,
    e1851, e1850, hret', h1849, hlamO, list_sum_range,
    sum_congr rfl fun j hj ↦ claimTerm_eq T (mem_range.mp hj),
    ringClaim_eq (show layout.placement qkeccak = _ from hq5) hxl,
    wOf_committed (by rw [hoc]; exact hq5) (by rw [hoL, hK5]) hxl (hK 5 (by decide)),
    (hselc 5 (by decide)).1, hK5]
  ring

end
end LeanVM.Guest.B1.VerifySub
