/-
  LeanVM.Guest.B1.Comp.Tables.GkrLoadsC

  `verify_bus_gkr`'s loops' valid trees under any semantics load the stream words they read.
-/

module

public import LeanVM.Guest.B1.Comp.Tables.LoadsL
public import LeanVM.Guest.B1.Comp.Tables.GkrAtC
public import LeanVM.Guest.B1.Tables.GkrLoops
public import LeanVM.Guest.B1.Tables.GkrLayer

/-!
# GKR's loops, loading what they read

GKR reads the stream at `g^c`: pair `j`'s rounds (four words each, at `gCur j + 4r`) are read by
`sumcheck_round5` (`sr5_loads`), called once per round by `__loop101` (`l101_loads`), which
`__loop10` calls at pair `j`; pair `j`'s twelve children words, past its rounds, are read by
`__loop10`'s path (`l10_loads`). Each over every valid tree under any semantics, on a memory holding
the stream and `verify_bus_gkr`'s honest buffers (`GkrMemC`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.Memory

@[expose] public section

variable {S : BlakeSem} {rd : Reader} {c : ℕ} {xs : List E}

/-! ## `sumcheck_round5` -/

set_option maxRecDepth 100000 in
theorem sr5_loadS : ∀ k < 4, ((.n 2 : V), k) ∈ vtcP5.filterMap Stmt.loadS := by decide +kernel

/-- **`sumcheck_round5`'s trees load the round's four words** at its cursor `g^(c+o)`. -/
theorem sr5_loads {o : ℕ} {a0 a1 a3 a4 : E} {t : Tree} {rets : List E}
    (hx : ReadsAt rd (ofK (Parameters.gpow c)) xs) (ho : o + 4 ≤ xs.length)
    (hn : t.name = "sumcheck_round5")
    (hv : t.ValidB S coreProgram rd [a0, a1, ofK (Parameters.gpow c) * gen ^ o, a3, a4] rets) :
    ∀ k < 4, (Parameters.gpow (c + (o + k)), xs.getD (o + k) 0) ∈ t.loadEqns coreProgram := by
  obtain ⟨σ, bufs, kids, rfl, hp, hw, hes, -⟩ :=
    nodeS_straight (S := S) find_sumcheck_round5 vtc_core7 vtc_p5.1 hn hv
  simp only [show Fn.params Data.core7 = [.n 0, .n 1, .n 2, .n 3, .n 4] from rfl, List.map_cons,
    List.map_nil, List.cons.injEq] at hp
  obtain ⟨-, -, h2, -, -, -⟩ := hp
  intro k hk
  obtain ⟨d, hd⟩ := exists_load_of_loadS (sr5_loadS k hk)
  have hk' : o + k < xs.length := by omega
  rw [List.getD_eq_getElem _ _ hk']
  refine mem_loadEqns_node find_sumcheck_round5 hw
    (loadEq_of_event hes (mem_slEvs_of hd) hx hk' ?_)
  rw [h2, addr_gen, Nat.add_assoc]

/-! ## `__loop101` -/

set_option maxRecDepth 100000 in
theorem l101_atoms :
    Stmt.atom (.mul (.n 6) (.n 3) (.n 0)) ∈ vtcP101 ∧ Stmt.atom (.mul (.n 7) (.n 6) (.n 6)) ∈ vtcP101 ∧
    Stmt.atom (.mul (.n 8) (.n 7) (.n 7)) ∈ vtcP101 ∧ Stmt.atom (.mul (.n 9) (.n 2) (.n 8)) ∈ vtcP101 ∧
    Stmt.atom (.load (.n 12) (.n 9) 2) ∈ vtcP101 ∧
    Stmt.atom (.const (.n 22) (word 2 0 0)) ∈ vtcP101 ∧ Stmt.atom (.mul (.n 23) (.n 0) (.n 22)) ∈ vtcP101 ∧
    Stmt.atom (.add (.n 24) (.n 23) (.n 1)) ∈ vtcP101 ∧ Stmt.atom (.const (.n 25) (word 2 0 0)) ∈ vtcP101 ∧
    Stmt.atom (.mul (.n 26) (.n 0) (.n 25)) ∈ vtcP101 :=
  ⟨mem_of_stmtsEqb (i := 0) (by decide +kernel), mem_of_stmtsEqb (i := 1) (by decide +kernel),
    mem_of_stmtsEqb (i := 2) (by decide +kernel), mem_of_stmtsEqb (i := 3) (by decide +kernel),
    mem_of_stmtsEqb (i := 6) (by decide +kernel), mem_of_stmtsEqb (i := 17) (by decide +kernel),
    mem_of_stmtsEqb (i := 18) (by decide +kernel), mem_of_stmtsEqb (i := 19) (by decide +kernel),
    mem_of_stmtsEqb (i := 20) (by decide +kernel), mem_of_stmtsEqb (i := 21) (by decide +kernel)⟩

/-- **`__loop101`'s trees load a pair's rounds' words**: rounds `r < L` from `g^0`, each four
words at `g^(c + o + 4r)`, on a memory holding the rounds' cursors in its rows `p + r`. -/
theorem l101_loads {o p L : ℕ} {rounds prow nrow : E} {t : Tree} {rets : List E}
    (hx : ReadsAt rd (ofK (Parameters.gpow c)) xs) (hL : L < 2 ^ 63) (ho : o + 4 * L ≤ xs.length)
    (hrow : ∀ r < L, LoadHolds rd rounds (4 * (p + r) + 2) (ofK (Parameters.gpow c) * gen ^ (o + 4 * r)))
    (hn : t.name = "__loop101")
    (hv : t.ValidB S coreProgram rd [1, gen ^ L, rounds, gen ^ p, prow, nrow] rets) :
    ∀ r < L, ∀ k < 4,
      (Parameters.gpow (c + (o + 4 * r + k)), xs.getD (o + 4 * r + k) 0) ∈ t.loadEqns coreProgram := by
  obtain ⟨m6, m7, m8, m9, l12, m22, m23, m24, m25, m26⟩ := l101_atoms
  have hL0 : 0 < L ∨ L = 0 := by omega
  rcases hL0 with hL0 | rfl
  swap
  · intro r hr; omega
  have h := loopS_loads (S := S) find_loop101 vtc_core574 vtc_p101.1 rd L hL [rounds, gen ^ p, prow, nrow]
    (fun r q => ∃ k < 4, q = (Parameters.gpow (c + (o + 4 * r + k)), xs.getD (o + 4 * r + k) 0))
    (fun σ r hr hp hes => ?_) L 0 t rets (by omega) hL0 hn (by rwa [pow_zero])
  · intro r hr k hk
    exact h r (Nat.zero_le _) hr _ ⟨k, hk, rfl⟩
  simp only [show Fn.params Data.core574 = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5] from rfl,
    List.map_cons, List.map_nil, List.cons.injEq] at hp
  obtain ⟨h0, h1, h2, h3, h4, h5, -⟩ := hp
  have hpre : ∀ a, Stmt.atom a ∈ vtcP101 → a.HoldsB S rd σ := fun a ha => vtcS_atom hes ha
  have a6 := hpre _ m6
  have a7 := hpre _ m7
  have a8 := hpre _ m8
  have a9 := hpre _ m9
  have a12 : LoadHolds rd (σ (.n 9)) 2 (σ (.n 12)) := hpre _ l12
  simp only [Atom.HoldsB] at a6 a7 a8 a9
  have a22 := hpre _ m22
  have a23 := hpre _ m23
  have a24 := hpre _ m24
  have a25 := hpre _ m25
  have a26 := hpre _ m26
  simp only [Atom.HoldsB, word_gen] at a22 a23 a24 a25 a26
  refine ⟨by rw [a24, a23, a22, h0, h1], by simp [a26, a25, h0, h1, h2, h3, h4, h5], fun kids hk q hq => ?_⟩
  obtain ⟨k, hk4, rfl⟩ := hq
  rw [vtc_p101.2.2] at hk
  simp only [List.map_cons, List.map_nil, Main.mkCall] at hk
  match kids, hk with
  | [kt], ⟨hnk, hvk, _⟩ =>
    simp only [↓reduceIte, List.map_cons, List.map_nil] at hvk
    rw [a9, a8, a7, a6, h2, h3, h0, ← pow_add] at a12
    have e9 : rounds * (gen ^ (p + r) * gen ^ (p + r) * (gen ^ (p + r) * gen ^ (p + r))) =
        rounds * gen ^ (4 * (p + r)) := by
      simp only [← pow_add]; congr 2; ring
    rw [e9, loadHolds_mul_gen_pow] at a12
    have e12 := loadHolds_unique a12 (hrow r hr)
    rw [e12] at hvk
    right
    rw [Tree.loadEqnsKids, Tree.loadEqnsKids, List.append_nil]
    have := sr5_loads (o := o + 4 * r) hx (by omega) hnk hvk k hk4
    simpa only [Nat.add_assoc] using this

/-! ## `__loop10` -/

set_option maxRecDepth 100000 in
theorem l10_atoms :
    Stmt.atom (.mul (.n 6) (.n 0) (.n 0)) ∈ vtcP10 ∧ Stmt.atom (.mul (.n 7) (.n 2) (.n 3)) ∈ vtcP10 ∧
    Stmt.atom (.load (.n 8) (.n 7) 0) ∈ vtcP10 ∧ Stmt.atom (.mul (.n 9) (.n 6) (.n 8)) ∈ vtcP10 ∧
    Stmt.atom (.mul (.n 10) (.n 9) (.n 9)) ∈ vtcP10 ∧ Stmt.atom (.mul (.n 11) (.n 10) (.n 10)) ∈ vtcP10 ∧
    Stmt.atom (.mul (.n 12) (.n 11) (.n 11)) ∈ vtcP10 ∧ Stmt.atom (.mul (.n 13) (.n 4) (.n 12)) ∈ vtcP10 ∧
    Stmt.atom (.load (.n 31) (.n 13) 7) ∈ vtcP10 ∧ Stmt.atom (.const (.n 43) (word 1 0 0)) ∈ vtcP10 ∧
    Stmt.atom (.add (.n 44) (.n 43) (.n 9)) ∈ vtcP10 ∧ Stmt.atom (.const (.n 45) (word 1 0 0)) ∈ vtcP10 ∧
    Stmt.atom (.mul (.n 48) (.n 31) (.n 9)) ∈ vtcP10 ∧ Stmt.atom (.mul (.n 49) (.n 48) (.n 48)) ∈ vtcP10 ∧
    Stmt.atom (.mul (.n 50) (.n 49) (.n 49)) ∈ vtcP10 ∧ Stmt.atom (.mul (.n 51) (.n 5) (.n 50)) ∈ vtcP10 ∧
    Stmt.atom (.load (.n 54) (.n 51) 2) ∈ vtcP10 ∧
    Stmt.atom (.const (.n 326) (word 2 0 0)) ∈ vtcP10 ∧ Stmt.atom (.mul (.n 327) (.n 0) (.n 326)) ∈ vtcP10 ∧
    Stmt.atom (.add (.n 328) (.n 327) (.n 1)) ∈ vtcP10 ∧ Stmt.atom (.const (.n 329) (word 2 0 0)) ∈ vtcP10 ∧
    Stmt.atom (.mul (.n 330) (.n 0) (.n 329)) ∈ vtcP10 :=
  ⟨mem_of_stmtsEqb (i := 0) (by decide +kernel), mem_of_stmtsEqb (i := 1) (by decide +kernel),
    mem_of_stmtsEqb (i := 2) (by decide +kernel), mem_of_stmtsEqb (i := 3) (by decide +kernel),
    mem_of_stmtsEqb (i := 4) (by decide +kernel), mem_of_stmtsEqb (i := 5) (by decide +kernel),
    mem_of_stmtsEqb (i := 6) (by decide +kernel), mem_of_stmtsEqb (i := 7) (by decide +kernel),
    mem_of_stmtsEqb (i := 25) (by decide +kernel), mem_of_stmtsEqb (i := 41) (by decide +kernel),
    mem_of_stmtsEqb (i := 42) (by decide +kernel), mem_of_stmtsEqb (i := 43) (by decide +kernel),
    mem_of_stmtsEqb (i := 47) (by decide +kernel), mem_of_stmtsEqb (i := 48) (by decide +kernel),
    mem_of_stmtsEqb (i := 49) (by decide +kernel), mem_of_stmtsEqb (i := 50) (by decide +kernel),
    mem_of_stmtsEqb (i := 53) (by decide +kernel),
    mem_of_stmtsEqb (i := 312) (by decide +kernel), mem_of_stmtsEqb (i := 313) (by decide +kernel),
    mem_of_stmtsEqb (i := 314) (by decide +kernel), mem_of_stmtsEqb (i := 315) (by decide +kernel),
    mem_of_stmtsEqb (i := 316) (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem l10_fs_loads : ∀ i < 12, stmtsEqb [.atom (.load (.n (56 + 16 * i)) (.n 54) i)]
    ((vtcP10.drop (55 + 14 * i)).take 1) = true := by decide +kernel

/-- **`__loop10`'s tree loads pair `j`'s words**, `4 gL + 12` of them from `gCur j`, for every
pair `j < μ/2`. -/
def L10Loads (μ c : ℕ) (xs : List E) (t : Tree) : Prop :=
  ∀ j < μ / 2, ∀ m < 4 * gL (μ % 2) j + 12,
    (Parameters.gpow (c + (gCur (μ % 2) j + m)), xs.getD (gCur (μ % 2) j + m) 0) ∈ t.loadEqns coreProgram

theorem gCur_succ_le {sh j n : ℕ} (h : j + 1 ≤ n) : gCur sh (j + 1) ≤ gCur sh n := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_or_lt_of_le h with h | h
    · rw [h]
    · exact (ih (by omega)).trans (by rw [gCur]; omega)

set_option maxHeartbeats 4000000 in
/-- **Every valid tree of `__loop10` loads the pairs' words**, on a memory holding the stream at
`g^c` and `verify_bus_gkr`'s honest buffers. -/
theorem l10_loads {M : HashModel} {T : GkrTrace} {μ : ℕ} {cv : Digest} {layers rounds pts pb dsb : E}
    (hμ : μ < 33) (hM : GkrMemC M rd T μ cv (ofK (Parameters.gpow c)) layers rounds pts pb dsb)
    (hx : ReadsAt rd (ofK (Parameters.gpow c)) xs) (hlen : gCur (μ % 2) (μ / 2) ≤ xs.length)
    {t : Tree} {rets : List E} (hn : t.name = "__loop10")
    (hv : t.ValidB S coreProgram rd [1, gen ^ (μ / 2), dsb, gen ^ μ, layers, rounds] rets) :
    L10Loads μ c xs t := by
  obtain ⟨m6, m7, l8, m9, m10, m11, m12, m13, l31, m43, m44, m45, m48, m49, m50, m51, l54, m326, m327,
    m328, m329, m330⟩ := l10_atoms
  have hds : LoadHolds rd (dsb * gen ^ μ) 0 (gen ^ (μ % 2)) :=
    loadHolds_unshift (by rw [← vbgDs_get hμ]; exact hM.ds μ (by omega)) rfl
  have hpos : 0 < μ / 2 ∨ μ / 2 = 0 := by omega
  rcases hpos with hpos | h0
  swap
  · intro j hj; omega
  have h := loopS_loads (S := S) find_loop10 vtc_core40 vtc_p10.1 rd (μ / 2) (by omega)
    [dsb, gen ^ μ, layers, rounds]
    (fun j q => ∃ m < 4 * gL (μ % 2) j + 12,
      q = (Parameters.gpow (c + (gCur (μ % 2) j + m)), xs.getD (gCur (μ % 2) j + m) 0))
    (fun σ j hj hp hes => ?_) (μ / 2) 0 t rets (by omega) hpos hn (by rwa [pow_zero])
  · intro j hj m hm
    exact h j (Nat.zero_le _) hj _ ⟨m, hm, rfl⟩
  simp only [show Fn.params Data.core40 = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5] from rfl,
    List.map_cons, List.map_nil, List.cons.injEq] at hp
  obtain ⟨h0, h1, h2, h3, h4, h5, -⟩ := hp
  have hpre : ∀ a, Stmt.atom a ∈ vtcP10 → a.HoldsB S rd σ := fun a ha => vtcS_atom hes ha
  have a6 := hpre _ m6
  have a7 := hpre _ m7
  have a8 : LoadHolds rd (σ (.n 7)) 0 (σ (.n 8)) := hpre _ l8
  have a9 := hpre _ m9
  have a10 := hpre _ m10
  have a11 := hpre _ m11
  have a12 := hpre _ m12
  have a13 := hpre _ m13
  have a31 : LoadHolds rd (σ (.n 13)) 7 (σ (.n 31)) := hpre _ l31
  have a43 := hpre _ m43
  have a44 := hpre _ m44
  have a45 := hpre _ m45
  have a48 := hpre _ m48
  have a49 := hpre _ m49
  have a50 := hpre _ m50
  have a51 := hpre _ m51
  have a54 : LoadHolds rd (σ (.n 51)) 2 (σ (.n 54)) := hpre _ l54
  have a326 := hpre _ m326
  have a327 := hpre _ m327
  have a328 := hpre _ m328
  have a329 := hpre _ m329
  have a330 := hpre _ m330
  simp only [Atom.HoldsB, word_gen, word_one] at a6 a7 a9 a10 a11 a12 a13 a43 a44 a45 a48 a49 a50 a51 a326 a327 a328 a329 a330
  refine ⟨by rw [a328, a327, a326, h0, h1], by simp [a330, a329, h0, h1, h2, h3, h4, h5],
    fun kids hk q hq => ?_⟩
  obtain ⟨m, hm, rfl⟩ := hq
  -- the layer's slot and cursor
  rw [a7, h2, h3] at a8
  have e8 := loadHolds_unique a8 hds
  have e9 : σ (.n 9) = gen ^ gL (μ % 2) j := by
    rw [a9, a6, e8, h0, ← pow_add, ← pow_add]; unfold gL; congr 1; ring
  have e13 : σ (.n 13) = layers * gen ^ (8 * gL (μ % 2) j) := by
    rw [a13, a12, a11, a10, e9, h4, ← pow_add, ← pow_add, ← pow_add]; congr 2; ring
  rw [e13, loadHolds_mul_gen_pow] at a31
  have e31 : σ (.n 31) = gen ^ gPos (μ % 2) j :=
    loadHolds_unique a31 (hM.lay j (by omega) 7 (by omega))
  have e51 : σ (.n 51) = rounds * gen ^ (4 * (gPos (μ % 2) j + gL (μ % 2) j)) := by
    rw [a51, a50, a49, a48, e31, e9, h5, ← pow_add, ← pow_add, ← pow_add]; congr 2; ring
  rw [e51, loadHolds_mul_gen_pow] at a54
  have e54 : σ (.n 54) = ofK (Parameters.gpow c) * gen ^ (gCur (μ % 2) j + 4 * gL (μ % 2) j) := by
    have := loadHolds_unique a54 (hM.rnd j hj (gL (μ % 2) j) le_rfl 2 (by omega))
    rw [this]; simp only [gRnd, List.getD_cons_succ, List.getD_cons_zero, mul_assoc, ← pow_add]
  have hnext : gCur (μ % 2) (j + 1) ≤ xs.length := (gCur_succ_le (by omega)).trans hlen
  rw [gCur] at hnext
  by_cases hmL : m < 4 * gL (μ % 2) j
  · -- a round's word: `__loop101`'s
    right
    rw [vtc_p10.2.2] at hk
    simp only [List.map_cons, List.map_nil, Main.mkCall] at hk
    match kids, hk with
    | [kt], ⟨hnk, hvk, _⟩ =>
      have hL0 : 0 < gL (μ % 2) j := by omega
      have ht : σ (.n 44) ≠ 0 := by
        rw [a44, a43, e9, ← pow_zero gen]
        exact gen_pow_ne_of_lt hL0 (by unfold gL; omega)
      simp only [ht, ne_eq, not_false_eq_true, decide_true, ↓reduceIte, List.map_cons,
        List.map_nil] at hvk
      rw [a45, e9, h5, e31] at hvk
      rw [Tree.loadEqnsKids, Tree.loadEqnsKids, List.append_nil]
      have := l101_loads (o := gCur (μ % 2) j) (p := gPos (μ % 2) j) (L := gL (μ % 2) j) hx
        (by unfold gL; omega) (by omega)
        (fun r hr => by
          have := hM.rnd j hj r hr.le 2 (by omega)
          simpa only [gRnd, List.getD_cons_succ, List.getD_cons_zero, mul_assoc, ← pow_add] using this)
        hnk hvk (m / 4) (by omega) (m % 4) (by omega)
      rwa [show gCur (μ % 2) j + 4 * (m / 4) + m % 4 = gCur (μ % 2) j + m by omega] at this
  · -- a child's word: the path's
    left
    have hi : m - 4 * gL (μ % 2) j < 12 := by omega
    have hm' : gCur (μ % 2) j + m < xs.length := by omega
    rw [List.getD_eq_getElem _ _ hm']
    refine loadEq_of_event hes (mem_slEvs_of (mem_of_stmtsEqb (l10_fs_loads _ hi))) hx hm' ?_
    rw [e54, addr_gen]
    congr 1
    omega

end
end LeanVM.Guest.B1.VerifySub
