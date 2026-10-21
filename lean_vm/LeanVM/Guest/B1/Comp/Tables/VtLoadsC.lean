/-
  LeanVM.Guest.B1.Comp.Tables.VtLoadsC

  `verify_tables`' sumcheck rounds' valid trees under any semantics load the stream words they
  read.
-/

module

public import LeanVM.Guest.B1.Comp.Tables.LoadsL
public import LeanVM.Guest.B1.Comp.Tables.VtPlacedC

/-!
# The table sumcheck's rounds, loading what they read

The tables' stream at `g^c`: round `r`'s three words, at `5 + 3r`, are read by `sumcheck_round4`
(`sr4_loads`), called once per round by `__loop79` (`l79_loads`) through the cursors its rows
hold (`zcRoundsW`). Each over every valid tree under any semantics.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.Memory

@[expose] public section

variable {S : BlakeSem} {rd : Reader} {c : ℕ} {xs : List E}

/-! ## `sumcheck_round4` -/

set_option maxRecDepth 100000 in
theorem sr4_loadS : ∀ k < 3, ((.n 2 : V), k) ∈ (Fn.body Data.core6).filterMap Stmt.loadS := by
  decide +kernel

/-- **`sumcheck_round4`'s trees load the round's three words** at its cursor `g^(c+o)`. -/
theorem sr4_loads {o : ℕ} {a0 a1 a3 : E} {t : Tree} {rets : List E}
    (hx : ReadsAt rd (ofK (Parameters.gpow c)) xs) (ho : o + 3 ≤ xs.length)
    (hn : t.name = "sumcheck_round4")
    (hv : t.ValidB S coreProgram rd [a0, a1, ofK (Parameters.gpow c) * gen ^ o, a3] rets) :
    ∀ k < 3, (Parameters.gpow (c + (o + k)), xs.getD (o + k) 0) ∈ t.loadEqns coreProgram := by
  have hok := vtc_sr4_leaf
  unfold vtcLeafOk at hok
  rw [find_sumcheck_round4] at hok
  dsimp only at hok
  split at hok
  · rename_i vs hl
    simp only [Bool.and_eq_true, List.isEmpty_iff] at hok
    obtain ⟨⟨hst, -⟩, -⟩ := hok
    have hb : (Fn.body Data.core6) = (Fn.body Data.core6).dropLast ++ [.ret vs] := by
      rw [← List.dropLast_append_getLast? _ hl]
      simp
    obtain ⟨σ, bufs, kids, rfl, hp, hw, hes, -⟩ :=
      nodeS_straight (S := S) find_sumcheck_round4 hb hst hn hv
    simp only [show Fn.params Data.core6 = [.n 0, .n 1, .n 2, .n 3] from rfl, List.map_cons,
      List.map_nil, List.cons.injEq] at hp
    obtain ⟨-, -, h2, -, -⟩ := hp
    intro k hk
    obtain ⟨d, hd⟩ := exists_load_of_loadS (sr4_loadS k hk)
    have hd' : Stmt.atom (.load d (.n 2) k) ∈ (Fn.body Data.core6).dropLast := by
      rw [hb] at hd
      rcases List.mem_append.mp hd with h | h
      · exact h
      · simp at h
    have hk' : o + k < xs.length := by omega
    rw [List.getD_eq_getElem _ _ hk']
    refine mem_loadEqns_node find_sumcheck_round4 hw
      (loadEq_of_event hes (mem_slEvs_of hd') hx hk' ?_)
    rw [h2, addr_gen, Nat.add_assoc]
  · exact absurd hok (by simp)

/-! ## `__loop79` -/

set_option maxRecDepth 100000 in
theorem l79_atoms :
    Stmt.atom (.mul (.n 6) (.n 0) (.n 0)) ∈ vtcP79 ∧ Stmt.atom (.mul (.n 7) (.n 6) (.n 6)) ∈ vtcP79 ∧
    Stmt.atom (.mul (.n 8) (.n 2) (.n 7)) ∈ vtcP79 ∧ Stmt.atom (.load (.n 11) (.n 8) 2) ∈ vtcP79 ∧
    Stmt.atom (.const (.n 26) (word 2 0 0)) ∈ vtcP79 ∧ Stmt.atom (.mul (.n 27) (.n 0) (.n 26)) ∈ vtcP79 ∧
    Stmt.atom (.add (.n 28) (.n 27) (.n 1)) ∈ vtcP79 ∧ Stmt.atom (.const (.n 29) (word 2 0 0)) ∈ vtcP79 ∧
    Stmt.atom (.mul (.n 30) (.n 0) (.n 29)) ∈ vtcP79 :=
  ⟨mem_of_stmtsEqb (i := 0) (by decide +kernel), mem_of_stmtsEqb (i := 1) (by decide +kernel),
    mem_of_stmtsEqb (i := 2) (by decide +kernel), mem_of_stmtsEqb (i := 5) (by decide +kernel),
    mem_of_stmtsEqb (i := 22) (by decide +kernel), mem_of_stmtsEqb (i := 23) (by decide +kernel),
    mem_of_stmtsEqb (i := 24) (by decide +kernel), mem_of_stmtsEqb (i := 25) (by decide +kernel),
    mem_of_stmtsEqb (i := 26) (by decide +kernel)⟩

/-- **`__loop79`'s tree loads the rounds' words**: round `r < n`'s three at `5 + 3r`. -/
def L79Loads (n c : ℕ) (xs : List E) (t : Tree) : Prop :=
  ∀ r < n, ∀ k < 3,
    (Parameters.gpow (c + (5 + 3 * r + k)), xs.getD (5 + 3 * r + k) 0) ∈ t.loadEqns coreProgram

/-- **Every valid tree of `__loop79` from `g^0` to `g^n` loads the rounds' words**, on a memory
holding the stream at `g^c` and the rounds' cursors in its rows. -/
theorem l79_loads {n : ℕ} {rounds chi gn cprod : E} {t : Tree} {rets : List E}
    (hx : ReadsAt rd (ofK (Parameters.gpow c)) xs) (hn63 : n < 2 ^ 63) (hlen : 5 + 3 * n ≤ xs.length)
    (hrow : ∀ r < n, LoadHolds rd rounds (4 * r + 2) (ofK (Parameters.gpow c) * gen ^ (5 + 3 * r)))
    (hn : t.name = "__loop79")
    (hv : t.ValidB S coreProgram rd [1, gen ^ n, rounds, chi, gn, cprod] rets) :
    L79Loads n c xs t := by
  obtain ⟨m6, m7, m8, l11, m26, m27, m28, m29, m30⟩ := l79_atoms
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · intro r hr; omega
  have h := loopS_loads (S := S) find_loop79 vtc_core138 vtc_p79_ok.1 rd n hn63 [rounds, chi, gn, cprod]
    (fun r q => ∃ k < 3, q = (Parameters.gpow (c + (5 + 3 * r + k)), xs.getD (5 + 3 * r + k) 0))
    (fun σ r hr hp hes => ?_) n 0 t rets (by omega) hpos hn (by rwa [pow_zero])
  · intro r hr k hk
    exact h r (Nat.zero_le _) hr _ ⟨k, hk, rfl⟩
  simp only [show Fn.params Data.core138 = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5] from rfl,
    List.map_cons, List.map_nil, List.cons.injEq] at hp
  obtain ⟨h0, h1, h2, h3, h4, h5, -⟩ := hp
  have hpre : ∀ a, Stmt.atom a ∈ vtcP79 → a.HoldsB S rd σ := fun a ha => vtcS_atom hes ha
  have a6 := hpre _ m6
  have a7 := hpre _ m7
  have a8 := hpre _ m8
  have a11 : LoadHolds rd (σ (.n 8)) 2 (σ (.n 11)) := hpre _ l11
  have a26 := hpre _ m26
  have a27 := hpre _ m27
  have a28 := hpre _ m28
  have a29 := hpre _ m29
  have a30 := hpre _ m30
  simp only [Atom.HoldsB, word_gen] at a6 a7 a8 a26 a27 a28 a29 a30
  refine ⟨by rw [a28, a27, a26, h0, h1], by simp [a30, a29, h0, h1, h2, h3, h4, h5],
    fun kids hk q hq => ?_⟩
  obtain ⟨k, hk3, rfl⟩ := hq
  rw [vtc_p79_ok.2.2] at hk
  simp only [List.map_cons, List.map_nil, Main.mkCall] at hk
  match kids, hk with
  | [kt], ⟨hnk, hvk, _⟩ =>
    simp only [↓reduceIte, List.map_cons, List.map_nil] at hvk
    rw [a8, a7, a6, h2, h0, ← pow_add, ← pow_add,
      show r + r + (r + r) = 4 * r by ring, loadHolds_mul_gen_pow] at a11
    have e11 := loadHolds_unique a11 (hrow r hr)
    rw [e11] at hvk
    right
    rw [Tree.loadEqnsKids, Tree.loadEqnsKids, List.append_nil]
    have := sr4_loads (o := 5 + 3 * r) hx (by omega) hnk hvk k hk3
    simpa only [Nat.add_assoc] using this

end
end LeanVM.Guest.B1.VerifySub
