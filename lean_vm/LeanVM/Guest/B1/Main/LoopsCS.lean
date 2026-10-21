/-
  LeanVM.Guest.B1.Main.LoopsCS

  `LoopsC.lean` under any semantics of `BLAKE2S` (`S : BlakeSem`).
-/

module

public import LeanVM.Guest.B1.Main.LoopsC
public import LeanVM.Guest.B1.UniformS
public import LeanVM.Guest.B1.BasicS
public import LeanVM.Guest.B1.Main.AggStepsCS

/-!
# `LoopsC.lean` under any `BLAKE2S` semantics

Each definition and lemma of `LoopsC.lean` that mentions the semantics, with `S : BlakeSem` a
parameter and a `S` in its name.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Verifier LeanVM.Node

@[expose] public section

variable {S : BlakeSem}

variable {rd : Reader}

/-! ## Loops whose body calls -/

/-- Finitely many relations hold at one depth. -/
theorem relS_uniform {F : ℕ → String} {A R : ℕ → List E} :
    ∀ m : ℕ, (∀ j < m, coreProgram.RelB S rd (F j) (A j) (R j)) →
      ∃ D, ∀ j < m, coreProgram.relNB S rd D (F j) (A j) (R j)
  | 0, _ => ⟨0, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | m + 1, h => by
    obtain ⟨D, hD⟩ := relS_uniform m fun j hj => h j (by omega)
    obtain ⟨D', hD'⟩ := h m (by omega)
    refine ⟨max D D', fun j hj => ?_⟩
    rcases Nat.lt_or_ge j m with hj' | hj'
    · exact relNB_mono coreProgram (le_max_left _ _) _ _ _ (hD j hj')
    · rw [show j = m by omega]; exact relNB_mono coreProgram (le_max_right _ _) _ _ _ hD'

/-- **A `mul_range` loop whose body calls, backward**: as `loopS_complete`, each iteration holding
at every depth from `D` on. -/
theorem loopS_complete_from {f : String} {ps : List E} {N : E} {m D : ℕ} {B : ℕ → Prop}
    (hm0 : 0 < m) (hN : N = gen ^ m) (hB : ∀ j < m, B j)
    (hstep : ∀ d j, D ≤ d → B j → IsInK (gen ^ j * gen + N) →
      (gen ^ j * gen + N ≠ 0 → coreProgram.relNB S rd d f (gen ^ j * gen :: ps) []) →
      coreProgram.relNB S rd (d + 1) f (gen ^ j :: ps) []) :
    coreProgram.RelB S rd f (1 :: ps) [] := by
  have hK : ∀ j, IsInK (gen ^ j * gen + N) := fun j => by
    rw [hN]
    exact isInK_add (isInK_mul (gen_pow_isInK j) (by simpa using gen_pow_isInK 1)) (gen_pow_isInK _)
  have key : ∀ t j, j + t + 1 = m → coreProgram.relNB S rd (D + t + 1) f (gen ^ j :: ps) [] := by
    intro t
    induction t with
    | zero =>
      intro j hj
      refine hstep (D + 0) j (by omega) (hB j (by omega)) (hK j) fun hne => absurd ?_ hne
      rw [gen_pow_add_eq_zero_iff, hN]; congr 1; omega
    | succ t ih =>
      intro j hj
      refine hstep (D + (t + 1)) j (by omega) (hB j (by omega)) (hK j) fun _ => ?_
      rw [gen_pow_mul_gen, show D + (t + 1) = D + t + 1 by omega]
      exact ih (j + 1) (by omega)
  refine ⟨D + (m - 1) + 1, ?_⟩
  have := key (m - 1) 0 (by omega)
  rwa [pow_zero] at this

/-! ## The hint-filling loops -/

theorem loop0S_back {N roots : E} (d j : ℕ) (hK : IsInK (gen ^ j * gen + N))
    (hnext : gen ^ j * gen + N ≠ 0 → coreProgram.relNB S rd d "__loop0" [gen ^ j * gen, N, roots] []) :
    coreProgram.relNB S rd (d + 1) "__loop0" [gen ^ j, N, roots] [] := by
  set x := gen ^ j
  rw [relNS_succ_iff find_loop0]
  refine ⟨setl (Val.ofArgs [x, N, roots]) 3 [x * x, x * x * (x * x), roots * (x * x * (x * x)), gen,
    x * gen, x * gen + N, gen, x * gen], by
      simp only [show Fn.params Data.core30 = [.n 0, .n 1, .n 2] from rfl, List.map_cons,
        List.map_nil]; b1_look, ?_⟩
  simp only [show Fn.body Data.core30 = Data.core30.body from rfl, Data.core30.body,
    Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, List.map_cons, List.map_nil, word_gen]
  b1_look
  simp only [true_and, and_true]
  exact ⟨hK, hnext⟩

/-- **`__loop0`** fills the DA roots from hints, on every memory. -/
theorem loop0S_complete {N roots : E} {m : ℕ} (hm0 : 0 < m) (hN : N = gen ^ m) :
    coreProgram.RelB S rd "__loop0" [1, N, roots] [] :=
  loopS_complete (B := fun _ => True) hm0 hN (fun _ _ => trivial)
    fun d j _ hK hnext => loop0S_back d j hK hnext

/-- `__loop1` and `__loop2`: the same body, under two names. -/
theorem loopDupS_back {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    (hp : fn.params = [.n 0, .n 1, .n 2, .n 3])
    (hb : fn.body = [.atom (.mul (.n 4) (.n 3) (.n 0)), .atom (.mul (.n 5) (.n 4) (.n 4)),
      .atom (.mul (.n 6) (.n 5) (.n 5)), .atom (.mul (.n 7) (.n 2) (.n 6)),
      .atom (.hint (.witness "dup_claims" (.heap (.n 7) 0 4))), .atom (.const (.n 8) (word 2 0 0)),
      .atom (.mul (.n 9) (.n 0) (.n 8)), .atom (.add (.n 10) (.n 9) (.n 1)),
      .atom (.const (.n 11) (word 2 0 0)), .atom (.mul (.n 12) (.n 0) (.n 11)),
      .callIf (.n 10) f [.n 12, .n 1, .n 2, .n 3], .ret []])
    {N table base : E} (d j : ℕ) (hK : IsInK (gen ^ j * gen + N))
    (hnext : gen ^ j * gen + N ≠ 0 → coreProgram.relNB S rd d f [gen ^ j * gen, N, table, base] []) :
    coreProgram.relNB S rd (d + 1) f [gen ^ j, N, table, base] [] := by
  set x := gen ^ j
  rw [relNS_succ_iff hf]
  refine ⟨setl (Val.ofArgs [x, N, table, base]) 4 [base * x, base * x * (base * x),
    base * x * (base * x) * (base * x * (base * x)),
    table * (base * x * (base * x) * (base * x * (base * x))), gen, x * gen, x * gen + N, gen,
    x * gen], by simp only [hp, List.map_cons, List.map_nil]; b1_look, ?_⟩
  simp only [hb, Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, List.map_cons, List.map_nil, word_gen]
  b1_look
  simp only [true_and, and_true]
  exact ⟨hK, hnext⟩

/-- **`__loop1`** fills the leanXMSS duplicates from hints, on every memory. -/
theorem loop1S_complete {N table base : E} {m : ℕ} (hm0 : 0 < m) (hN : N = gen ^ m) :
    coreProgram.RelB S rd "__loop1" [1, N, table, base] [] :=
  loopS_complete (B := fun _ => True) hm0 hN (fun _ _ => trivial)
    fun d j _ hK hnext => loopDupS_back find_loop1 rfl rfl d j hK hnext

/-- **`__loop2`** fills the leanSPHINCS duplicates from hints, on every memory. -/
theorem loop2S_complete {N table base : E} {m : ℕ} (hm0 : 0 < m) (hN : N = gen ^ m) :
    coreProgram.RelB S rd "__loop2" [1, N, table, base] [] :=
  loopS_complete (B := fun _ => True) hm0 hN (fun _ _ => trivial)
    fun d j _ hK hnext => loopDupS_back find_loop2 rfl rfl d j hK hnext

/-! ## The raw signatures -/

/-- **`__loop3` at `x = g^c`, backward**: the slot `s` of the leanXMSS region `g^M`, its mark `x` in
the coverage table, and the verifier on its claim give the iteration. -/
theorem loop3S_back (hm : MemOk rd) {N cover table : E} {M : ℕ} (hM : M ≤ 2 ^ 16) (d c s : ℕ)
    (hs : s < M) (hmark : LoadHolds rd cover s (gen ^ c))
    (hv : coreProgram.relNB S rd d "verify_lean_xmss" [table * gen ^ (4 * s)] [])
    (hK : IsInK (gen ^ c * gen + N))
    (hnext : gen ^ c * gen + N ≠ 0 →
      coreProgram.relNB S rd d "__loop3" [gen ^ c * gen, N, gen ^ M, cover, table] []) :
    coreProgram.relNB S rd (d + 1) "__loop3" [gen ^ c, N, gen ^ M, cover, table] [] := by
  set x := gen ^ c
  obtain ⟨t1, t2, l1, hk, l2⟩ := LeanVM.Guest.B1.Digest.rangeCheck_complete (rd := rd) hm (e := s) (e' := M - 1 - s) (by omega)
    (by omega)
  rw [relNS_succ_iff find_loop3]
  refine ⟨setl (Val.ofArgs [x, N, gen ^ M, cover, table]) 5 [gen ^ s, ginvW, gen ^ M * ginvW,
    gen ^ (M - 1 - s), t1, t2, cover * gen ^ s, gen ^ s * gen ^ s,
    gen ^ s * gen ^ s * (gen ^ s * gen ^ s), table * (gen ^ s * gen ^ s * (gen ^ s * gen ^ s)), gen,
    x * gen, x * gen + N, gen, x * gen], by
      simp only [show Fn.params Data.core33 = [.n 0, .n 1, .n 2, .n 3, .n 4] from rfl,
        List.map_cons, List.map_nil]; b1_look, ?_⟩
  simp only [show Fn.body Data.core33 = Data.core33.body from rfl, Data.core33.body,
    Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, List.map_cons, List.map_nil, word_gen]
  b1_look
  simp only [true_and, and_true]
  exact ⟨⟨l1, gen_pow_mul_ginv s hs, l2⟩, by rw [loadHolds_mul_gen_pow, Nat.add_zero]; exact hmark,
    by rw [gen_pow_four]; exact hv, hK, hnext⟩

/-- **`__loop3`**, backward: its `m` iterations, iteration `c` writing the mark `g^c` in its slot
`sl c` of the leanXMSS region `g^M` and verifying the table's claim there. -/
theorem loop3S_complete (hm : MemOk rd) {cover table : E} {M m : ℕ} (hM : M ≤ 2 ^ 16) (hm0 : 0 < m)
    (sl : ℕ → ℕ) (hs : ∀ c < m, sl c < M) (hmark : ∀ c < m, LoadHolds rd cover (sl c) (gen ^ c))
    (hv : ∀ c < m, coreProgram.RelB S rd "verify_lean_xmss" [table * gen ^ (4 * sl c)] []) :
    coreProgram.RelB S rd "__loop3" [1, gen ^ m, gen ^ M, cover, table] [] := by
  obtain ⟨D, hD⟩ := relS_uniform m hv
  exact loopS_complete_from (D := D) (B := fun j => j < m) hm0 rfl (fun j hj => hj)
    fun d j hd hj hK hnext => loop3S_back hm hM d j (sl j) (hs j hj) (hmark j hj)
      (relNB_mono coreProgram hd _ _ _ (hD j hj)) hK hnext

/-- **`__loop4` at `x = g^c`, backward**: the slot `s` of the leanSPHINCS region `g^M` after the
leanXMSS region `g^Lx`, its mark `w·x` in the coverage table, and the verifier on its claim. -/
theorem loop4S_back (hm : MemOk rd) {N cover w table : E} {M Lx : ℕ} (hM : M ≤ 2 ^ 16) (d c s : ℕ)
    (hs : s < M) (hmark : LoadHolds rd cover (Lx + s) (w * gen ^ c))
    (hv : coreProgram.relNB S rd d "verify_sig_lean_sphincs" [table * gen ^ (4 * s)] [])
    (hK : IsInK (gen ^ c * gen + N))
    (hnext : gen ^ c * gen + N ≠ 0 →
      coreProgram.relNB S rd d "__loop4" [gen ^ c * gen, N, gen ^ M, cover, gen ^ Lx, w, table] []) :
    coreProgram.relNB S rd (d + 1) "__loop4" [gen ^ c, N, gen ^ M, cover, gen ^ Lx, w, table] [] := by
  set x := gen ^ c
  obtain ⟨t1, t2, l1, hk, l2⟩ := LeanVM.Guest.B1.Digest.rangeCheck_complete (rd := rd) hm (e := s)
    (e' := M - 1 - s) (by omega) (by omega)
  rw [relNS_succ_iff find_loop4]
  refine ⟨setl (Val.ofArgs [x, N, gen ^ M, cover, gen ^ Lx, w, table]) 7 [gen ^ s, ginvW,
    gen ^ M * ginvW, gen ^ (M - 1 - s), t1, t2, w * x, gen ^ Lx * gen ^ s,
    cover * (gen ^ Lx * gen ^ s), gen ^ s * gen ^ s, gen ^ s * gen ^ s * (gen ^ s * gen ^ s),
    table * (gen ^ s * gen ^ s * (gen ^ s * gen ^ s)), gen, x * gen, x * gen + N, gen, x * gen], by
      simp only [show Fn.params Data.core34 = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6] from rfl,
        List.map_cons, List.map_nil]; b1_look, ?_⟩
  simp only [show Fn.body Data.core34 = Data.core34.body from rfl, Data.core34.body,
    Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, List.map_cons, List.map_nil, word_gen]
  b1_look
  simp only [true_and, and_true]
  exact ⟨⟨l1, gen_pow_mul_ginv s hs, l2⟩,
    by rw [← pow_add, loadHolds_mul_gen_pow, Nat.add_zero]; exact hmark,
    by rw [gen_pow_four]; exact hv, hK, hnext⟩

/-- **`__loop4`**, backward: iteration `c` writing the mark `w·g^c` in slot `Lx + sl c`, `sl c`
in the leanSPHINCS region `g^M`, and verifying the table's claim `sl c`. -/
theorem loop4S_complete (hm : MemOk rd) {cover w table : E} {M Lx m : ℕ} (hM : M ≤ 2 ^ 16)
    (hm0 : 0 < m) (sl : ℕ → ℕ) (hs : ∀ c < m, sl c < M)
    (hmark : ∀ c < m, LoadHolds rd cover (Lx + sl c) (w * gen ^ c))
    (hv : ∀ c < m, coreProgram.RelB S rd "verify_sig_lean_sphincs" [table * gen ^ (4 * sl c)] []) :
    coreProgram.RelB S rd "__loop4" [1, gen ^ m, gen ^ M, cover, gen ^ Lx, w, table] [] := by
  obtain ⟨D, hD⟩ := relS_uniform m hv
  exact loopS_complete_from (D := D) (B := fun j => j < m) hm0 rfl (fun j hj => hj)
    fun d j hd hj hK hnext => loop4S_back hm hM d j (sl j) (hs j hj) (hmark j hj)
      (relNB_mono coreProgram hd _ _ _ (hD j hj)) hK hnext

/-! ## A child's DA roots -/

/-- **`__loop100` at `x = g^c`, backward**: the DA slot `i`'s root cells, copied to the child's list
`cda·g^(4c)`, and `cover_da_root`'s relation. -/
theorem loop100S_back {N cda roots dcov dslots base nsub r0 r1 r2 r3 : E} (d c : ℕ)
    (hcov : coreProgram.relNB S rd d "cover_da_root" [roots, dcov, dslots, base * nsub * gen ^ c]
      [r0, r1, r2, r3])
    (hcda : ReadsAt rd (cda * gen ^ (4 * c)) [r0, r1, r2, r3])
    (hK : IsInK (gen ^ c * gen + N))
    (hnext : gen ^ c * gen + N ≠ 0 → coreProgram.relNB S rd d "__loop100"
      [gen ^ c * gen, N, cda, roots, dcov, dslots, base, nsub] []) :
    coreProgram.relNB S rd (d + 1) "__loop100" [gen ^ c, N, cda, roots, dcov, dslots, base, nsub] [] := by
  set x := gen ^ c with hx
  have e4 : cda * (x * x * (x * x)) = cda * gen ^ (4 * c) := by rw [hx, gen_pow_four]
  rw [relNS_succ_iff find_loop100]
  refine ⟨setl (Val.ofArgs [x, N, cda, roots, dcov, dslots, base, nsub]) 8 [x * x, x * x * (x * x),
    cda * (x * x * (x * x)), base * nsub, base * nsub * x, r0, r1, r2, r3, gen, x * gen, x * gen + N,
    gen, x * gen], by
      simp only [show Fn.params Data.core573 = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7]
        from rfl, List.map_cons, List.map_nil]; b1_look, ?_⟩
  simp only [show Fn.body Data.core573 = Data.core573.body from rfl, Data.core573.body,
    Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, List.map_cons, List.map_nil, word_gen]
  b1_look
  simp only [true_and, and_true, e4]
  exact ⟨hcov, readsAt_getD' hcda (k := 0) (by simp), readsAt_getD' hcda (k := 1) (by simp),
    readsAt_getD' hcda (k := 2) (by simp), readsAt_getD' hcda (k := 3) (by simp), hK, hnext⟩

/-- **`__loop100`**, backward: iteration `c` marking its DA slot with `base·nsub·g^c` by
`cover_da_root`, which returns its root's cells `rt c`, copied to `cda·g^(4c)`. -/
theorem loop100S_complete {cda roots dcov dslots base nsub : E} {m : ℕ} (hm0 : 0 < m)
    (rt : ℕ → List E) (hl : ∀ c < m, (rt c).length = 4)
    (hcov : ∀ c < m, coreProgram.RelB S rd "cover_da_root" [roots, dcov, dslots, base * nsub * gen ^ c]
      (rt c))
    (hcda : ∀ c < m, ReadsAt rd (cda * gen ^ (4 * c)) (rt c)) :
    coreProgram.RelB S rd "__loop100" [1, gen ^ m, cda, roots, dcov, dslots, base, nsub] [] := by
  obtain ⟨D, hD⟩ := relS_uniform m hcov
  refine loopS_complete_from (D := D) (B := fun j => j < m) hm0 rfl (fun j hj => hj)
    fun d j hd hj hK hnext => ?_
  have h1 := hD j hj
  have h2 := hcda j hj
  have hl' := hl j hj
  match hr : rt j, hl' with
  | [r0, r1, r2, r3], _ =>
    rw [hr] at h1 h2
    exact loop100S_back d j (relNB_mono coreProgram hd _ _ _ h1) h2 hK hnext

end
end LeanVM.Guest.B1.Main
