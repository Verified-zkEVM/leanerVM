/-
  LeanVM.Guest.B1.Main.LoopsAtS

  `LoopsAt.lean` under any semantics of `BLAKE2S` (`S : BlakeSem`).
-/

module

public import LeanVM.Guest.B1.Main.LoopsAt
public import LeanVM.Guest.B1.Main.LoopsCS
public import LeanVM.Guest.B1.Main.MainCS
public import LeanVM.Guest.B1.Main.LoopAtS

/-!
# `LoopsAt.lean` under any `BLAKE2S` semantics

Each definition and lemma of `LoopsAt.lean` that mentions the semantics, with `S : BlakeSem` a
parameter and a `S` in its name.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest.B1 (DisjL disj_nil disj_append bufL_disj Within LowDef CompleteAtB CompleteRelB Returns Kid CallsMatch
  OutsOk relAtIn_dmono Meaning_verify_lean_xmss Meaning_verify_sig_lean_sphincs kidsBound)

@[expose] public section

variable {S : BlakeSem}

variable {fs : String → ℕ} {cert : String → V → ℕ} {rd : Reader}

/-! ## The hint-filling loops -/

/-- **A quiet loop holding on every memory is complete** at every frame pointer, within the bound
`B` of its valid trees. -/
theorem quietLoopS_completeAt {f : String} (hS : coreProgram.QuietIn [f]) (κ : ℕ) (Lin : Layout)
    {args : List E} (h : ∀ rd, coreProgram.RelB S rd f args []) {B : ℕ}
    (hB : ∀ (rd : Reader) (t : Tree), t.name = f → t.ValidB S coreProgram rd args [] →
      t.BufsOk coreProgram → t.total fs ≤ B) :
    CompleteAtBS S fs cert κ f Lin args (Returns []) B := by
  obtain ⟨n, hn⟩ := relAtInB_uniform_quiet (fs := fs) (cert := cert) coreProgram_wf coreProgram_fresh hS
    (List.mem_singleton_self f) (h fun _ => none)
  intro fp
  have hnB : n ≤ B := by
    obtain ⟨t, hname, hv, hbo, -, ht, -⟩ := hn fp (RegionL Lin) (fun _ => none) fun A hA => by simp at hA
    rw [← ht]; exact hB _ t hname hv hbo
  refine ⟨n, [], [], [], ⟨rfl, rfl⟩, fun q hq => by simp at hq, disj_nil, hnB, fun rd _ _ => ?_⟩
  refine relAtInS_dmono (hn fp (RegionL Lin) rd fun A hA => by simp at hA) fun i hi => ?_
  obtain ⟨q, hq, _⟩ := hi; simp at hq

/-- `__loop0`'s valid trees over `m` iterations. -/
theorem loop0S_total {rd : Reader} {m : ℕ} {rest : List E} {t : Tree} {rets : List E} (hm : 0 < m)
    (hn : t.name = "__loop0") (hv : t.ValidB S coreProgram rd (1 :: gen ^ m :: rest) rets)
    (hbo : t.BufsOk coreProgram) : t.total fs ≤ m * fs "__loop0" + fs "__loop0" :=
  leafLoopS_total find_loop0 core30_split rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (mem_of_getElem? 4 rfl) (mem_of_getElem? 5 rfl) (mem_of_getElem? 6 rfl) (mem_of_getElem? 7 rfl)
    (mem_of_getElem? 8 rfl) hm hn hv hbo

/-- `__loop1`'s valid trees over `m` iterations. -/
theorem loop1S_total {rd : Reader} {m : ℕ} {rest : List E} {t : Tree} {rets : List E} (hm : 0 < m)
    (hn : t.name = "__loop1") (hv : t.ValidB S coreProgram rd (1 :: gen ^ m :: rest) rets)
    (hbo : t.BufsOk coreProgram) : t.total fs ≤ m * fs "__loop1" + fs "__loop1" :=
  leafLoopS_total find_loop1 core31_split rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (mem_of_getElem? 5 rfl) (mem_of_getElem? 6 rfl) (mem_of_getElem? 7 rfl) (mem_of_getElem? 8 rfl)
    (mem_of_getElem? 9 rfl) hm hn hv hbo

/-- `__loop2`'s valid trees over `m` iterations. -/
theorem loop2S_total {rd : Reader} {m : ℕ} {rest : List E} {t : Tree} {rets : List E} (hm : 0 < m)
    (hn : t.name = "__loop2") (hv : t.ValidB S coreProgram rd (1 :: gen ^ m :: rest) rets)
    (hbo : t.BufsOk coreProgram) : t.total fs ≤ m * fs "__loop2" + fs "__loop2" :=
  leafLoopS_total find_loop2 core32_split rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (mem_of_getElem? 5 rfl) (mem_of_getElem? 6 rfl) (mem_of_getElem? 7 rfl) (mem_of_getElem? 8 rfl)
    (mem_of_getElem? 9 rfl) hm hn hv hbo

/-! ## `__loop3` -/

theorem loop3S_holds {C : CallRel} (hl : LowDef 16 rd) {x N cover table : E} {M : ℕ}
    (hM : M ≤ 2 ^ 16) {s : ℕ} (hs : s < M) (hmark : LoadHolds rd cover s x)
    (hv : C "verify_lean_xmss" [table * gen ^ (4 * s)] []) (hK : IsInK (x * gen + N))
    (hnext : x * gen + N ≠ 0 → C "__loop3" [x * gen, N, gen ^ M, cover, table] []) :
    Stmt.HoldsListB S C rd (loop3Val rd x N M cover table s) (Fn.body Data.core33) False
      (fun rs => rs = []) := by
  simp only [show Fn.body Data.core33 = Data.core33.body from rfl, Data.core33.body,
    Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, List.map_cons, List.map_nil, word_gen, loop3Val]
  b1_look
  simp only [true_and, and_true]
  exact ⟨⟨loadHolds_cellAt_gen hl (by omega), gen_pow_mul_ginv s hs,
      loadHolds_cellAt_gen hl (by omega)⟩,
    by rw [loadHolds_mul_gen_pow, Nat.add_zero]; exact hmark, by rw [gen_pow_four]; exact hv, hK,
    hnext⟩

/-- **`__loop3`, placed**: iteration `c < m` marks slot `sl c` of the leanXMSS region `g^M` of the
coverage table at `cb` with `g^c`, and verifies the claim at `tb·g^(4·sl c)`; the marks are words
of `Lin`, and the claims' signatures verify on every memory holding it; each verification within
`Bx`. -/
theorem loop3S_completeAt {κ Bx : ℕ} {Px : Reader → List E → List E → Prop}
    (H : CompleteRelBS S fs cert κ "verify_lean_xmss" Px Bx)
    (hκ : 16 ≤ κ) {M m cb tb : ℕ} (hM : M ≤ 2 ^ 16) (hm : m < 2 ^ 16) (hm0 : 0 < m) (sl : ℕ → ℕ)
    (hs : ∀ c < m, sl c < M) (Lin : Layout) (hmark : ∀ c < m, CellL Lin (cb + sl c) (gen ^ c))
    (hv : ∀ c < m, ∀ rd, LowDef κ rd → MemL rd Lin →
      Px rd [ofK (gpow tb) * gen ^ (4 * sl c)] []) :
    CompleteAtBS S fs cert κ "__loop3" Lin [1, gen ^ m, gen ^ M, ofK (gpow cb), ofK (gpow tb)]
      (Returns []) (m * (fs "__loop3" + Bx) + fs "__loop3") := by
  have h := completeAtS_loop (S := S) (fs := fs) (cert := cert) (f := "__loop3") κ Lin
    (fun j => [gen ^ j, gen ^ m, gen ^ M, ofK (gpow cb), ofK (gpow tb)]) m (fun _ => Bx)
    (fun j hj fp mt => ?_) 0 hm0
  · rw [loopSum_const, Nat.sub_zero] at h; simpa using h
  obtain ⟨p1, p2, p3, p4, p5⟩ := loop3_parts
  refine Exists.elim (loopStepS_straight (fs := fs) (cert := cert) find_loop3 loop3_isLoop
    core33_split p1 p2 p3 κ Lin _ _ _ _ p4
    [⟨"verify_lean_xmss", true, [ofK (gpow tb) * gen ^ (4 * sl j)], Lin, Returns []⟩] (fun _ => Bx)
    (fun k hk _ => by
      rw [List.mem_singleton] at hk; subst hk
      exact H _ _ Lin fun rd hl hL => hv j hj rd hl hL)
    (fun k hk q hq => by rw [List.mem_singleton] at hk; subst hk; exact hq)
    [gen ^ (j + 1), gen ^ m, gen ^ M, ofK (gpow cb), ofK (gpow tb)] (decide (j + 1 ≠ m)) fp mt
    (fun rd hl hL outs ho => ?_)) fun n ⟨L, hW, hD, hNb, hS⟩ =>
      ⟨n, L, hW, hD, by simpa [kidsBound] using hNb, fun rd hl hL ht hn =>
        hS rd hl hL (fun h => ht (by simp at h; omega)) fun h => hn (by simpa using h)⟩
  match outs, ho with
  | [o], ⟨ho1, _⟩ =>
    obtain ⟨hr1, -⟩ := ho1 rfl
    have hl16 : LowDef 16 rd := hl.mono hκ
    have hsj := hs j hj
    refine ⟨loop3Val rd (gen ^ j) (gen ^ m) M (ofK (gpow cb)) (ofK (gpow tb)) (sl j), ?_,
      loop3S_holds (C := fun _ _ _ => True) hl16 hM hsj ((hmark j hj).load hL) trivial
        (isInK_add (isInK_mul (gen_pow_isInK j) (by simpa using gen_pow_isInK 1)) (gen_pow_isInK _))
        (fun _ => trivial), ?_, ?_, ?_, ?_⟩
    · simp only [show Fn.params Data.core33 = [.n 0, .n 1, .n 2, .n 3, .n 4] from rfl,
        List.map_cons, List.map_nil, loop3Val]; b1_look
    · simp only [List.map_cons, List.map_nil, mkCall, CallsMatch, true_and, forall_const, and_true]
      simp only [loop3Val]; b1_look
      exact ⟨by rw [gen_pow_four], hr1.symm⟩
    · simp only [loop3Val]; b1_look
      exact gen_pow_succ_add_ne (by omega) (by omega)
    · simp only [List.map_cons, List.map_nil, loop3Val]; b1_look
      rw [gen_pow_mul_gen]
    · intro q hq
      rw [p5, List.mem_singleton] at hq; subst hq
      simp only [loop3Val]; b1_look
      refine ⟨cb + sl j, ?_, (hmark j hj).region⟩
      rw [ofK_gpow_mul_gen, addr_ofK, Nat.add_zero]

/-! ## `__loop4` -/

theorem loop4S_holds {C : CallRel} (hl : LowDef 16 rd) {x N cover w table : E} {M Lx : ℕ}
    (hM : M ≤ 2 ^ 16) {s : ℕ} (hs : s < M) (hmark : LoadHolds rd cover (Lx + s) (w * x))
    (hv : C "verify_sig_lean_sphincs" [table * gen ^ (4 * s)] []) (hK : IsInK (x * gen + N))
    (hnext : x * gen + N ≠ 0 → C "__loop4" [x * gen, N, gen ^ M, cover, gen ^ Lx, w, table] []) :
    Stmt.HoldsListB S C rd (loop4Val rd x N M cover Lx w table s) (Fn.body Data.core34) False
      (fun rs => rs = []) := by
  simp only [show Fn.body Data.core34 = Data.core34.body from rfl, Data.core34.body,
    Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, List.map_cons, List.map_nil, word_gen, loop4Val]
  b1_look
  simp only [true_and, and_true]
  exact ⟨⟨loadHolds_cellAt_gen hl (by omega), gen_pow_mul_ginv s hs,
      loadHolds_cellAt_gen hl (by omega)⟩,
    by rw [← pow_add, loadHolds_mul_gen_pow, Nat.add_zero]; exact hmark,
    by rw [gen_pow_four]; exact hv, hK, hnext⟩

/-- **`__loop4`, placed**: iteration `c < m` marks slot `Lx + sl c` of the coverage table at `cb`
with `w·g^c`, `sl c` in the leanSPHINCS region `g^M`, and verifies the claim at
`tb·g^(4·sl c)`, each verification within `Bs`. -/
theorem loop4S_completeAt {κ Bs : ℕ} {Ps : Reader → List E → List E → Prop}
    (H : CompleteRelBS S fs cert κ "verify_sig_lean_sphincs" Ps Bs)
    (hκ : 16 ≤ κ) {M Lx m cb tb : ℕ} {w : E} (hM : M ≤ 2 ^ 16) (hm : m < 2 ^ 16) (hm0 : 0 < m)
    (sl : ℕ → ℕ) (hs : ∀ c < m, sl c < M) (Lin : Layout)
    (hmark : ∀ c < m, CellL Lin (cb + (Lx + sl c)) (w * gen ^ c))
    (hv : ∀ c < m, ∀ rd, LowDef κ rd → MemL rd Lin →
      Ps rd [ofK (gpow tb) * gen ^ (4 * sl c)] []) :
    CompleteAtBS S fs cert κ "__loop4" Lin
      [1, gen ^ m, gen ^ M, ofK (gpow cb), gen ^ Lx, w, ofK (gpow tb)] (Returns [])
      (m * (fs "__loop4" + Bs) + fs "__loop4") := by
  have h := completeAtS_loop (S := S) (fs := fs) (cert := cert) (f := "__loop4") κ Lin
    (fun j => [gen ^ j, gen ^ m, gen ^ M, ofK (gpow cb), gen ^ Lx, w, ofK (gpow tb)]) m (fun _ => Bs)
    (fun j hj fp mt => ?_) 0 hm0
  · rw [loopSum_const, Nat.sub_zero] at h; simpa using h
  obtain ⟨p1, p2, p3, p4, p5⟩ := loop4_parts
  refine Exists.elim (loopStepS_straight (fs := fs) (cert := cert) find_loop4 loop4_isLoop
    core34_split p1 p2 p3 κ Lin _ _ _ _ p4
    [⟨"verify_sig_lean_sphincs", true, [ofK (gpow tb) * gen ^ (4 * sl j)], Lin, Returns []⟩]
    (fun _ => Bs) (fun k hk _ => by
      rw [List.mem_singleton] at hk; subst hk
      exact H _ _ Lin fun rd hl hL => hv j hj rd hl hL)
    (fun k hk q hq => by rw [List.mem_singleton] at hk; subst hk; exact hq)
    [gen ^ (j + 1), gen ^ m, gen ^ M, ofK (gpow cb), gen ^ Lx, w, ofK (gpow tb)] (decide (j + 1 ≠ m))
    fp mt (fun rd hl hL outs ho => ?_)) fun n ⟨L, hW, hD, hNb, hS⟩ =>
      ⟨n, L, hW, hD, by simpa [kidsBound] using hNb, fun rd hl hL ht hn =>
        hS rd hl hL (fun h => ht (by simp at h; omega)) fun h => hn (by simpa using h)⟩
  match outs, ho with
  | [o], ⟨ho1, _⟩ =>
    obtain ⟨hr1, -⟩ := ho1 rfl
    have hl16 : LowDef 16 rd := hl.mono hκ
    have hsj := hs j hj
    have e15 : ofK (gpow cb) * (gen ^ Lx * gen ^ sl j) = ofK (gpow (cb + (Lx + sl j))) := by
      rw [← pow_add, ofK_gpow_mul_gen]
    refine ⟨loop4Val rd (gen ^ j) (gen ^ m) M (ofK (gpow cb)) Lx w (ofK (gpow tb)) (sl j), ?_,
      loop4S_holds (C := fun _ _ _ => True) hl16 hM hsj ((hmark j hj).load hL) trivial
        (isInK_add (isInK_mul (gen_pow_isInK j) (by simpa using gen_pow_isInK 1)) (gen_pow_isInK _))
        (fun _ => trivial), ?_, ?_, ?_, ?_⟩
    · simp only [show Fn.params Data.core34 = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6] from rfl,
        List.map_cons, List.map_nil, loop4Val]; b1_look
    · simp only [List.map_cons, List.map_nil, mkCall, CallsMatch, true_and, forall_const, and_true]
      simp only [loop4Val]; b1_look
      exact ⟨by rw [gen_pow_four], hr1.symm⟩
    · simp only [loop4Val]; b1_look
      exact gen_pow_succ_add_ne (by omega) (by omega)
    · simp only [List.map_cons, List.map_nil, loop4Val]; b1_look
      rw [gen_pow_mul_gen]
    · intro q hq
      rw [p5, List.mem_singleton] at hq; subst hq
      simp only [loop4Val]; b1_look
      refine ⟨cb + (Lx + sl j), ?_, (hmark j hj).region⟩
      rw [e15, addr_ofK, Nat.add_zero]

/-! ## `__loop100` -/

theorem loop100S_holds {C : CallRel} {x N cda roots dcov dslots base nsub r0 r1 r2 r3 : E}
    (hcov : C "cover_da_root" [roots, dcov, dslots, base * nsub * x] [r0, r1, r2, r3])
    (hcda : ReadsAt rd (cda * (x * x * (x * x))) [r0, r1, r2, r3]) (hK : IsInK (x * gen + N))
    (hnext : x * gen + N ≠ 0 → C "__loop100" [x * gen, N, cda, roots, dcov, dslots, base, nsub] []) :
    Stmt.HoldsListB S C rd (loop100Val x N cda roots dcov dslots base nsub r0 r1 r2 r3)
      (Fn.body Data.core573) False (fun rs => rs = []) := by
  simp only [show Fn.body Data.core573 = Data.core573.body from rfl, Data.core573.body,
    Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, List.map_cons, List.map_nil, word_gen, loop100Val]
  b1_look
  simp only [true_and, and_true]
  exact ⟨hcov, readsAt_getD' hcda (k := 0) (by simp), readsAt_getD' hcda (k := 1) (by simp),
    readsAt_getD' hcda (k := 2) (by simp), readsAt_getD' hcda (k := 3) (by simp), hK, hnext⟩

/-- **`__loop100`, placed**: iteration `c < m` marks its DA slot by `cover_da_root` with
`base·nsub·g^c` in DA slot `sl c`, which returns the root's cells `rt c`, stored at `cdab + 4c`
(words of `Lin`), each `cover_da_root` within `Bc`. -/
theorem loop100S_completeAt {κ Bc : ℕ} (H : ∀ i, CompleteRelBS S fs cert κ "cover_da_root" (CoverPreAt i) Bc)
    {m cdab : ℕ} {roots dcov dslots base nsub : E} (hm : m < 2 ^ 16) (hm0 : 0 < m) (Lin : Layout)
    (rt : ℕ → List E) (hlen : ∀ c < m, (rt c).length = 4) (sl : ℕ → ℕ)
    (hcov : ∀ c < m, ∀ rd, LowDef κ rd → MemL rd Lin →
      CoverPreAt (sl c) rd [roots, dcov, dslots, base * nsub * gen ^ c] (rt c))
    (hcda : ∀ c < m, ∀ k < 4, CellL Lin (cdab + 4 * c + k) ((rt c).getD k 0)) :
    CompleteAtBS S fs cert κ "__loop100" Lin
      [1, gen ^ m, ofK (gpow cdab), roots, dcov, dslots, base, nsub] (Returns [])
      (m * (fs "__loop100" + Bc) + fs "__loop100") := by
  have h := completeAtS_loop (S := S) (fs := fs) (cert := cert) (f := "__loop100") κ Lin
    (fun j => [gen ^ j, gen ^ m, ofK (gpow cdab), roots, dcov, dslots, base, nsub]) m (fun _ => Bc)
    (fun j hj fp mt => ?_) 0 hm0
  · rw [loopSum_const, Nat.sub_zero] at h; simpa using h
  obtain ⟨p1, p2, p3, p4, p5⟩ := loop100_parts
  refine Exists.elim (loopStepS_straight (fs := fs) (cert := cert) find_loop100 loop100_isLoop
    core573_split p1 p2 p3 κ Lin _ _ _ _ p4
    [⟨"cover_da_root", true, [roots, dcov, dslots, base * nsub * gen ^ j], Lin, Returns (rt j)⟩]
    (fun _ => Bc) (fun k hk _ => by
      rw [List.mem_singleton] at hk; subst hk
      exact H (sl j) _ _ Lin fun rd hl hL => hcov j hj rd hl hL)
    (fun k hk q hq => by rw [List.mem_singleton] at hk; subst hk; exact hq)
    [gen ^ (j + 1), gen ^ m, ofK (gpow cdab), roots, dcov, dslots, base, nsub] (decide (j + 1 ≠ m))
    fp mt (fun rd hl hL outs ho => ?_)) fun n ⟨L, hW, hD, hNb, hS⟩ =>
      ⟨n, L, hW, hD, by simpa [kidsBound] using hNb, fun rd hl hL ht hn =>
        hS rd hl hL (fun h => ht (by simp at h; omega)) fun h => hn (by simpa using h)⟩
  have hcj := hcda j hj
  obtain ⟨r0, r1, r2, r3, hr⟩ : ∃ a b c d, rt j = [a, b, c, d] := by
    have := hlen j hj
    match rt j, this with
    | [a, b, c, d], _ => exact ⟨a, b, c, d, rfl⟩
  rw [hr] at hcj ho ⊢
  match outs, ho with
  | [o], ⟨ho1, _⟩ =>
    obtain ⟨hr1, -⟩ := ho1 rfl
    have e10 : ∀ k, ofK (gpow cdab) * (gen ^ j * gen ^ j * (gen ^ j * gen ^ j)) * gen ^ k =
        ofK (gpow (cdab + 4 * j + k)) := fun k => by
      rw [gen_pow_four, ofK_gpow_mul_gen, ofK_gpow_mul_gen]
    have hrd : ReadsAt rd (ofK (gpow cdab) * (gen ^ j * gen ^ j * (gen ^ j * gen ^ j)))
        [r0, r1, r2, r3] := by
      rw [gen_pow_four, ofK_gpow_mul_gen]
      intro k hk
      simp only [List.length_cons, List.length_nil] at hk
      have := (hcj k hk).load hL
      interval_cases k <;> simpa using this
    refine ⟨loop100Val (gen ^ j) (gen ^ m) (ofK (gpow cdab)) roots dcov dslots base nsub r0 r1 r2 r3,
      ?_, loop100S_holds (C := fun _ _ _ => True) trivial hrd
        (isInK_add (isInK_mul (gen_pow_isInK j) (by simpa using gen_pow_isInK 1)) (gen_pow_isInK _))
        (fun _ => trivial), ?_, ?_, ?_, ?_⟩
    · simp only [show Fn.params Data.core573 = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7]
        from rfl, List.map_cons, List.map_nil, loop100Val]; b1_look
    · simp only [List.map_cons, List.map_nil, mkCall, CallsMatch, true_and, forall_const, and_true]
      simp only [loop100Val]; b1_look
      exact ⟨trivial, hr1.symm⟩
    · simp only [loop100Val]; b1_look
      exact gen_pow_succ_add_ne (by omega) (by omega)
    · simp only [List.map_cons, List.map_nil, loop100Val]; b1_look
      rw [gen_pow_mul_gen]
    · intro q hq
      rw [p5] at hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      have hreg : ∀ k < 4, RegionL Lin (cdab + 4 * j + k) := fun k hk => by
        have := (hcj k hk).region; exact this
      rcases hq with rfl | rfl | rfl | rfl <;> simp only [loop100Val] <;> b1_look
      · exact ⟨_, by rw [← mul_one (ofK _ * _), ← pow_zero gen, e10, addr_ofK], hreg 0 (by omega)⟩
      · exact ⟨_, by rw [← mul_one (ofK _ * _), ← pow_zero gen, e10, addr_ofK], hreg 1 (by omega)⟩
      · exact ⟨_, by rw [← mul_one (ofK _ * _), ← pow_zero gen, e10, addr_ofK], hreg 2 (by omega)⟩
      · exact ⟨_, by rw [← mul_one (ofK _ * _), ← pow_zero gen, e10, addr_ofK], hreg 3 (by omega)⟩

end
end LeanVM.Guest.B1.Main
