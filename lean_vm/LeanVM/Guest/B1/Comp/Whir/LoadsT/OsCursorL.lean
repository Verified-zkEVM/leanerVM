/-
  LeanVM.Guest.B1.Comp.Whir.LoadsT.OsCursorL

  `open_stacked`'s body templates, at a valuation its path holds of: where each leaves the
  stream's cursor and which stream words its loads and its callees' read.
-/

module

public import LeanVM.Guest.B1.Comp.Whir.LoadsT.KidsL
public import LeanVM.Guest.B1.Whir.StackedBlocks

/-!
# The stacked opening's cursor, template by template

`osBody cfg` (`Whir/StackedT.lean`) is generated block by block from a running `OsSt`, whose
`cb`, `co` name the stream's cursor: the pointer value `cb` and the words read since it, `co`.
At a valuation `σ` whose path holds (`OsLdCtx`: the body's atoms hold, its loads and its callees'
trees' loads are among `Ld`), `OsCurL σ c s p` says the cursor is `g^(c+p)`, and `OsRdL Ld c p n`
that the stream words `p ..< p + n` at `g^c` are loaded. Each template advances the cursor by the
words it reads, those words loaded: `osFsNext` and `osGrind` one, by their own load; `osFold` two,
by `opening_fold`'s (`osL_fold`); `osFinal` the final message's, by its callee's (`osL_fm`);
`osOodSample` three; `osCommit` two and its samples'; `osQueries` two; the others none. Hence a
level (`osL_level`), the levels (`osL_levels`), the tail (`osL_tail`) and the head (`osL_head`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- **What the cursor tracking assumes of a node**: the body's atoms hold at `σ`, its loads are
among `Ld`, and each call of the body has a callee tree valid on its words whose loads are among
`Ld`. -/
structure OsLdCtx (S : BlakeSem) (rd : Reader) (σ : Val) (pre : List Stmt) (Ld : List (K × E)) :
    Prop where
  atoms : ∀ a, Stmt.atom a ∈ pre → a.HoldsB S rd σ
  loads : ∀ d p off, Stmt.atom (.load d p off) ∈ pre →
    ((σ p).limb 0 * Parameters.gpow off, σ d) ∈ Ld
  calls : ∀ f args rets, Stmt.call f args rets ∈ pre → ∃ k : Tree, k.name = f ∧
    k.ValidB S coreProgram rd (args.map σ) (rets.map σ) ∧ ∀ q ∈ k.loadEqns coreProgram, q ∈ Ld

/-- **The cursor of `s` is `g^(c+p)`**: its pointer `g^(c+q)`, `co` words read since. -/
def OsCurL (σ : Val) (c : ℕ) (s : OsSt) (p : ℕ) : Prop :=
  ∃ q, p = q + s.co ∧ σ (.n s.cb) = ofK (Parameters.gpow c) * gen ^ q

/-- **The stream words `p ..< p + n` at `g^c` are loaded.** -/
def OsRdL (Ld : List (K × E)) (c p n : ℕ) : Prop :=
  ∀ j < n, ∃ v, (Parameters.gpow (c + (p + j)), v) ∈ Ld

theorem OsRdL.zero {Ld : List (K × E)} {c p : ℕ} : OsRdL Ld c p 0 := fun _ h => absurd h (by omega)

theorem OsRdL.append {Ld : List (K × E)} {c p n m : ℕ} (h1 : OsRdL Ld c p n)
    (h2 : OsRdL Ld c (p + n) m) : OsRdL Ld c p (n + m) := by
  intro j hj
  by_cases h : j < n
  · exact h1 j h
  · obtain ⟨v, hv⟩ := h2 (j - n) (by omega)
    exact ⟨v, by rwa [show p + n + (j - n) = p + j by omega] at hv⟩

/-- Membership in a template's statements, from the body's. -/
abbrev OsSub (l pre : List Stmt) : Prop := ∀ x ∈ l, x ∈ pre

theorem OsSub.left {l1 l2 pre : List Stmt} (h : OsSub (l1 ++ l2) pre) : OsSub l1 pre :=
  fun x hx => h x (List.mem_append_left _ hx)

theorem OsSub.right {l1 l2 pre : List Stmt} (h : OsSub (l1 ++ l2) pre) : OsSub l2 pre :=
  fun x hx => h x (List.mem_append_right _ hx)

/-- The address of word `off` past `g^(a+m)`. -/
theorem osL_addr (a m off : ℕ) :
    (ofK (Parameters.gpow a) * gen ^ m).limb 0 * Parameters.gpow off = Parameters.gpow (a + m + off) := by
  rw [gen_pow_eq_ofK, ← ofK_mul]
  simp [Parameters.gpow, pow_add]

section
variable {S : BlakeSem} {rd : Reader} {σ : Val} {pre : List Stmt} {Ld : List (K × E)} {c : ℕ}

/-- `fs_next`: one word at the cursor. -/
theorem osL_fsNext (X : OsLdCtx S rd σ pre Ld) {s : OsSt} {p : ℕ} (hs : OsSub (osFsNext s).1 pre)
    (h : OsCurL σ c s p) : OsCurL σ c (osFsNext s).2 (p + 1) ∧ OsRdL Ld c p 1 := by
  obtain ⟨q, rfl, hq⟩ := h
  refine ⟨⟨q, by simp only [osFsNext]; omega, by simpa only [osFsNext] using hq⟩, fun j hj => ?_⟩
  obtain rfl : j = 0 := by omega
  refine ⟨σ (.n s.k), ?_⟩
  have hm : Stmt.atom (.load (.n s.k) (.n s.cb) s.co) ∈ pre := hs _ (by simp [osFsNext, fsNextT])
  have := X.loads _ _ _ hm
  rwa [hq, osL_addr, show c + q + s.co = c + (q + s.co + 0) by omega] at this

/-- A pointer materialized at the cursor's offset. -/
theorem osL_mat (X : OsLdCtx S rd σ pre Ld) {base off k q : ℕ} (hs : OsSub (osMat base off k).1 pre)
    (hb : σ (.n base) = ofK (Parameters.gpow c) * gen ^ q) (hoff : off < 2 ^ 128) :
    σ (.n (osMat base off k).2.1) = ofK (Parameters.gpow c) * gen ^ (q + off) := by
  unfold osMat at hs ⊢
  split_ifs at hs ⊢ with h0
  · rw [h0, Nat.add_zero]; exact hb
  · have a0 := X.atoms (.const (.n k) (osGw off)) (hs _ (by simp))
    have a1 := X.atoms (.mul (.n (k + 1)) (.n base) (.n k)) (hs _ (by simp))
    simp only [Atom.HoldsB] at a0 a1
    rw [a1, a0, hb, os_gw_eq hoff, mul_assoc, ← pow_add]

/-- `opening_fold`: the two words at the cursor, by its callee. -/
theorem osL_fold1 (X : OsLdCtx S rd σ pre Ld) {s : OsSt} {fch fo p : ℕ} (hs : OsSub (osFold s fch fo).1 pre)
    (h : OsCurL σ c s p) (hp : p < 2 ^ 128) :
    OsCurL σ c (osFold s fch fo).2 (p + 2) ∧ OsRdL Ld c p 2 := by
  obtain ⟨q, rfl, hq⟩ := h
  have hm := osL_mat X (base := s.cb) (off := s.co) (k := s.k) (fun x hx => hs x (by
    simp only [osFold]; exact List.mem_append_left _ hx)) hq (by omega)
  set m := osMat s.cb s.co s.k with hmd
  have hc : Stmt.call "opening_fold" [.n s.f0, .n s.f1, .n m.2.1, .n s.c, .n s.b, .n s.a]
      ((List.range 7).map fun j => .n (m.2.2 + j)) ∈ pre := hs _ (by simp [osFold, hmd])
  obtain ⟨kt, hkn, hkv, hkl⟩ := X.calls _ _ _ hc
  obtain ⟨hret, hld⟩ := osL_fold hkn hkv
  simp only [List.map_cons, List.map_nil, List.getD_cons_succ, List.getD_cons_zero, List.map_map,
    Function.comp_def] at hret hld
  have hr2 : σ (.n (m.2.2 + 2)) = ofK (Parameters.gpow c) * gen ^ (q + s.co + 2) := by
    have e : ((List.range 7).map fun j => σ (.n (m.2.2 + j))).getD 2 0 = σ (.n (m.2.2 + 2)) := by
      simp
    rw [← e, hret, hm, mul_assoc, ← pow_add]
  refine ⟨⟨q + s.co + 2, by simp [osFold], by simpa [osFold] using hr2⟩, fun j hj => ?_⟩
  obtain ⟨v, hv⟩ := hld j hj
  refine ⟨v, ?_⟩
  have := hkl _ hv
  rwa [hm, osL_addr, show c + (q + s.co) + j = c + (q + s.co + j) by omega] at this

/-- `n` rounds of `opening_fold`. -/
theorem osL_folds (X : OsLdCtx S rd σ pre Ld) (fch : ℕ) : ∀ (n fo : ℕ) (s : OsSt) (p : ℕ),
    OsSub (osFolds fch fo n s).1 pre → OsCurL σ c s p → p + 2 * n < 2 ^ 128 →
    OsCurL σ c (osFolds fch fo n s).2 (p + 2 * n) ∧ OsRdL Ld c p (2 * n)
  | 0, _, _, _, _, h, _ => ⟨by simpa [osFolds] using h, OsRdL.zero⟩
  | n + 1, fo, s, p, hs, h, hp => by
    simp only [osFolds] at hs ⊢
    obtain ⟨h1, r1⟩ := osL_fold1 X hs.left h (by omega)
    obtain ⟨h2, r2⟩ := osL_folds X fch n (fo + 1) _ (p + 2) hs.right h1 (by omega)
    refine ⟨by rwa [show p + 2 * (n + 1) = p + 2 + 2 * n by ring], ?_⟩
    rw [show 2 * (n + 1) = 2 + 2 * n by ring]
    exact r1.append r2

/-- `opening_final_message__L{n}`: the `n` words at the cursor, by its callee. -/
theorem osL_final (X : OsLdCtx S rd σ pre Ld) {name : String} {fmsg : ℕ} {s : OsSt} {p : ℕ}
    {fn : Fn} (n : ℕ) (hn64 : n < 64) (hfind : coreProgram.find? name = some fn)
    (hparams : fn.params = [.n 0, .n 1, .n 2, .n 3]) (hbody : fn.body = ofmBody n)
    (hs : OsSub (osFinal name fmsg s).1 pre) (h : OsCurL σ c s p) (hp : p < 2 ^ 128) :
    OsCurL σ c (osFinal name fmsg s).2 (p + n) ∧ OsRdL Ld c p n := by
  obtain ⟨q, rfl, hq⟩ := h
  have hm := osL_mat X (base := s.cb) (off := s.co) (k := s.k) (fun x hx => hs x (by
    simp only [osFinal]; exact List.mem_append_left _ hx)) hq (by omega)
  set m := osMat s.cb s.co s.k with hmd
  have hc : Stmt.call name [.n s.f0, .n s.f1, .n m.2.1, .n fmsg] [.n m.2.2, .n (m.2.2 + 1), .n (m.2.2 + 2)] ∈ pre :=
    hs _ (by simp [osFinal, hmd])
  obtain ⟨kt, hkn, hkv, hkl⟩ := X.calls _ _ _ hc
  obtain ⟨hret, hld⟩ := osL_fm n hn64 hfind hparams hbody hkn hkv
  simp only [List.map_cons, List.map_nil, List.getD_cons_succ, List.getD_cons_zero] at hret hld
  refine ⟨⟨q + s.co + n, by simp [osFinal], by
    simp only [osFinal, ← hmd]; rw [hret, hm, mul_assoc, ← pow_add]⟩, fun j hj => ?_⟩
  obtain ⟨v, hv⟩ := hld j hj
  refine ⟨v, ?_⟩
  have := hkl _ hv
  rwa [hm, osL_addr, show c + (q + s.co) + j = c + (q + s.co + j) by omega] at this

theorem OsCurL.of_eq {s s' : OsSt} {p p' : ℕ} (h : OsCurL σ c s p) (hcb : s'.cb = s.cb)
    (hco : s'.co = s.co) (hp : p' = p) : OsCurL σ c s' p' := by
  obtain ⟨q, hq, hσ⟩ := h
  exact ⟨q, by rw [hp, hq, hco], by rw [hcb]; exact hσ⟩

theorem OsRdL.cat {p q n m k : ℕ} (h1 : OsRdL Ld c p n) (h2 : OsRdL Ld c q m) (hq : q = p + n)
    (hk : k = n + m) : OsRdL Ld c p k := by
  subst hq hk; exact h1.append h2

/-- An out-of-domain sample: its value and intro's three words. -/
theorem osL_oodSample (X : OsLdCtx S rd σ pre Ld) {oz so logCols oodz ood : ℕ} {s : OsSt} {p : ℕ}
    (hs : OsSub (osOodSample oz so logCols oodz ood s).1 pre) (h : OsCurL σ c s p) :
    OsCurL σ c (osOodSample oz so logCols oodz ood s).2 (p + 3) ∧ OsRdL Ld c p 3 := by
  have e := hs.left
  obtain ⟨h1, r1⟩ := osL_fsNext X e.left.left.right (h.of_eq rfl rfl rfl)
  obtain ⟨h2, r2⟩ := osL_fsNext X e.left.right h1
  obtain ⟨h3, r3⟩ := osL_fsNext X e.right h2
  exact ⟨h3.of_eq rfl rfl (by omega), (r1.cat r2 rfl rfl).cat r3 rfl rfl⟩

/-- The out-of-domain samples `os ..< os + n`. -/
theorem osL_oods (X : OsLdCtx S rd σ pre Ld) (lvl logCols oodz ood : ℕ) :
    ∀ (n os : ℕ) (st : OsSt) (p : ℕ), OsSub (osOods lvl logCols oodz ood os n st).1 pre →
    OsCurL σ c st p →
    OsCurL σ c (osOods lvl logCols oodz ood os n st).2 (p + 3 * n) ∧ OsRdL Ld c p (3 * n)
  | 0, _, _, _, _, h => ⟨by simpa [osOods] using h, OsRdL.zero⟩
  | n + 1, os, st, p, hs, h => by
    obtain ⟨h1, r1⟩ := osL_oodSample X hs.left h
    obtain ⟨h2, r2⟩ := osL_oods X lvl logCols oodz ood n (os + 1) _ (p + 3) hs.right h1
    exact ⟨h2.of_eq rfl rfl (by ring), r1.cat r2 rfl (by ring)⟩

/-- The next commitment: its two root words, then its out-of-domain samples. -/
theorem osL_commit (X : OsLdCtx S rd σ pre Ld) {lvl logCols oodNext roots oodz ood : ℕ} {s : OsSt}
    {p : ℕ} (hs : OsSub (osCommit lvl logCols oodNext roots oodz ood s).1 pre) (h : OsCurL σ c s p) :
    OsCurL σ c (osCommit lvl logCols oodNext roots oodz ood s).2 (p + (2 + 3 * oodNext)) ∧
      OsRdL Ld c p (2 + 3 * oodNext) := by
  obtain ⟨h1, r1⟩ := osL_fsNext X hs.left.left.left h
  obtain ⟨h2, r2⟩ := osL_fsNext X hs.left.left.right h1
  obtain ⟨h3, r3⟩ := osL_oods X lvl logCols oodz ood oodNext 0 _ (p + 1 + 1) hs.right
    (h2.of_eq rfl rfl rfl)
  exact ⟨h3.of_eq rfl rfl (by ring), (r1.cat r2 rfl rfl).cat r3 rfl (by ring)⟩

/-- The query nonce: one word at the cursor. -/
theorem osL_grind (X : OsLdCtx S rd σ pre Ld) {bits : ℕ} {s : OsSt} {p : ℕ}
    (hs : OsSub (osGrind bits s).1 pre) (h : OsCurL σ c s p) :
    OsCurL σ c (osGrind bits s).2 (p + 1) ∧ OsRdL Ld c p 1 := by
  obtain ⟨q, rfl, hq⟩ := h
  refine ⟨⟨q, by simp only [osGrind]; omega, by simpa only [osGrind] using hq⟩, fun j hj => ?_⟩
  obtain rfl : j = 0 := by omega
  refine ⟨σ (.n s.k), ?_⟩
  have hm : Stmt.atom (.load (.n s.k) (.n s.cb) s.co) ∈ pre := hs _ (by simp [osGrind])
  have := X.loads _ _ _ hm
  rwa [hq, osL_addr, show c + q + s.co = c + (q + s.co + 0) by omega] at this

/-- The level's queries: the intro's two words. -/
theorem osL_queries (X : OsLdCtx S rd σ pre Ld) {cfg : OsCfg} {lv : OsLvl} {lvl : ℕ} {s : OsSt} {p : ℕ}
    (hs : OsSub (osQueries cfg lv lvl s).1 pre) (h : OsCurL σ c s p) :
    OsCurL σ c (osQueries cfg lv lvl s).2.1 (p + 2) ∧ OsRdL Ld c p 2 := by
  obtain ⟨h1, r1⟩ := osL_fsNext X hs.left.left.right (h.of_eq rfl rfl rfl)
  obtain ⟨h2, r2⟩ := osL_fsNext X hs.left.right h1
  exact ⟨h2.of_eq rfl rfl rfl, r1.cat r2 rfl rfl⟩

theorem osL_oodGlues_cur (lvl lam : ℕ) : ∀ (os n sc : ℕ) (st : OsSt),
    (osOodGlues lvl lam os n sc st).2.1.cb = st.cb ∧ (osOodGlues lvl lam os n sc st).2.1.co = st.co
  | _, 0, _, _ => ⟨rfl, rfl⟩
  | os, n + 1, _, _ => osL_oodGlues_cur lvl lam (os + 1) n _ _

/-- What a final level's message callee is: `ofmBody` of the residual's length. -/
def OsFmOk (cfg : OsCfg) : Prop :=
  ∃ fn : Fn, coreProgram.find? cfg.finalMsg = some fn ∧ fn.params = [.n 0, .n 1, .n 2, .n 3] ∧
    fn.body = ofmBody cfg.yrLen ∧ cfg.yrLen < 64

/-- The words a level reads. -/
def osLvRdL (cfg : OsCfg) (lvl : ℕ) (lv : OsLvl) : ℕ :=
  2 * lv.folds + (if lvl = cfg.yrLevel then cfg.yrLen else 2 + 3 * lv.oodNext) + 3

/-- **A level**: its folds, its message or next commitment, its nonce, its intro. -/
theorem osL_level (X : OsLdCtx S rd σ pre Ld) {cfg : OsCfg} {lvl : ℕ} {lv : OsLvl} {s : OsSt} {p : ℕ}
    (hfm : lvl = cfg.yrLevel → OsFmOk cfg) (hs : OsSub (osLevel cfg lvl lv s).1 pre)
    (h : OsCurL σ c s p) (hp : p + osLvRdL cfg lvl lv < 2 ^ 128) :
    OsCurL σ c (osLevel cfg lvl lv s).2 (p + osLvRdL cfg lvl lv) ∧ OsRdL Ld c p (osLvRdL cfg lvl lv) := by
  unfold osLvRdL at hp ⊢
  have e3 := hs.left.left.left
  obtain ⟨h1, r1⟩ := osL_folds X osFch lv.folds lv.foldsOff s p e3.left.left.left.left.left h
    (by omega)
  have hm := e3.left.left.left.left.right
  have hm2 : OsCurL σ c (if lvl = cfg.yrLevel then osFinal cfg.finalMsg osFmsg
        (osFolds osFch lv.foldsOff lv.folds s).2
      else osCommit lvl lv.logCols lv.oodNext osRoots osOodz osOod (osFolds osFch lv.foldsOff lv.folds s).2).2
        (p + 2 * lv.folds + (if lvl = cfg.yrLevel then cfg.yrLen else 2 + 3 * lv.oodNext)) ∧
      OsRdL Ld c (p + 2 * lv.folds) (if lvl = cfg.yrLevel then cfg.yrLen else 2 + 3 * lv.oodNext) := by
    by_cases hy : lvl = cfg.yrLevel
    · obtain ⟨fn, hf, hpar, hbody, h64⟩ := hfm hy
      simp only [hy, ↓reduceIte] at hm ⊢
      exact osL_final X cfg.yrLen h64 hf hpar hbody hm h1 (by omega)
    · simp only [hy, ↓reduceIte] at hm ⊢
      exact osL_commit X hm h1
  obtain ⟨h2, r2⟩ := hm2
  obtain ⟨h3, r3⟩ := osL_grind X e3.left.left.left.right h2
  obtain ⟨h4, r4⟩ := osL_queries X e3.right (h3.of_eq rfl rfl rfl)
  refine ⟨h4.of_eq ?_ ?_ (by omega), (r1.cat r2 rfl rfl).cat (r3.cat r4 rfl rfl) (by omega) (by omega)⟩
  · by_cases hy : lvl = cfg.yrLevel
    · simp only [osLevel, osGlue, hy, ↓reduceIte]
    · simp only [osLevel, osGlue, hy, ↓reduceIte]
      exact (osL_oodGlues_cur _ _ _ _ _ _).1
  · by_cases hy : lvl = cfg.yrLevel
    · simp only [osLevel, osGlue, hy, ↓reduceIte]
    · simp only [osLevel, osGlue, hy, ↓reduceIte]
      exact (osL_oodGlues_cur _ _ _ _ _ _).2

/-- The words the levels `lvl ..` read. -/
def osLvsCntL (cfg : OsCfg) : ℕ → List OsLvl → ℕ
  | _, [] => 0
  | lvl, lv :: rest => osLvRdL cfg lvl lv + osLvsCntL cfg (lvl + 1) rest

/-- **The levels `lvl ..`.** -/
theorem osL_levels (X : OsLdCtx S rd σ pre Ld) (cfg : OsCfg) :
    ∀ (lvl : ℕ) (lvs : List OsLvl) (s : OsSt) (p : ℕ), (∀ i < lvs.length, lvl + i = cfg.yrLevel → OsFmOk cfg) →
    OsSub (osLevels cfg lvl lvs s).1 pre → OsCurL σ c s p → p + osLvsCntL cfg lvl lvs < 2 ^ 128 →
    OsCurL σ c (osLevels cfg lvl lvs s).2 (p + osLvsCntL cfg lvl lvs) ∧ OsRdL Ld c p (osLvsCntL cfg lvl lvs)
  | _, [], _, _, _, _, h, _ => ⟨h.of_eq rfl rfl rfl, OsRdL.zero⟩
  | lvl, lv :: rest, s, p, hf, hs, h, hp => by
    simp only [osLvsCntL] at hp
    obtain ⟨h1, r1⟩ := osL_level X (fun hy => hf 0 (by simp) (by omega)) hs.left h (by omega)
    obtain ⟨h2, r2⟩ := osL_levels X cfg (lvl + 1) rest _ _
      (fun i hi hy => hf (i + 1) (by simp; omega) (by omega)) hs.right h1 (by omega)
    exact ⟨h2.of_eq rfl rfl (by simp only [osLvsCntL]; omega), r1.cat r2 rfl rfl⟩

/-- **The tail rounds**: two words each. -/
theorem osL_tail (X : OsLdCtx S rd σ pre Ld) {yrLog : ℕ} {s : OsSt} {p : ℕ}
    (hs : OsSub (osTail yrLog s).1 pre) (h : OsCurL σ c s p) (hp : p + 2 * (yrLog - 1) < 2 ^ 128) :
    OsRdL Ld c p (2 * (yrLog - 1)) :=
  (osL_folds X (s.k + 1) (yrLog - 1) 0 { s with k := s.k + 2 } p hs.left.left.left.right
    (h.of_eq rfl rfl rfl) hp).2

/-- **The head**: the first quadratic's two words, from the cursor argument. -/
theorem osL_head (X : OsLdCtx S rd σ pre Ld) {cfg : OsCfg} (hs : OsSub (osHead cfg).1 pre)
    (h5 : σ (.n 5) = ofK (Parameters.gpow c)) :
    OsCurL σ c (osHead cfg).2 2 ∧ OsRdL Ld c 0 2 := by
  have h0 : OsCurL σ c ⟨8, 6, 7, 5, 0, 0, 0, 0, 2⟩ 0 := ⟨0, rfl, by rw [pow_zero, mul_one]; exact h5⟩
  have e := hs.left.left.left.left.left.left.left.left.left.left.left.left.left.left.left
  obtain ⟨h1, r1⟩ := osL_fsNext X e.left.right h0
  obtain ⟨h2, r2⟩ := osL_fsNext X e.right h1
  exact ⟨h2.of_eq rfl rfl rfl, r1.cat r2 rfl rfl⟩

end

end
end LeanVM.Guest.B1
