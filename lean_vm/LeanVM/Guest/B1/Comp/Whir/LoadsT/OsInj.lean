/-
  LeanVM.Guest.B1.Comp.Whir.LoadsT.OsInj

  Instance injectivity in the stacked opening's tree: every valid placed tree of an
  `open_stacked` specialization satisfies `OsInj`.
-/

module

public import LeanVM.Guest.B1.Comp.Whir.LoadsT.OsInjT
public import LeanVM.Guest.B2C.Cells

/-!
# `os_inj`

In a valid tree of `open_stacked` placed at `fp`, an instance of a function of `osInjNames` is

* an `opening_queries` specialization's node, a callee of the root at a level `a`: its fifth
  argument `rew_a` is a `HeapBuf` of the root, its third `qw·g^(a·maxQ)`, so the level, hence the
  callee, is its arguments' (`OsIKid`);
* an iteration `d` of its loop helper's chain: its fourth argument is the query sums' buffer
  `g^(p + fs q)` right after its `opening_queries` frame `p`, its first `g^d`.

The other callees' subtrees reach `osInjZ` only. Hence `os_injCfg` for a configuration, and
`os_inj` at `openName μ r`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.Located LeanVM.Guest.B1.VerifySub
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

/-! ## Lists -/

theorem osI_mem_bases : ∀ {b0 : ℕ} {ss : List ℕ} {b : ℕ}, b ∈ bases b0 ss → b0 ≤ b ∧ b ≤ b0 + ss.sum
  | _, [], _, h => (List.not_mem_nil h).elim
  | b0, s :: ss, b, h => by
    simp only [bases, List.mem_cons] at h
    rcases h with rfl | h
    · simp
    · have := osI_mem_bases h
      simp only [List.sum_cons]; omega

theorem osI_takeSum_lt : ∀ {ns : List ℕ}, (∀ n ∈ ns, 0 < n) → ∀ {i i' : ℕ}, i < i' → i' ≤ ns.length →
    (ns.take i).sum < (ns.take i').sum
  | [], _, _, _, _, h' => by simp at h'; omega
  | n :: ns, hp, i, i', h, h' => by
    cases i' with
    | zero => omega
    | succ i' =>
      cases i with
      | zero =>
        simp only [List.take_zero, List.sum_nil, List.take_succ_cons, List.sum_cons]
        have := hp n List.mem_cons_self
        omega
      | succ i =>
        simp only [List.take_succ_cons, List.sum_cons]
        have := osI_takeSum_lt (fun x hx => hp x (List.mem_cons_of_mem _ hx)) (i := i) (i' := i')
          (by omega) (by simpa using h')
        omega

theorem osI_takeSum_inj {ns : List ℕ} (hp : ∀ n ∈ ns, 0 < n) {i i' : ℕ} (h : i ≤ ns.length)
    (h' : i' ≤ ns.length) (he : (ns.take i).sum = (ns.take i').sum) : i = i' := by
  rcases Nat.lt_trichotomy i i' with hl | rfl | hl
  · exact absurd he (Nat.ne_of_lt (osI_takeSum_lt hp hl h'))
  · rfl
  · exact absurd he (Nat.ne_of_gt (osI_takeSum_lt hp hl h))

theorem osI_filter_get {α : Type} (p : α → Bool) : ∀ (l : List α) (i : ℕ) (x : α), l[i]? = some x →
    p x = true → (l.filter p)[(l.take i).countP p]? = some x
  | [], _, _, h, _ => by simp at h
  | y :: l, 0, x, h, hp => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    simp [hp]
  | y :: l, i + 1, x, h, hp => by
    simp only [List.getElem?_cons_succ] at h
    have := osI_filter_get p l i x h hp
    by_cases hy : p y = true
    · simp [hy, this]
    · simp [hy, this]

theorem osI_countP_inj {α : Type} (p : α → Bool) : ∀ (l : List α) (i i' : ℕ) (x x' : α), l[i]? = some x →
    l[i']? = some x' → p x = true → p x' = true → (l.take i).countP p = (l.take i').countP p → i = i'
  | [], _, _, _, _, h, _, _, _, _ => by simp at h
  | y :: l, 0, 0, _, _, _, _, _, _, _ => rfl
  | y :: l, 0, i' + 1, x, x', h, h', hp, hp', he => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    simp [hp] at he
  | y :: l, i + 1, 0, x, x', h, h', hp, hp', he => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h'
    subst h'
    simp [hp'] at he
  | y :: l, i + 1, i' + 1, x, x', h, h', hp, hp', he => by
    simp only [List.getElem?_cons_succ] at h h'
    simp only [List.take_succ_cons, List.countP_cons] at he
    have := osI_countP_inj p l i i' x x' h h' hp hp' (by omega)
    omega

/-! ## The levels' queries -/

/-- The level's query weights' pointer `qw·g^(lvl·maxQ)`. -/
def osQpOf (cfg : OsCfg) (lv : OsLvl) (lvl : ℕ) (s : OsSt) : List Stmt × ℕ × ℕ :=
  let k := s.k
  let p := osMat osFch lv.foldsOff (k + 2)
  let cp := osMat osCaps (4 * lv.capOff) p.2.2
  let fp := osMat osFlags lv.capOff cp.2.2
  let r := fp.2.2
  let cp2 := osMat osCaps (4 * lv.capOff) (r + 2)
  let fp2 := osMat osFlags lv.capOff cp2.2.2
  osMat osQw (lvl * cfg.maxQ) fp2.2.2

theorem osI_qcall_args (cfg : OsCfg) (lv : OsLvl) (lvl : ℕ) (s : OsSt) :
    ((osQCallOf cfg lv lvl s).2.2.1)[2]? = some (.n (osQpOf cfg lv lvl s).2.1) ∧
      ((osQCallOf cfg lv lvl s).2.2.1)[4]? = some (.n (s.k + 1)) ∧ (osQCallOf cfg lv lvl s).2.2.1.length = 6 ∧
      (osQCallOf cfg lv lvl s).1 = none ∧ (osQCallOf cfg lv lvl s).2.1 = lv.queriesFn :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem osI_qparts (cfg : OsCfg) (lv : OsLvl) (lvl : ℕ) (s : OsSt) :
    OsSub (osQpOf cfg lv lvl s).1 (osQueries cfg lv lvl s).1 ∧
      Stmt.atom (.hint (.allocDyn (.n (s.k + 1)) (.n s.k))) ∈ (osQueries cfg lv lvl s).1 := by
  have h : OsSub (osQueries cfg lv lvl s).1 (osQueries cfg lv lvl s).1 := fun _ h => h
  refine ⟨h.left.left.left.left.left.right, ?_⟩
  have hr : OsSub (osHeap cfg.maxIl s.k) (osQueries cfg lv lvl s).1 :=
    h.left.left.left.left.left.left.left.left.left.left.left.left.left
  exact hr _ (by simp [osHeap])

theorem osI_qsub (cfg : OsCfg) (lv : OsLvl) (lvl : ℕ) (s : OsSt) :
    OsSub (osQueries cfg lv lvl (osQIn cfg lvl lv s)).1 (osLevel cfg lvl lv s).1 := by
  have h : OsSub (osLevel cfg lvl lv s).1 (osLevel cfg lvl lv s).1 := fun _ h => h
  exact h.left.left.left.right

theorem osI_qcalls_get (cfg : OsCfg) : ∀ (lvs : List OsLvl) (lvl : ℕ) (s : OsSt) (a : ℕ)
    (x : Option V × String × List V × List V), (osQCalls cfg lvl lvs s)[a]? = some x →
    ∃ lv s', lvs[a]? = some lv ∧ x = osQCallOf cfg lv (lvl + a) (osQIn cfg (lvl + a) lv s') ∧
      OsSub (osLevel cfg (lvl + a) lv s').1 (osLevels cfg lvl lvs s).1
  | [], _, _, _, _, h => by simp [osQCalls] at h
  | lv :: rest, lvl, s, 0, x, h => by
    simp only [osQCalls, List.getElem?_cons_zero, Option.some.injEq] at h
    exact ⟨lv, s, rfl, by rw [← h, Nat.add_zero],
      fun y hy => by simp only [osLevels, Nat.add_zero] at hy ⊢; exact List.mem_append_left _ hy⟩
  | lv :: rest, lvl, s, a + 1, x, h => by
    simp only [osQCalls, List.getElem?_cons_succ] at h
    obtain ⟨lv', s', h1, h2, h3⟩ := osI_qcalls_get cfg rest (lvl + 1) _ a x h
    rw [show lvl + (a + 1) = lvl + 1 + a by omega]
    exact ⟨lv', s', by simpa using h1, h2, fun y hy => by simp only [osLevels]; exact List.mem_append_right _ (h3 y hy)⟩

theorem osI_length_qcalls (cfg : OsCfg) : ∀ (lvs : List OsLvl) (lvl : ℕ) (s : OsSt),
    (osQCalls cfg lvl lvs s).length = lvs.length
  | [], _, _ => rfl
  | _ :: rest, _, _ => by simp [osQCalls, osI_length_qcalls cfg rest]

/-! ## A queries callee of the root -/

/-- **The root's callee `k` at `p` is a level's `opening_queries`**: its function and its loop
helper's, its validity and placement on `A`, its third argument `g^(b6 + a·maxQ)`, its fifth a
`HeapBuf` `g^aR` of the root. -/
structure OsIKid (S : BlakeSem) (rd : Reader) (maxQ fp b6 a : ℕ) (k : Tree) (p : ℕ) (q L : String)
    (fnQ lf : Fn) (preL : List Stmt) (c : V) (m k2 : ℕ) (A : List E) (aR : ℕ) : Prop where
  name : k.name = q
  findQ : coreProgram.find? q = some fnQ
  paramsQ : fnQ.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5]
  bodyQ : fnQ.body = oqBody L
  loopQ : coreProgram.loop q = false
  loop : OsILoop L lf preL c m k2
  inQ : q ∈ oqTable.map (·.1)
  notL : q ∉ oqTable.map (·.2.1)
  inL : L ∈ oqTable.map (·.2.1)
  notQ : L ∉ oqTable.map (·.1)
  uniq : ∀ e ∈ oqTable, e.2.1 = L → e.1 = q
  entry : ∃ e ∈ oqTable, e.1 = q ∧ e.2.1 = L
  valid : ∃ rets, k.ValidB S coreProgram rd A rets
  placed : k.Placed coreProgram B2C.fs B2C.cert p
  qp : A[2]? = some (gen ^ (b6 + a * maxQ))
  rv : A[4]? = some (ofK (Parameters.gpow aR))
  rvle : fp ≤ aR ∧ aR ≤ p

theorem osI_kids_length {S : BlakeSem} {P : Core.Program} {rd : Reader} {σ : Val} :
    ∀ {cs : List Call} {ks : List Tree}, Tree.KidsValidB S P rd σ cs ks → ks.length = cs.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, ⟨_, _, h⟩ => by simp [osI_kids_length h]
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

/-- A specialization of the table and its loop helper's facts. -/
theorem osI_spec {q : String} (hq : (oqLookup q).isSome = true) :
    ∃ L fnQ lf preL c m k2, coreProgram.find? q = some fnQ ∧
      fnQ.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5] ∧ fnQ.body = oqBody L ∧ coreProgram.loop q = false ∧
      OsILoop L lf preL c m k2 ∧ q ∈ oqTable.map (·.1) ∧ q ∉ oqTable.map (·.2.1) ∧ L ∈ oqTable.map (·.2.1) ∧
      L ∉ oqTable.map (·.1) ∧ (∀ e ∈ oqTable, e.2.1 = L → e.1 = q) ∧ ∃ e ∈ oqTable, e.1 = q ∧ e.2.1 = L := by
  unfold oqLookup at hq
  rcases hf : oqTable.find? (fun e => e.1 == q) with _ | e
  · rw [hf] at hq; cases hq
  have he := List.mem_of_find?_eq_some hf
  have hn : e.1 = q := by simpa using List.find?_some hf
  obtain ⟨-, ⟨fnQ, hfQ, hpQ, hbQ⟩, ⟨lf, hlf, hlp, hlb⟩⟩ := oqTable_spec e he
  obtain ⟨hst, hal, hcs⟩ := osI_oqLoop e he
  obtain ⟨ha2, ham⟩ := osI_oqLoop_atoms e he
  have hnm : ∀ e' ∈ oqTable, e.1 ≠ e'.2.1 ∧ (e.2.1 = e'.2.1 → e.1 = e'.1) := osI_oqNames e he
  rw [hn] at hfQ hnm
  refine ⟨e.2.1, fnQ, lf, _, _, _, _, hfQ, hpQ, hbQ, ?_,
    ⟨hlf, hlp, hlb.trans (oqLoopBody_split _ _ _ _ _ _), hst, hal, hcs, osI_mem_of_any ha2, osI_mem_of_any ham⟩,
    List.mem_map.mpr ⟨e, he, hn⟩, ?_, List.mem_map.mpr ⟨e, he, rfl⟩, ?_, ?_, ⟨e, he, hn, rfl⟩⟩
  · rw [Program.loop_of_find? hfQ]
    unfold Fn.loop
    rw [hbQ]
    rfl
  · intro hm
    obtain ⟨e', he', h'⟩ := List.mem_map.mp hm
    exact (hnm e' he').1 h'.symm
  · intro hm
    obtain ⟨e', he', h'⟩ := List.mem_map.mp hm
    exact (osI_oqNames e' he' e he).1 h'
  · intro e' he' h'
    exact ((hnm e' he').2 h'.symm).symm

/-! ## A configuration -/

theorem osI_mkCall_f (σ : Val) (r : Option V × String × List V × List V) : (Main.mkCall σ r).f = r.2.1 := by
  obtain ⟨_ | _, _, _, _⟩ := r <;> rfl

theorem osI_mkCall_args (σ : Val) (r : Option V × String × List V × List V) :
    (Main.mkCall σ r).args = r.2.2.1 := by
  obtain ⟨_ | _, _, _, _⟩ := r <;> rfl

theorem osI_mkCall_none (σ : Val) (f : String) (args rets : List V) :
    Main.mkCall σ (none, f, args, rets) = ⟨f, args, rets, true⟩ := rfl

theorem osI_coreOf {f : String} {fn : Fn} {j : ℕ} (hf : coreProgram.find? f = some fn)
    (hj : B2C.idxOf f = some j) : coreOf j = fn := by
  obtain ⟨i, -, hi, -, hf', hc, -⟩ := B2C.fn_of_idx hj
  rw [hc]
  exact Option.some.inj (hf'.symm.trans hf)

theorem osI_gpow_inj {a b : ℕ} (ha : a < 2 ^ 64 - 1) (hb : b < 2 ^ 64 - 1)
    (h : ofK (Parameters.gpow a) = ofK (Parameters.gpow b)) : a = b := by
  rw [← gen_pow_eq_ofK, ← gen_pow_eq_ofK] at h
  exact gen_pow_inj ha hb h

theorem osI_validB_params {S : BlakeSem} {P : Core.Program} {rd : Reader} :
    ∀ {t : Tree} {args rets : List E} {fn : Fn}, t.ValidB S P rd args rets → P.find? t.name = some fn →
      fn.params.map t.val = args
  | .node f σ _ _, _, _, fn, ⟨fn', hf', hp, _⟩, hf => by
    simp only [Tree.name] at hf
    rw [hf, Option.some.injEq] at hf'
    subst hf'
    exact hp
  | .phantom .., _, _, _, h, _ => h.elim

theorem OsSub.trans' {l1 l2 l3 : List Stmt} (h1 : OsSub l1 l2) (h2 : OsSub l2 l3) : OsSub l1 l3 :=
  fun x hx => h2 x (h1 x hx)

theorem osI_bases_get {b : ℕ} {ns : List ℕ} {i p : ℕ} (h : (bases b ns)[i]? = some p) :
    i < ns.length ∧ p = b + (ns.take i).sum := by
  have hi : i < ns.length := by
    have := (List.getElem?_eq_some_iff.mp h).1
    rwa [Memory.length_bases] at this
  rw [getElem?_bases hi, Option.some.injEq] at h
  exact ⟨hi, h.symm⟩

/-- **`OsInj` at a configuration.** -/
theorem os_injCfg {S : BlakeSem} {cfg : OsCfg} {name : String} {fn : Fn}
    (hf : coreProgram.find? name = some fn) (hbody : fn.body = osBody cfg) (hbf : OsBodyFacts cfg)
    (hic : OsICfg cfg) (hlp : coreProgram.loop name = false) (hnN : name ∉ osInjNames)
    (hlv' : ∀ i < cfg.levels.length, lvOk i (cfg.lv i) = true)
    {rd : Reader} {args rets : List E} {fp : ℕ} {t : Tree} (hn : t.name = name)
    (hv : t.ValidB S coreProgram rd args rets) (hp : t.Placed coreProgram B2C.fs B2C.cert fp) :
    OsInj fp t := by
  intro htot H hdr
  have hb' : fn.body = (osBody cfg).dropLast ++ [.ret (osRetVs cfg)] := by rw [hbody]; exact hbf.last
  have hst := hbf.straight
  have hsub : OsSub ((osHead cfg).1 ++ (osLevels cfg 0 cfg.levels (osHead cfg).2).1 ++
      (osTail cfg.yrLog (OsRun.sL cfg)).1 ++ osFinPre cfg) (osBody cfg).dropLast := by
    rw [os_pre_eq]; exact fun _ h => h
  have hfilt := hic.filt
  have hcal := hic.cal
  obtain ⟨hmq0, hmq⟩ := hic.mq
  have hqw : Stmt.atom (.hint (.allocDyn (.n 52) (.n 51))) ∈ (osHead cfg).1 := by
    simp [osHead, osHeap]
  generalize (osBody cfg).dropLast = pre at hb' hst hsub hfilt hcal
  obtain ⟨σ, bufs, kids, rfl, -, hw, -, hes, hk⟩ := osL_node (S := S) hf hb' hst hn hv
  have X := osL_ctx (bufs := bufs) hf hw hes hk
  rw [placed_node, events_node hf hw] at hp
  obtain ⟨hNA, hPK⟩ := hp
  set ns := kids.map (Tree.total B2C.fs) with hns
  set csR := pre.filterMap Main.Stmt.callS with hcsR
  have hbb : bufBase B2C.fs coreProgram.loop fp name ns = fp + B2C.fs name := by simp [bufBase, hlp]
  have hps : kidPos B2C.fs coreProgram.loop fp name bufs ns = bases (fp + B2C.fs name + bufs.sum) ns := by
    simp [kidPos, hlp, hbb]
  have htotal : (Memory.Tree.node name σ bufs kids).total B2C.fs = B2C.fs name + ns.sum + bufs.sum := by
    rw [total_node, totalKids_eq_sum]
  -- `HeapBuf` pointers of the root
  obtain ⟨i1, -, -, -⟩ := Main.straight_parts σ pre hst
  have hal : ∀ d s, Stmt.atom (.hint (.allocDyn d s)) ∈ pre →
      ∃ a, σ d = ofK (Parameters.gpow a) ∧ fp ≤ a ∧ a ≤ fp + B2C.fs name + bufs.sum := by
    intro d s hm
    have hd : d ∈ allocDsts (pre.flatMap (Main.slEvs σ)) := by
      rw [i1]
      exact List.mem_map.mpr ⟨(d, .inr s), List.mem_filterMap.mpr ⟨_, hm, rfl⟩, rfl⟩
    have hv' : σ d ∈ (bases (bufBase B2C.fs coreProgram.loop fp name ns) bufs).map
        (fun b => ofK (Parameters.gpow b)) := by
      rw [← hNA.1]; exact List.mem_map.mpr ⟨d, hd, rfl⟩
    obtain ⟨a, ha, he⟩ := List.mem_map.mp hv'
    rw [hbb] at ha
    have := osI_mem_bases ha
    exact ⟨a, he.symm, by omega, this.2⟩
  obtain ⟨b6, h52, hb6, hb6'⟩ := hal _ _ (hsub.left.left.left _ hqw)
  have hlvsub : OsSub (osLevels cfg 0 cfg.levels (osHead cfg).2).1 pre := hsub.left.left.right
  -- kids
  have hklen : kids.length = csR.length := by
    simpa using osI_kids_length hk
  have hns : ∀ n ∈ ns, 0 < n := by
    intro n hn'
    obtain ⟨k, -, rfl⟩ := List.mem_map.mp hn'
    have := le_total (fs := B2C.fs) k
    have := osI_fs_two k.name
    omega
  -- a queries callee
  have hkid : ∀ i k p r, kids[i]? = some k → (bases (fp + B2C.fs name + bufs.sum) ns)[i]? = some p →
      csR[i]? = some r → osInjNames.contains r.2.1 = true →
      ∃ a q L fnQ lf preL c m k2 A aR, (csR.take i).countP (fun c => osInjNames.contains c.2.1) = a ∧
        a < cfg.levels.length ∧ OsIKid S rd cfg.maxQ fp b6 a k p q L fnQ lf preL c m k2 A aR := by
    intro i k p r hk' hp' hr hN
    have hfa := osI_filter_get (fun c => osInjNames.contains c.2.1) csR i r hr hN
    rw [hfilt] at hfa
    obtain ⟨lv, s', hlv, hx, hsl⟩ := osI_qcalls_get cfg cfg.levels 0 (osHead cfg).2 _ r hfa
    simp only [Nat.zero_add] at hx hsl
    set a := (csR.take i).countP (fun c => osInjNames.contains c.2.1) with ha_def
    have ha : a < cfg.levels.length := (List.getElem?_eq_some_iff.mp hlv).1
    have hlvd : cfg.lv a = lv := by simp [OsCfg.lv, List.getD_eq_getElem?_getD, hlv]
    have hok := hlv' a ha
    rw [hlvd] at hok
    have hlk : (oqLookup lv.queriesFn).isSome = true := by
      unfold lvOk at hok
      cases hl : oqLookup lv.queriesFn with
      | none => rw [hl] at hok; cases hok
      | some _ => rfl
    obtain ⟨L, fnQ, lf, preL, c, m, k2, hfQ, hpQ, hbQ, hlQ, hL, hinQ, hnotL, hinL, hnotQ, huniq, hentry⟩ :=
      osI_spec hlk
    set s := osQIn cfg a lv s' with hs_def
    obtain ⟨har2, har4, harl, har1, harn⟩ := osI_qcall_args cfg lv a s
    rw [← hx] at har2 har4 harl har1 harn
    -- the callee
    obtain ⟨c', hc', hkn, hkv, -⟩ := osI_kidsGet hk hk'
    rw [List.getElem?_map, hr, Option.map_some, Option.some.injEq] at hc'
    have hrr : r = (none, lv.queriesFn, r.2.2.1, r.2.2.2) := by
      obtain ⟨r1, r2, r3, r4⟩ := r
      simp only at har1 harn
      rw [har1, harn]
    have hc'' : c' = ⟨lv.queriesFn, r.2.2.1, r.2.2.2, true⟩ := by rw [← hc', hrr]; rfl
    subst hc''
    have hkv' := hkv rfl
    have hsq : OsSub (osQueries cfg lv a s).1 pre :=
      OsSub.trans' (osI_qsub cfg lv a s') (OsSub.trans' hsl hlvsub)
    obtain ⟨hqp, hrw⟩ := osI_qparts cfg lv a s
    -- the third argument
    have hqpv : σ (.n (osQpOf cfg lv a s).2.1) = gen ^ (b6 + a * cfg.maxQ) := by
      have hm := osL_mat X (OsSub.trans' hqp hsq) (c := b6) (q := 0)
        (by rw [pow_zero, mul_one]; exact h52) (by have := Nat.mul_lt_mul_of_pos_right ha hmq0; omega)
      have e : σ (.n (osQpOf cfg lv a s).2.1) = σ (.n (osMat osQw (a * cfg.maxQ) _).2.1) := rfl
      rw [e, hm, ← gen_pow_eq_ofK, ← pow_add, Nat.zero_add]
    -- the fifth
    obtain ⟨aR, hrv, haR1, haR2⟩ := hal _ _ (hsq _ hrw)
    obtain ⟨-, hpe⟩ := osI_bases_get hp'
    refine ⟨a, lv.queriesFn, L, fnQ, lf, preL, c, m, k2, r.2.2.1.map σ, aR, rfl, ha,
      ⟨by rw [hkn], hfQ, hpQ, hbQ, hlQ, hL, hinQ, hnotL, hinL, hnotQ, huniq, hentry, ⟨_, hkv'⟩,
        osI_placedKidsGet hPK hk' (by rw [hps]; exact hp'), ?_, ?_, ⟨haR1, by omega⟩⟩⟩
    · rw [List.getElem?_map, har2, Option.map_some, hqpv]
    · rw [List.getElem?_map, har4, Option.map_some, hrv]
  -- the instances
  have hcls : ∀ I ∈ (Memory.Tree.node name σ bufs kids).insts B2C.fs coreProgram.loop H fp hdr,
      I.t.name ∈ osInjNames →
      ∃ i k p r a q L fnQ lf preL c m k2 A aR, kids[i]? = some k ∧
        (bases (fp + B2C.fs name + bufs.sum) ns)[i]? = some p ∧ csR[i]? = some r ∧
        osInjNames.contains r.2.1 = true ∧ (csR.take i).countP (fun c => osInjNames.contains c.2.1) = a ∧
        a < cfg.levels.length ∧ OsIKid S rd cfg.maxQ fp b6 a k p q L fnQ lf preL c m k2 A aR ∧
        ((I.t = k ∧ I.fp = p) ∨ OsIChainAt L lf B2C.fs 1 (osIQRest B2C.fs q p A) (p + B2C.fs q + k.bufs.sum) I) := by
    intro I hI hIN
    rw [insts_node, List.mem_cons] at hI
    rcases hI with rfl | hI
    · exact absurd hIN hnN
    obtain ⟨i, k, p, hk', hp', hIk⟩ := osI_mem_instsKids kids _ _ 0 I hI
    rw [hps] at hp'
    have hi : i < csR.length := by rw [← hklen]; exact (List.getElem?_eq_some_iff.mp hk').1
    obtain ⟨r, hr⟩ : ∃ r, csR[i]? = some r := ⟨_, List.getElem?_eq_getElem hi⟩
    obtain ⟨c', hc', hkn, hkv, hkp⟩ := osI_kidsGet hk hk'
    rw [List.getElem?_map, hr, Option.map_some, Option.some.injEq] at hc'
    subst hc'
    rw [osI_mkCall_f] at hkn
    by_cases hN : osInjNames.contains r.2.1 = true
    · obtain ⟨a, q, L, fnQ, lf, preL, c, m, k2, A, aR, ha, hal', hK⟩ := hkid i k p r hk' hp' hr hN
      obtain ⟨rets', hkv'⟩ := hK.valid
      have := osI_q (H := H) hK.findQ hK.paramsQ hK.bodyQ hK.loopQ hK.loop hK.name hkv' hK.placed I hIk
      exact ⟨i, k, p, r, a, q, L, fnQ, lf, preL, c, m, k2, A, aR, hk', hp', hr, hN, ha, hal', hK, this⟩
    · exfalso
      have hZ : r.2.1 ∈ osInjZ := by
        have := List.all_eq_true.mp hcal r (List.mem_of_getElem? hr)
        simp only [Bool.or_eq_true] at this
        rcases this with h | h
        · exact List.contains_iff_mem.mp h
        · exact absurd h hN
      have hkZ : k.name ∈ osInjZ := by rw [hkn]; exact hZ
      have hIZ : I.t.name ∈ osInjZ := by
        by_cases ht : (Main.mkCall σ r).taken = true
        · exact osI_instsZ k (hkv ht) hkZ p _ I hIk
        · obtain ⟨⟨f', σ', rfl⟩, -⟩ := hkp (by simpa using ht)
          rw [insts_phantom, List.mem_singleton] at hIk
          rw [hIk]; exact hkZ
      exact osInjZ_notMem hIZ hIN
  -- bounds
  have hfpI : ∀ I ∈ (Memory.Tree.node name σ bufs kids).insts B2C.fs coreProgram.loop H fp hdr,
      I.fp < fp + (Memory.Tree.node name σ bufs kids).total B2C.fs := by
    intro I hI
    have := insts_within _ fp hdr I hI I.fp (Or.inl ⟨le_refl _, by have := osI_fs_two I.t.name; omega⟩)
    exact this.2
  intro I hI j hj hIN
  obtain ⟨i, k, p, r, a, q, L, fnQ, lf, preL, c, m, k2, A, aR, hk', hp', hr, hN, hcnt, hlt, hK, hcase⟩ :=
    hcls I hI hIN
  have hIlt := hfpI I hI
  obtain ⟨-, hpe⟩ := osI_bases_get hp'
  rcases hcase with ⟨hIt, hIfp⟩ | ⟨hIn, d, hd, hIfp⟩
  · -- an `opening_queries` node
    have hname : I.t.name = q := by rw [hIt]; exact hK.name
    have hcj : coreOf j = fnQ := osI_coreOf hK.findQ (hname ▸ hj)
    obtain ⟨rets', hkv'⟩ := hK.valid
    have hpm : (coreOf j).params.map I.t.val = A := by
      rw [hcj, hIt]; exact osI_validB_params hkv' (by rw [hK.name]; exact hK.findQ)
    have hrv := hK.rvle
    refine ⟨⟨aR, ?_, hK.rvle.1, by omega⟩, ?_⟩
    · simp only [hpm, hname, osPtrIdx, hK.inQ, ↓reduceIte]; exact hK.rv
    intro I' hI' hn' hpe'
    obtain ⟨i', k', p', r', a', q', L', fnQ', lf', preL', c', m', k2', A', aR', hk'', hp'', hr', hN', hcnt', hlt',
      hK', hcase'⟩ := hcls I' hI' (by rw [hn']; exact hIN)
    rcases hcase' with ⟨hIt', hIfp'⟩ | ⟨hIn', -⟩
    · have hname' : I'.t.name = q' := by rw [hIt']; exact hK'.name
      have hqq : q = q' := (hname'.symm.trans (hn'.trans hname)).symm
      subst hqq
      have hfn : fnQ = fnQ' := Option.some.inj (hK.findQ.symm.trans hK'.findQ)
      subst hfn
      obtain ⟨rets'', hkv''⟩ := hK'.valid
      have hpm' : (coreOf j).params.map I'.t.val = A' := by
        rw [hcj, hIt']; exact osI_validB_params hkv'' (by rw [hK'.name]; exact hK.findQ)
      rw [hpm, hpm'] at hpe'
      have h2 := hK.qp
      rw [← hpe', hK'.qp, Option.some.injEq] at h2
      have hb6' : b6 + a * cfg.maxQ < 2 ^ 64 - 1 := by
        have := Nat.mul_lt_mul_of_pos_right hlt hmq0; omega
      have hb6'' : b6 + a' * cfg.maxQ < 2 ^ 64 - 1 := by
        have := Nat.mul_lt_mul_of_pos_right hlt' hmq0; omega
      have haa := gen_pow_inj hb6'' hb6' h2
      have haa' : a' = a := Nat.eq_of_mul_eq_mul_right hmq0 (by omega)
      have hii : i = i' := osI_countP_inj (fun c => osInjNames.contains c.2.1) csR i i' r r' hr hr' hN hN'
        (by rw [hcnt', hcnt, haa'])
      subst hii
      rw [hp'] at hp''
      rw [hIfp, hIfp', Option.some.inj hp'']
    · exact absurd (hIn'.symm.trans (hn'.trans hname) ▸ hK'.inL) hK.notL
  · -- an iteration of a loop helper
    have hcj : coreOf j = lf := osI_coreOf hK.loop.find (hIn ▸ hj)
    have hpm : (coreOf j).params.map I.t.val = (1 * gen ^ d) :: osIQRest B2C.fs q p A := by rw [hcj]; exact hd
    have hfsq := osI_fs_two q
    refine ⟨⟨p + B2C.fs q, ?_, by omega, by
      have := Nat.zero_le (d * B2C.fs L); omega⟩, ?_⟩
    · simp only [hpm, hIn, osPtrIdx, hK.notQ, ↓reduceIte]; rfl
    intro I' hI' hn' hpe'
    obtain ⟨i', k', p', r', a', q', L', fnQ', lf', preL', c', m', k2', A', aR', hk'', hp'', hr', hN', hcnt', hlt',
      hK', hcase'⟩ := hcls I' hI' (by rw [hn']; exact hIN)
    have hIlt' := hfpI I' hI'
    obtain ⟨-, hpe2⟩ := osI_bases_get hp''
    rcases hcase' with ⟨hIt', -⟩ | ⟨hIn', d', hd', hIfp'⟩
    · have hname' : I'.t.name = q' := by rw [hIt']; exact hK'.name
      exact absurd ((hname'.symm.trans (hn'.trans hIn)) ▸ hK.inL) hK'.notL
    have hLL : L = L' := (hIn'.symm.trans (hn'.trans hIn)).symm
    subst hLL
    have hlf : lf = lf' := Option.some.inj (hK.loop.find.symm.trans hK'.loop.find)
    subst hlf
    obtain ⟨e', he', he1, he2⟩ := hK'.entry
    have hqq : q = q' := (hK.uniq e' he' he2).symm.trans he1
    subst hqq
    rw [hpm, hcj, hd', List.cons.injEq] at hpe'
    obtain ⟨hdd, hrest⟩ := hpe'
    have h3 := congrArg (fun l => l[2]?) hrest
    simp only [osIQRest, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at h3
    have hpp := osI_gpow_inj (by omega) (by omega) h3
    have hpp' : p' = p := by omega
    have hsum : (ns.take i').sum = (ns.take i).sum := by omega
    have hii : i = i' := osI_takeSum_inj hns
      (by have := (osI_bases_get hp').1; omega) (by have := (osI_bases_get hp'').1; omega) hsum.symm
    subst hii
    have hkk : k = k' := Option.some.inj (hk'.symm.trans hk'')
    subst hkk
    have hfsL := osI_fs_two L
    have hd1 : d' < 2 ^ 64 - 1 := by
      have : d' * 2 ≤ d' * B2C.fs L := Nat.mul_le_mul_left _ hfsL
      omega
    have hd2 : d < 2 ^ 64 - 1 := by
      have : d * 2 ≤ d * B2C.fs L := Nat.mul_le_mul_left _ hfsL
      omega
    rw [one_mul, one_mul] at hdd
    have hdd' := gen_pow_inj hd1 hd2 hdd
    rw [hIfp, hIfp', hdd', hpp']


/-- **Instance injectivity in every valid placed tree of `open_stacked` at `openName μ r`.** -/
theorem os_inj {S : BlakeSem} {μ r : ℕ} (h22 : 22 ≤ μ) (h28 : μ ≤ 28) (h1 : 1 ≤ r) (h4 : r ≤ 4) {rd : Reader}
    {args rets : List E} {fp : ℕ} {t : Tree} (hn : t.name = openName μ r)
    (hv : t.ValidB S coreProgram rd args rets) (hp : t.Placed coreProgram B2C.fs B2C.cert fp) : OsInj fp t := by
  have hj : μ - 22 + 7 * (r - 1) < 28 := by omega
  obtain ⟨⟨fn, hf, -, hbody⟩, -, -⟩ := os_inst _ hj
  exact os_injCfg hf hbody (osL_bodyFacts _ hj) (osI_cfg _ hj) (osI_loop _ hj) (osI_openNames _ hj)
    (osCfgs_lvOk _ hj) hn hv hp

end
end LeanVM.Guest.B1
