/-
  LeanVM.Guest.B2C.CplWalkB

  The completeness walk along a path (`CplWalk.lean`) under any semantics of `BLAKE2S`.
-/

module

public import LeanVM.Guest.B2C.CplWalk
public import LeanVM.Guest.B2C.CplSemB

/-!
# The walk along a path under any `BLAKE2S` semantics

`CplWalk.lean`'s `WH`, `PosZ`, `Arr`, `ArrMid`, `FinZ`, `WGood` with `S : BlakeSem` a parameter
(`WHB`, `PosZB`, `ArrB`, `ArrMidB`, `FinZB`, `WGoodB`), each run also keeping the callees entered
so far on it (`KidsOn`: a call's callee entered at its entry and frame, the run going on from its
return registers) and the return's arity (`FinZB`: `vs'.length = X.nret`), and the walk's moves and cases
(`segAtCB_pos`, `endAtCB_reach`, `brAtCB_pos`, `walkB_nilZ`, `walkB_step`, `walkB_atomZ`,
`walkB_callZ`, `walkB_iteZ`, `walkB_callIfZ`, `walkB_retZ`, …), proved as there.

* `whB_deployed`: at `blakeDeployed`, `WHB` is `WH`; `arrB_deployed`, `arrMidB_deployed`: `ArrB`,
  `ArrMidB` are `Arr`, `ArrMid` with the callees on the run; `finZB_deployed`: `FinZB` gives `FinZ`.
-/

namespace LeanVM.Guest.B2C

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Exec
open LeanVM.Guest.Check LeanVM.Guest.Memory

@[expose] public section

variable {S : BlakeSem}

/-! ## Bit sets -/

section Walk

variable {κ : ℕ} {L : MemImage κ} {j fp : ℕ} {σ : Val} {es : List Ev} {vs : List V}
  {kfps : List ℕ} {hdr : E × E} {ck : List (Opcode → ℕ)} {segs : List Exec.Seg} {X : CX}
  {wJ : ℕ} {wenv : Trie Sym}

variable (S) in
/-- **What the walk of a window assumes.** -/
structure WHB (L : MemImage κ) (j fp : ℕ) (X : CX) (segs : List Exec.Seg) (wJ : ℕ) (wenv : Trie Sym)
    (σ : Val) (es : List Ev) (vs : List V) (kfps : List ℕ) (hdr : E × E)
    (ck : List (Opcode → ℕ)) : Prop where
  hX : CXOk L fp X
  ctx : Exec.Ctx X.F κ (gpow fp)
  segz : ∀ s ∈ segs, SegZB S L (gpow fp) guest X.entry s
  exits : ∀ s ∈ segs, ∀ x, x = s.exit ∨ x ∈ branchExits s.items → x ∈ s.exits
  idx : X.idx = index segs
  linked : linkedWeak X.idx segs wJ wenv = true
  loc : LocOk j X.loc
  fs : X.fs = fsN j
  G : X.G = glob
  main : X.main = (j == 1)
  name : X.name = (coreOf j).name
  nargs : X.nargs = (coreOf j).params.length
  sites : X.sites = (plumbOf j).sites
  arms : X.arms = (plumbOf j).arms
  self : X.self = (certOf j).facts.env.map (·.1)
  entry : X.entry = (fnOf j).entry
  /-- A parameter, or a value of one of the body's atoms, is a value the path names. -/
  named : ∀ n, (Nat.blt n X.nargs || bitK X.nv n) = true → V.n n ∈ namedOf (coreOf j).params es vs
  frame : FrameHolds L j fp σ es vs kfps hdr
  kids : KidsRunB S L σ es kfps ck
  hev : ∀ e ∈ es, e.HoldsB S L.read σ
  /-- A loop helper's last call is its closing one. -/
  lastCall : (coreOf j).loop = true → ∀ c, (calls es).getLast? = some c → c.f = (coreOf j).name
  jt : JTHolds glob L
  tab : ∀ q ∈ Memory.tableCells, L.read (gpow q.1) = some q.2
  j1 : 1 ≤ j
  jn : j < nFns

variable (S) in
/-- **The run is at the walk's position `st`**, from `W0`, the first `n` callees run, the
separately counted arms passed counting `x`. -/
structure PosZB (H : WHB S L j fp X segs wJ wenv σ es vs kfps hdr ck) (st : CW) (W0 : Regs K)
    (n : ℕ) (x : Opcode → ℕ) : Prop where
  seg : st.seg ∈ segs
  ok : CWOkB S L fp X st
  run : ∃ pre c, pre ++ st.its = st.seg.items ∧ FallB S L (gpow fp) pre ∧
    RunCB S guest L W0 ⟨gpow (X.entry + st.seg.start), gpow fp⟩ c ∧
    (∀ op, c op + itemOps pre op ≤ st.cnt.get op + x op + ksum ck n op) ∧
    KidsOn S L es kfps n W0 ⟨gpow (X.entry + st.seg.start), gpow fp⟩
  fresh : ∀ t, st.fresh = some t → st.seg.start = t ∧ st.its = st.seg.items ∧ getF X.idx t = some st.seg
  nm : ∀ n, st.nm.testBit n = true → V.n n ∈ namedOf (coreOf j).params es vs
  ix : getF X.idx st.seg.start = some st.seg

/-- **A selector the check accepts is a value the path names.** -/
theorem PosZB.sel {H : WHB S L j fp X segs wJ wenv σ es vs kfps hdr ck} {st : CW} {W0 : Regs K} {n : ℕ}
    {x : Opcode → ℕ} (hp : PosZB S H st W0 n x) {v : V} (hv : v = V.n v.idx) (hs : selOk X st v = true) :
    v ∈ namedOf (coreOf j).params es vs := by
  unfold selOk at hs
  rw [hv]
  rcases Bool.or_eq_true_iff.mp hs with h | h
  · exact H.named _ h
  · rw [bitK_eq] at h
    exact hp.nm _ h

variable (S) in
/-- **The run arrives at offset `J`**, from `W0`, within the counts `c` and the first `n`
callees'. -/
def ArrB (L : MemImage κ) (fp : ℕ) (X : CX) (wJ : ℕ) (wenv : Trie Sym) (ck : List (Opcode → ℕ))
    (es : List Ev) (kfps : List ℕ) (W0 : Regs K) (J : ℕ) (c : Cnt) (n : ℕ) (x : Opcode → ℕ) : Prop :=
  (∃ cr, RunCB S guest L W0 ⟨gpow (X.entry + J), gpow fp⟩ cr ∧ (∀ op, cr op ≤ c.get op + x op + ksum ck n op) ∧
    KidsOn S L es kfps n W0 ⟨gpow (X.entry + J), gpow fp⟩) ∧
    EnvAt L fp X wJ wenv J

variable (S) in
/-- **The run is inside the segment starting at `J`**, its first `m` items passed, within the
counts `c` and the first `n` callees'. -/
def ArrMidB (L : MemImage κ) (fp : ℕ) (X : CX) (ck : List (Opcode → ℕ)) (es : List Ev) (kfps : List ℕ)
    (W0 : Regs K) (J m : ℕ) (c : Cnt) (n : ℕ) (x : Opcode → ℕ) : Prop :=
  ∃ s, getF X.idx J = some s ∧ s.start = J ∧ m ≤ s.items.length ∧ EnvHolds L (gpow fp) s.env ∧
    ∃ cr, FallB S L (gpow fp) (s.items.take m) ∧ RunCB S guest L W0 ⟨gpow (X.entry + J), gpow fp⟩ cr ∧
      (∀ op, cr op + itemOps (s.items.take m) op ≤ c.get op + x op + ksum ck n op) ∧
      KidsOn S L es kfps n W0 ⟨gpow (X.entry + J), gpow fp⟩

/-! ## Moves -/

/-- Entering offset `t`, in its environment: the run is at the segment starting there. -/
theorem segAtCB_pos (H : WHB S L j fp X segs wJ wenv σ es vs kfps hdr ck) {t : ℕ} {st sn : CW}
    (h : segAtC X t st = some sn) (hb : BookOkB S L fp st.book) (hfr : FrOk L fp st.fr)
    (htg : TgOk L fp st.tg) (hnx : NxOk L fp X.fs st.nx) (he : EnvAt L fp X wJ wenv t)
    {W0 : Regs K} {n : ℕ} {xc : Opcode → ℕ} {c : Opcode → ℕ}
    (hr : RunCB S guest L W0 ⟨gpow (X.entry + t), gpow fp⟩ c)
    (hc : ∀ op, c op ≤ st.cnt.get op + xc op + ksum ck n op)
    (hko : KidsOn S L es kfps n W0 ⟨gpow (X.entry + t), gpow fp⟩)
    (hnm : ∀ n, st.nm.testBit n = true → V.n n ∈ namedOf (coreOf j).params es vs) :
    PosZB S H sn W0 n xc ∧ sn.book = st.book ∧ sn.fr = st.fr ∧ sn.tg = st.tg ∧ sn.nx = st.nx ∧
      sn.cnt = st.cnt ∧ sn.uq = st.uq ∧ sn.seg.start = t := by
  obtain ⟨s, hs, hst, rfl⟩ := segAtC_eq h
  have hmem : s ∈ segs := by
    rw [H.idx, getF_eq] at hs
    exact index_get hs
  refine ⟨⟨hmem, ⟨he.1 s hs hst, hb, hfr, htg, hnx⟩, ⟨[], c, rfl, trivial, hst ▸ hr, fun op ↦ ?_,
    hst ▸ hko⟩, fun t' ht' ↦ ?_, hnm, by rw [hst]; exact hs⟩, rfl, rfl, rfl, rfl, rfl, rfl, hst⟩
  · simpa [itemOps] using hc op
  · obtain rfl := Option.some.inj ht'
    exact ⟨hst, rfl, hs⟩

/-- The successor `t` of an exit whose environment holds has its environment holding. -/
theorem envAtB_of_exit (H : WHB S L j fp X segs wJ wenv σ es vs kfps hdr ck) {s : Exec.Seg}
    (hs : s ∈ segs) {x : Exit} (hx : x ∈ s.exits) {t : ℕ} (ht : t ∈ x.succ)
    (he : EnvHolds L (gpow fp) x.env) : EnvAt L fp X wJ wenv t := by
  refine ⟨fun s' hs' _ ↦ ?_, fun htJ hn ↦ ?_⟩
  · rw [getF_eq] at hs'
    exact he.sub (linkedWeak_get H.linked hs hx ht hs').2
  · subst htJ
    rw [getF_eq] at hn
    exact he.sub (linkedWeak_none H.linked hs hx ht hn)

/-- **At the end of its segment the run reaches the segment exit's registers**, its environment
holding there. -/
theorem endAtCB_reach (H : WHB S L j fp X segs wJ wenv σ es vs kfps hdr ck) {st se : CW} {W0 : Regs K}
    {n : ℕ} {xc : Opcode → ℕ} (hp : PosZB S H st W0 n xc) (he : endAtC X st = .ok se) :
    se.seg = st.seg ∧ se.book = st.book ∧ se.fr = st.fr ∧ se.tg = st.tg ∧ se.nx = st.nx ∧
      se.uq = st.uq ∧
      ∀ r, st.seg.exit.kind.Regs L (gpow fp) X.entry r → ∃ cr, RunCB S guest L W0 r cr ∧
        (∀ op, cr op ≤ se.cnt.get op + xc op + ksum ck n op) ∧ EnvHolds L (gpow fp) st.seg.exit.env ∧
        KidsOn S L es kfps n W0 r := by
  obtain ⟨c, hpl, rfl⟩ := endAtC_eq he
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun r hr ↦ ?_⟩
  obtain ⟨pre2, hpre2, hf2, hc2, -⟩ := passLB_sound H.hX hp.ok st.its st.cnt hpl
  obtain ⟨pre, c0, hpre, hf, hrun, hc0, hko⟩ := hp.run
  rw [List.append_nil] at hpre2
  subst hpre2
  have hfall : FallB S L (gpow fp) st.seg.items := by
    rw [← hpre]
    exact (fallB_append _ _).mpr ⟨hf, hf2⟩
  obtain ⟨cs, hcs, hle, henv⟩ := (H.segz _ hp.seg hp.ok.env).1 hfall r hr
  refine ⟨c0 + cs, hrun.trans hcs, fun op ↦ ?_, henv, hko.reach hcs.reach⟩
  have h1 := hle op
  have h2 := hc0 op
  rw [← hpre, itemOps_append] at h1
  rw [Pi.add_apply, hc2 op]
  omega

theorem brAtCB_pos (H : WHB S L j fp X segs wJ wenv σ es vs kfps hdr ck) {st st' : CW} {oc od of : ℕ}
    {x : Exit} {W0 : Regs K} {n : ℕ} {xc : Opcode → ℕ} (hp : PosZB S H st W0 n xc)
    (hb : brAtC X st = .ok (st', oc, od, of, x)) :
    st'.seg = st.seg ∧ st'.book = st.book ∧ st'.fr = st.fr ∧ st'.tg = st.tg ∧ st'.nx = st.nx ∧
      st'.uq = st.uq ∧ st'.fresh = none ∧ x ∈ st.seg.exits ∧ CWOkB S L fp X st' ∧
      ((Atom.jump oc od of).HoldsB S L (gpow fp) → rdc L fp oc = some 0 → PosZB S H st' W0 n xc) ∧
      (TakenB S L (gpow fp) oc od of → ∀ r, x.kind.Regs L (gpow fp) X.entry r → ∃ cr,
        RunCB S guest L W0 r cr ∧ (∀ op, cr op ≤ st'.cnt.get op + xc op + ksum ck n op) ∧
        EnvHolds L (gpow fp) x.env ∧ KidsOn S L es kfps n W0 r) := by
  obtain ⟨its, c, hpl, rfl⟩ := brAtC_eq hb
  obtain ⟨pre2, hpre2, hf2, hc2, -⟩ := passLB_sound H.hX hp.ok st.its st.cnt hpl
  obtain ⟨pre, c0, hpre, hf, hrun, hc0, hko⟩ := hp.run
  have hitems : st.seg.items = (pre ++ pre2) ++ .branch oc od of x :: its := by
    rw [← hpre, ← hpre2, List.append_assoc]
  have hx : x ∈ st.seg.exits := H.exits _ hp.seg x (Or.inr (by
    rw [hitems, branchExits_append]
    simp [branchExits]))
  have hok : CWOkB S L fp X ⟨st.seg, its, st.book, st.fr, st.tg, st.nx, c.bumpJ, st.uq, none, st.nm⟩ :=
    ⟨hp.ok.env, hp.ok.book, hp.ok.fr, hp.ok.tg, hp.ok.nx⟩
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, hx, hok, fun hj h0 ↦ ?_, fun ht r hr ↦ ?_⟩
  · refine ⟨hp.seg, hok, ⟨pre ++ pre2 ++ [.branch oc od of x], c0, by rw [hitems]; simp, ?_, hrun,
      fun op ↦ ?_, hko⟩, fun t ht ↦ (by cases ht), hp.nm, hp.ix⟩
    · rw [fallB_append, fallB_append]
      exact ⟨⟨hf, hf2⟩, hj, h0, trivial⟩
    · have h1 := hc0 op
      simp only [itemOps_append, Cnt.get_bumpJ, hc2 op]
      simp only [itemOps_cons, itemOps_nil, itemOp]
      omega
  · have hfall : FallB S L (gpow fp) (pre ++ pre2) := (fallB_append _ _).mpr ⟨hf, hf2⟩
    obtain ⟨cs, hcs, hle, henv⟩ := (H.segz _ hp.seg hp.ok.env).2 _ oc od of x its hitems hfall ht r hr
    refine ⟨c0 + cs, hrun.trans hcs, fun op ↦ ?_, henv, hko.reach hcs.reach⟩
    have h1 := hle op
    have h2 := hc0 op
    simp only [itemOps_append, itemOps_cons, itemOps_nil, itemOp] at h1
    rw [Pi.add_apply, Cnt.get_bumpJ, hc2 op]
    omega

/-! ## The walk -/

variable (S) in
/-- **How the walk of a window ends by the return**: the run reaches the return registers
(`main`: the final ones) within the most a path runs and the first `n` callees' counts, its
returned values at the cells after its parameters. -/
def FinZB (L : MemImage κ) (j fp : ℕ) (X : CX) (ck : List (Opcode → ℕ)) (es : List Ev) (kfps : List ℕ)
    (W0 : Regs K) (n : ℕ) (x : Opcode → ℕ) (vs' : List V) : Prop :=
  (∃ r cr, (if j = 1 then r = Regs.final guest else retRegs L (gpow fp) = some r) ∧
    RunCB S guest L W0 r cr ∧ (∀ op, cr op ≤ X.pmax.get op + x op + ksum ck n op) ∧
    KidsOn S L es kfps n W0 r) ∧
  (∀ k (hk : k < vs'.length), X.loc.cell vs'[k] = 2 + X.nargs + k ∧ 2 ≤ X.loc.cell vs'[k] ∧
    X.loc.cell vs'[k] < X.fs) ∧ vs'.length = X.nret

variable (S) in
/-- **What the walk of a block from a position gives**: on a path through the block, from a
position the run is at, the run arrives where the walk ends, or returns. -/
def WGoodB (H : WHB S L j fp X segs wJ wenv σ es vs kfps hdr ck) (ss : List Stmt) (st : CW) : Prop :=
  ∀ (ebef eaft : List Ev) (o : Out) (W0 : Regs K) (pre : List Stmt) (xc : Opcode → ℕ),
    walk σ ss = o → es = ebef ++ o.evs ++ eaft → o ≠ .stuck →
    (Stmt.noRetList ss = true ∨ (lastOkC ss = true ∧ eaft = [] ∧ (coreOf j).body = pre ++ ss)) →
    PosZB S H st W0 (calls ebef).length xc → (cw X ss st).ok = true →
    (∀ J c u, cw X ss st = .join J c u → ∃ es', o = .fall es' ∧
      ArrB S L fp X wJ wenv ck es kfps W0 J c (calls (ebef ++ es')).length (xc + costW X.acs σ ss)) ∧
    (∀ J m c u, cw X ss st = .mid J m c u → ∃ es', o = .fall es' ∧
      ArrMidB S L fp X ck es kfps W0 J m c (calls (ebef ++ es')).length (xc + costW X.acs σ ss)) ∧
    (cw X ss st = .done → ∃ es' vs', o = .ret es' vs' ∧
      FinZB S L j fp X ck es kfps W0 (calls (ebef ++ es')).length (xc + costW X.acs σ ss) vs')

theorem walkB_nilZ (H : WHB S L j fp X segs wJ wenv σ es vs kfps hdr ck) (st : CW) : WGoodB S H [] st := by
  intro ebef eaft o W0 pre xc hw hes hs hshape hp hok
  rw [walk] at hw
  subst hw
  rw [cw_nil] at hok ⊢
  refine ⟨fun J c u hj ↦ ⟨[], rfl, ?_⟩, fun J m c u hj ↦ ⟨[], rfl, ?_⟩, fun hd ↦ ?_⟩
  · rw [List.append_nil]
    rcases endC_ok hok with ⟨t, hf, he⟩ | ⟨hf, -, se, t, hse, hk, hsu, he⟩ | ⟨-, _, _, _, -, -, -, -, -, he⟩
    · rw [he] at hj
      simp only [RC.join.injEq] at hj
      obtain ⟨rfl, rfl, rfl⟩ := hj
      obtain ⟨hst, hits, hidx⟩ := hp.fresh _ hf
      obtain ⟨pre, c, hpre, -, hrun, hc, hko⟩ := hp.run
      have : pre = [] := by
        rw [hits] at hpre
        simpa using hpre
      subst this
      refine ⟨⟨c, hst ▸ hrun, fun op ↦ by simpa [itemOps, costW] using hc op, hst ▸ hko⟩, fun s hs _ ↦ ?_,
        fun _ hn ↦ by rw [hidx] at hn; cases hn⟩
      rw [hidx] at hs
      obtain rfl := Option.some.inj hs
      exact hp.ok.env
    · rw [he] at hj
      simp only [RC.join.injEq] at hj
      obtain ⟨rfl, rfl, rfl⟩ := hj
      obtain ⟨hseg, -, -, -, -, -, hr⟩ := endAtCB_reach H hp hse
      rw [hseg] at hk hsu
      obtain ⟨cr, hcr, hle, henv, hko⟩ := hr _ (by rw [hk]; rfl)
      exact ⟨⟨cr, hcr, hle, hko⟩, envAtB_of_exit H hp.seg (H.exits _ hp.seg _ (Or.inl rfl))
        (by rw [hsu]; exact List.mem_singleton_self _) henv⟩
    · rw [he] at hj
      cases hj
  · rw [List.append_nil]
    rcases endC_ok hok with ⟨t, -, he⟩ | ⟨-, -, se, t, -, -, -, he⟩ |
      ⟨-, J', m', c', -, hJ, hm, hlen, hpl, he⟩
    · rw [he] at hj
      cases hj
    · rw [he] at hj
      cases hj
    · rw [he] at hj
      simp only [RC.mid.injEq] at hj
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hj
      obtain ⟨pre2, hpre2, hf2, hc2, -⟩ := passLB_sound H.hX hp.ok _ st.cnt hpl
      obtain ⟨pre, c0, hpre, hf, hrun, hc0, hko⟩ := hp.run
      rw [List.append_nil] at hpre2
      have hl : pre.length + st.its.length = st.seg.items.length := by
        rw [← hpre, List.length_append]
      have ht : st.seg.items.take m' = pre ++ pre2 := by
        have hk : m' = pre.length + (st.its.length - (st.seg.items.length - m')) := by omega
        calc st.seg.items.take m'
            = (pre ++ st.its).take (pre.length + (st.its.length - (st.seg.items.length - m'))) := by
              rw [hpre, ← hk]
          _ = pre ++ pre2 := by
              rw [List.take_append, hpre2, List.take_of_length_le (by omega), Nat.add_sub_cancel_left]
      refine ⟨st.seg, by rw [← hJ]; exact hp.ix, hJ, hm, hp.ok.env, c0, ?_, by rw [← hJ]; exact hrun,
        fun op ↦ ?_, by rw [← hJ]; exact hko⟩
      · rw [ht, fallB_append]
        exact ⟨hf, hf2⟩
      · rw [ht, itemOps_append, hc2 op]
        have := hc0 op
        simp only [Pi.add_apply, costW, Pi.zero_apply, Nat.add_zero]
        omega
  · rcases endC_ok hok with ⟨t, -, he⟩ | ⟨-, -, se, t, -, -, -, he⟩ | ⟨-, _, _, _, -, -, -, -, -, he⟩ <;>
      rw [he] at hd <;> cases hd

/-- **A statement falling through, then the rest of the block.** -/
theorem walkB_step (H : WHB S L j fp X segs wJ wenv σ es vs kfps hdr ck) {s : Stmt} {ss : List Stmt}
    (ih : ∀ st, WGoodB S H ss st) (hs : Stmt.noRet s = true)
    {st st'' : CW} {ebef eaft e1 : List Ev} {o : Out} {W0 : Regs K} {pre : List Stmt}
    (hw1 : walk1 σ s = .fall e1) (hw : walk σ (s :: ss) = o) (hes : es = ebef ++ o.evs ++ eaft)
    (hstk : o ≠ .stuck)
    (hshape : Stmt.noRetList (s :: ss) = true ∨
      (lastOkC (s :: ss) = true ∧ eaft = [] ∧ (coreOf j).body = pre ++ s :: ss))
    {xc : Opcode → ℕ} (hp'' : PosZB S H st'' W0 (calls (ebef ++ e1)).length (xc + cost1 X.acs σ s))
    (hcw : cw X (s :: ss) st = cw X ss st'') (hok : (cw X (s :: ss) st).ok = true) :
    (∀ J c u, cw X (s :: ss) st = .join J c u → ∃ es', o = .fall es' ∧
      ArrB S L fp X wJ wenv ck es kfps W0 J c (calls (ebef ++ es')).length (xc + costW X.acs σ (s :: ss))) ∧
    (∀ J m c u, cw X (s :: ss) st = .mid J m c u → ∃ es', o = .fall es' ∧
      ArrMidB S L fp X ck es kfps W0 J m c (calls (ebef ++ es')).length (xc + costW X.acs σ (s :: ss))) ∧
    (cw X (s :: ss) st = .done → ∃ es' vs', o = .ret es' vs' ∧
      FinZB S L j fp X ck es kfps W0 (calls (ebef ++ es')).length (xc + costW X.acs σ (s :: ss)) vs') := by
  have ex : xc + costW X.acs σ (s :: ss) = (xc + cost1 X.acs σ s) + costW X.acs σ ss := by
    rw [costW, add_assoc]
  rw [ex]
  rw [walk, hw1] at hw
  subst hw
  have hstk' : walk σ ss ≠ .stuck := fun h ↦ hstk (by rw [h]; rfl)
  have hes' : es = (ebef ++ e1) ++ (walk σ ss).evs ++ eaft := by
    rw [hes]
    cases hws : walk σ ss with
    | fall _ => simp [Out.seq, Out.pre, Out.evs, List.append_assoc]
    | ret _ _ => simp [Out.seq, Out.pre, Out.evs, List.append_assoc]
    | stuck => exact absurd hws hstk'
  have hshape' : Stmt.noRetList ss = true ∨
      (lastOkC ss = true ∧ eaft = [] ∧ (coreOf j).body = (pre ++ [s]) ++ ss) := by
    rcases hshape with h | ⟨h, he, hb⟩
    · simp only [Stmt.noRetList, Bool.and_eq_true] at h
      exact Or.inl h.2
    · refine Or.inr ⟨(lastOkC_cons h fun vs hv ↦ by subst hv; simp [Stmt.noRet] at hs).2, he, ?_⟩
      rw [hb, List.append_assoc]
      rfl
  rw [hcw] at hok ⊢
  obtain ⟨h1, hm, h2⟩ := ih st'' (ebef ++ e1) eaft _ W0 (pre ++ [s]) _ rfl hes' hstk' hshape' hp'' hok
  refine ⟨fun J c u hj ↦ ?_, fun J m c u hj ↦ ?_, fun hd ↦ ?_⟩
  · obtain ⟨es', he, ha⟩ := h1 J c u hj
    refine ⟨e1 ++ es', by rw [he]; rfl, ?_⟩
    rw [← List.append_assoc]
    exact ha
  · obtain ⟨es', he, ha⟩ := hm J m c u hj
    refine ⟨e1 ++ es', by rw [he]; rfl, ?_⟩
    rw [← List.append_assoc]
    exact ha
  · obtain ⟨es', vs', he, hf⟩ := h2 hd
    refine ⟨e1 ++ es', vs', by rw [he]; rfl, ?_⟩
    rw [← List.append_assoc]
    exact hf

theorem walkB_atomZ (H : WHB S L j fp X segs wJ wenv σ es vs kfps hdr ck) (a : Core.Atom)
    (ss : List Stmt) (st : CW) (ih : ∀ st, WGoodB S H ss st) : WGoodB S H (.atom a :: ss) st := by
  intro ebef eaft o W0 pre xc hw hes hs hshape hp hok
  refine walkB_step H ih rfl rfl hw hes hs hshape ?_ (cw_atom a ss st) hok
  have hc : calls (ebef ++ [.atom a]) = calls ebef := by simp [calls, Ev.call?]
  rw [hc]
  refine ⟨hp.seg, ⟨hp.ok.env, hp.ok.book, hp.ok.fr, hp.ok.tg, hp.ok.nx⟩, hp.run, fun t ht ↦ (by cases ht),
    fun n hn ↦ ?_, hp.ix⟩
  rcases nvVals_spec _ _ n hn with h | h
  · exact hp.nm n h
  · refine uses_named (e := .atom a) ?_ h
    have hst : walk σ ss ≠ .stuck := fun h ↦ hs (by rw [← hw, walk, h]; rfl)
    rw [hes, ← hw]
    cases h : walk σ ss with
    | fall e => simp [walk, walk1, h, Out.seq, Out.pre, Out.evs]
    | ret e v => simp [walk, walk1, h, Out.seq, Out.pre, Out.evs]
    | stuck => exact absurd h hst

/-! ## Calls -/

theorem posZB_fr (H : WHB S L j fp X segs wJ wenv σ es vs kfps hdr ck) {st : CW} {W0 : Regs K} {n : ℕ}
    {xc : Opcode → ℕ} (hp : PosZB S H st W0 n xc) {q : ℕ} {fcs : List (ℕ × FC)} {kfp : ℕ}
    (hq : rdc L fp q = some (ofK (gpow kfp))) (hf : ∀ p ∈ fcs, FCHolds L fp kfp p.1 p.2) :
    PosZB S H { st with fr := (q, fcs) :: st.fr } W0 n xc :=
  ⟨hp.seg, ⟨hp.ok.env, hp.ok.book, fun x hx ↦ by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨kfp, hq, hf⟩
    · exact hp.ok.fr x hx, hp.ok.tg, hp.ok.nx⟩, hp.run, hp.fresh, hp.nm, hp.ix⟩

/-- **A call's callee frame**, its `n`-th on the path, not a loop's closing one: its pointer cell
holds it, it holds the arguments, the self frame pointer cells, the caller's frame pointer and
the return pc, and it returns there. -/
theorem callB_frame (H : WHB S L j fp X segs wJ wenv σ es vs kfps hdr ck) {n : ℕ} {c : Call}
    (hci : (calls es)[n]? = some c) {j' : ℕ} (hj1 : 2 ≤ j') (hj2 : j' < nFns)
    (hf : c.f = (coreOf j').name) {s0 : Site} (hs0 : siteC X c.args c.rets = some s0)
    (hnl : (coreOf j).loop = true → n + 1 < (calls es).length)
    (hin : inFrame X.fs (s0.q :: c.args.map X.loc.cell) = true) {selfs : List ℕ}
    (hsf : ∀ o ∈ selfs, o ∈ (certOf j').facts.env.map (·.1)) :
    ∃ kfp, kfps[n]? = some kfp ∧ rdc L fp s0.q = some (ofK (gpow kfp)) ∧
      (∀ p ∈ callFC X c.args selfs s0.r, FCHolds L fp kfp p.1 p.2) ∧
      retRegs L (gpow kfp) = some ⟨gpow s0.r, gpow fp⟩ := by
  have hlen : n < kfps.length := by
    rw [H.frame.len]
    exact (List.getElem?_eq_some_iff.mp hci).1
  refine ⟨kfps[n], List.getElem?_eq_getElem hlen, ?_⟩
  have hkfp := List.getElem?_eq_getElem hlen
  have hfr := inFrame_mem hin
  have hq : rdc L fp s0.q = some (ofK (gpow kfps[n])) := by
    have := (H.frame.site n c kfps[n] s0 hci hkfp (by rw [← siteC_eq H.sites]; exact hs0)).1
      (hfr _ List.mem_cons_self).1 (by rw [← H.fs]; exact (hfr _ List.mem_cons_self).2)
    rw [gpow_addC] at this
    exact this
  obtain ⟨h0, h1, hargs, hself⟩ := H.frame.kid n c kfps[n] hci hkfp
  have hhdr : kidHdr j fp hdr es n = (ofK (gpow s0.r), ofK (gpow fp)) := by
    unfold kidHdr
    rw [hci]
    simp only
    split_ifs with hh
    · have := hnl hh.1
      omega
    · rw [← siteC_eq H.sites, hs0]
  rw [hhdr] at h0 h1
  rw [gpow_addC] at h0 h1
  refine ⟨hq, fun p hp ↦ ?_, retRegs_eq_some_iff.mpr ⟨_, _, h0, h1, by simp⟩⟩
  unfold callFC at hp
  simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with (hp | ⟨o, ho, rfl⟩) | (rfl | rfl)
  · obtain ⟨k, hk, rfl⟩ := argFC_mem hp
    have hv : X.loc.cell c.args[k] ∈ c.args.map X.loc.cell := List.mem_map.mpr ⟨_, List.getElem_mem hk, rfl⟩
    have hc := hfr _ (List.mem_cons_of_mem _ hv)
    obtain ⟨e', hm, hc'⟩ := List.mem_filterMap.mp (List.mem_of_getElem? hci)
    have huses : c.args[k] ∈ e'.uses := by
      rcases e' with _ | _ | ⟨f', a', r'⟩ | ⟨f', a'⟩ <;> simp only [Ev.call?, Option.some.injEq,
        reduceCtorEq] at hc'
      · subst hc'; simp [Ev.uses, List.getElem_mem]
      · subst hc'; simp [Ev.uses, List.getElem_mem]
    refine ⟨σ c.args[k], val_cell H.frame H.loc (uses_named hm huses) hc.1 (H.fs ▸ hc.2), ?_⟩
    have := hargs k hk
    rw [gpow_addC] at this
    exact this
  · have hm : o ∈ selfCells c.f := by
      rw [hf, selfCells_callee hj1 hj2]
      exact hsf o ho
    have := hself o hm
    rw [gpow_addC] at this
    exact this
  · exact h1
  · exact h0

/-- A call on the path, other than to the function itself, is not a loop's last. -/
theorem notLastB (H : WHB S L j fp X segs wJ wenv σ es vs kfps hdr ck) {n : ℕ} {c : Call}
    (hc : (calls es)[n]? = some c) (hf : c.f ≠ (coreOf j).name) :
    (coreOf j).loop = true → n + 1 < (calls es).length := by
  intro hl
  have hlt : n < (calls es).length := (List.getElem?_eq_some_iff.mp hc).1
  refine lt_of_le_of_ne hlt fun he ↦ hf (H.lastCall hl c ?_)
  rw [List.getLast?_eq_getElem?, ← he, Nat.add_sub_cancel]
  exact hc

theorem walkB_callZ (H : WHB S L j fp X segs wJ wenv σ es vs kfps hdr ck) (f : String)
    (args rets : List V) (ss : List Stmt) (st : CW) (ih : ∀ st, WGoodB S H ss st) :
    WGoodB S H (.call f args rets :: ss) st := by
  intro ebef eaft o W0 pre xc hw hes hs hshape hp hok
  obtain ⟨e, q, r, j', sr, hk, hj, hf, hna, hnr, hle, hsu, hsite, hbit, hin, hself, haf, hcw⟩ :=
    cw_call H.G hok
  obtain ⟨se, s', hse, hs', rfl⟩ := afterC_ok haf
  obtain ⟨hj1, hj2, he⟩ := calleeC_some H.G hj
  have hfn : f = (coreOf j').name := by rw [hf, H.G]; rfl
  have hw' : o = (walk σ ss).pre [.call f args rets] := by rw [← hw]; rfl
  have hst' : walk σ ss ≠ .stuck := fun h ↦ hs (by rw [hw', h]; rfl)
  have hes2 : es = ebef ++ Ev.call f args rets :: ((walk σ ss).evs ++ eaft) := by
    rw [hes, hw', walk_pre_evs hst']
    simp
  set n := (calls ebef).length with hn
  have hci : (calls es)[n]? = some ⟨f, args, rets, true⟩ := by rw [hes2]; exact calls_at rfl
  obtain ⟨s0, hs0, hq0, hr0, ht0⟩ := siteOk_spec hsite
  have hnl := notLastB H hci fun h ↦ hself (h.trans H.name.symm)
  have hin' : inFrame X.fs (s0.q :: args.map X.loc.cell) = true := by
    rw [hq0]
    simp only [inFrame, Bool.and_eq_true] at hin ⊢
    refine ⟨hin.1, ?_⟩
    have h2 := hin.2
    rw [List.map_append, inFrame_append, Bool.and_eq_true] at h2
    exact h2.1
  obtain ⟨kfp, hkfp, hq, hfcs, hret⟩ := callB_frame H hci hj1 hj2 hfn hs0 hnl hin'
    (selfs := (X.G.sig j').env.map (·.1)) (fun o ho ↦ by rw [H.G] at ho; exact ho)
  rw [hq0] at hq
  rw [hr0] at hfcs hret
  obtain ⟨-, hkid⟩ := H.kids
  obtain ⟨⟨rr, hrr, hrun⟩, hrets⟩ := hkid n _ kfp hci hkfp rfl
  rw [hret] at hrr
  obtain rfl := Option.some.inj hrr
  have hp1 := posZB_fr H hp hq hfcs
  obtain ⟨hseg, hbk, hfr, htg, hnx, huq, hreach⟩ := endAtCB_reach H hp1 hse
  simp only at hseg hbk hfr htg hnx huq hreach
  obtain ⟨cr, hcr, hcle, henv, hko⟩ := hreach ⟨gpow e, gpow kfp⟩ (by
    rw [hk]
    exact ⟨_, gpow e, hq, isInK_ofK _, rfl, by simp⟩)
  have hent : entryOf f = e := by rw [hfn, entryOf_callee hj1 hj2, he]
  rw [hent] at hrun
  have hgr : gpow r = gpow (X.entry + (r - X.entry)) := by rw [Nat.add_sub_cancel' hle]
  have hrun2 : RunCB S guest L W0 ⟨gpow (X.entry + (r - X.entry)), gpow fp⟩ (cr + ck.getD n 0) := by
    rw [← hgr]
    exact hcr.trans hrun
  have hko2 : KidsOn S L es kfps (n + 1) W0 ⟨gpow (X.entry + (r - X.entry)), gpow fp⟩ := by
    rw [← hgr]
    refine (hko.reach hrun.reach).succ fun c' kfp' hc' hk' _ ↦ ?_
    obtain rfl := Option.some.inj (hc'.symm.trans hci)
    obtain rfl := Option.some.inj (hk'.symm.trans hkfp)
    exact ⟨by rw [hent]; exact hcr.reach, _, hret, ReachB.refl _⟩
  have henvR : EnvAt L fp X wJ wenv (r - X.entry) :=
    envAtB_of_exit H hp.seg (H.exits _ hp.seg _ (Or.inl rfl)) (by rw [hsu]; simp) henv
  obtain ⟨hps, hbk', hfr', htg', hnx', hcnt', huq', hstart'⟩ :=
    segAtCB_pos H (xc := xc) hs' (by rw [hbk]; exact hp.ok.book) (by rw [hfr]; exact hp1.ok.fr)
      (by rw [htg]; exact hp.ok.tg) (by rw [hnx]; exact hp.ok.nx) henvR (n := n + 1) hrun2
      (fun op ↦ by rw [Pi.add_apply, ksum_succ]; have := hcle op; omega) hko2
      (by rw [endAtC_nm hse]; exact hp.nm)
  have hc1 : (calls (ebef ++ [.call f args rets])).length = n + 1 := calls_append_one rfl
  refine walkB_step H ih rfl rfl hw hes hs hshape ?_ hcw ?_
  · rw [hc1]
    refine ⟨hps.seg, ⟨hps.ok.env, hps.ok.book, fun x hx ↦ ?_, hps.ok.tg, hps.ok.nx⟩, hps.run,
      fun t ht ↦ ?_, hps.nm, hps.ix⟩
    · rcases List.mem_cons.mp hx with rfl | hx
      · refine ⟨kfp, hq, fun p hp' ↦ ?_⟩
        rcases List.mem_append.mp hp' with hp' | hp'
        · exact hfcs p hp'
        · obtain ⟨k, hk', rfl⟩ := argFC_mem hp'
          have hv : X.loc.cell rets[k] ∈ (args ++ rets).map X.loc.cell :=
            List.mem_map.mpr ⟨_, List.mem_append_right _ (List.getElem_mem hk'), rfl⟩
          have hc := inFrame_mem hin _ (List.mem_cons_of_mem _ hv)
          have hm : Ev.call f args rets ∈ es := by rw [hes2]; simp
          refine ⟨σ rets[k], val_cell H.frame H.loc (uses_named hm (by simp [Ev.uses, List.getElem_mem]))
            hc.1 (H.fs ▸ hc.2), ?_⟩
          have := hrets k hk'
          rw [gpow_addC] at this
          exact this
      · exact hp.ok.fr x hx
    · simp only at ht
      cases hre : rets.isEmpty
      · rw [hre] at ht; cases ht
      · rw [hre] at ht
        exact hps.fresh t ht
  · exact hok

/-! ## Branches -/

theorem posZB_book (H : WHB S L j fp X segs wJ wenv σ es vs kfps hdr ck) {st : CW} {W0 : Regs K} {n : ℕ}
    {xc : Opcode → ℕ} (hp : PosZB S H st W0 n xc) {B : BookC} (hB : BookOkB S L fp B) : PosZB S H { st with book := B } W0 n xc :=
  ⟨hp.seg, ⟨hp.ok.env, hB, hp.ok.fr, hp.ok.tg, hp.ok.nx⟩, hp.run, hp.fresh, hp.nm, hp.ix⟩

/-- Entering offset `t` with given counts and set-up cells. -/
theorem segAtCB_posW (H : WHB S L j fp X segs wJ wenv σ es vs kfps hdr ck) {t : ℕ} {st sn : CW}
    (h : segAtC X t st = some sn) (hok : CWOkB S L fp X st) (he : EnvAt L fp X wJ wenv t)
    {W0 : Regs K} {n : ℕ} {xc : Opcode → ℕ} {c : Opcode → ℕ}
    (hr : RunCB S guest L W0 ⟨gpow (X.entry + t), gpow fp⟩ c)
    {C : Cnt} {U : ℕ} (hc : ∀ op, c op ≤ C.get op + xc op + ksum ck n op)
    (hko : KidsOn S L es kfps n W0 ⟨gpow (X.entry + t), gpow fp⟩)
    (hnm : ∀ n, st.nm.testBit n = true → V.n n ∈ namedOf (coreOf j).params es vs) :
    PosZB S H { sn with cnt := C, uq := U } W0 n xc ∧ sn.book = st.book ∧ sn.fr = st.fr ∧
      sn.tg = st.tg ∧ sn.nx = st.nx := by
  obtain ⟨s, hs, hst, rfl⟩ := segAtC_eq h
  have hmem : s ∈ segs := by
    rw [H.idx, getF_eq] at hs
    exact index_get hs
  refine ⟨⟨hmem, ⟨he.1 s hs hst, hok.book, hok.fr, hok.tg, hok.nx⟩,
    ⟨[], c, rfl, trivial, hst ▸ hr, fun op ↦ ?_, hst ▸ hko⟩, fun t' ht' ↦ ?_, hnm, by rw [hst]; exact hs⟩,
    rfl, rfl, rfl, rfl⟩
  · simpa [itemOps] using hc op
  · obtain rfl := Option.some.inj ht'
    exact ⟨hst, rfl, hs⟩

theorem walkB_iteZ (H : WHB S L j fp X segs wJ wenv σ es vs kfps hdr ck) (c : V) (z n ss : List Stmt)
    (st : CW) (ihz : ∀ st, WGoodB S H z st) (ihn : ∀ st, WGoodB S H n st) (ih : ∀ st, WGoodB S H ss st) :
    WGoodB S H (.ite c z n :: ss) st := by
  intro ebef eaft o W0 pre xc hw hes hs hshape hp hok
  obtain ⟨st', od, of, x, t, sn, J, c1, u1, c2, u2, sj, hb, hk, hfr, hod, hof, hsu, hsn, hz, hn,
    hsj, hcw⟩ := cw_ite hok
  obtain ⟨hseg', hbk', hfr', htg', hnx', huq', hfresh', hx, hok', hfall, htaken⟩ := brAtCB_pos H hp hb
  have hnr := noRet_of_shape (fun _ h ↦ by cases h) hshape
  simp only [Stmt.noRet, Bool.and_eq_true] at hnr
  -- the branch the path takes
  set wb := if σ c = 0 then walk σ z else walk σ n with hwb
  have hw1 : walk1 σ (.ite c z n) = wb.pre [.inK c] := rfl
  have hwo : o = (wb.pre [.inK c]).seq (walk σ ss) := by rw [← hw, walk, hw1]
  have hwb_ns : wb ≠ .stuck := fun h ↦ hs (by rw [hwo, h]; rfl)
  obtain ⟨eb, hweb⟩ : ∃ eb, wb = .fall eb := by
    rcases (show (∃ es, wb = .fall es) ∨ wb = .stuck by
      rw [hwb]; split_ifs
      · exact walk_noRetC z hnr.1
      · exact walk_noRetC n hnr.2) with h | h
    · exact h
    · exact absurd h hwb_ns
  have hst' : walk σ ss ≠ .stuck := fun h ↦ hs (by rw [hwo, hweb, h]; rfl)
  have hes2 : es = ebef ++ (Ev.inK c :: eb) ++ ((walk σ ss).evs ++ eaft) := by
    rw [hes, hwo, hweb]
    cases hws : walk σ ss with
    | fall _ => simp [Out.seq, Out.pre, Out.evs]
    | ret _ _ => simp [Out.seq, Out.pre, Out.evs]
    | stuck => exact absurd hws hst'
  have hinK : Ev.inK c ∈ es := by rw [hes2]; simp
  have hcK : IsInK (σ c) := H.hev _ hinK
  have hfc := inFrame_mem hfr _ List.mem_cons_self
  have hcell : rdc L fp (X.loc.cell c) = some (σ c) :=
    val_cell H.frame H.loc (uses_named hinK (by simp [Ev.uses])) hfc.1 (H.fs ▸ hfc.2)
  obtain ⟨vd, hvd, hKd⟩ := cellKB_sound H.hX hok' hod
  obtain ⟨vf, hvf, hKf⟩ := cellKB_sound H.hX hok' hof
  have hjump : (Atom.jump (X.loc.cell c) od of).HoldsB S L (gpow fp) :=
    ⟨σ c, vd, vf, hcell, hvd, hvf, hcK, hKd, hKf⟩
  -- the rest of the path after the branch
  have hatoms : ∀ b : List Stmt, walk σ b = .fall eb → ∀ a, Stmt.atom a ∈ b → Ev.atom a ∈ es :=
    fun b hb a ha ↦ by rw [hes2]; simp [atom_on_pathC hb ha]
  have hn1 : (calls (ebef ++ [Ev.inK c])).length = (calls ebef).length := by
    rw [calls_append_none rfl]
  -- the branch's walk, to its join
  obtain ⟨cb, hcb, crun⟩ : ∃ cb : Cnt, (cb = c1 ∨ cb = c2) ∧
      ArrB S L fp X wJ wenv ck es kfps W0 J cb (calls (ebef ++ [Ev.inK c] ++ eb)).length
        (xc + cost1 X.acs σ (.ite c z n)) := by
    by_cases h0 : σ c = 0
    · have hwz : walk σ z = .fall eb := by rw [← hweb, hwb]; simp only [h0, ↓reduceIte]
      have hpz := posZB_book H (hfall hjump (h0 ▸ hcell))
        (fileBB_ok H.frame H.loc H.hev z st'.book (hbk' ▸ hp.ok.book) (hatoms z hwz))
      have hpz' : PosZB S H { st' with book := fileB X.loc X.fs z st'.book } W0
          (calls (ebef ++ [Ev.inK c])).length xc := by
        rw [hn1, H.fs]
        exact hpz
      obtain ⟨h1, -, -⟩ := ihz _ (ebef ++ [Ev.inK c]) ((walk σ ss).evs ++ eaft) _ W0 [] xc hwz
        (by rw [hes2, show (Out.fall eb).evs = eb from rfl]; simp) (by simp) (Or.inl hnr.1) hpz' (by rw [hz]; rfl)
      obtain ⟨es', he', ha⟩ := h1 J c1 u1 hz
      simp only [Out.fall.injEq] at he'
      subst he'
      have e : cost1 X.acs σ (.ite c z n) = costW X.acs σ z := by simp only [cost1, h0, ↓reduceIte]
      exact ⟨c1, Or.inl rfl, by rw [e]; exact ha⟩
    · have hwn : walk σ n = .fall eb := by rw [← hweb, hwb]; simp only [h0, ↓reduceIte]
      obtain ⟨cr, hcr, hcle, henv, hko⟩ := htaken ⟨hjump, σ c, hcell, h0⟩ _ (by rw [hk]; rfl)
      have henvT : EnvAt L fp X wJ wenv t :=
        envAtB_of_exit H hp.seg hx (by rw [hsu]; simp) henv
      obtain ⟨hps, hbkn, -, -, -, -, -, -⟩ := segAtCB_pos H (xc := xc) hsn hok'.book hok'.fr hok'.tg hok'.nx
        henvT hcr hcle hko (by rw [brAtC_nm hb]; exact hp.nm)
      have hpn : PosZB S H { sn with book := fileB X.loc X.fs n st'.book } W0
          (calls (ebef ++ [Ev.inK c])).length xc := by
        rw [hn1, H.fs]
        exact posZB_book H hps (fileBB_ok H.frame H.loc H.hev n st'.book (hbk' ▸ hp.ok.book)
          (hatoms n hwn))
      obtain ⟨h1, -, -⟩ := ihn _ (ebef ++ [Ev.inK c]) ((walk σ ss).evs ++ eaft) _ W0 [] xc hwn
        (by rw [hes2, show (Out.fall eb).evs = eb from rfl]; simp) (by simp) (Or.inl hnr.2) hpn (by rw [hn]; rfl)
      obtain ⟨es', he', ha⟩ := h1 J c2 u2 hn
      simp only [Out.fall.injEq] at he'
      subst he'
      have e : cost1 X.acs σ (.ite c z n) = costW X.acs σ n := by simp only [cost1, h0, ↓reduceIte]
      exact ⟨c2, Or.inr rfl, by rw [e]; exact ha⟩
  -- the join, then the rest
  obtain ⟨⟨cr, hcr, hcle, hko⟩, henvJ⟩ := crun
  obtain ⟨hpj, -⟩ := segAtCB_posW H (xc := xc + cost1 X.acs σ (.ite c z n)) hsj hok' henvJ hcr
    (C := Cnt.max c1 c2) (U := Nat.lor u1 u2)
    (n := (calls (ebef ++ [Ev.inK c] ++ eb)).length)
    (fun op ↦ by
      have := hcle op
      have h1 : c1.get op ≤ Nat.max (c1.get op) (c2.get op) := Nat.le_max_left _ _
      have h2 : c2.get op ≤ Nat.max (c1.get op) (c2.get op) := Nat.le_max_right _ _
      rw [Cnt.get_max]
      rcases hcb with rfl | rfl <;> omega) hko
    (by rw [brAtC_nm hb]; exact hp.nm)
  have hw1' : walk1 σ (.ite c z n) = .fall (Ev.inK c :: eb) := by rw [hw1, hweb]; rfl
  refine walkB_step H ih (by simp [Stmt.noRet, hnr.1, hnr.2]) hw1' hw hes hs hshape ?_ hcw hok
  rw [show ebef ++ Ev.inK c :: eb = ebef ++ [Ev.inK c] ++ eb by simp]
  exact hpj

/-! ## Conditional calls -/

theorem posZB_nx (H : WHB S L j fp X segs wJ wenv σ es vs kfps hdr ck) {st : CW} {W0 : Regs K} {n : ℕ}
    {xc : Opcode → ℕ} (hp : PosZB S H st W0 n xc) {nx : List (ℕ × FC)} (hn : NxOk L fp X.fs nx) :
    PosZB S H { st with nx := nx } W0 n xc :=
  ⟨hp.seg, ⟨hp.ok.env, hp.ok.book, hp.ok.fr, hp.ok.tg, hn⟩, hp.run, hp.fresh, hp.nm, hp.ix⟩

/-- **A conditional call**, along the path: of another function, or a loop's closing one. -/
theorem walkB_callIfZ (H : WHB S L j fp X segs wJ wenv σ es vs kfps hdr ck) (c : V) (f : String)
    (args : List V) (ss : List Stmt) (st : CW) (ih : ∀ st, WGoodB S H ss st) :
    WGoodB S H (.callIf c f args :: ss) st := by
  intro ebef eaft o W0 pre xc hw hes hs hshape hp hok
  obtain ⟨x, hpk, hin, hcase⟩ := cw_callIf H.G hok
  set ev : Ev := if σ c = 0 then Ev.skip f args else Ev.call f args [] with hev
  have hwo : o = (walk σ ss).pre [.inK c, ev] := by rw [← hw]; rfl
  have hst' : walk σ ss ≠ .stuck := fun h ↦ hs (by rw [hwo, h]; rfl)
  have hes2 : es = (ebef ++ [Ev.inK c]) ++ ev :: ((walk σ ss).evs ++ eaft) := by
    rw [hes, hwo, walk_pre_evs hst']
    simp
  have hinK : Ev.inK c ∈ es := by rw [hes2]; simp
  have hcK : IsInK (σ c) := H.hev _ hinK
  have hfr0 := inFrame_mem hin _ List.mem_cons_self
  have hcell : rdc L fp (X.loc.cell c) = some (σ c) :=
    val_cell H.frame H.loc (uses_named hinK (by simp [Ev.uses])) hfr0.1 (H.fs ▸ hfr0.2)
  set n := (calls ebef).length with hn
  have hn' : (calls (ebef ++ [Ev.inK c])).length = n := by rw [calls_append_none rfl]
  have hci : (calls es)[n]? = some ⟨f, args, [], !(decide (σ c = 0))⟩ := by
    rw [hes2, ← hn']
    exact calls_at (callIf_ev c f args)
  have hc1 : (calls (ebef ++ [Ev.inK c, ev])).length = n + 1 := by
    rw [show ebef ++ [Ev.inK c, ev] = (ebef ++ [Ev.inK c]) ++ [ev] by simp,
      calls_append_one (callIf_ev c f args), hn']
  have hargs : ∀ k (hk : k < args.length), rdc L fp (X.loc.cell args[k]) = some (σ args[k]) := by
    intro k hk
    have hv : X.loc.cell args[k] ∈ X.loc.cell c :: args.map X.loc.cell :=
      List.mem_cons_of_mem _ (List.mem_map.mpr ⟨_, List.getElem_mem hk, rfl⟩)
    have hc := inFrame_mem hin _ hv
    have hevm : ev ∈ es := by rw [hes2]; simp
    refine val_cell H.frame H.loc (uses_named hevm ?_) hc.1 (H.fs ▸ hc.2)
    rw [hev]
    split_ifs <;> simp [Ev.uses, List.getElem_mem]
  rcases hcase with ⟨e, q, r, j', st', oc', od, of, x', se, t, sr, hk, hj, hf, hna, hnr, hle, hsu,
      hsite, hbit, hinq, hfne, hb, hod, hof, hse, ht, hrt, hsu', hsr, hcw⟩ |
    ⟨e, Sz, st', oc', od, of, x', se, hk, hss, he, hf, hS, hna, hnr, hmain, hsn, hb, hod, hof,
      hle1, hse, hkr, hle2, hcw⟩
  · -- a call of another function
    obtain ⟨hj1, hj2, hent⟩ := calleeC_some H.G hj
    have hfn : f = (coreOf j').name := by rw [hf, H.G]; rfl
    obtain ⟨s0, hs0, hq0, hr0, -⟩ := siteOk_spec hsite
    have hnl := notLastB H hci fun h ↦ hfne (h.trans H.name.symm)
    have hin' : inFrame X.fs (s0.q :: args.map X.loc.cell) = true := by
      rw [hq0]
      simp only [inFrame, Bool.and_eq_true] at hin hinq ⊢
      exact ⟨hinq.1, hin.2⟩
    obtain ⟨kfp, hkfp, hq, hfcs, hret⟩ := callB_frame H hci hj1 hj2 hfn hs0 hnl hin'
      (selfs := (X.G.sig j').env.map (·.1)) (fun o ho ↦ by rw [H.G] at ho; exact ho)
    rw [hq0] at hq
    rw [hr0] at hfcs hret
    have hp1 := posZB_fr H hp hq hfcs
    obtain ⟨hseg', -, -, -, -, -, -, hx, hok', hfall, htaken⟩ := brAtCB_pos H hp1 hb
    have hpk' := brAtC_peek hb
    simp only at hpk' hseg' hx
    rw [hpk] at hpk'
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hpk')
    obtain ⟨vd, hvd, hKd⟩ := cellKB_sound H.hX hok' hod
    obtain ⟨vf, hvf, hKf⟩ := cellKB_sound H.hX hok' hof
    have hjump : (Atom.jump (X.loc.cell c) od of).HoldsB S L (gpow fp) :=
      ⟨σ c, vd, vf, hcell, hvd, hvf, hcK, hKd, hKf⟩
    have hgr : gpow r = gpow (X.entry + (r - X.entry)) := by rw [Nat.add_sub_cancel' hle]
    obtain ⟨cr, hcr, hcle, henvR, hkoR⟩ : ∃ cr,
        RunCB S guest L W0 ⟨gpow (X.entry + (r - X.entry)), gpow fp⟩ cr ∧
        (∀ op, cr op ≤ (Cnt.max se.cnt st'.cnt).get op + xc op + ksum ck (n + 1) op) ∧
        EnvAt L fp X wJ wenv (r - X.entry) ∧
        KidsOn S L es kfps (n + 1) W0 ⟨gpow (X.entry + (r - X.entry)), gpow fp⟩ := by
      by_cases h0 : σ c = 0
      · have hp' := hfall hjump (h0 ▸ hcell)
        obtain ⟨hsg, -, -, -, -, -, hr⟩ := endAtCB_reach H hp' hse
        rw [hsg] at ht hsu'
        obtain ⟨cr, hcr, hle', henv, hko⟩ := hr ⟨gpow (X.entry + t), gpow fp⟩ (by rw [ht]; rfl)
        rw [hrt] at hcr hko
        refine ⟨cr, hcr, fun op ↦ ?_, ?_, hko.succ fun c' kfp' hc' _ ht' ↦ ?_⟩
        · have := hle' op
          have h1 : se.cnt.get op ≤ Nat.max (se.cnt.get op) (st'.cnt.get op) := Nat.le_max_left _ _
          have h2 := ksum_mono ck (show n ≤ n + 1 by omega) op
          rw [Cnt.get_max]
          omega
        · rw [← hrt]
          exact envAtB_of_exit H hp'.seg (H.exits _ hp'.seg _ (Or.inl rfl)) (by rw [hsu']; simp) henv
        · obtain rfl := Option.some.inj (hc'.symm.trans hci)
          simp [h0] at ht'
      · obtain ⟨cr, hcr, hle', henv, hko⟩ := htaken ⟨hjump, σ c, hcell, h0⟩ ⟨gpow e, gpow kfp⟩
          (by rw [hk]; exact ⟨_, gpow e, hq, isInK_ofK _, rfl, by simp⟩)
        obtain ⟨-, hkid⟩ := H.kids
        obtain ⟨⟨rr, hrr, hrun⟩, -⟩ := hkid n _ kfp hci hkfp (by simp [h0])
        rw [hret] at hrr
        obtain rfl := Option.some.inj hrr
        have hentf : entryOf f = e := by rw [hfn, entryOf_callee hj1 hj2, hent]
        rw [hentf] at hrun
        refine ⟨cr + ck.getD n 0, by rw [← hgr]; exact hcr.trans hrun, fun op ↦ ?_, ?_, ?_⟩
        · have h2 : st'.cnt.get op ≤ (Cnt.max se.cnt st'.cnt).get op := by
            rw [Cnt.get_max]
            exact Nat.le_max_right _ _
          rw [Pi.add_apply, ksum_succ]
          have := hle' op
          omega
        · exact envAtB_of_exit H hp.seg hx (by rw [hsu]; simp) henv
        · rw [← hgr]
          refine (hko.reach hrun.reach).succ fun c' kfp' hc' hk' _ ↦ ?_
          obtain rfl := Option.some.inj (hc'.symm.trans hci)
          obtain rfl := Option.some.inj (hk'.symm.trans hkfp)
          exact ⟨by rw [hentf]; exact hcr.reach, _, hret, ReachB.refl _⟩
    obtain ⟨hpr, -⟩ := segAtCB_posW H (xc := xc) hsr hok' (by rw [hrt]; exact henvR) (n := n + 1)
      (C := Cnt.max se.cnt st'.cnt) (U := setK st.uq q) (by rw [hrt]; exact hcr) hcle
      (by rw [hrt]; exact hkoR) (by rw [brAtC_nm hb]; exact hp.nm)
    refine walkB_step H ih rfl rfl hw hes hs hshape (by rw [hc1]; exact hpr) hcw hok
  · -- a loop's closing call
    subst hss
    have hwo' : o = .ret [Ev.inK c, ev] [] := by rw [hwo]; rfl
    rcases hshape with hsh | ⟨-, heaft, hbody⟩
    · simp [Stmt.noRetList, Stmt.noRet] at hsh
    subst heaft
    have hloop : (coreOf j).loop = true := by
      unfold Core.Fn.loop
      rw [hbody]
      simp [hf, H.name]
    have hj1' : j ≠ 1 := fun h ↦ by simp [H.main, h] at hmain
    have hj2 : 2 ≤ j := by have := H.j1; omega
    have hes3 : es = (ebef ++ [Ev.inK c]) ++ [ev] := by
      rw [hes2]
      simp [walk, walk1, Out.seq, Out.evs]
    have hlen : (calls es).length = n + 1 := by
      rw [hes3, calls_append_one (callIf_ev c f args), hn']
    have hlenk : n < kfps.length := by rw [H.frame.len, hlen]; omega
    set kfp := kfps[n] with hkfpd
    have hkfp : kfps[n]? = some kfp := List.getElem?_eq_getElem hlenk
    have hlast : kfps.getLast? = some kfp := by
      rw [List.getLast?_eq_getElem?, show kfps.length - 1 = n by rw [H.frame.len, hlen]; omega]
      exact hkfp
    have hkt := H.frame.tail hloop kfp hlast
    have hkh : kidHdr j fp hdr es n = hdr := by
      unfold kidHdr
      rw [hci]
      simp [hloop, hlen]
    obtain ⟨h0', h1', hargsK, hselfK⟩ := H.frame.kid n _ kfp hci hkfp
    rw [hkh] at h0' h1'
    have hd0 := H.frame.hdr0
    have hd1 := H.frame.hdr1
    rw [gpow_addC] at hd0 hd1 h0' h1'
    have hnx : NxOk L fp X.fs (argFC X.loc 2 args ++ [(0, .hdr 0), (1, .hdr 1)] ++
        X.self.map (fun o ↦ (o, FC.self))) := by
      intro p hp'
      rw [show fp + X.fs = kfp by rw [hkt, H.fs]]
      simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hp'
      rcases hp' with (hp' | (rfl | rfl)) | ⟨o, ho, rfl⟩
      · obtain ⟨k, hk', rfl⟩ := argFC_mem hp'
        refine ⟨σ args[k], hargs k hk', ?_⟩
        have := hargsK k hk'
        rw [gpow_addC] at this
        exact this
      · exact ⟨hdr.1, hd0, h0'⟩
      · exact ⟨hdr.2, hd1, h1'⟩
      · have hm : o ∈ selfCells f := by
          rw [hf, H.name, selfCells_callee hj2 H.jn, ← H.self]
          exact ho
        have := hselfK o hm
        rw [gpow_addC] at this
        exact this
    have hpN := posZB_nx H hp hnx
    obtain ⟨hseg', -, -, -, -, -, -, hx, hok', hfall, htaken⟩ := brAtCB_pos H hpN hb
    have hpk' := brAtC_peek hb
    simp only at hpk' hseg' hx
    rw [hpk] at hpk'
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hpk')
    obtain ⟨vd, hvd, hKd⟩ := cellKB_sound H.hX hok' hod
    obtain ⟨vf, hvf, hKf⟩ := cellKB_sound H.hX hok' hof
    have hjump : (Atom.jump (X.loc.cell c) od of).HoldsB S L (gpow fp) :=
      ⟨σ c, vd, vf, hcell, hvd, hvf, hcK, hKd, hKf⟩
    have hrT : retRegs L (gpow fp) = some ⟨hdr.1.limb 0, hdr.2.limb 0⟩ :=
      retRegs_eq_some_iff.mpr ⟨_, _, hd0, hd1, rfl⟩
    obtain ⟨cr, hcr, hcle, hkoF⟩ : ∃ cr, RunCB S guest L W0 ⟨hdr.1.limb 0, hdr.2.limb 0⟩ cr ∧
        (∀ op, cr op ≤ X.pmax.get op + xc op + ksum ck (n + 1) op) ∧
        KidsOn S L es kfps (n + 1) W0 ⟨hdr.1.limb 0, hdr.2.limb 0⟩ := by
      by_cases h0 : σ c = 0
      · have hp' := hfall hjump (h0 ▸ hcell)
        obtain ⟨hsg, -, -, -, -, -, hr⟩ := endAtCB_reach H hp' hse
        rw [hsg] at hkr
        obtain ⟨cr, hcr, hle', -, hko⟩ := hr _ (by rw [hkr]; exact hrT)
        refine ⟨cr, hcr, fun op ↦ ?_, hko.succ fun c' kfp' hc' _ ht' ↦ ?_⟩
        · have := hle' op
          have h1 := Cnt.le_spec hle2 op
          have h2 := ksum_mono ck (show n ≤ n + 1 by omega) op
          omega
        · obtain rfl := Option.some.inj (hc'.symm.trans hci)
          simp [h0] at ht'
      · obtain ⟨cr, hcr, hle', -, hko⟩ := htaken ⟨hjump, σ c, hcell, h0⟩ ⟨gpow e, gpow fp * gpow Sz⟩
          (by rw [hk]; exact ⟨_, _, rfl, rfl, rfl⟩)
        obtain ⟨-, hkid⟩ := H.kids
        obtain ⟨⟨rr, hrr, hrun⟩, -⟩ := hkid n _ kfp hci hkfp (by simp [h0])
        have hrr' : retRegs L (gpow kfp) = some ⟨hdr.1.limb 0, hdr.2.limb 0⟩ :=
          retRegs_eq_some_iff.mpr ⟨_, _, h0', h1', rfl⟩
        rw [hrr'] at hrr
        obtain rfl := Option.some.inj hrr
        have hentf : entryOf f = e := by
          rw [hf, H.name, entryOf_callee hj2 H.jn, ← H.entry, he]
        have hkf : gpow fp * gpow Sz = gpow kfp := by rw [hkt, hS, H.fs, gpow_addC]
        rw [hentf, ← hkf] at hrun
        refine ⟨cr + ck.getD n 0, hcr.trans hrun, fun op ↦ ?_,
          (hko.reach hrun.reach).succ fun c' kfp' hc' hk' _ ↦ ?_⟩
        · rw [Pi.add_apply, ksum_succ]
          have := hle' op
          have h2 := Cnt.le_spec hle1 op
          omega
        · obtain rfl := Option.some.inj (hc'.symm.trans hci)
          obtain rfl := Option.some.inj (hk'.symm.trans hkfp)
          refine ⟨?_, _, hrr', ReachB.refl _⟩
          have := hcr.reach
          rw [hkf] at this
          simpa [hentf] using this
    refine ⟨fun J c' u hj ↦ (by rw [hcw] at hj; cases hj), fun J m c' u hj ↦ (by rw [hcw] at hj; cases hj),
      fun _ ↦ ⟨[Ev.inK c, ev], [], hwo', ?_⟩⟩
    rw [hc1]
    unfold FinZB
    refine ⟨⟨_, cr, ?_, hcr, hcle, hkoF⟩, fun k hk ↦ absurd hk (Nat.not_lt_zero _), hnr.symm⟩
    simp only [hj1', ↓reduceIte]
    exact hrT

/-! ## The return -/

theorem walkB_retZ (H : WHB S L j fp X segs wJ wenv σ es vs kfps hdr ck) (vs' : List V)
    (ss : List Stmt) (st : CW) : WGoodB S H (.ret vs' :: ss) st := by
  intro ebef eaft o W0 pre xc hw hes hs hshape hp hok
  obtain ⟨se, hse, hkind, hle, hlen, hrun, hin, hcw⟩ := cw_ret hok
  have hwo : o = .ret [] vs' := by
    rw [← hw, walk]
    rfl
  refine ⟨fun J c u hj ↦ (by rw [hcw] at hj; cases hj), fun J m c u hj ↦ (by rw [hcw] at hj; cases hj),
    fun _ ↦ ⟨[], vs', hwo, ?_⟩⟩
  obtain ⟨hsg, -, -, -, -, -, hr⟩ := endAtCB_reach H hp hse
  rw [hsg] at hkind
  have hd0 := H.frame.hdr0
  have hd1 := H.frame.hdr1
  rw [gpow_addC] at hd0 hd1
  have hrT : retRegs L (gpow fp) = some ⟨hdr.1.limb 0, hdr.2.limb 0⟩ :=
    retRegs_eq_some_iff.mpr ⟨_, _, hd0, hd1, rfl⟩
  obtain ⟨r, hrg, hregs⟩ : ∃ r, (if j = 1 then r = Regs.final guest else retRegs L (gpow fp) = some r) ∧
      st.seg.exit.kind.Regs L (gpow fp) X.entry r := by
    by_cases hj1 : j = 1
    · have hm : X.main = true := by rw [H.main, hj1]; rfl
      simp only [hm, ↓reduceIte] at hkind
      refine ⟨_, by simp only [hj1, ↓reduceIte]; exact final_guest, ?_⟩
      rw [hkind]
      exact ⟨_, _, rfl, rfl, rfl⟩
    · have hm : X.main = false := by rw [H.main]; simpa using hj1
      simp only [hm, Bool.false_eq_true, ↓reduceIte] at hkind
      refine ⟨_, by simp only [hj1, ↓reduceIte]; exact hrT, ?_⟩
      rw [hkind]
      exact hrT
  obtain ⟨cr, hcr, hcle, -, hko⟩ := hr r hregs
  rw [List.append_nil]
  refine ⟨⟨r, cr, hrg, hcr, fun op ↦ ?_, hko⟩, fun k hk ↦ ?_, hlen⟩
  · have h1 := hcle op
    have h2 := Cnt.le_spec hle op
    simp only [Pi.add_apply] at h1 ⊢
    omega
  have hk' : k < (vs'.map X.loc.cell).length := by simpa using hk
  have hc := runCells_get hrun k hk'
  have hf := inFrame_mem hin _ (List.getElem_mem hk')
  simp only [List.getElem_map] at hc hf
  exact ⟨hc, hf.1, hf.2⟩

end Walk


/-! ## At the deployed semantics -/

section Deployed

variable {κ : ℕ} {L : MemImage κ} {fp : ℕ}

/-- At the deployed semantics, `WHB` is `CplWalk.lean`'s `WH`. -/
theorem whB_deployed (j : ℕ) (X : CX) (segs : List Exec.Seg) (wJ : ℕ) (wenv : Trie Sym) (σ : Val)
    (es : List Ev) (vs : List V) (kfps : List ℕ) (hdr : E × E) (ck : List (Opcode → ℕ)) :
    WHB blakeDeployed L j fp X segs wJ wenv σ es vs kfps hdr ck =
      WH L j fp X segs wJ wenv σ es vs kfps hdr ck := by
  apply propext
  constructor <;> intro h <;> cases h <;> constructor <;>
    first
    | assumption
    | (simp only [segZB_deployed, kidsRunB_deployed, ev_holdsB_deployed] at *; assumption)

/-- At the deployed semantics, `ArrB` is `CplWalk.lean`'s `Arr` with the callees' entries on the
run (`KidsOn`). -/
theorem arrB_deployed (X : CX) (wJ : ℕ) (wenv : Trie Sym) (ck : List (Opcode → ℕ)) (es : List Ev)
    (kfps : List ℕ) (W0 : Regs K) (J : ℕ) (c : Cnt) (n : ℕ) (x : Opcode → ℕ) :
    ArrB blakeDeployed L fp X wJ wenv ck es kfps W0 J c n x ↔
      Arr L fp X wJ wenv ck W0 J c n x ∧
        KidsOn blakeDeployed L es kfps n W0 ⟨gpow (X.entry + J), gpow fp⟩ := by
  simp only [ArrB, Arr, runCB_deployed]
  constructor
  · rintro ⟨⟨cr, h1, h2, h3⟩, h4⟩
    exact ⟨⟨⟨cr, h1, h2⟩, h4⟩, h3⟩
  · rintro ⟨⟨⟨cr, h1, h2⟩, h4⟩, h3⟩
    exact ⟨⟨cr, h1, h2, h3⟩, h4⟩

/-- At the deployed semantics, `ArrMidB` is `CplWalk.lean`'s `ArrMid` with the callees' entries
on the run (`KidsOn`). -/
theorem arrMidB_deployed (X : CX) (ck : List (Opcode → ℕ)) (es : List Ev) (kfps : List ℕ)
    (W0 : Regs K) (J m : ℕ) (c : Cnt) (n : ℕ) (x : Opcode → ℕ) :
    ArrMidB blakeDeployed L fp X ck es kfps W0 J m c n x ↔
      ArrMid L fp X ck W0 J m c n x ∧
        KidsOn blakeDeployed L es kfps n W0 ⟨gpow (X.entry + J), gpow fp⟩ := by
  simp only [ArrMidB, ArrMid, runCB_deployed, fallB_deployed]
  constructor
  · rintro ⟨s, h1, h2, h3, h4, cr, h5, h6, h7, h8⟩
    exact ⟨⟨s, h1, h2, h3, h4, cr, h5, h6, h7⟩, h8⟩
  · rintro ⟨⟨s, h1, h2, h3, h4, cr, h5, h6, h7⟩, h8⟩
    exact ⟨s, h1, h2, h3, h4, cr, h5, h6, h7, h8⟩

/-- At the deployed semantics, `FinZB` gives `CplWalk.lean`'s `FinZ` (and the callees' entries
on the run to the return registers). -/
theorem finZB_deployed (j : ℕ) (X : CX) (ck : List (Opcode → ℕ)) (es : List Ev) (kfps : List ℕ)
    (W0 : Regs K) (n : ℕ) (x : Opcode → ℕ) (vs' : List V)
    (h : FinZB blakeDeployed L j fp X ck es kfps W0 n x vs') : FinZ L j fp X ck W0 n x vs' := by
  obtain ⟨⟨r, cr, h1, h2, h3, -⟩, h4, -⟩ := h
  exact ⟨⟨r, cr, h1, (runCB_deployed _ _ _).mp h2, h3⟩, h4⟩

end Deployed

end
end LeanVM.Guest.B2C
