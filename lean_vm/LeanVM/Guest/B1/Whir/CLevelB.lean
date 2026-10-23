/-
  LeanVM.Guest.B1.Whir.CLevelB

  A level's part after its grinding check, honestly: the squeezes, the query weights, the
  queries, the out-of-domain glue, the batching scalar stored and the glue.
-/

module

public import LeanVM.Guest.B1.Whir.CSqueezes
public import LeanVM.Guest.B1.Whir.CGlue
public import LeanVM.Guest.B1.Whir.CQueries
public import LeanVM.Guest.B1.Whir.LevelB

/-!
# A level after its grinding check, honestly

`osLevelB_final_complete`, `osLevelB_nonfinal_complete`: from the sponge's capacity (nothing
waiting), the queries' calls given (`osQueries_complete`), the honest buffers (the squeezes' rows,
the query weights `λ^i`, the roots, the intro's words at the cursor, the out-of-domain slots and
the batching scalar `β`), the level's statements hold at the values `lvBFinF` / `lvBNonF`, leaving
the capacity after the batching challenge's squeeze, the intro's two words waiting, the glued
quadratic and claim (`LvBOut`).
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-- An atom on earlier values, then a block. -/
theorem BlkF.cons {σ : Val} {k k' : ℕ} {f : ℕ → E} {ss : List Stmt} {Out : Val → Prop} {a : Atom}
    (ha : ∀ σ', AgreeBelow k σ σ' → a.Holds rd σ') (h : BlkF C rd σ k k' f ss Out) :
    BlkF C rd σ k k' f (.atom a :: ss) Out := fun σ' hag hr ↦
  ⟨allOk_cons.mpr ⟨ha σ' hag, (h σ' hag hr).1⟩, (h σ' hag hr).2⟩

/-- Two blocks in sequence, the second's outcome the whole's. -/
theorem BlkF.then {σ : Val} {k k1 k2 : ℕ} {A B : List Stmt} {OutA Out : Val → Prop}
    {fA : ℕ → E} {fB : Val → ℕ → E}
    (h1 : k ≤ k1) (h2 : k1 ≤ k2) (hA : BlkF C rd σ k k1 fA A OutA)
    (hB : ∀ σ1, AgreeBelow k σ σ1 → OutA σ1 → BlkF C rd σ1 k1 k2 (fB σ1) B Out) :
    BlkF C rd σ k k2 (seqF σ k k1 fA fB) (A ++ B) Out :=
  BlkF.mono (BlkF.seq h1 h2 hA hB) fun _ h ↦ h.2

/-- What a level's part after its grinding check leaves. -/
structure LvBOut (σ' : Val) (st st' : OsSt) (Fq : Fs) (ic0 ic2 : E) (quad : List E) (t : E) :
    Prop where
  fsv : st'.fsv σ' = Fq.squeeze.2.cap
  w0 : σ' (.n st'.w0) = ic0
  w1 : σ' (.n st'.w1) = ic2
  quad : st'.quad σ' = quad
  t : σ' (.n st'.t) = t
  cb : st'.cb = st.cb
  co : st'.co = st.co + 2
  fs : st'.fs.length = 5
  can : AllCanonical (st'.fsv σ')
  below : st'.Below
  pad : PadOk σ' st'.pad
  padSome : ∃ p, st'.pad = some p ∧ p + 4 < st'.k
  k : st.k ≤ st'.k

theorem osQueries_rets (c : OsCfg) (lvl : ℕ) (lv : OsLv) (lam lamN : ℕ) (s : OsSt) :
    ∃ g, (osQueries c lvl lv lam lamN s).2 = (g + 5, g + 1, g + 2, g + 4, g + 3) ∧ s.k + 2 ≤ g := by
  refine ⟨_, rfl, ?_⟩
  have o1 := osMat_next osFch lv.foldsOff (s.k + 2)
  have o2 := osMat_next osCaps (4 * lv.capOff) (osMat osFch lv.foldsOff (s.k + 2)).2.2
  have o3 := osMat_next osFlags lv.capOff
    (osMat osCaps (4 * lv.capOff) (osMat osFch lv.foldsOff (s.k + 2)).2.2).2.2
  have o4 := osMat_next osCaps (4 * lv.capOff) ((osMat osFlags lv.capOff
    (osMat osCaps (4 * lv.capOff) (osMat osFch lv.foldsOff (s.k + 2)).2.2).2.2).2.2 + 2)
  have o5 := osMat_next osFlags lv.capOff (osMat osCaps (4 * lv.capOff) ((osMat osFlags lv.capOff
    (osMat osCaps (4 * lv.capOff) (osMat osFch lv.foldsOff (s.k + 2)).2.2).2.2).2.2 + 2)).2.2
  have o6 := osMat_next osQbp lv.posOff (osMat osFlags lv.capOff (osMat osCaps (4 * lv.capOff)
    ((osMat osFlags lv.capOff (osMat osCaps (4 * lv.capOff)
      (osMat osFch lv.foldsOff (s.k + 2)).2.2).2.2).2.2 + 2)).2.2).2.2
  show s.k + 2 ≤ (osMat osQbp lv.posOff (osMat osFlags lv.capOff (osMat osCaps (4 * lv.capOff)
    ((osMat osFlags lv.capOff (osMat osCaps (4 * lv.capOff)
      (osMat osFch lv.foldsOff (s.k + 2)).2.2).2.2).2.2 + 2)).2.2).2.2).2.2
  omega

/-- The values of a level's part after its grinding check, at the last level. -/
def lvBFinF (c : OsCfg) (lvl : ℕ) (lv : OsLv) (st : OsSt) (σ : Val) (sqz wp r0 r1 sum ic0 ic2 : E) :
    ℕ → E :=
  let sq := osSqueezes c lvl lv st
  let lam := sq.2.k - 1
  let lamN := if lv.queries ≤ 1 then lam else sq.2.k + lv.queries - 1
  let s2 : OsSt := { sq.2 with k := sq.2.k + lv.queries }
  let q := osQueries c lvl lv lam lamN s2
  let s1 : OsSt := { sq.2 with k := q.2.1, w0 := q.2.2.2.1, w1 := q.2.2.2.2.2, co := sq.2.co + 2 }
  seqF σ st.k sq.2.k (fun i ↦ segLookup (sqzSegs c lv st sqz ⟨st.fsv σ, []⟩) (i - st.k)) fun σ1 ↦
  seqF σ1 sq.2.k s2.k (lamVals (σ1 (.n lam)) sq.2.k) fun σ2 ↦
  seqF σ2 s2.k q.2.1 (queriesF c lvl lv s2 σ2 wp r0 r1 sum ic0 ic2) fun σ3 ↦
  fun i ↦ (glueVals σ3 s1 lam q.2.2.1 q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2).getD (i - s1.k) 0

/-- **The last level after its grinding check, honestly.** -/
theorem osLevelB_final_complete {c : OsCfg} {lvl : ℕ} {lv : OsLv} {st : OsSt} (σ : Val)
    (hfin : lvl = c.yrLevel)
    (hn0 : 0 < lv.squeezes) (hn5 : lv.squeezes * 5 < u128Bound)
    (hfs : st.fs.length = 5) (hb : st.Below) (hk : 34 ≤ st.k) (hcan : AllCanonical (st.fsv σ))
    (hpad : PadOk σ st.pad) (hpk : ∀ p, st.pad = some p → p + 4 < st.k)
    (sqz : E) (h0 : ∀ i < 5, LoadHolds rd sqz i ((st.fsv σ).getD i 0))
    (hm : ∀ j < lv.squeezes, SqIterMem rd lv.depth lv.posOff sqz (σ (.n osQpos)) (σ (.n osQbp))
      (gen ^ j) ((⟨st.fsv σ, []⟩ : Fs).squeezeN j).2.cap)
    (hL : IsInK (1 + gen ^ lv.squeezes) ∧ (1 + gen ^ lv.squeezes ≠ 0 →
      C (c.sqLoop lvl) [1, gen ^ lv.squeezes, sqz, σ (.n osQpos), σ (.n osQbp)] []))
    (hQ2 : 2 ≤ lv.queries)
    (hqw : ∀ i < lv.queries, LoadHolds rd (σ (.n osQw)) (lvl * c.maxQ + i)
      (((⟨st.fsv σ, []⟩ : Fs).squeezeN lv.squeezes).2.squeeze.1 ^ i))
    (hbo : lv.foldsOff < u128Bound ∧ 4 * lv.capOff < u128Bound ∧ lv.capOff < u128Bound ∧
      lv.posOff < u128Bound ∧ lv.queries / (1 + if lvl = 0 then 1 else 0) < u128Bound)
    (wp r0 r1 sum ic0 ic2 : E)
    (hRW : C ("opening_row_weights__L" ++ natStr lv.folds ++ "_L" ++ natStr (if lvl = 0 then 1 else 0))
      [σ (.n osFch) * gen ^ lv.foldsOff, wp] [])
    (hCap : C ("verify_merkle_cap__L" ++ natStr lv.capDepth)
      [σ (.n osCaps) * gen ^ (4 * lv.capOff), σ (.n osFlags) * gen ^ lv.capOff] [r0, r1])
    (hr0 : LoadHolds rd (σ (.n osRoots)) (2 * lvl) r0)
    (hr1 : LoadHolds rd (σ (.n osRoots)) (2 * lvl + 1) r1)
    (hQ : C (osQueriesName lvl lv) [σ (.n osCaps) * gen ^ (4 * lv.capOff),
      σ (.n osFlags) * gen ^ lv.capOff, ((⟨st.fsv σ, []⟩ : Fs).squeezeN lv.squeezes).2.squeeze.1,
      ((⟨st.fsv σ, []⟩ : Fs).squeezeN lv.squeezes).2.squeeze.1 ^ lv.queries,
      σ (.n osQbp) * gen ^ lv.posOff, wp,
      gen ^ (lv.queries / (1 + if lvl = 0 then 1 else 0))] [sum])
    (hi0 : LoadHolds rd (σ (.n st.cb)) st.co ic0) (hi2 : LoadHolds rd (σ (.n st.cb)) (st.co + 1) ic2)
    (hbeta : LoadHolds rd (σ (.n osBetas)) lvl
      ((⟨st.fsv σ, []⟩ : Fs).squeezeN lv.squeezes).2.squeeze.1) :
    BlkF C rd σ st.k (osLevelB c lvl lv st).2.k (lvBFinF c lvl lv st σ sqz wp r0 r1 sum ic0 ic2)
      (osLevelB c lvl lv st).1
      (fun σ' ↦ LvBOut σ' st (osLevelB c lvl lv st).2
        ((⟨st.fsv σ, []⟩ : Fs).squeezeN lv.squeezes).2 ic0 ic2
        [σ (.n st.c) + ((⟨st.fsv σ, []⟩ : Fs).squeezeN lv.squeezes).2.squeeze.1 * ic0,
          σ (.n st.b) + ((⟨st.fsv σ, []⟩ : Fs).squeezeN lv.squeezes).2.squeeze.1 * (sum + ic2),
          σ (.n st.a) + ((⟨st.fsv σ, []⟩ : Fs).squeezeN lv.squeezes).2.squeeze.1 * ic2]
        (σ (.n st.t) + ((⟨st.fsv σ, []⟩ : Fs).squeezeN lv.squeezes).2.squeeze.1 * sum) ∧
        AgreeBelow st.k σ σ') := by
  obtain ⟨hb1, hb2, hb3, hb4, hb6⟩ := hbo
  unfold lvBFinF
  set Fq := ((⟨st.fsv σ, []⟩ : Fs).squeezeN lv.squeezes).2 with hFq
  set lv0 := Fq.squeeze.1 with hlv0
  set sq := osSqueezes c lvl lv st with hsq
  set K1 := sq.2.k with hK1
  set lam := K1 - 1 with hlam
  set lamN := if lv.queries ≤ 1 then lam else K1 + lv.queries - 1 with hlamN
  set s2 : OsSt := { sq.2 with k := K1 + lv.queries } with hs2
  set q := osQueries c lvl lv lam lamN s2 with hq
  set s1 : OsSt := { sq.2 with k := q.2.1, w0 := q.2.2.2.1, w1 := q.2.2.2.2.2, co := sq.2.co + 2 }
    with hs1
  set gl := osGlue lam q.2.2.1 q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2 s1 with hgl
  have hc : (lvl = c.yrLevel) = True := eq_true hfin
  have e : osLevelB c lvl lv st = (sq.1 ++ (osLamPows lam (lvl * c.maxQ) K1 lv.queries ++
      (q.1 ++ (.atom (.load (.n lam) (.n osBetas) lvl) :: gl.1))), gl.2) := by
    rw [osLevelB_eq]
    simp only [hc, ↓reduceIte, List.append_assoc, List.nil_append, List.singleton_append]
    rfl
  rw [e]
  dsimp only
  obtain ⟨g, hqr, hqk⟩ := osQueries_rets c lvl lv lam lamN s2
  have hKs : st.k + 34 ≤ K1 := by
    show st.k + 34 ≤ (osPad st.pad (st.k + 14)).2.2 + 20
    have := osPad_next st.pad (st.k + 14); omega
  have hs2k : s2.k = K1 + lv.queries := rfl
  have hend : gl.2.k = g + 13 := by
    show q.2.1 + 8 = g + 13
    rw [hqr]
  -- the squeezes
  have hA := osSqueezes_completeC (C := C) (rd := rd) (c := c) (lvl := lvl) (lv := lv) σ hn0 hn5 hfs
    hb hk hcan hpad hpk sqz h0 hm hL
  refine BlkF.then (k1 := K1) (k2 := gl.2.k) (by omega) (by rw [hend]; omega) hA
    fun σ1 ha1 ⟨so, ha1'⟩ ↦ ?_
  have hb1' := so.below
  have el1 : σ1 (.n lam) = lv0 := so.lam
  have hqw1 : σ1 (.n osQw) = σ (.n osQw) := ha1' _ (by unfold osQw; omega)
  -- the query weights
  have hB := osLamPows_complete (C := C) (rd := rd) (base := lvl * c.maxQ) hQ2 σ1
    (show lam < K1 by omega) (show osQw < K1 by unfold osQw; omega)
    (fun i hi ↦ by rw [hqw1, el1]; exact hqw i hi)
  have hB' := BlkF.mono hB (Out' := fun σ' ↦ σ' (.n (K1 + lv.queries - 1)) = lv0 ^ lv.queries ∧
    AgreeBelow K1 σ1 σ') fun σ' ⟨h, a⟩ ↦ ⟨by rw [h, el1], a⟩
  refine BlkF.then (k1 := s2.k) (k2 := gl.2.k) (by omega) (by rw [hend]; omega) hB'
    fun σ2 ha2 ⟨hlN, ha2'⟩ ↦ ?_
  -- the queries
  have hs2b : s2.Below :=
    ⟨fun f hf ↦ Nat.lt_add_right _ (hb1'.fs f hf), Nat.lt_add_right _ hb1'.w0,
      Nat.lt_add_right _ hb1'.w1, Nat.lt_add_right _ hb1'.cb, Nat.lt_add_right _ hb1'.c,
      Nat.lt_add_right _ hb1'.b, Nat.lt_add_right _ hb1'.a, Nat.lt_add_right _ hb1'.t⟩
  have hag12 : AgreeBelow st.k σ σ2 := fun i hi ↦ (ha2' i (by omega)).trans (ha1' i hi)
  have e2 : ∀ v, v < st.k → σ2 (.n v) = σ (.n v) := fun v hv ↦ hag12 v hv
  have el2 : σ2 (.n lam) = lv0 := (ha2' lam (by omega)).trans el1
  have elN2 : σ2 (.n lamN) = lv0 ^ lv.queries := by
    simp only [hlamN, show ¬ lv.queries ≤ 1 by omega, ↓reduceIte]
    rw [show K1 + lv.queries - 1 = K1 + lv.queries - 1 from rfl]; exact hlN
  have hcb2 : σ2 (.n s2.cb) = σ (.n st.cb) := by
    rw [show s2.cb = st.cb from so.cb]; exact e2 _ hb.cb
  have hC := osQueries_complete (C := C) (rd := rd) (c := c) (lvl := lvl) (lv := lv) (lam := lam)
    (lamN := lamN) (s := s2) σ2 hs2b (by rw [hs2k]; omega) (by rw [hs2k]; omega)
    (by rw [hs2k]; simp only [hlamN]; split_ifs <;> omega) ⟨hb1, hb2, hb3, hb4, hb6⟩ wp r0 r1 sum ic0 ic2
    (by rw [e2 osFch (by unfold osFch; omega)]; exact hRW)
    (by rw [e2 osCaps (by unfold osCaps; omega), e2 osFlags (by unfold osFlags; omega)]; exact hCap)
    (by rw [e2 osRoots (by unfold osRoots; omega)]; exact hr0)
    (by rw [e2 osRoots (by unfold osRoots; omega)]; exact hr1)
    (by rw [e2 osCaps (by unfold osCaps; omega), e2 osFlags (by unfold osFlags; omega),
          e2 osQbp (by unfold osQbp; omega), el2, elN2]; exact hQ)
    (by rw [hcb2, show s2.co = st.co from so.co]; exact hi0)
    (by rw [hcb2, show s2.co = st.co from so.co]; exact hi2)
  have eq1 : q.2.1 = g + 5 := by rw [hqr]
  have eq2 : q.2.2.1 = g + 1 := by rw [hqr]
  have eq3 : q.2.2.2.1 = g + 2 := by rw [hqr]
  have eq4 : q.2.2.2.2.1 = g + 4 := by rw [hqr]
  have eq5 : q.2.2.2.2.2 = g + 3 := by rw [hqr]
  have hqk' : K1 + lv.queries + 2 ≤ g := hqk
  refine BlkF.then (k1 := q.2.1) (k2 := gl.2.k) (by rw [hs2k, eq1]; omega) (by rw [hend, eq1]; omega)
    hC fun σ3 ha3 ⟨q1, q2, q3, q4, ha3'⟩ ↦ ?_
  -- the batching scalar and the glue
  have bfs : ∀ f ∈ sq.2.fs, f < K1 := hb1'.fs
  have bcb : sq.2.cb < K1 := hb1'.cb
  have bc : sq.2.c < K1 := hb1'.c
  have bb : sq.2.b < K1 := hb1'.b
  have ba : sq.2.a < K1 := hb1'.a
  have bt : sq.2.t < K1 := hb1'.t
  have hs1b : s1.Below :=
    ⟨fun f hf ↦ by show f < q.2.1; have := bfs f hf; rw [eq1]; omega,
      by show q.2.2.2.1 < q.2.1; rw [eq1, eq3]; omega,
      by show q.2.2.2.2.2 < q.2.1; rw [eq1, eq5]; omega,
      by show sq.2.cb < q.2.1; rw [eq1]; omega,
      by show sq.2.c < q.2.1; rw [eq1]; omega,
      by show sq.2.b < q.2.1; rw [eq1]; omega,
      by show sq.2.a < q.2.1; rw [eq1]; omega,
      by show sq.2.t < q.2.1; rw [eq1]; omega⟩
  have hs1k : s1.k = q.2.1 := rfl
  have hag13 : AgreeBelow st.k σ σ3 := fun i hi ↦ (ha3' i (by omega)).trans (hag12 i hi)
  have el3 : σ3 (.n lam) = lv0 := (ha3' lam (by omega)).trans el2
  refine BlkF.cons (fun σ' ha ↦ ?_) ?_
  · show LoadHolds rd (σ' (.n osBetas)) lvl (σ' (.n lam))
    rw [ha lam (by rw [eq1]; omega), ha osBetas (by rw [eq1]; unfold osBetas; omega),
      hag13 osBetas (by unfold osBetas; omega), el3]
    exact hbeta
  have hD := osGlue_complete (C := C) (rd := rd) (beta := lam) (v := q.2.2.1) (c0 := q.2.2.2.1)
    (c1 := q.2.2.2.2.1) (c2 := q.2.2.2.2.2) (s := s1) σ3 hs1b
    (by rw [hs1k, eq1, eq2, eq3, eq4, eq5]; refine ⟨by omega, by omega, by omega, by omega, by omega⟩)
  have tr : ∀ i, i < K1 → ∀ σ', AgreeBelow s1.k σ3 σ' → σ' (.n i) = σ1 (.n i) := fun i hi σ' ha4 ↦
    (ha4 i (by rw [hs1k, eq1]; omega)).trans ((ha3' i (by omega)).trans (ha2' i hi))
  have hfsv' : ∀ σ', AgreeBelow s1.k σ3 σ' → s1.fsv σ' = sq.2.fsv σ1 := fun σ' ha4 ↦ by
    show sq.2.fs.map (fun i ↦ σ' (.n i)) = sq.2.fs.map (fun i ↦ σ1 (.n i))
    exact List.map_congr_left fun f hf ↦ tr f (bfs f hf) σ' ha4
  refine BlkF.mono hD fun σ' ⟨gq, gt, gb, ha4⟩ ↦ ⟨⟨?_, ?_, ?_, ?_, ?_, rfl, ?_, so.fs, ?_, gb, ?_, ?_, ?_⟩,
    ?_⟩
  · exact (hfsv' σ' ha4).trans so.fsv
  · show σ' (.n q.2.2.2.1) = ic0
    rw [ha4 _ (by rw [hs1k, eq1, eq3]; omega), q2]
  · show σ' (.n q.2.2.2.2.2) = ic2
    rw [ha4 _ (by rw [hs1k, eq1, eq5]; omega), q3]
  · rw [gq, el3, q2, q3, q4]
    have ec : σ3 (.n s1.c) = σ (.n st.c) := hag13 _ hb.c
    have eb : σ3 (.n s1.b) = σ (.n st.b) := hag13 _ hb.b
    have ea : σ3 (.n s1.a) = σ (.n st.a) := hag13 _ hb.a
    rw [ec, eb, ea]
  · rw [gt, el3, q1]
    have et : σ3 (.n s1.t) = σ (.n st.t) := hag13 _ hb.t
    rw [et]
  · show sq.2.co + 2 = st.co + 2
    rw [so.co]
  · show AllCanonical (s1.fsv σ')
    rw [hfsv' σ' ha4]; exact so.can
  · obtain ⟨p, hp, hp4⟩ := so.padSome
    have hp4' : p + 4 < K1 := hp4
    have hpo := so.pad
    rw [hp] at hpo
    show PadOk σ' sq.2.pad
    rw [hp]
    obtain ⟨z1, z2, z3, z4⟩ := hpo
    exact ⟨by rw [tr _ (by omega) σ' ha4]; exact z1, by rw [tr _ (by omega) σ' ha4]; exact z2,
      by rw [tr _ (by omega) σ' ha4]; exact z3, by rw [tr _ (by omega) σ' ha4]; exact z4⟩
  · obtain ⟨p, hp, hp4⟩ := so.padSome
    have hp4' : p + 4 < K1 := hp4
    refine ⟨p, hp, ?_⟩
    rw [hend]; omega
  · rw [hend]; omega
  · intro i hi
    exact (ha4 i (by rw [hs1k, eq1]; omega)).trans ((ha3' i (by omega)).trans (hag12 i hi))

end
end LeanVM.Guest.B1.Whir
