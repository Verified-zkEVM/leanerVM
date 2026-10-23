/-
  LeanVM.Guest.B1.Whir.CLevelBN

  A level that is not the last, after its grinding check, honestly.
-/

module

public import LeanVM.Guest.B1.Whir.CLevelB

/-!
# A level that is not the last, after its grinding check, honestly

`osLevelB_nonfinal_complete`: as `osLevelB_final_complete`, the out-of-domain claim glued with
`λ` before the batch is glued with `β = λ²`.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-- The values of a level's part after its grinding check, at a level that is not the last. -/
def lvBNonF (c : OsCfg) (lvl : ℕ) (lv : OsLv) (st : OsSt) (σ : Val)
    (sqz wp r0 r1 sum ic0 ic2 y oc0 oc2 : E) :
    ℕ → E :=
  let sq := osSqueezes c lvl lv st
  let lam := sq.2.k - 1
  let lamN := if lv.queries ≤ 1 then lam else sq.2.k + lv.queries - 1
  let s2 : OsSt := { sq.2 with k := sq.2.k + lv.queries }
  let q := osQueries c lvl lv lam lamN s2
  let s1 : OsSt := { sq.2 with k := q.2.1, w0 := q.2.2.2.1, w1 := q.2.2.2.2.2, co := sq.2.co + 2 }
  seqF σ st.k sq.2.k (fun i ↦ segLookup (sqzSegs c lv st sqz ⟨st.fsv σ, []⟩) (i - st.k)) fun σ1 ↦
  seqF σ1 sq.2.k s2.k (lamVals (σ1 (.n lam)) sq.2.k) fun σ2 ↦
  let o := osOodGlue lvl lam s1
  seqF σ2 s2.k q.2.1 (queriesF c lvl lv s2 σ2 wp r0 r1 sum ic0 ic2) fun σ3 ↦
  seqF σ3 q.2.1 o.2.k (fun i ↦ (oodGlueVals σ3 s1 lam y oc0 oc2).getD (i - s1.k) 0) fun σ4 ↦
  fun i ↦ (glueVals σ4 o.2 (s1.k + 12) q.2.2.1 q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2).getD (i - o.2.k) 0

/-- **A level that is not the last, after its grinding check, honestly.** -/
theorem osLevelB_nonfinal_complete {c : OsCfg} {lvl : ℕ} {lv : OsLv} {st : OsSt} (σ : Val)
    (hnf : lvl ≠ c.yrLevel)
    (hn0 : 0 < lv.squeezes) (hn5 : lv.squeezes * 5 < u128Bound)
    (hfs : st.fs.length = 5) (hb : st.Below) (hk : 34 ≤ st.k) (hcan : AllCanonical (st.fsv σ))
    (hpad : PadOk σ st.pad) (hpk : ∀ p, st.pad = some p → p + 4 < st.k)
    (sqz : E) (h0 : ∀ i < 5, LoadHolds rd sqz i ((st.fsv σ).getD i 0))
    (hm : ∀ j < lv.squeezes, SqNextMem rd sqz (gen ^ j) ((⟨st.fsv σ, []⟩ : Fs).squeezeN j).2.cap)
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
    {y oc0 oc2 : E}
    (hy : LoadHolds rd (σ (.n osOod)) ((lvl + 1) * oodSlots + 1) y)
    (hc0 : LoadHolds rd (σ (.n osOod)) ((lvl + 1) * oodSlots + 2) oc0)
    (hc2 : LoadHolds rd (σ (.n osOod)) ((lvl + 1) * oodSlots + 3) oc2)
    (hlo : LoadHolds rd (σ (.n osOod)) ((lvl + 1) * oodSlots)
      ((⟨st.fsv σ, []⟩ : Fs).squeezeN lv.squeezes).2.squeeze.1)
    (hbeta : LoadHolds rd (σ (.n osBetas)) lvl
      (((⟨st.fsv σ, []⟩ : Fs).squeezeN lv.squeezes).2.squeeze.1 *
        ((⟨st.fsv σ, []⟩ : Fs).squeezeN lv.squeezes).2.squeeze.1)) :
    BlkF C rd σ st.k (osLevelB c lvl lv st).2.k
      (lvBNonF c lvl lv st σ sqz wp r0 r1 sum ic0 ic2 y oc0 oc2)
      (osLevelB c lvl lv st).1
      (fun σ' ↦ LvBOut σ' st (osLevelB c lvl lv st).2
        ((⟨st.fsv σ, []⟩ : Fs).squeezeN lv.squeezes).2 ic0 ic2
        [σ (.n st.c) + ((⟨st.fsv σ, []⟩ : Fs).squeezeN lv.squeezes).2.squeeze.1 * oc0 + ((⟨st.fsv σ, []⟩ : Fs).squeezeN lv.squeezes).2.squeeze.1 * ((⟨st.fsv σ, []⟩ : Fs).squeezeN lv.squeezes).2.squeeze.1 * ic0,
          σ (.n st.b) + ((⟨st.fsv σ, []⟩ : Fs).squeezeN lv.squeezes).2.squeeze.1 * (y + oc2) + ((⟨st.fsv σ, []⟩ : Fs).squeezeN lv.squeezes).2.squeeze.1 * ((⟨st.fsv σ, []⟩ : Fs).squeezeN lv.squeezes).2.squeeze.1 * (sum + ic2),
          σ (.n st.a) + ((⟨st.fsv σ, []⟩ : Fs).squeezeN lv.squeezes).2.squeeze.1 * oc2 + ((⟨st.fsv σ, []⟩ : Fs).squeezeN lv.squeezes).2.squeeze.1 * ((⟨st.fsv σ, []⟩ : Fs).squeezeN lv.squeezes).2.squeeze.1 * ic2]
        (σ (.n st.t) + ((⟨st.fsv σ, []⟩ : Fs).squeezeN lv.squeezes).2.squeeze.1 * y + ((⟨st.fsv σ, []⟩ : Fs).squeezeN lv.squeezes).2.squeeze.1 * ((⟨st.fsv σ, []⟩ : Fs).squeezeN lv.squeezes).2.squeeze.1 * sum) ∧
        AgreeBelow st.k σ σ') := by
  obtain ⟨hb1, hb2, hb3, hb4, hb6⟩ := hbo
  unfold lvBNonF
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
  set o := osOodGlue lvl lam s1 with ho
  set gl := osGlue (s1.k + 12) q.2.2.1 q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2 o.2 with hgl
  have hc : (lvl = c.yrLevel) = False := eq_false hnf
  have e : osLevelB c lvl lv st = (sq.1 ++ (osLamPows lam (lvl * c.maxQ) K1 lv.queries ++
      (q.1 ++ (o.1 ++ (.atom (.load (.n (s1.k + 12)) (.n osBetas) lvl) :: gl.1)))), gl.2) := by
    rw [osLevelB_eq]
    simp only [hc, ↓reduceIte, List.append_assoc, List.singleton_append]
    rfl
  rw [e]
  dsimp only
  obtain ⟨g, hqr, hqk⟩ := osQueries_rets c lvl lv lam lamN s2
  have hKs : st.k + 34 ≤ K1 := by
    show st.k + 34 ≤ (osPad st.pad (st.k + 14)).2.2 + 20
    have := osPad_next st.pad (st.k + 14); omega
  have hs2k : s2.k = K1 + lv.queries := rfl
  have hend : gl.2.k = g + 26 := by
    show q.2.1 + 13 + 8 = g + 26
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
  have eO : σ3 (.n osOod) = σ (.n osOod) := hag13 osOod (by unfold osOod; omega)
  have hO := osOodGlue_complete (C := C) (rd := rd) (lvl := lvl) (lam := lam) (s := s1) σ3 hs1b
    (by rw [hs1k, eq1]; omega) (by rw [hs1k, eq1]; omega) (y := y) (c0 := oc0) (c2 := oc2)
    (by rw [eO]; exact hy) (by rw [eO]; exact hc0) (by rw [eO]; exact hc2)
    (by rw [eO, el3]; exact hlo)
  have ho2k : o.2.k = q.2.1 + 13 := rfl
  refine BlkF.then (k1 := o.2.k) (k2 := gl.2.k) (by rw [ho2k]; omega) (by rw [hend, ho2k, eq1]; omega)
    hO fun σ4 ha4 ⟨oq, ot, ol2, ob, ha4'⟩ ↦ ?_
  have hag14 : AgreeBelow st.k σ σ4 := fun i hi ↦ (ha4' i (by rw [hs1k, eq1]; omega)).trans (hag13 i hi)
  have tr4 : ∀ i, i < q.2.1 → σ4 (.n i) = σ3 (.n i) := fun i hi ↦ ha4' i hi
  rw [el3] at oq ot ol2
  simp only [OsSt.quad, List.cons.injEq, and_true] at oq
  obtain ⟨oc, obb, oa⟩ := oq
  refine BlkF.cons (fun σ' ha ↦ ?_) ?_
  · show LoadHolds rd (σ' (.n osBetas)) lvl (σ' (.n (s1.k + 12)))
    rw [ha (s1.k + 12) (by rw [ho2k, hs1k]; omega), ha osBetas (by rw [ho2k]; unfold osBetas; omega),
      hag14 osBetas (by unfold osBetas; omega), ol2]
    exact hbeta
  have hD := osGlue_complete (C := C) (rd := rd) (beta := s1.k + 12) (v := q.2.2.1) (c0 := q.2.2.2.1)
    (c1 := q.2.2.2.2.1) (c2 := q.2.2.2.2.2) (s := o.2) σ4 ob
    (by rw [ho2k, hs1k, eq1, eq2, eq3, eq4, eq5]
        refine ⟨by omega, by omega, by omega, by omega, by omega⟩)
  have tr : ∀ i, i < K1 → ∀ σ', AgreeBelow o.2.k σ4 σ' → σ' (.n i) = σ1 (.n i) := fun i hi σ' ha5 ↦
    (ha5 i (by rw [ho2k, eq1]; omega)).trans ((tr4 i (by rw [eq1]; omega)).trans
      ((ha3' i (by omega)).trans (ha2' i hi)))
  have hfsv' : ∀ σ', AgreeBelow o.2.k σ4 σ' → o.2.fsv σ' = sq.2.fsv σ1 := fun σ' ha5 ↦ by
    show sq.2.fs.map (fun i ↦ σ' (.n i)) = sq.2.fs.map (fun i ↦ σ1 (.n i))
    exact List.map_congr_left fun f hf ↦ tr f (bfs f hf) σ' ha5
  have q2' : σ4 (.n q.2.2.2.1) = ic0 := by rw [tr4 _ (by rw [eq1, eq3]; omega), q2]
  have q3' : σ4 (.n q.2.2.2.2.2) = ic2 := by rw [tr4 _ (by rw [eq1, eq5]; omega), q3]
  have q4' : σ4 (.n q.2.2.2.2.1) = sum + ic2 := by
    rw [tr4 _ (by rw [eq1, eq4]; omega), q4]
  have q1' : σ4 (.n q.2.2.1) = sum := by rw [tr4 _ (by rw [eq1, eq2]; omega), q1]
  refine BlkF.mono hD fun σ' ⟨gq, gt, gb, ha5⟩ ↦ ⟨⟨?_, ?_, ?_, ?_, ?_, rfl, ?_, so.fs, ?_, gb, ?_, ?_, ?_⟩,
    ?_⟩
  · exact (hfsv' σ' ha5).trans so.fsv
  · show σ' (.n q.2.2.2.1) = ic0
    rw [ha5 _ (by rw [ho2k, eq1, eq3]; omega), q2']
  · show σ' (.n q.2.2.2.2.2) = ic2
    rw [ha5 _ (by rw [ho2k, eq1, eq5]; omega), q3']
  · rw [gq, ol2, q2', q3', q4']
    show [σ4 (.n o.2.c) + _, σ4 (.n o.2.b) + _, σ4 (.n o.2.a) + _] = _
    rw [oc, obb, oa]
    have ec : σ3 (.n s1.c) = σ (.n st.c) := hag13 _ hb.c
    have eb : σ3 (.n s1.b) = σ (.n st.b) := hag13 _ hb.b
    have ea : σ3 (.n s1.a) = σ (.n st.a) := hag13 _ hb.a
    rw [ec, eb, ea]
  · rw [gt, ol2, q1', ot]
    have et : σ3 (.n s1.t) = σ (.n st.t) := hag13 _ hb.t
    rw [et]
  · show sq.2.co + 2 = st.co + 2
    rw [so.co]
  · show AllCanonical (o.2.fsv σ')
    rw [hfsv' σ' ha5]; exact so.can
  · obtain ⟨p, hp, hp4⟩ := so.padSome
    have hp4' : p + 4 < K1 := hp4
    have hpo := so.pad
    rw [hp] at hpo
    show PadOk σ' sq.2.pad
    rw [hp]
    obtain ⟨z1, z2, z3, z4⟩ := hpo
    exact ⟨by rw [tr _ (by omega) σ' ha5]; exact z1, by rw [tr _ (by omega) σ' ha5]; exact z2,
      by rw [tr _ (by omega) σ' ha5]; exact z3, by rw [tr _ (by omega) σ' ha5]; exact z4⟩
  · obtain ⟨p, hp, hp4⟩ := so.padSome
    have hp4' : p + 4 < K1 := hp4
    refine ⟨p, hp, ?_⟩
    rw [hend]; omega
  · rw [hend]; omega
  · intro i hi
    exact (ha5 i (by rw [ho2k, eq1]; omega)).trans (hag14 i hi)

end
end LeanVM.Guest.B1.Whir
