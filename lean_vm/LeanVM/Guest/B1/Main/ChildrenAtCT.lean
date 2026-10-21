/-
  LeanVM.Guest.B1.Main.ChildrenAtCT

  `main`'s loop over its children placed under a semantics `S` over an answered hash, its tree
  keeping each child's `verify_sub` tree's predicate (`ChildrenAtC.lean` with tree predicates).
-/

module

public import LeanVM.Guest.B1.Main.ChildrenAtC
public import LeanVM.Guest.B1.Main.TreeLoopT
public import LeanVM.Guest.B1.Comp.VerifySub.PlacedRoot
public import LeanVM.Guest.B1.Main.Loop100T

/-!
# The children, placed, their `verify_sub` trees kept

`loop5C_completeAtWT`: `loop5C_completeAtW` with `verify_sub` complete by trees satisfying
`VsQ D R` at every good run (`HV`), the runs chosen per child (`vr`): `__loop5`'s tree from
iteration `0` satisfies `Loop5Q VsQ vr (fs "__loop5") m 0`, i.e. iteration `j`'s node has a callee
satisfying `VsQ (vr j).1 (vr j).2` where it is placed, and its tail is iteration `j + 1`'s.
The other callees' trees are kept by predicates too: the child-claim digests' (`CQ`, callees `0`,
`1`), the DA roots' loop (`LQ`, callee `2`, `Loop100Q` here, when entered) and the statement
digest's (`SQ`, callee `4`), at their call words.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest.B1 (DisjL disj_nil disj_append bufL_disj Within LowDef CompleteAtB CompleteRelB Returns Kid
  CallsMatch OutsOk relAtIn_dmono bufL kidsBound Meaning_statement_digest Meaning_da_list_digest DaClaimsAt
  RelAtInWST CompleteAtWST KidsWST KidsSat)
open LeanVM.Guest.B1.Digest (CellsAt SdPreAtC DaListPreAtC ClPreAtC CclPreAtC)

@[expose] public section

/-- **`__loop5`'s tree from iteration `j` at `fp`, `n` iterations kept**: the node of `__loop5`, one
callee's tree satisfying `VsQ` at child `j`'s run `vr j` where it is placed, its tail the tree from
iteration `j + 1` at `fp + f5` (`f5` the loop's frame size); the child-claim digests' trees
satisfying `CQ`, the DA roots' loop's `LQ` when entered, the statement digest's `SQ`. -/
def Loop5Q (VsQ : VerifySub.VsData → VerifySub.VsRunC → ℕ → Reader → Memory.Tree → Prop)
    (vr : ℕ → VerifySub.VsData × VerifySub.VsRunC)
    (CQ : List E → List E → ℕ → Reader → Memory.Tree → Prop)
    (SQ : List E → List E → ℕ → Reader → Memory.Tree → Prop)
    (LQ : List E → ℕ → Reader → Memory.Tree → Prop) (IQ : ℕ → Reader → Val → Prop)
    (fs : String → ℕ) :
    ℕ → ℕ → ℕ → Reader → Memory.Tree → Prop
  | 0, _, _, _, _ => True
  | n + 1, j, fp, rd, t => ∃ (σ : Val) (bufs : List ℕ) (ks : List Memory.Tree) (k : Memory.Tree),
      t = Memory.Tree.node "__loop5" σ bufs (ks ++ [k]) ∧ IQ j rd σ ∧
      (∃ (kc : Memory.Tree) (b : ℕ), ks[0]? = some kc ∧
        (bases (fp + fs "__loop5" + k.total fs + bufs.sum) (ks.map (Memory.Tree.total fs)))[0]? = some b ∧
        CQ ([.n 3, .n 4, .n 19, .n 31, .n 5, .n 20, .n 6].map σ) ([.n 32, .n 33].map σ) b rd kc) ∧
      (∃ (kc : Memory.Tree) (b : ℕ), ks[1]? = some kc ∧
        (bases (fp + fs "__loop5" + k.total fs + bufs.sum) (ks.map (Memory.Tree.total fs)))[1]? = some b ∧
        CQ ([.n 7, .n 4, .n 34, .n 5, .n 8, .n 21, .n 6].map σ) ([.n 35, .n 36].map σ) b rd kc) ∧
      (σ (.n 61) ≠ 0 → ∃ (kl : Memory.Tree) (b : ℕ), ks[2]? = some kl ∧
        (bases (fp + fs "__loop5" + k.total fs + bufs.sum) (ks.map (Memory.Tree.total fs)))[2]? = some b ∧
        LQ ([.n 62, .n 52, .n 59, .n 10, .n 11, .n 12, .n 19, .n 30].map σ) b rd kl) ∧
      (∃ (kd : Memory.Tree) (b : ℕ), ks[4]? = some kd ∧
        (bases (fp + fs "__loop5" + k.total fs + bufs.sum) (ks.map (Memory.Tree.total fs)))[4]? = some b ∧
        SQ ([.n 13, .n 14, .n 42, .n 63, .n 64, .n 51].map σ) ([.n 65, .n 66].map σ) b rd kd) ∧
      (∃ (kv : Memory.Tree) (b : ℕ), ks[5]? = some kv ∧
        (bases (fp + fs "__loop5" + k.total fs + bufs.sum) (ks.map (Memory.Tree.total fs)))[5]? = some b ∧
        VsQ (vr j).1 (vr j).2 b rd kv) ∧
      Loop5Q VsQ vr CQ SQ LQ IQ fs n (j + 1) (fp + fs "__loop5") rd k

variable {S : BlakeSem}

variable {fs : String → ℕ} {cert : String → V → ℕ} {rd : Reader}

set_option maxHeartbeats 1000000 in
/-- **`__loop5`, placed**: its `m ≤ 16` children, child `c` computing `rs c` as `ChildWordsOkS`
says, each iteration's signer pair and DA roots in its own `HeapBuf`s, by a tree within
`childWS`'s weights at every `w θ`. -/
theorem loop5C_completeAtWT {Ha : List UInt8 → Option Digest} {κ : ℕ} {VsGood : VerifySub.VsData → VerifySub.VsRunC → Prop} {Bd : CalleeBounds}
    (H : CalleesAtC Ha S fs cert κ VsGood Bd) {Θ : Type} {w : Θ → String → ℕ}
    (Wt : ∀ θ, MainWeightHypsS S fs (w θ))
    (hκ : 16 ≤ κ) {m wb cpib : ℕ} {lxT cover lxS gsq spT spS carried daR daC daS seed0 seed1 glp
      cfresh : E} {seedD : Digest} (hm : m ≤ 16) (hm0 : 0 < m) (Lin : Layout)
    (rs : ℕ → ChildWords)
    (hok : ∀ c < m, ChildWordsOkC S Ha κ VsGood Lin wb cpib lxT cover lxS gsq spT spS carried daR daC daS
      seed0 seed1 glp cfresh seedD c (rs c))
    (VsQ : VerifySub.VsData → VerifySub.VsRunC → ℕ → Reader → Memory.Tree → Prop)
    (HV : ∀ D R, VsGood D R → ∀ lpA sqA outA : ℕ, ∀ (c : Θ → VerifySub.VsStat),
      (∀ θ, VerifySub.VsStatOkS S (w θ) (c θ)) →
      CompleteAtWST S fs cert w κ "verify_sub" (vsExtLR lpA sqA outA D R)
        [(digestScalars D.pi).1, (digestScalars D.pi).2, (digestScalars D.seed).1,
          (digestScalars D.seed).2, ofK (gpow lpA), ofK (gpow sqA), ofK (gpow outA)] (Returns []) Bd.vs
        (fun θ => Bd.vsW (w θ) (c θ)) (VsQ D R))
    (vr : ℕ → VerifySub.VsData × VerifySub.VsRunC)
    (hvr : ∀ c < m, ∃ lpA sqA outA : ℕ, VsGood (vr c).1 (vr c).2 ∧ (vr c).1.pi = (rs c).pd ∧
      (vr c).1.seed = seedD ∧ glp = ofK (gpow lpA) ∧ gsq = ofK (gpow sqA) ∧
      cfresh * gen ^ (106 * c) = ofK (gpow outA) ∧ SubL (vsExtLR lpA sqA outA (vr c).1 (vr c).2) Lin)
    (QC : (ℕ → ℕ) → List E → List E → List E → ℕ → Reader → Memory.Tree → Prop)
    (HC : ∀ off cs args rets Lin', (∀ rd, LowDef κ rd → MemL rd Lin' → CclPreAtC Ha off cs rd args rets) →
      LeanVM.Guest.B1.CompleteAtBST S fs cert κ "child_claim_list_digest" Lin' args (Returns rets)
        (Bd.ccl (cs.length / 4)) (QC off cs args rets))
    (QS : Digest → List E → List E → List E → ℕ → Reader → Memory.Tree → Prop)
    (HS : ∀ sig cells args rets Lin', (∀ rd, LowDef κ rd → MemL rd Lin' → SdPreAtC Ha sig cells rd args rets) →
      LeanVM.Guest.B1.CompleteAtBST S fs cert κ "statement_digest" Lin' args (Returns rets) Bd.sd
        (QS sig cells args rets))
    (HCov : ∀ i, LeanVM.Guest.B1.CompleteRelBST S fs cert κ "cover_da_root" (CoverPreAt i) Bd.cover
      (LeanVM.Guest.B1.Digest.CoverLoadsQ i)) :
    CompleteAtWST S fs cert w κ "__loop5" Lin [1, gen ^ m, ofK (gpow wb), lxT, cover, lxS, gsq, spT, spS,
      carried, daR, daC, daS, seed0, seed1, ofK (gpow cpib), glp, cfresh] (Returns [])
      (loopSum (fs "__loop5") (fun c => childBd fs Bd (rs c)) 0 m)
      (fun θ => loopSum (w θ "__loop5") (fun c => childWS S (w θ) Bd (Wt θ) (rs c)) 0 m)
      (Loop5Q VsQ vr (fun args rets b rd t => ∃ off cs, QC off cs args rets b rd t)
        (fun args rets b rd t => ∃ sig cells, QS sig cells args rets b rd t) Loop100Q
        (fun j rd σ => ∃ (b : ℕ) (dd : Digest), σ = loop5ValC rd (gen ^ m) (ofK (gpow wb)) lxT cover lxS gsq
          spT spS carried daR daC daS seed0 seed1 (ofK (gpow cpib)) glp cfresh j (rs j) (ofK (gpow b))
          (ofK (gpow (b + 2))) dd) fs m 0) := by
  have h := completeAtS_loopWT (S := S) (fs := fs) (cert := cert) (w := w) (f := "__loop5") κ Lin
    (fun j => [gen ^ j, gen ^ m, ofK (gpow wb), lxT, cover, lxS, gsq, spT, spS, carried, daR, daC,
      daS, seed0, seed1, ofK (gpow cpib), glp, cfresh]) m (fun c => childBd fs Bd (rs c))
    (fun c θ => childWS S (w θ) Bd (Wt θ) (rs c))
    (fun j fp rd t => Loop5Q VsQ vr (fun args rets b rd t => ∃ off cs, QC off cs args rets b rd t)
        (fun args rets b rd t => ∃ sig cells, QS sig cells args rets b rd t) Loop100Q
      (fun j rd σ => ∃ (b : ℕ) (dd : Digest), σ = loop5ValC rd (gen ^ m) (ofK (gpow wb)) lxT cover lxS gsq
        spT spS carried daR daC daS seed0 seed1 (ofK (gpow cpib)) glp cfresh j (rs j) (ofK (gpow b))
        (ofK (gpow (b + 2))) dd) fs (m - j) j fp rd t) (fun j hj fp mt => ?_) 0 hm0
  · simpa using h
  obtain ⟨p1, p2, p3, p4, p5⟩ := loop5_parts
  have o := hok j hj
  obtain ⟨lpA, sqA, outA, hgood, hpi, hseed, hglp, hgsq, hout, hvsub⟩ := hvr j hj
  set D := (vr j).1 with hDdef
  set R := (vr j).2 with hRdef
  obtain ⟨dd, hdl, hpd⟩ := o.pd
  obtain ⟨offx, csx, hlx, hccx⟩ := o.ccx
  obtain ⟨offs, css, hls, hccs⟩ := o.ccs
  obtain ⟨dsl, hcov⟩ := o.cov
  set r := rs j with hr
  set b := fp + fs "__loop5" + mt with hb
  set nda := r.da.length with hnda
  set cells := r.da.flatMap daCellsOf with hcells
  set Lb := bufL b [2, 4 * nda] [[(digestScalars r.sigD).1, (digestScalars r.sigD).2], cells]
    with hLb
  have hlenc : cells.length = 4 * nda := by
    rw [hcells, List.length_flatMap]
    simp only [daCellsOf_length, List.map_const', List.sum_replicate, smul_eq_mul]
    ring
  have hbl : List.Forall₂ (fun c s => c.length ≤ s) [[(digestScalars r.sigD).1,
      (digestScalars r.sigD).2], cells] [2, 4 * nda] := by
    simp only [List.forall₂_cons, List.length_cons, List.length_nil, hlenc, le_refl, and_self,
      List.Forall₂.nil]
  have hLbm : Lb = [(b, [(digestScalars r.sigD).1, (digestScalars r.sigD).2]), (b + 2, cells)] := by
    simp [hLb, bufL, bases]
  have mLb : ∀ rd, MemL rd (Lb ++ Lin) → MemL rd Lin := fun rd h => (memL_append.mp h).2
  have hsigp : ∀ rd, MemL rd (Lb ++ Lin) →
      ReadsAt rd (ofK (gpow b)) [(digestScalars r.sigD).1, (digestScalars r.sigD).2] :=
    fun rd h => (memL_append.mp h).1 (b, [(digestScalars r.sigD).1, (digestScalars r.sigD).2])
      (by rw [hLbm]; simp)
  have hcda : ∀ rd, MemL rd (Lb ++ Lin) → ReadsAt rd (ofK (gpow (b + 2))) cells :=
    fun rd h => (memL_append.mp h).1 (b + 2, cells) (by rw [hLbm]; simp)
  have hclaims : ∀ rd, MemL rd (Lb ++ Lin) → DaClaimsAt rd (ofK (gpow (b + 2))) r.da := by
    intro rd h i hi
    have := readsAt_flatMap_of (w := 4) r.da (fun a _ => daCellsOf_length a) (hcda rd h) i hi
    have g : ∀ k (hk : k < 4), LoadHolds rd (ofK (gpow (b + 2))) (4 * i + k) (daCellsOf r.da[i])[k] :=
      fun k hk => (loadHolds_mul_gen_pow _ _ _ _ _).mp (this k (by rw [daCellsOf_length]; exact hk))
    exact ⟨by rw [← Nat.add_zero (4 * i)]; exact g 0 (by omega), g 1 (by omega), g 2 (by omega),
      g 3 (by omega)⟩
  have hx : IsInK (gen ^ j * gen + gen ^ m) :=
    isInK_add (isInK_mul (gen_pow_isInK j) (by simpa using gen_pow_isInK 1)) (gen_pow_isInK _)
  -- the callees
  let ks : List Kid :=
    [⟨"child_claim_list_digest", true, [lxT, cover, r.base, 1, lxS, gen ^ r.nx, gsq], Lb ++ Lin,
        Returns [r.dx.1, r.dx.2]⟩,
      ⟨"child_claim_list_digest", true, [spT, cover, r.base * gen ^ r.nx, lxS, spS, gen ^ r.ns, gsq],
        Lb ++ Lin, Returns [r.ds.1, r.ds.2]⟩,
      ⟨"__loop100", decide (nda ≠ 0), [1, gen ^ nda, ofK (gpow (b + 2)), daR, daC, daS, r.base,
        gen ^ r.nx * gen ^ r.ns], Lb ++ Lin, Returns []⟩,
      ⟨"da_list_digest", true, [ofK (gpow (b + 2)), gen ^ nda], Lb ++ Lin,
        Returns [(digestScalars (dd)).1, (digestScalars (dd)).2]⟩,
      ⟨"statement_digest", true, [seed0, seed1, ofK (gpow b), (digestScalars (dd)).1,
        (digestScalars (dd)).2, carried * gen ^ (53 * j)], Lb ++ Lin,
        Returns [(digestScalars r.pd).1, (digestScalars r.pd).2]⟩,
      ⟨"verify_sub", true, [(digestScalars r.pd).1, (digestScalars r.pd).2, seed0, seed1, glp, gsq,
        cfresh * gen ^ (106 * j)], vsExtLR lpA sqA outA D R, Returns []⟩]
  have c1 : LeanVM.Guest.B1.CompleteAtBST S fs cert κ "child_claim_list_digest" (Lb ++ Lin)
      [lxT, cover, r.base, 1, lxS, gen ^ r.nx, gsq] (Returns [r.dx.1, r.dx.2]) (Bd.ccl r.nx)
      (fun b rd t => ∃ off cs, QC off cs [lxT, cover, r.base, 1, lxS, gen ^ r.nx, gsq]
        [r.dx.1, r.dx.2] b rd t) := by
    have := HC offx csx _ _ _ fun rd hl h => hccx rd hl (mLb rd h)
    rw [hlx, Nat.mul_div_cancel_left _ (by norm_num : 0 < 4)] at this
    exact LeanVM.Guest.B1.CompleteAtBST.qmono' this fun _ _ _ h => ⟨offx, csx, h⟩
  have c2 : LeanVM.Guest.B1.CompleteAtBST S fs cert κ "child_claim_list_digest" (Lb ++ Lin)
      [spT, cover, r.base * gen ^ r.nx, lxS, spS, gen ^ r.ns, gsq] (Returns [r.ds.1, r.ds.2])
      (Bd.ccl r.ns) (fun b rd t => ∃ off cs, QC off cs [spT, cover, r.base * gen ^ r.nx, lxS, spS,
        gen ^ r.ns, gsq] [r.ds.1, r.ds.2] b rd t) := by
    have := HC offs css _ _ _ fun rd hl h => hccs rd hl (mLb rd h)
    rw [hls, Nat.mul_div_cancel_left _ (by norm_num : 0 < 4)] at this
    exact LeanVM.Guest.B1.CompleteAtBST.qmono' this fun _ _ _ h => ⟨offs, css, h⟩
  have c3 : nda ≠ 0 → LeanVM.Guest.B1.CompleteAtBST S fs cert κ "__loop100" (Lb ++ Lin)
      [1, gen ^ nda, ofK (gpow (b + 2)), daR, daC, daS, r.base, gen ^ r.nx * gen ^ r.ns] (Returns [])
      (nda * (fs "__loop100" + Bd.cover) + fs "__loop100")
      (fun b' rd' t => Loop100Q [1, gen ^ nda, ofK (gpow (b + 2)), daR, daC, daS, r.base,
        gen ^ r.nx * gen ^ r.ns] b' rd' t) := by
    intro ht
    refine LeanVM.Guest.B1.CompleteAtBST.qmono (loop100S_completeAtBST HCov (by have := o.nda; omega)
      (by omega) (Lb ++ Lin) (fun k => (r.da.map daCellsOf).getD k []) (fun c hc => ?_) dsl
      (fun c hc rd hl h => ?_) (fun c hc k hk => ?_)) fun _ _ t h => ⟨nda, _, _, rfl, h⟩
    · rw [List.getD_eq_getElem _ _ (by simpa using hc), List.getElem_map]; rfl
    · rw [List.getD_eq_getElem _ _ (by simpa using hc), List.getElem_map]
      exact hcov c hc rd hl (mLb rd h)
    · obtain ⟨h1, h2⟩ := getElem_flatten_uniform (w := 4) (r.da.map daCellsOf)
        (fun x hx => by obtain ⟨a, -, rfl⟩ := List.mem_map.mp hx; rfl) c (by simpa using hc) k hk
      refine ⟨b + 2, cells, by rw [hLbm]; simp, by omega, ?_⟩
      have e : b + 2 + 4 * c + k - (b + 2) = 4 * c + k := by omega
      refine ⟨by rw [e, hcells, List.flatMap_def]; exact h1, ?_⟩
      simp only [e, hcells, List.flatMap_def]
      exact h2
  have c4 : CompleteAtBS S fs cert κ "da_list_digest" (Lb ++ Lin) [ofK (gpow (b + 2)), gen ^ nda]
      (Returns [(digestScalars (dd)).1, (digestScalars (dd)).2])
      (Bd.daList nda) :=
    H.da_list_digest r.da _ _ _ fun rd hl h => ⟨o.nda, rfl, hclaims rd h, dd, hdl, rfl⟩
  have c5 : LeanVM.Guest.B1.CompleteAtBST S fs cert κ "statement_digest" (Lb ++ Lin)
      [seed0, seed1, ofK (gpow b), (digestScalars (dd)).1, (digestScalars (dd)).2,
        carried * gen ^ (53 * j)] (Returns [(digestScalars r.pd).1, (digestScalars r.pd).2]) Bd.sd
      (fun b' rd' t => ∃ sig cells, QS sig cells [seed0, seed1, ofK (gpow b), (digestScalars (dd)).1,
        (digestScalars (dd)).2, carried * gen ^ (53 * j)] [(digestScalars r.pd).1, (digestScalars r.pd).2]
        b' rd' t) :=
    LeanVM.Guest.B1.CompleteAtBST.qmono' (HS r.sigD r.dcells _ _ _ fun rd hl h => ⟨seedD, dd, o.dlen,
      o.seed, hsigp rd h 0 (by simp), hsigp rd h 1 (by simp), rfl, o.defer rd (mLb rd h), r.pd, hpd,
      rfl⟩) fun _ _ _ h => ⟨r.sigD, r.dcells, h⟩
  have c6 : CompleteAtWST S fs cert w κ "verify_sub" (vsExtLR lpA sqA outA D R)
      [(digestScalars r.pd).1, (digestScalars r.pd).2, seed0, seed1, glp, gsq,
        cfresh * gen ^ (106 * j)] (Returns []) Bd.vs (fun θ => Bd.vsW (w θ) (Wt θ).vsc) (VsQ D R) := by
    have := HV D R hgood lpA sqA outA (fun θ => (Wt θ).vsc) fun θ => (Wt θ).vsOk
    obtain ⟨hs0, hs1⟩ := Prod.ext_iff.mp o.seed
    simp only at hs0 hs1
    rw [hpi, hseed] at this
    rw [hs0, hs1, hglp, hgsq, hout]
    exact this
  have hkw : KidsWST S fs cert w κ ks [Bd.ccl r.nx, Bd.ccl r.ns,
      nda * (fs "__loop100" + Bd.cover) + fs "__loop100", Bd.daList nda, Bd.sd, Bd.vs]
      [fun θ => (Wt θ).αccl * Bd.ccl r.nx / 1000, fun θ => (Wt θ).αccl * Bd.ccl r.ns / 1000,
        fun θ => nda * (Wt θ).Kl100, fun θ => (Wt θ).Bdl, fun θ => (Wt θ).Bsd,
        fun θ => Bd.vsW (w θ) (Wt θ).vsc]
      [fun b rd t => ∃ off cs, QC off cs [lxT, cover, r.base, 1, lxS, gen ^ r.nx, gsq]
          [r.dx.1, r.dx.2] b rd t,
        fun b rd t => ∃ off cs, QC off cs [spT, cover, r.base * gen ^ r.nx, lxS, spS, gen ^ r.ns, gsq]
          [r.ds.1, r.ds.2] b rd t,
        fun b' rd' t => Loop100Q [1, gen ^ nda, ofK (gpow (b + 2)), daR, daC, daS, r.base,
          gen ^ r.nx * gen ^ r.ns] b' rd' t, fun _ _ _ => True,
        fun b' rd' t => ∃ sig cells, QS sig cells [seed0, seed1, ofK (gpow b), (digestScalars (dd)).1,
          (digestScalars (dd)).2, carried * gen ^ (53 * j)] [(digestScalars r.pd).1, (digestScalars r.pd).2]
          b' rd' t, VsQ D R] := by
    refine ⟨fun _ => CompleteAtBST.toWST_tot c1 fun θ => (Wt θ).ccl,
      fun h => by simp at h,
      fun _ => CompleteAtBST.toWST_tot c2 fun θ => (Wt θ).ccl,
      fun h => by simp at h,
      fun ht => CompleteAtBST.toWST_valid (c3 (by simpa using ht))
        fun θ rd t rets hn hv hb =>
        (Wt θ).l100.from_one (e := nda) (Nat.pos_of_ne_zero (by simpa using ht))
          (by have := o.nda; omega) (by simp) (by simp) rd t rets hn hv hb,
      fun _ => show fs "__loop100" ≤ _ by omega,
      fun _ => LeanVM.Guest.B1.CompleteAtWS.toWST
        (CompleteAtB.toWS_weightLe (Bf := fun θ _ => (Wt θ).Bdl) c4 fun θ => (Wt θ).dl),
      fun h => by simp at h,
      fun _ => LeanVM.Guest.B1.CompleteAtBST.toWST_weightLe (Bf := fun θ _ => (Wt θ).Bsd) c5
        fun θ => (Wt θ).sd,
      fun h => by simp at h,
      fun _ => c6, fun h => by simp at h, trivial⟩
  refine Exists.elim (loopStepS_bufsWT (fs := fs) (cert := cert) (w := w) find_loop5 loop5_isLoop core35_split
    p1 _ p2 p3 κ Lin [gen ^ j, gen ^ m, ofK (gpow wb), lxT, cover, lxS, gsq, spT, spS, carried, daR,
      daC, daS, seed0, seed1, ofK (gpow cpib), glp, cfresh] loop5Fronts (.n 85) loop5Targs p4
    [2, 4 * nda] [[(digestScalars r.sigD).1, (digestScalars r.sigD).2], cells] hbl fp mt ks _ _ _ hkw
    (fun k hk => by simp only [ks, List.mem_cons, List.not_mem_nil, or_false] at hk
                    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
                    iterate 5 exact ⟨fun _ h => h, fun _ h => h⟩
                    exact hvsub.trans (SubL.of_mem fun q hq => List.mem_append_right _ hq))
    [gen ^ (j + 1), gen ^ m, ofK (gpow wb), lxT, cover, lxS, gsq, spT, spS, carried, daR, daC, daS,
      seed0, seed1, ofK (gpow cpib), glp, cfresh] (decide (j + 1 ≠ m))
    (fun rd t => Loop5Q VsQ vr (fun args rets b rd t => ∃ off cs, QC off cs args rets b rd t)
        (fun args rets b rd t => ∃ sig cells, QS sig cells args rets b rd t) Loop100Q
      (fun j rd σ => ∃ (b : ℕ) (dd : Digest), σ = loop5ValC rd (gen ^ m) (ofK (gpow wb)) lxT cover lxS gsq
        spT spS carried daR daC daS seed0 seed1 (ofK (gpow cpib)) glp cfresh j (rs j) (ofK (gpow b))
        (ofK (gpow (b + 2))) dd) fs (m - (j + 1)) (j + 1) (fp + fs "__loop5") rd t)
    (fun rd t => Loop5Q VsQ vr (fun args rets b rd t => ∃ off cs, QC off cs args rets b rd t)
        (fun args rets b rd t => ∃ sig cells, QS sig cells args rets b rd t) Loop100Q
      (fun j rd σ => ∃ (b : ℕ) (dd : Digest), σ = loop5ValC rd (gen ^ m) (ofK (gpow wb)) lxT cover lxS gsq
        spT spS carried daR daC daS seed0 seed1 (ofK (gpow cpib)) glp cfresh j (rs j) (ofK (gpow b))
        (ofK (gpow (b + 2))) dd) fs (m - j) j fp rd t)
    (fun rd hl hL outs ho => ?_)) fun n ⟨L, hW, hD, hNb, hS⟩ =>
      ⟨n, L, hW, hD, by
        simp only [List.sum_cons, List.sum_nil] at hNb
        simp only [childBd, ← hnda]
        omega, fun rd hl hL bt ht hn => RelAtInWST.wmono (hS rd hl hL bt (fun h => ht (by simp at h; omega))
        fun h => hn (by simpa using h)) fun θ => by
          simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, childWS, ← hnda]
          omega⟩
  match outs, ho with
  | [q1, q2, q3, q4, q5, q6], ho =>
    simp only [ks, OutsOk, Returns, forall_const] at ho
    obtain ⟨⟨e1, -⟩, ⟨e2, -⟩, e3, ⟨e4, -⟩, ⟨e5, -⟩, ⟨e6, -⟩, -⟩ := ho
    have hl16 : LowDef 16 rd := hl.mono hκ
    have hLin := mLb rd hL
    refine ⟨loop5ValC rd (gen ^ m) (ofK (gpow wb)) lxT cover lxS gsq spT spS carried daR daC daS seed0
      seed1 (ofK (gpow cpib)) glp cfresh j r (ofK (gpow b)) (ofK (gpow (b + 2))) dd, ?_,
      loop5C_holds (C := fun _ _ _ => True) hl16 j r (o.base.load hLin) o.nx o.ns o.nda trivial trivial
        o.sig (hsigp rd hL) (fun _ => trivial) trivial trivial (o.pi0.load hLin)
        (o.pi1.load hLin)
        trivial (o.next.load hLin) hx (fun _ => trivial), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [show Fn.params Data.core35 = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8,
        .n 9, .n 10, .n 11, .n 12, .n 13, .n 14, .n 15, .n 16, .n 17] from rfl, List.map_cons,
        List.map_nil, loop5ValC]; b1_look
    · simp only [List.map_cons, List.map_nil, Sum.elim_inl, Sum.elim_inr, id, loop5ValC]; b1_look
      rw [gen_pow_four, logG_gen_pow' (by have := o.nda; omega)]
    · simp only [List.map_cons, List.map_nil, bases, loop5ValC]; b1_look; rfl
    · simp only [loop5Fronts, List.map_cons, List.map_nil, mkCall, CallsMatch, ks, loop5ValC]
      b1_look
      simp only [true_and, forall_const, and_true]
      exact ⟨e1.symm, e2.symm, one_add_gen_pow_decide o.nda, fun h => ⟨rfl, (e3 h).1.symm⟩,
        ⟨rfl, e4.symm⟩, e5.symm, e6.symm⟩
    · simp only [loop5ValC]; b1_look
      exact gen_pow_succ_add_ne (by omega) (by omega)
    · simp only [loop5Targs, List.map_cons, List.map_nil, loop5ValC]; b1_look
      rw [gen_pow_mul_gen]
    · intro q hq
      have hb0 : (b, [(digestScalars r.sigD).1, (digestScalars r.sigD).2]) ∈ Lb := by rw [hLbm]; simp
      rw [p5] at hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [loop5ValC] <;> b1_look
      exacts [⟨wb + j, by rw [ofK_gpow_mul_gen, addr_ofK, Nat.add_zero], Or.inl o.base.region⟩,
        ⟨b + 0, addr_ofK b 0, Or.inr (regionL_of_mem hb0 (by simp))⟩,
        ⟨b + 1, addr_ofK b 1, Or.inr (regionL_of_mem hb0 (by simp))⟩,
        ⟨cpib + 2 * j, by rw [ofK_gpow_mul_gen, addr_ofK, Nat.add_zero], Or.inl o.pi0.region⟩,
        ⟨cpib + (2 * j + 1), by rw [ofK_gpow_mul_gen, addr_ofK, Nat.add_assoc], Or.inl o.pi1.region⟩,
        ⟨wb + (j + 1), by rw [ofK_gpow_mul_gen, addr_ofK, Nat.add_assoc], Or.inl o.next.region⟩]
    · intro kts k hkv hks ht hkt
      obtain ⟨n', hn'⟩ : ∃ n', m - j = n' + 1 := ⟨m - j - 1, by omega⟩
      rw [hn', Loop5Q]
      have hlq : (List.map (fun (Q : ℕ → Reader → Memory.Tree → Prop) b t => Q b rd t)
          [fun b rd t => ∃ off cs, QC off cs [lxT, cover, r.base, 1, lxS, gen ^ r.nx, gsq]
            [r.dx.1, r.dx.2] b rd t,
          fun b rd t => ∃ off cs, QC off cs [spT, cover, r.base * gen ^ r.nx, lxS, spS, gen ^ r.ns, gsq]
            [r.ds.1, r.ds.2] b rd t,
          fun b' rd' t => Loop100Q [1, gen ^ nda, ofK (gpow (b + 2)), daR, daC, daS, r.base,
            gen ^ r.nx * gen ^ r.ns] b' rd' t, fun _ _ _ => True,
          fun b' rd' t => ∃ sig cells, QS sig cells [seed0, seed1, ofK (gpow b), (digestScalars (dd)).1,
            (digestScalars (dd)).2, carried * gen ^ (53 * j)] [(digestScalars r.pd).1,
            (digestScalars r.pd).2] b' rd' t, VsQ D R]).length =
          (loop5Fronts.map (mkCall (loop5ValC rd (gen ^ m) (ofK (gpow wb)) lxT cover lxS gsq spT spS
            carried daR daC daS seed0 seed1 (ofK (gpow cpib)) glp cfresh j r (ofK (gpow b))
            (ofK (gpow (b + 2))) dd))).length := by simp [loop5Fronts]
      have hbl : (bases (fp + fs "__loop5" + mt + [2, 4 * nda].sum) (kts.map (Memory.Tree.total fs))).length =
          kts.length := by rw [length_bases, List.length_map]
      refine ⟨_, _, kts, k, rfl, ⟨b, dd, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · obtain ⟨kc, bc, q, hk0, hb0, hq0, hqc⟩ := kidsSat_get hkv hlq hbl hks 0 (by simp [loop5Fronts]) rfl
        simp only [List.map_cons, List.map_nil, List.getElem?_cons_zero, Option.some.injEq] at hq0
        subst hq0
        refine ⟨kc, bc, hk0, by rw [hkt]; exact hb0, ?_⟩
        simp only [loop5ValC] at hqc ⊢
        b1_look
        exact hqc
      · obtain ⟨kc, bc, q, hk1, hb1, hq1, hqc⟩ := kidsSat_get hkv hlq hbl hks 1 (by simp [loop5Fronts]) rfl
        simp only [List.map_cons, List.map_nil, List.getElem?_cons_succ, List.getElem?_cons_zero,
          Option.some.injEq] at hq1
        subst hq1
        refine ⟨kc, bc, hk1, by rw [hkt]; exact hb1, ?_⟩
        simp only [loop5ValC] at hqc ⊢
        b1_look
        exact hqc
      · intro h61
        obtain ⟨kl, bl, q, hk2, hb2, hq2, hql⟩ := kidsSat_get hkv hlq hbl hks 2 (by simp [loop5Fronts])
          (by simp only [loop5Fronts, List.map_cons, List.getElem_cons_succ, List.getElem_cons_zero,
            mkCall, decide_eq_true_eq]; exact h61)
        simp only [List.map_cons, List.map_nil, List.getElem?_cons_succ, List.getElem?_cons_zero,
          Option.some.injEq] at hq2
        subst hq2
        refine ⟨kl, bl, hk2, by rw [hkt]; exact hb2, ?_⟩
        simp only [List.map_cons, List.map_nil, loop5ValC]
        b1_look
        exact hql
      · obtain ⟨kd, bd, q, hk4, hb4, hq4, hqd⟩ := kidsSat_get hkv hlq hbl hks 4 (by simp [loop5Fronts]) rfl
        simp only [List.map_cons, List.map_nil, List.getElem?_cons_succ, List.getElem?_cons_zero,
          Option.some.injEq] at hq4
        subst hq4
        refine ⟨kd, bd, hk4, by rw [hkt]; exact hb4, ?_⟩
        simp only [List.map_cons, List.map_nil, loop5ValC]
        b1_look
        exact hqd
      · obtain ⟨kv, bv, q, hk5, hb5, hq5, hqv⟩ := kidsSat_get hkv hlq hbl hks 5 (by simp [loop5Fronts]) rfl
        simp only [List.map_cons, List.map_nil, List.getElem?_cons_succ, List.getElem?_cons_zero,
          Option.some.injEq] at hq5
        subst hq5
        exact ⟨kv, bv, hk5, by rw [hkt]; exact hb5, hqv⟩
      · by_cases hlast : j + 1 = m
        · obtain rfl : n' = 0 := by omega
          rw [Loop5Q]; trivial
        · have h' := ht (by simp only [decide_eq_true_eq]; omega)
          rwa [show n' = m - (j + 1) by omega]

end
end LeanVM.Guest.B1.Main
