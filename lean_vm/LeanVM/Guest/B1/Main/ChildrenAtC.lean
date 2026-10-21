/-
  LeanVM.Guest.B1.Main.ChildrenAtC

  `main`'s loop over its children (`__loop5`) placed under a semantics `S` over an answered hash
  `Ha` (`ChildrenAt.lean` over `S` and `Ha`).
-/

module

public import LeanVM.Guest.B1.Main.ChildrenAt
public import LeanVM.Guest.B1.Main.LoopsAtS
public import LeanVM.Guest.B1.Main.WeightLoopS
public import LeanVM.Guest.B1.Main.CalleesAtC

/-!
# The children, placed, over an answered hash

`ChildrenAt.lean` under `S : BlakeSem` over the answered hash `Ha`: the iteration's valuation
takes the DA list's digest `dd` as a word (`loop5ValC`, `loop5C_holds`), what child `c` needs
(`ChildWordsOkC`) asks the callees' preconditions over `Ha` (`CclPreAtC`) and the DA list's and the
statement's digests answered by `Ha` (`pd`), the signer set's row under `S`, and
`loop5C_completeAtW` composes the callees of `CalleesAtC Ha S`.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest.B1 (DisjL disj_nil disj_append bufL_disj Within LowDef CompleteAtB CompleteRelB Returns Kid CallsMatch OutsOk
  relAtIn_dmono bufL kidsBound Meaning_statement_digest Meaning_da_list_digest DaClaimsAt)
open LeanVM.Guest.B1.Digest (CellsAt)

@[expose] public section

variable {S : BlakeSem}

variable {fs : String → ℕ} {cert : String → V → ℕ} {rd : Reader}

/-- `__loop5`'s valuation at child `c` (`loop5Val`), the signer pair at `sigp`, the DA roots at `cda`,
the DA list's digest `dd`. -/
noncomputable def loop5ValC (rd : Reader) (N written lxT cover lxS gsq spT spS carried daR daC daS
    seed0 seed1 cpi glp cfresh : E) (c : ℕ) (r : ChildWords) (sigp cda : E) (dd : Digest) : Val :=
  setl (Val.ofArgs [gen ^ c, N, written, lxT, cover, lxS, gsq, spT, spS, carried, daR, daC, daS,
      seed0, seed1, cpi, glp, cfresh]) 18
    [written * gen ^ c, r.base, gen ^ r.nx, gen ^ r.ns, gen ^ 65535, gen ^ (65535 - r.nx),
      cellAt rd (gen ^ r.nx) 0, cellAt rd (gen ^ (65535 - r.nx)) 0,
      gen ^ 65535, gen ^ (65535 - r.ns), cellAt rd (gen ^ r.ns) 0,
      cellAt rd (gen ^ (65535 - r.ns)) 0, gen ^ r.nx * gen ^ r.ns, 1, r.dx.1, r.dx.2,
      r.base * gen ^ r.nx, r.ds.1, r.ds.2, ivCells.1, ivCells.2, metadataCell 64 true,
      (digestScalars r.sigD).1, (digestScalars r.sigD).2, sigp, gen ^ (2 * c), gen ^ (3 * c),
      gen ^ (6 * c), gen ^ (12 * c), gen ^ (13 * c), gen ^ (26 * c), gen ^ (52 * c), gen ^ (53 * c),
      carried * gen ^ (53 * c), gen ^ r.da.length, gen ^ 16, gen ^ (16 - r.da.length),
      cellAt rd (gen ^ r.da.length) 0, cellAt rd (gen ^ (16 - r.da.length)) 0,
      gen ^ r.da.length * gen ^ r.da.length,
      gen ^ r.da.length * gen ^ r.da.length * (gen ^ r.da.length * gen ^ r.da.length), cda, 1,
      1 + gen ^ r.da.length, 1, (digestScalars dd).1,
      (digestScalars dd).2, (digestScalars r.pd).1, (digestScalars r.pd).2,
      gen ^ (2 * c), cpi * gen ^ (2 * c), cpi * gen ^ (2 * c), gen ^ (2 * c),
      gen ^ (3 * c), gen ^ (6 * c), gen ^ (12 * c), gen ^ (13 * c), gen ^ (26 * c), gen ^ (52 * c),
      gen ^ (53 * c), gen ^ (106 * c), cfresh * gen ^ (106 * c), r.base * (gen ^ r.nx * gen ^ r.ns),
      r.base * (gen ^ r.nx * gen ^ r.ns) * gen ^ r.da.length, written * gen ^ c, gen, gen ^ c * gen,
      gen ^ c * gen + N, gen, gen ^ c * gen]

set_option maxRecDepth 100000 in
/-- **`__loop5`'s body at child `c`**, for any call relation holding of its calls. -/
theorem loop5C_holds {C : CallRel} (hl : LowDef 16 rd) {N written lxT cover lxS gsq spT spS carried
    daR daC daS seed0 seed1 cpi glp cfresh sigp cda : E} {dd : Digest} (c : ℕ) (r : ChildWords)
    (hbase : LoadHolds rd written c r.base) (hnx : r.nx < 2 ^ 16) (hns : r.ns < 2 ^ 16)
    (hnda : r.da.length ≤ 16)
    (hccx : C "child_claim_list_digest" [lxT, cover, r.base, 1, lxS, gen ^ r.nx, gsq]
      [r.dx.1, r.dx.2])
    (hccs : C "child_claim_list_digest" [spT, cover, r.base * gen ^ r.nx, lxS, spS, gen ^ r.ns, gsq]
      [r.ds.1, r.ds.2])
    (hsig : S.check ![r.dx.1, r.dx.2, r.ds.1, r.ds.2] ivCells.1 ivCells.2
      (digestScalars r.sigD).1 (digestScalars r.sigD).2 (metadataCell 64 true))
    (hsigp : ReadsAt rd sigp [(digestScalars r.sigD).1, (digestScalars r.sigD).2])
    (hdas : r.da.length ≠ 0 → C "__loop100"
      [1, gen ^ r.da.length, cda, daR, daC, daS, r.base, gen ^ r.nx * gen ^ r.ns] [])
    (hdl : C "da_list_digest" [cda, gen ^ r.da.length]
      [(digestScalars (dd)).1, (digestScalars (dd)).2])
    (hsd : C "statement_digest" [seed0, seed1, sigp, (digestScalars (dd)).1,
      (digestScalars (dd)).2, carried * gen ^ (53 * c)]
      [(digestScalars r.pd).1, (digestScalars r.pd).2])
    (hpi0 : LoadHolds rd cpi (2 * c) (digestScalars r.pd).1)
    (hpi1 : LoadHolds rd cpi (2 * c + 1) (digestScalars r.pd).2)
    (hvs : C "verify_sub" [(digestScalars r.pd).1, (digestScalars r.pd).2, seed0, seed1, glp, gsq,
      cfresh * gen ^ (106 * c)] [])
    (hnext : LoadHolds rd written (c + 1) (r.base * (gen ^ r.nx * gen ^ r.ns) * gen ^ r.da.length))
    (hK : IsInK (gen ^ c * gen + N))
    (htail : gen ^ c * gen + N ≠ 0 → C "__loop5" [gen ^ c * gen, N, written, lxT, cover, lxS, gsq,
      spT, spS, carried, daR, daC, daS, seed0, seed1, cpi, glp, cfresh] []) :
    Stmt.HoldsListB S C rd (loop5ValC rd N written lxT cover lxS gsq spT spS carried daR daC daS seed0
      seed1 cpi glp cfresh c r sigp cda dd) (Fn.body Data.core35) False (fun rs => rs = []) := by
  simp only [show Fn.body Data.core35 = Data.core35.body from rfl, Data.core35.body,
    Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, List.map_cons, List.map_nil, word_gen, word_one,
    word_iv0, word_iv1, word_md64, word_gmax, word_g16, loop5ValC]
  b1_look
  simp only [true_and, and_true]
  have hKd : IsInK (1 + gen ^ r.da.length) :=
    isInK_add (by simpa using gen_pow_isInK 0) (gen_pow_isInK _)
  exact ⟨loadHolds_of_mul0 rfl hbase,
    ⟨loadHolds_cellAt_gen hl hnx, gen_pow_mul_gmax (by omega), loadHolds_cellAt_gen hl (by omega)⟩,
    ⟨loadHolds_cellAt_gen hl hns, gen_pow_mul_gmax (by omega), loadHolds_cellAt_gen hl (by omega)⟩,
    hccx, hccs, rfl, rfl, hsig,
    by simpa using hsigp 0 (by simp), by simpa using hsigp 1 (by simp), by ring, by ring, by ring,
    by ring, by ring, by ring, by ring, by ring,
    ⟨loadHolds_cellAt_gen hl (by omega), by rw [← pow_add]; congr 1; omega,
      loadHolds_cellAt_gen hl (by omega)⟩, hKd,
    fun hne => hdas fun h0 => hne (by rw [h0, pow_zero]; exact e_add_eq_zero_iff.mpr rfl), hdl,
    hsd, by ring, loadHolds_of_mul0 rfl hpi0, loadHolds_of_mul rfl hpi1, by ring, by ring, by ring,
    by ring, by ring, by ring, by ring, by ring, by ring, hvs, loadHolds_of_mul rfl hnext, hK,
    htail⟩

/-! ## Placed -/

variable (S) in
/-- **What child `c`'s iteration needs** of the caller's layout `Lin` (the running counts at
`wb`, the public inputs at `cpib`) and of its callees' preconditions on every memory holding
`Lin`, the seed `seedD`. -/
structure ChildWordsOkC (Ha : List UInt8 → Option Digest) (κ : ℕ) (VsGood : VerifySub.VsData → Prop) (Lin : Layout) (wb cpib : ℕ)
    (lxT cover lxS gsq spT spS carried daR daC daS seed0 seed1 glp cfresh : E) (seedD : Digest)
    (c : ℕ) (r : ChildWords) : Prop where
  base : CellL Lin (wb + c) r.base
  next : CellL Lin (wb + (c + 1)) (r.base * (gen ^ r.nx * gen ^ r.ns) * gen ^ r.da.length)
  nx : r.nx < 2 ^ 16
  ns : r.ns < 2 ^ 16
  nda : r.da.length ≤ 16
  ccx : ∃ off cs, cs.length = 4 * r.nx ∧ ∀ rd, LowDef κ rd → MemL rd Lin →
    CclPreAtC Ha off cs rd [lxT, cover, r.base, 1, lxS, gen ^ r.nx, gsq] [r.dx.1, r.dx.2]
  ccs : ∃ off cs, cs.length = 4 * r.ns ∧ ∀ rd, LowDef κ rd → MemL rd Lin →
    CclPreAtC Ha off cs rd [spT, cover, r.base * gen ^ r.nx, lxS, spS, gen ^ r.ns, gsq] [r.ds.1, r.ds.2]
  sig : S.check ![r.dx.1, r.dx.2, r.ds.1, r.ds.2] ivCells.1 ivCells.2
    (digestScalars r.sigD).1 (digestScalars r.sigD).2 (metadataCell 64 true)
  cov : ∃ sl : ℕ → ℕ, ∀ k (hk : k < r.da.length), ∀ rd, LowDef κ rd → MemL rd Lin →
    CoverPreAt (sl k) rd [daR, daC, daS, r.base * (gen ^ r.nx * gen ^ r.ns) * gen ^ k] (daCellsOf r.da[k])
  defer : ∀ rd, MemL rd Lin → CellsAt rd (carried * gen ^ (53 * c)) r.dcells
  dlen : r.dcells.length = 53
  seed : (seed0, seed1) = digestScalars seedD
  pd : ∃ dd, daListDigestWith Ha r.da = some dd ∧
    Digest.stmtDigestOfWith Ha seedD r.sigD dd r.dcells = some r.pd
  pi0 : CellL Lin (cpib + 2 * c) (digestScalars r.pd).1
  pi1 : CellL Lin (cpib + (2 * c + 1)) (digestScalars r.pd).2
  vs : ∃ (D : VerifySub.VsData) (lpA sqA outA : ℕ), VsGood D ∧ D.pi = r.pd ∧ D.seed = seedD ∧
    glp = ofK (gpow lpA) ∧ gsq = ofK (gpow sqA) ∧ cfresh * gen ^ (106 * c) = ofK (gpow outA) ∧
    SubL (VerifySub.vsExtL lpA sqA outA D) Lin

variable (S) in
/-- **A child's iteration's weight** at `ω`: its callees'. -/
def childWS (ω : String → ℕ) (Bd : CalleeBounds) (H : MainWeightHypsS S fs ω) (r : ChildWords) : ℕ :=
  H.αccl * Bd.ccl r.nx / 1000 + (H.αccl * Bd.ccl r.ns / 1000 + (r.da.length * H.Kl100 + (H.Bdl +
    (H.Bsd + Bd.vsW ω H.vsc))))

set_option maxHeartbeats 1000000 in
/-- **`__loop5`, placed**: its `m ≤ 16` children, child `c` computing `rs c` as `ChildWordsOkS`
says, each iteration's signer pair and DA roots in its own `HeapBuf`s, by a tree within
`childWS`'s weights at every `w θ`. -/
theorem loop5C_completeAtW {Ha : List UInt8 → Option Digest} {κ : ℕ} {VsGood : VerifySub.VsData → Prop} {Bd : CalleeBounds}
    (H : CalleesAtC Ha S fs cert κ VsGood Bd) {Θ : Type} {w : Θ → String → ℕ}
    (Wt : ∀ θ, MainWeightHypsS S fs (w θ))
    (hκ : 16 ≤ κ) {m wb cpib : ℕ} {lxT cover lxS gsq spT spS carried daR daC daS seed0 seed1 glp
      cfresh : E} {seedD : Digest} (hm : m ≤ 16) (hm0 : 0 < m) (Lin : Layout)
    (rs : ℕ → ChildWords)
    (hok : ∀ c < m, ChildWordsOkC S Ha κ VsGood Lin wb cpib lxT cover lxS gsq spT spS carried daR daC daS
      seed0 seed1 glp cfresh seedD c (rs c)) :
    CompleteAtWS S fs cert w κ "__loop5" Lin [1, gen ^ m, ofK (gpow wb), lxT, cover, lxS, gsq, spT, spS,
      carried, daR, daC, daS, seed0, seed1, ofK (gpow cpib), glp, cfresh] (Returns [])
      (loopSum (fs "__loop5") (fun c => childBd fs Bd (rs c)) 0 m)
      (fun θ => loopSum (w θ "__loop5") (fun c => childWS S (w θ) Bd (Wt θ) (rs c)) 0 m) := by
  have h := completeAtS_loopW (S := S) (fs := fs) (cert := cert) (w := w) (f := "__loop5") κ Lin
    (fun j => [gen ^ j, gen ^ m, ofK (gpow wb), lxT, cover, lxS, gsq, spT, spS, carried, daR, daC,
      daS, seed0, seed1, ofK (gpow cpib), glp, cfresh]) m (fun c => childBd fs Bd (rs c))
    (fun c θ => childWS S (w θ) Bd (Wt θ) (rs c)) (fun j hj fp mt => ?_) 0 hm0
  · simpa using h
  obtain ⟨p1, p2, p3, p4, p5⟩ := loop5_parts
  have o := hok j hj
  obtain ⟨D, lpA, sqA, outA, hgood, hpi, hseed, hglp, hgsq, hout, hvsub⟩ := o.vs
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
        cfresh * gen ^ (106 * j)], VerifySub.vsExtL lpA sqA outA D, Returns []⟩]
  have c1 : CompleteAtBS S fs cert κ "child_claim_list_digest" (Lb ++ Lin)
      [lxT, cover, r.base, 1, lxS, gen ^ r.nx, gsq] (Returns [r.dx.1, r.dx.2]) (Bd.ccl r.nx) := by
    have := H.child_claim_list_digest offx csx _ _ _ fun rd hl h => hccx rd hl (mLb rd h)
    rwa [hlx, Nat.mul_div_cancel_left _ (by norm_num : 0 < 4)] at this
  have c2 : CompleteAtBS S fs cert κ "child_claim_list_digest" (Lb ++ Lin)
      [spT, cover, r.base * gen ^ r.nx, lxS, spS, gen ^ r.ns, gsq] (Returns [r.ds.1, r.ds.2])
      (Bd.ccl r.ns) := by
    have := H.child_claim_list_digest offs css _ _ _ fun rd hl h => hccs rd hl (mLb rd h)
    rwa [hls, Nat.mul_div_cancel_left _ (by norm_num : 0 < 4)] at this
  have c3 : nda ≠ 0 → CompleteAtBS S fs cert κ "__loop100" (Lb ++ Lin) [1, gen ^ nda, ofK (gpow (b + 2)),
      daR, daC, daS, r.base, gen ^ r.nx * gen ^ r.ns] (Returns [])
      (nda * (fs "__loop100" + Bd.cover) + fs "__loop100") := by
    intro ht
    · refine loop100S_completeAt H.cover_da_root (by have := o.nda; omega) (by omega) (Lb ++ Lin)
        (fun k => (r.da.map daCellsOf).getD k []) (fun c hc => ?_) dsl (fun c hc rd hl h => ?_)
        (fun c hc k hk => ?_)
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
  have c5 : CompleteAtBS S fs cert κ "statement_digest" (Lb ++ Lin) [seed0, seed1, ofK (gpow b),
      (digestScalars (dd)).1, (digestScalars (dd)).2,
      carried * gen ^ (53 * j)] (Returns [(digestScalars r.pd).1, (digestScalars r.pd).2]) Bd.sd :=
    H.statement_digest r.sigD r.dcells _ _ _ fun rd hl h => ⟨seedD, dd, o.dlen,
      o.seed, hsigp rd h 0 (by simp), hsigp rd h 1 (by simp), rfl, o.defer rd (mLb rd h), r.pd, hpd,
      rfl⟩
  have c6 : CompleteAtWS S fs cert w κ "verify_sub" (VerifySub.vsExtL lpA sqA outA D)
      [(digestScalars r.pd).1, (digestScalars r.pd).2, seed0, seed1, glp, gsq,
        cfresh * gen ^ (106 * j)] (Returns []) Bd.vs fun θ => Bd.vsW (w θ) (Wt θ).vsc := by
    have := H.verify_sub D hgood lpA sqA outA w (fun θ => (Wt θ).vsc) fun θ => (Wt θ).vsOk
    obtain ⟨hs0, hs1⟩ := Prod.ext_iff.mp o.seed
    simp only at hs0 hs1
    rw [hpi, hseed] at this
    rw [hs0, hs1, hglp, hgsq, hout]
    exact this
  have hkw : KidsWS S fs cert w κ ks [Bd.ccl r.nx, Bd.ccl r.ns,
      nda * (fs "__loop100" + Bd.cover) + fs "__loop100", Bd.daList nda, Bd.sd, Bd.vs]
      [fun θ => (Wt θ).αccl * Bd.ccl r.nx / 1000, fun θ => (Wt θ).αccl * Bd.ccl r.ns / 1000,
        fun θ => nda * (Wt θ).Kl100, fun θ => (Wt θ).Bdl, fun θ => (Wt θ).Bsd,
        fun θ => Bd.vsW (w θ) (Wt θ).vsc] := by
    refine ⟨fun _ => CompleteAtB.toWS_tot c1 fun θ => (Wt θ).ccl, fun h => by simp at h,
      fun _ => CompleteAtB.toWS_tot c2 fun θ => (Wt θ).ccl, fun h => by simp at h,
      fun ht => CompleteAtB.toWS (c3 (by simpa using ht)) fun θ rd t rets hn hv hb =>
        (Wt θ).l100.from_one (e := nda) (Nat.pos_of_ne_zero (by simpa using ht))
          (by have := o.nda; omega) (by simp) (by simp) rd t rets hn hv hb,
      fun _ => show fs "__loop100" ≤ _ by omega,
      fun _ => CompleteAtB.toWS_weightLe (Bf := fun θ _ => (Wt θ).Bdl) c4 fun θ => (Wt θ).dl,
      fun h => by simp at h,
      fun _ => CompleteAtB.toWS_weightLe (Bf := fun θ _ => (Wt θ).Bsd) c5 fun θ => (Wt θ).sd,
      fun h => by simp at h,
      fun _ => c6, fun h => by simp at h, trivial⟩
  refine Exists.elim (loopStepS_bufsW (fs := fs) (cert := cert) (w := w) find_loop5 loop5_isLoop core35_split
    p1 _ p2 p3 κ Lin [gen ^ j, gen ^ m, ofK (gpow wb), lxT, cover, lxS, gsq, spT, spS, carried, daR,
      daC, daS, seed0, seed1, ofK (gpow cpib), glp, cfresh] loop5Fronts (.n 85) loop5Targs p4
    [2, 4 * nda] [[(digestScalars r.sigD).1, (digestScalars r.sigD).2], cells] hbl fp mt ks _ _ hkw
    (fun k hk => by simp only [ks, List.mem_cons, List.not_mem_nil, or_false] at hk
                    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
                    iterate 5 exact ⟨fun _ h => h, fun _ h => h⟩
                    exact hvsub.trans (SubL.of_mem fun q hq => List.mem_append_right _ hq))
    [gen ^ (j + 1), gen ^ m, ofK (gpow wb), lxT, cover, lxS, gsq, spT, spS, carried, daR, daC, daS,
      seed0, seed1, ofK (gpow cpib), glp, cfresh] (decide (j + 1 ≠ m))
    (fun rd hl hL outs ho => ?_)) fun n ⟨L, hW, hD, hNb, hS⟩ =>
      ⟨n, L, hW, hD, by
        simp only [List.sum_cons, List.sum_nil] at hNb
        simp only [childBd, ← hnda]
        omega, fun rd hl hL bt ht hn => (hS rd hl hL bt (fun h => ht (by simp at h; omega))
        fun h => hn (by simpa using h)).wmono fun θ => by
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
        trivial (o.next.load hLin) hx (fun _ => trivial), ?_, ?_, ?_, ?_, ?_, ?_⟩
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

end
end LeanVM.Guest.B1.Main
