/-
  LeanVM.Guest.B1.Main.LoopsWM

  `main`'s loops read forward over a hash model, for any call relation that unfolds under the
  model's semantics, their callees' witnesses named (`LoopsW.lean` over a `HashModel`).
-/

module

public import LeanVM.Guest.B1.Main.CalleesWM
public import LeanVM.Guest.B1.Main.LoopsW

/-!
# The loops over a hash model

`loop3_step_w`, `loop4_step_w`, `loop100_stepC` and `loop5_step_w` over a hash model `M`: the
helper's call unfolds under `M.sem` (`UnfoldsB`), its callees' facts are `CalleesWM`'s. A child's
iteration gives `ChildAtM`: `ChildAt` with the child's statement digest the answered
`statementDigestWith M.H seed st = some pi` and its proof accepted by
`verifyDeferredWith M.H … = some true`. The guarded loop itself (`loop_soundC`) is
semantics-free and is used as it is.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Verifier LeanVM.Node

@[expose] public section

/-- **What iteration `c` of the children's loop establishes of the child `ch` over a model**
(`ChildAt`): its counts, its claims' slots and marks, its deferred cells, its statement's answered
digest `pi` under `seed` at `child_pi·g^(2c)`, its fresh claims at `child_fresh·g^(106c)`, and the
deferring verifier accepting its proof over the model. -/
def ChildAtM (M : HashModel) (bytecode : List K) (rd : Reader) (F : Frame) (seed : Digest) (c : ℕ)
    (ch : Child) : Prop :=
  ∃ base : E, LoadHolds rd F.written c base ∧
    LoadHolds rd F.written (c + 1) (base * gen ^ (ch.statement.claims.xmss.length +
      ch.statement.claims.sphincs.length + ch.statement.claims.da.length)) ∧
    ch.statement.claims.xmss.length < 2 ^ 16 ∧ ch.statement.claims.sphincs.length < 2 ^ 16 ∧
    ch.statement.claims.da.length ≤ 16 ∧
    (∀ j < ch.statement.claims.xmss.length, ∃ s < F.Lx, LoadHolds rd F.cover s (base * gen ^ j) ∧
      ch.statement.claims.xmss[j]? = some (entryX rd F.lxT s)) ∧
    (∀ j < ch.statement.claims.sphincs.length, ∃ s < F.Ls,
      LoadHolds rd F.cover (F.Lx + s) (base * gen ^ (ch.statement.claims.xmss.length + j)) ∧
      ch.statement.claims.sphincs[j]? = some (entryS rd F.spT s)) ∧
    (∀ j < ch.statement.claims.da.length, ∃ i < F.Md,
      LoadHolds rd F.daC i (base * gen ^ (ch.statement.claims.xmss.length +
        ch.statement.claims.sphincs.length + j)) ∧
      ∀ cl, ch.statement.claims.da[j]? = some cl → DaAt rd F.daR i cl) ∧
    ch.statement.defer.bytecodePoint.length = 22 ∧ ch.statement.defer.matrixPoint.length = 28 ∧
    ReadsAt rd (F.carried * gen ^ (53 * c)) ch.statement.defer.cells ∧
    ∃ pi, statementDigestWith M.H seed ch.statement = some pi ∧
      LoadHolds rd F.cpi (2 * c) (digestScalars pi).1 ∧
      LoadHolds rd F.cpi (2 * c + 1) (digestScalars pi).2 ∧
      FreshShaped ch.fresh ∧ ReadsAt rd (F.cfresh * gen ^ (106 * c)) (fixedCells ch.fresh) ∧
      verifyDeferredWith M.H bytecode seed pi ch.fresh ch.proof = some true

variable {M : HashModel} {s0 : Digest} {bytecode : List K} {rd : Reader} {C : CallRel}
  {wX : E → LeanXmss.Signature} {wS : E → Sphincs.Signature} {wD : List E → List E → Da.Witness}
  {wV : List E → Proof} {wA : List E → List E → BatchHints}

/-- **`__loop3` at `x` over a model** (`loop3_step_w`): the signature `wX p` on the claim at
`p = table·g^(4s)`, verifying with the model's hash. -/
theorem loop3_step_wM (hm : MemOk rd) (hC : UnfoldsB M.sem rd C)
    (H : CalleesWM M s0 bytecode rd C wX wS wD wV wA) {N lxS cover table : E} {Mx : ℕ}
    (hM : Mx < 2 ^ 33) (hL : lxS = gen ^ Mx) (x : E)
    (h : C "__loop3" [x, N, lxS, cover, table] []) :
    (∃ s < Mx, LoadHolds rd cover s x ∧
      XmssOutM M rd (table * gen ^ (4 * s)) (wX (table * gen ^ (4 * s)))) ∧
      (x * gen + N ≠ 0 → C "__loop3" [x * gen, N, lxS, cover, table] []) := by
  obtain ⟨fn, σ, hf, hp, h⟩ := hC _ _ _ h
  rw [find_loop3, Option.some.injEq] at hf
  subst hf
  simp only [show Fn.params Data.core33 = [.n 0, .n 1, .n 2, .n 3, .n 4] from rfl, List.map_cons,
    List.map_nil, List.cons.injEq, and_true] at hp
  obtain ⟨h0, h1, h2, h3, h4⟩ := hp
  simp only [show Fn.body Data.core33 = Data.core33.body from rfl, Data.core33.body,
    Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, List.map_cons, List.map_nil, word_gen] at h
  obtain ⟨-, h6, h7, hrc, h11, hl, h12, h13, h14, hv, h15, h16, h17, h18, h19, -, hcall, -⟩ := h
  obtain ⟨s, hs, hx⟩ := rc_bound hm hM hL (by rw [h7, h2, h6]) hrc
  refine ⟨⟨s, hs, ?_, ?_⟩, fun hne => ?_⟩
  · rw [h11, h3, hx, h0, loadHolds_mul_gen_pow] at hl
    exact hl
  · have := H.verify_lean_xmss _ hv
    rwa [h14, h13, h12, h4, hx, gen_pow_four] at this
  · have := hcall (by rw [h17, h16, h15, h0, h1]; exact hne)
    rwa [h19, h18, h0, h1, h2, h3, h4] at this

/-- **`__loop4` at `x` over a model** (`loop4_step_w`): the signature `wS p` on the claim at
`p = table·g^(4s)`, verifying with the model's hash. -/
theorem loop4_step_wM (hm : MemOk rd) (hC : UnfoldsB M.sem rd C)
    (H : CalleesWM M s0 bytecode rd C wX wS wD wV wA) {N spS cover lxS w table : E} {Mx Lx : ℕ}
    (hM : Mx < 2 ^ 33) (hL : spS = gen ^ Mx) (hLx : lxS = gen ^ Lx) (x : E)
    (h : C "__loop4" [x, N, spS, cover, lxS, w, table] []) :
    (∃ s < Mx, LoadHolds rd cover (Lx + s) (w * x) ∧
      SphincsOutM M rd (table * gen ^ (4 * s)) (wS (table * gen ^ (4 * s)))) ∧
      (x * gen + N ≠ 0 → C "__loop4" [x * gen, N, spS, cover, lxS, w, table] []) := by
  obtain ⟨fn, σ, hf, hp, h⟩ := hC _ _ _ h
  rw [find_loop4, Option.some.injEq] at hf
  subst hf
  simp only [show Fn.params Data.core34 = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6] from rfl,
    List.map_cons, List.map_nil, List.cons.injEq, and_true] at hp
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := hp
  simp only [show Fn.body Data.core34 = Data.core34.body from rfl, Data.core34.body,
    Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, List.map_cons, List.map_nil, word_gen] at h
  obtain ⟨-, h8, h9, hrc, h13, h14, h15, hl, h16, h17, h18, hv, h19, h20, h21, h22, h23,
    -, hcall, -⟩ := h
  obtain ⟨s, hs, hx⟩ := rc_bound hm hM hL (by rw [h9, h2, h8]) hrc
  refine ⟨⟨s, hs, ?_, ?_⟩, fun hne => ?_⟩
  · rw [h15, h14, h13, h3, h4, hx, h5, h0, hLx, ← pow_add, loadHolds_mul_gen_pow] at hl
    exact hl
  · have := H.verify_sig_lean_sphincs _ hv
    rwa [h18, h17, h16, h6, hx, gen_pow_four] at this
  · have := hcall (by rw [h21, h20, h19, h0, h1]; exact hne)
    rwa [h23, h22, h0, h1, h2, h3, h4, h5, h6] at this

/-- **`__loop100` at `x` over a model** (`loop100_stepC`). -/
theorem loop100_stepCM (hC : UnfoldsB M.sem rd C) (H : CalleesWM M s0 bytecode rd C wX wS wD wV wA)
    {N cda roots dcov dslots base nsub : E} {Mx : ℕ}
    (hM : Mx < 2 ^ 33) (hL : dslots = gen ^ Mx) (x : E)
    (h : C "__loop100" [x, N, cda, roots, dcov, dslots, base, nsub] []) :
    (∃ i < Mx, LoadHolds rd dcov i (base * nsub * x) ∧ ∃ r0 r1 r2 r3,
        ReadsAt rd (roots * gen ^ (4 * i)) [r0, r1, r2, r3] ∧
        ReadsAt rd (cda * (x * x * (x * x))) [r0, r1, r2, r3]) ∧
      (x * gen + N ≠ 0 → C "__loop100" [x * gen, N, cda, roots, dcov, dslots, base, nsub] []) := by
  obtain ⟨fn, σ, hf, hp, h⟩ := hC _ _ _ h
  rw [find_loop100, Option.some.injEq] at hf
  subst hf
  simp only [show Fn.params Data.core573 = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7] from rfl,
    List.map_cons, List.map_nil, List.cons.injEq, and_true] at hp
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := hp
  simp only [show Fn.body Data.core573 = Data.core573.body from rfl, Data.core573.body,
    Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, List.map_cons, List.map_nil, word_gen] at h
  obtain ⟨h8, h9, h10, h11, h12, hc, l0, l1, l2, l3, h17, h18, h19, h20, h21, -, hcall, -⟩ := h
  obtain ⟨i, M', hM', hi, hsl, hmk, hr⟩ := H.cover_da_root _ _ _ _ _ _ _ _ hc
  have hMM : M' = Mx := gen_pow_inj' (by omega) (by omega) (hsl.symm.trans (h5 ▸ hL))
  subst hMM
  refine ⟨⟨i, hi, ?_, σ (.n 13), σ (.n 14), σ (.n 15), σ (.n 16), ?_, ?_⟩, fun hne => ?_⟩
  · rw [h4, h12, h11, h6, h7, h0, loadHolds_mul_gen_pow, Nat.add_zero] at hmk
    exact hmk
  · rwa [h3] at hr
  · rw [← h0, ← h2, ← h8, ← h9, ← h10]
    intro k hk
    simp only [List.length_cons, List.length_nil] at hk
    interval_cases k
    · exact l0
    · exact l1
    · exact l2
    · exact l3
  · have := hcall (by rw [h19, h18, h17, h0, h1]; exact hne)
    rwa [h21, h20, h0, h1, h2, h3, h4, h5, h6, h7] at this

/-- **Iteration `c` of `__loop5` over a model** (`loop5_step_w`): the child it reads
(`ChildAtM`), its proof `wV` at its `verify_sub` call's words, the public input the child's
answered statement digest. -/
theorem loop5_step_wM (hC : UnfoldsB M.sem rd C) (H : CalleesWM M s0 bytecode rd C wX wS wD wV wA)
    {F : Frame} {N gsq glp lxS spS daS seed0 seed1 : E} {seed : Digest} (hLx : lxS = gen ^ F.Lx)
    (hLs : spS = gen ^ F.Ls) (hMd : daS = gen ^ F.Md) (hLx' : F.Lx < 2 ^ 33)
    (hLs' : F.Ls < 2 ^ 33) (hMd' : F.Md < 2 ^ 33) (hseed : (seed0, seed1) = digestScalars seed)
    (ht : ExpTables rd glp gsq) (x : E)
    (h : C "__loop5" [x, N, F.written, F.lxT, F.cover, lxS, gsq, F.spT, spS,
      F.carried, F.daR, F.daC, daS, seed0, seed1, F.cpi, glp, F.cfresh] []) :
    (∀ c, x = gen ^ c → ∃ ch, ChildAtM M bytecode rd F seed c ch ∧
      ∃ pi, statementDigestWith M.H seed ch.statement = some pi ∧
        ch.proof = wV (subArgs pi seed0 seed1 glp gsq F.cfresh c)) ∧
      (x * gen + N ≠ 0 → C "__loop5" [x * gen, N, F.written, F.lxT, F.cover,
        lxS, gsq, F.spT, spS, F.carried, F.daR, F.daC, daS, seed0, seed1, F.cpi, glp,
        F.cfresh] []) := by
  obtain ⟨fn, σ, hf, hp, h⟩ := hC _ _ _ h
  rw [find_loop5, Option.some.injEq] at hf
  subst hf
  simp only [show Fn.params Data.core35 = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8,
    .n 9, .n 10, .n 11, .n 12, .n 13, .n 14, .n 15, .n 16, .n 17] from rfl, List.map_cons,
    List.map_nil, List.cons.injEq, and_true] at hp
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17⟩ := hp
  simp only [show Fn.body Data.core35 = Data.core35.body from rfl, Data.core35.body,
    Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, List.map_cons, List.map_nil, word_gen, word_one,
    word_iv0, word_iv1, word_md64] at h
  obtain ⟨h18, l19, -, -, -, -, -, h30, h31, hcx, h34, hcs, h37, h38, h39, hbl, -, l40, l41,
    h43, h44, h45, h46, h47, h48, h49, h50, h51, -, -, -, -, h57, h58, -, h60, h61, h62, -, hl100,
    hdl, hsd, h67, h68, l65, h69, l66, h70, h71, h72, h73, h74, h75, h76, h77, h78, h79, hvs, h80,
    h81, h82, l81, h83, h84, h85, h86, h87, -, hcall, -⟩ := h
  refine ⟨fun c hx => ?_, fun hne => ?_⟩
  swap
  · have := hcall (by rw [h85, h84, h83, p0, p1]; exact hne)
    rwa [h87, h86, p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16,
      p17] at this
  have hsq : SquaresTable rd (σ (.n 6)) := by rw [p6]; exact squaresTable_of_expTables ht
  -- the two claim lists
  obtain ⟨nx, hnx, hn20, offx, csx, hcsx, hRx, dx, hHx, hdx⟩ :=
    H.child_claim_list_digest _ _ _ _ _ _ _ _ _ hsq hcx
  obtain ⟨ns, hns, hn21, offs, css, hcss, hRs, ds, hHs, hds⟩ :=
    H.child_claim_list_digest _ _ _ _ _ _ _ _ _ hsq hcs
  obtain ⟨hlx, hgx, -⟩ := xmssClaims_spec nx csx hcsx
  obtain ⟨hls, hgs, -⟩ := sphincsClaims_spec ns css hcss
  rw [← xmssListDigestWith_claims hcsx] at hHx
  rw [← sphincsListDigestWith_claims hcss] at hHs
  -- the signer set
  rw [h37, h38, h39, show σ (.n 32) = _ from congrArg Prod.fst hdx,
    show σ (.n 33) = _ from congrArg Prod.snd hdx, show σ (.n 35) = _ from congrArg Prod.fst hds,
    show σ (.n 36) = _ from congrArg Prod.snd hds] at hbl
  obtain ⟨dsig, hHsig, hsig⟩ := signers_compress_model hbl
  have hsigW := signersDigestWith_of hHx hHs hHsig
  -- the DA roots
  obtain ⟨dcl, hdlen, hn52, hDCA, dd, hHd, hdd⟩ := H.da_list_digest _ _ _ _ hdl
  have h100 := loop_soundC (C := C) (f := "__loop100")
    (ps := [σ (.n 52), σ (.n 59), σ (.n 10), σ (.n 11), σ (.n 12), σ (.n 19), σ (.n 30)])
    (m := dcl.length) (by unfold ordG; omega) hn52
    (fun x h => loop100_stepCM hC H hMd' (by rw [p12]; exact hMd) x h)
    (by rw [h61, h60, h62] at hl100; exact hl100)
  -- the statement and its digest
  obtain ⟨seed', sig, da, cells, hcl, hseed', hsig0, hsig1, hda, hcells, pi0, hHpi, hpi⟩ :=
    H.statement_digest _ _ _ _ _ _ _ _ hsd
  rw [p13, p14, hseed] at hseed'
  have hss : seed' = seed := (digestScalars_injective hseed').symm
  subst hss
  have hsg : sig = dsig := by
    apply digestScalars_injective
    rw [← hsig, ← loadHolds_unique hsig0 l40, ← loadHolds_unique hsig1 l41]
  have hdg : da = dd := digestScalars_injective (hda.symm.trans hdd)
  subst hsg hdg
  let st : NodeStatement := ⟨⟨xmssClaims csx, sphincsClaims css, dcl⟩, deferOfCells cells⟩
  have hstW : statementDigestWith M.H seed' st = some pi0 :=
    Digest.statementDigestWith_of (s := st) hsigW hHd (by
      show Digest.stmtDigestOfWith M.H seed' sig da (deferOfCells cells).cells = some pi0
      rw [cells_deferOfCells hcl]; exact hHpi)
  -- the child's proof
  obtain ⟨pi, iv, fresh, hpi', hiv, hfs, hfr, hver⟩ := H.verify_sub _ _ _ _ _ _ _
    (by rw [p16, p6]; exact ht) hvs
  rw [hpi] at hpi'
  rw [p13, p14, hseed] at hiv
  have hpe : pi = pi0 := (digestScalars_injective hpi').symm
  have hie : iv = seed' := (digestScalars_injective hiv).symm
  subst hpe hie
  have e79 : σ (.n 79) = F.cfresh * gen ^ (106 * c) := by
    have e78 : σ (.n 78) = σ (.n 0) ^ 106 := by
      rw [h78, h77, h76, h75, h74, h73, h72, h71, h70]; ring
    rw [h79, e78, p17, p0, hx, gen_pow_pow]
  refine ⟨⟨st, fresh, wV [σ (.n 65), σ (.n 66), σ (.n 13), σ (.n 14), σ (.n 16), σ (.n 6),
    σ (.n 79)]⟩, ⟨σ (.n 19), ?_, ?_, by simpa [st, hlx] using hnx,
    by simpa [st, hls] using hns, by simpa [st] using hdlen, ?_, ?_, ?_, ?_, ?_, ?_, pi, hstW, ?_,
    ?_, hfs, ?_, hver⟩, pi, hstW, ?_⟩
  · rw [h18, p2, p0, hx, loadHolds_mul_gen_pow, Nat.add_zero] at l19
    exact l19
  · rw [h82, p2, p0, hx, loadHolds_mul_gen_pow, h81, h80, h30, hn20, hn21, hn52] at l81
    simp only [st, hlx, hls]
    simp only [mul_assoc, ← pow_add] at l81
    exact l81
  · intro j hj
    simp only [st, hlx] at hj
    obtain ⟨⟨L, hL, hLe, hoff⟩, hmk, hrd⟩ := hRx j hj
    rw [p5, hLx] at hLe
    have := gen_pow_inj' (by omega) (by omega) hLe
    subst this
    refine ⟨offx j, hoff, ?_, ?_⟩
    · rw [h31, one_mul, p4, loadHolds_mul_gen_pow, Nat.add_zero] at hmk
      exact hmk
    · rw [p3] at hrd
      simp only [st]
      rw [List.getElem?_eq_getElem (by rw [hlx]; exact hj), hgx j (by rw [hlx]; exact hj),
        entryX_of_reads hrd]
  · intro j hj
    simp only [st, hls] at hj
    obtain ⟨⟨L, hL, hLe, hoff⟩, hmk, hrd⟩ := hRs j hj
    rw [p8, hLs] at hLe
    have := gen_pow_inj' (by omega) (by omega) hLe
    subst this
    refine ⟨offs j, hoff, ?_, ?_⟩
    · rw [h34, p4, p5, hLx, hn20, ← pow_add, loadHolds_mul_gen_pow, Nat.add_zero, mul_assoc,
        ← pow_add] at hmk
      simp only [st, hlx]
      exact hmk
    · rw [p7] at hrd
      simp only [st]
      rw [List.getElem?_eq_getElem (by rw [hls]; exact hj), hgs j (by rw [hls]; exact hj),
        entryS_of_reads hrd]
  · intro j hj
    simp only [st] at hj
    obtain ⟨i, hi, hmk, r0, r1, r2, r3, hroot, hcda⟩ := h100 j hj
    refine ⟨i, hi, ?_, fun cl hcl' => ?_⟩
    · rw [p11, h30, hn20, hn21] at hmk
      simp only [mul_assoc, ← pow_add] at hmk
      simp only [st, hlx, hls]
      exact hmk
    · simp only [st] at hcl'
      rw [List.getElem?_eq_getElem hj, Option.some.injEq] at hcl'
      subst hcl'
      have hD := daAt_of_claimsAt hDCA j hj
      rw [gen_pow_four] at hcda
      have := readsAt_unique hcda hD (by simp only [List.length_cons, List.length_nil])
      rw [p10, this] at hroot
      exact hroot
  · simp only [st]; exact (length_deferOfCells hcl).1
  · simp only [st]; exact (length_deferOfCells hcl).2
  · simp only [st]
    rw [cells_deferOfCells hcl]
    have e50 : σ (.n 50) = σ (.n 0) ^ 53 := by
      rw [h50, h49, h48, h47, h46, h45, h44, h43]; ring
    rw [h51, e50, p9, p0, hx, gen_pow_pow] at hcells
    exact hcells
  · rw [h68, h67, p15, p0, hx, ← pow_add, loadHolds_mul_gen_pow, Nat.add_zero,
      show c + c = 2 * c by ring, show σ (.n 65) = _ from congrArg Prod.fst hpi] at l65
    exact l65
  · rw [h69, h67, p15, p0, hx, ← pow_add, loadHolds_mul_gen_pow,
      show c + c = 2 * c by ring, show σ (.n 66) = _ from congrArg Prod.snd hpi] at l66
    exact l66
  · rw [e79] at hfr
    exact hfr
  · exact congrArg wV (by
      rw [subArgs, show σ (.n 65) = _ from congrArg Prod.fst hpi,
        show σ (.n 66) = _ from congrArg Prod.snd hpi, p13, p14, p16, p6, e79])

end
end LeanVM.Guest.B1.Main
