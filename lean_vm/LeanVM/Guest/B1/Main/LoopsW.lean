/-
  LeanVM.Guest.B1.Main.LoopsW

  `main`'s loops read forward for any call relation that unfolds (`Unfolds`), their callees'
  witnesses named: the raw signatures (`__loop3`, `__loop4`), a child's DA roots (`__loop100`)
  and the children (`__loop5`).
-/

module

public import LeanVM.Guest.B1.Main.CalleesW
public import LeanVM.Guest.B1.Main.Children

/-!
# The loops, for any call relation

These are `loop_sound`, `loop3_step`, `loop4_step`, `loop100_step` and `loop5_step` with the call
relation `C` in place of `coreProgram.Rel rd`: a helper's call is unfolded by `Unfolds rd C`, and
its callees' facts are `CalleesW`'s. The raw signatures' iterations give the signature `wX p`
(`wS p`) on the claim at `p`, and a child's iteration gives a child whose proof is `wV` at the
words of its `verify_sub` call: its public input's cells, the seed's, the exponent tables and its
fresh claims' pointer `child_fresh·g^(106c)`.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Verifier LeanVM.Node

@[expose] public section

variable {bytecode : List K} {rd : Reader} {C : CallRel}
  {wX : E → LeanXmss.Signature} {wS : E → Sphincs.Signature} {wD : List E → List E → Da.Witness}
  {wV : List E → Proof} {wA : List E → List E → BatchHints}

/-- **A guarded loop, forward**, for a call relation `C`: `loop_sound` with `C` for
`coreProgram.Rel rd`. -/
theorem loop_soundC {f : String} {ps : List E} {N : E} {m : ℕ} {B : E → Prop}
    (hm : m < ordG) (hN : N = gen ^ m)
    (hstep : ∀ x, C f (x :: ps) [] → B x ∧ (x * gen + N ≠ 0 → C f (x * gen :: ps) []))
    (h : 1 + N ≠ 0 → C f (1 :: ps) []) : ∀ j < m, B (gen ^ j) := by
  have key : ∀ t k, k + t = m → C f (gen ^ k :: ps) [] → ∀ j, k ≤ j → j < m → B (gen ^ j) := by
    intro t
    induction t with
    | zero => intro k hk _ j h1 h2; omega
    | succ t ih =>
      intro k hk hrun j h1 h2
      obtain ⟨hB, hnext⟩ := hstep _ hrun
      rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
      · exact hB
      · have hne : gen ^ k * gen + N ≠ 0 := by
          intro he
          rw [gen_pow_add_eq_zero_iff, hN] at he
          have := gen_pow_inj hm (by unfold ordG at hm; omega) he
          omega
        have := hnext hne
        rw [gen_pow_mul_gen] at this
        exact ih (k + 1) (by omega) this j hlt h2
  intro j hj
  have h1 := h (by rw [hN]; exact one_add_gen_pow_ne_zero (by omega) hm)
  rw [← pow_zero gen] at h1
  exact key m 0 (by omega) h1 j (Nat.zero_le j) hj

/-- **`__loop3` at `x`**, for a call relation that unfolds: `loop3_step` with the signature
`wX p` on the claim at `p = table·g^(4s)`. -/
theorem loop3_step_w (hm : MemOk rd) (hC : Unfolds rd C)
    (H : CalleesW bytecode rd C wX wS wD wV wA) {N lxS cover table : E} {M : ℕ}
    (hM : M < 2 ^ 33) (hL : lxS = gen ^ M) (x : E)
    (h : C "__loop3" [x, N, lxS, cover, table] []) :
    (∃ s < M, LoadHolds rd cover s x ∧
      Sig.XmssOut rd (table * gen ^ (4 * s)) (wX (table * gen ^ (4 * s)))) ∧
      (x * gen + N ≠ 0 → C "__loop3" [x * gen, N, lxS, cover, table] []) := by
  obtain ⟨fn, σ, hf, hp, h⟩ := hC _ _ _ h
  rw [find_loop3, Option.some.injEq] at hf
  subst hf
  simp only [show Fn.params Data.core33 = [.n 0, .n 1, .n 2, .n 3, .n 4] from rfl, List.map_cons,
    List.map_nil, List.cons.injEq, and_true] at hp
  obtain ⟨h0, h1, h2, h3, h4⟩ := hp
  simp only [show Fn.body Data.core33 = Data.core33.body from rfl, Data.core33.body,
    Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, word_gen] at h
  obtain ⟨-, h6, h7, hrc, h11, hl, h12, h13, h14, hv, h15, h16, h17, h18, h19, -, hcall, -⟩ := h
  obtain ⟨s, hs, hx⟩ := rc_bound hm hM hL (by rw [h7, h2, h6]) hrc
  refine ⟨⟨s, hs, ?_, ?_⟩, fun hne => ?_⟩
  · rw [h11, h3, hx, h0, loadHolds_mul_gen_pow] at hl
    exact hl
  · have := H.verify_lean_xmss _ hv
    rwa [h14, h13, h12, h4, hx, gen_pow_four] at this
  · have := hcall (by rw [h17, h16, h15, h0, h1]; exact hne)
    rwa [h19, h18, h0, h1, h2, h3, h4] at this

/-- **`__loop4` at `x`**, for a call relation that unfolds: `loop4_step` with the signature
`wS p` on the claim at `p = table·g^(4s)`. -/
theorem loop4_step_w (hm : MemOk rd) (hC : Unfolds rd C)
    (H : CalleesW bytecode rd C wX wS wD wV wA) {N spS cover lxS w table : E} {M Lx : ℕ}
    (hM : M < 2 ^ 33) (hL : spS = gen ^ M) (hLx : lxS = gen ^ Lx) (x : E)
    (h : C "__loop4" [x, N, spS, cover, lxS, w, table] []) :
    (∃ s < M, LoadHolds rd cover (Lx + s) (w * x) ∧
      Sig.SphincsOut rd (table * gen ^ (4 * s)) (wS (table * gen ^ (4 * s)))) ∧
      (x * gen + N ≠ 0 → C "__loop4" [x * gen, N, spS, cover, lxS, w, table] []) := by
  obtain ⟨fn, σ, hf, hp, h⟩ := hC _ _ _ h
  rw [find_loop4, Option.some.injEq] at hf
  subst hf
  simp only [show Fn.params Data.core34 = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6] from rfl,
    List.map_cons, List.map_nil, List.cons.injEq, and_true] at hp
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := hp
  simp only [show Fn.body Data.core34 = Data.core34.body from rfl, Data.core34.body,
    Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, word_gen] at h
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

/-- **`__loop100` at `x`**, for a call relation that unfolds: `loop100_step`. -/
theorem loop100_stepC (hC : Unfolds rd C) (H : CalleesW bytecode rd C wX wS wD wV wA)
    {N cda roots dcov dslots base nsub : E} {M : ℕ}
    (hM : M < 2 ^ 33) (hL : dslots = gen ^ M) (x : E)
    (h : C "__loop100" [x, N, cda, roots, dcov, dslots, base, nsub] []) :
    (∃ i < M, LoadHolds rd dcov i (base * nsub * x) ∧ ∃ r0 r1 r2 r3,
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
    Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, word_gen] at h
  obtain ⟨h8, h9, h10, h11, h12, hc, l0, l1, l2, l3, h17, h18, h19, h20, h21, -, hcall, -⟩ := h
  obtain ⟨i, M', hM', hi, hsl, hmk, hr⟩ := H.cover_da_root _ _ _ _ _ _ _ _ hc
  have hMM : M' = M := gen_pow_inj' (by omega) (by omega) (hsl.symm.trans (h5 ▸ hL))
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

/-- The words of child `c`'s `verify_sub` call: its public input's cells, the seed's, the exponent
tables and its fresh claims' pointer. -/
def subArgs (pi : Digest) (seed0 seed1 glp gsq cfresh : E) (c : ℕ) : List E :=
  [(digestScalars pi).1, (digestScalars pi).2, seed0, seed1, glp, gsq, cfresh * gen ^ (106 * c)]

/-- **Iteration `c` of `__loop5`**, for a call relation that unfolds: `loop5_step`, the child's
proof `wV` at its `verify_sub` call's words (`subArgs`). -/
theorem loop5_step_w (hC : Unfolds rd C) (H : CalleesW bytecode rd C wX wS wD wV wA) {F : Frame}
    {N gsq glp lxS spS daS seed0 seed1 : E} {seed : Digest} (hLx : lxS = gen ^ F.Lx)
    (hLs : spS = gen ^ F.Ls) (hMd : daS = gen ^ F.Md) (hLx' : F.Lx < 2 ^ 33)
    (hLs' : F.Ls < 2 ^ 33) (hMd' : F.Md < 2 ^ 33) (hseed : (seed0, seed1) = digestScalars seed)
    (ht : ExpTables rd glp gsq) (x : E)
    (h : C "__loop5" [x, N, F.written, F.lxT, F.cover, lxS, gsq, F.spT, spS,
      F.carried, F.daR, F.daC, daS, seed0, seed1, F.cpi, glp, F.cfresh] []) :
    (∀ c, x = gen ^ c → ∃ ch, ChildAt bytecode rd F seed c ch ∧
      ch.proof = wV (subArgs (statementDigest seed ch.statement) seed0 seed1 glp gsq F.cfresh c)) ∧
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
    Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, word_gen, word_one,
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
  obtain ⟨nx, hnx, hn20, offx, csx, hcsx, hRx, hdx⟩ :=
    H.child_claim_list_digest _ _ _ _ _ _ _ _ _ hsq hcx
  obtain ⟨ns, hns, hn21, offs, css, hcss, hRs, hds⟩ :=
    H.child_claim_list_digest _ _ _ _ _ _ _ _ _ hsq hcs
  obtain ⟨hlx, hgx, -⟩ := xmssClaims_spec nx csx hcsx
  obtain ⟨hls, hgs, -⟩ := sphincsClaims_spec ns css hcss
  rw [← xmssListDigest_claims hcsx] at hdx
  rw [← sphincsListDigest_claims hcss] at hds
  -- the signer set
  rw [h37, h38, h39, show σ (.n 32) = _ from congrArg Prod.fst hdx,
    show σ (.n 33) = _ from congrArg Prod.snd hdx, show σ (.n 35) = _ from congrArg Prod.fst hds,
    show σ (.n 36) = _ from congrArg Prod.snd hds] at hbl
  have hsig := signers_compress hbl
  -- the DA roots
  obtain ⟨dcl, hdlen, hn52, hDCA, hdd⟩ := H.da_list_digest _ _ _ _ hdl
  have h100 := loop_soundC (C := C) (f := "__loop100")
    (ps := [σ (.n 52), σ (.n 59), σ (.n 10), σ (.n 11), σ (.n 12), σ (.n 19), σ (.n 30)])
    (m := dcl.length) (by unfold ordG; omega) hn52
    (fun x h => loop100_stepC hC H hMd' (by rw [p12]; exact hMd) x h)
    (by rw [h61, h60, h62] at hl100; exact hl100)
  -- the statement and its digest
  obtain ⟨seed', sig, da, cells, hcl, hseed', hsig0, hsig1, hda, hcells, hpi⟩ :=
    H.statement_digest _ _ _ _ _ _ _ _ hsd
  rw [p13, p14, hseed] at hseed'
  have hss : seed' = seed := (digestScalars_injective hseed').symm
  subst hss
  have hsg : sig = signersDigest (xmssClaims csx) (sphincsClaims css) := by
    apply digestScalars_injective
    rw [signersDigest, ← hsig, ← loadHolds_unique hsig0 l40, ← loadHolds_unique hsig1 l41]
  have hdg : da = daListDigest dcl := digestScalars_injective (hda.symm.trans hdd)
  subst hsg hdg
  let st : NodeStatement := ⟨⟨xmssClaims csx, sphincsClaims css, dcl⟩, deferOfCells cells⟩
  have hst : (σ (.n 65), σ (.n 66)) = digestScalars (statementDigest seed' st) := by
    rw [statementDigest_eq, cells_deferOfCells hcl]
    exact hpi
  -- the child's proof
  obtain ⟨pi, iv, fresh, hpi', hiv, hfs, hfr, hver⟩ := H.verify_sub _ _ _ _ _ _ _
    (by rw [p16, p6]; exact ht) hvs
  rw [hst] at hpi'
  rw [p13, p14, hseed] at hiv
  have hpe : pi = statementDigest seed' st := (digestScalars_injective hpi').symm
  have hie : iv = seed' := (digestScalars_injective hiv).symm
  subst hpe hie
  have e79 : σ (.n 79) = F.cfresh * gen ^ (106 * c) := by
    have e78 : σ (.n 78) = σ (.n 0) ^ 106 := by
      rw [h78, h77, h76, h75, h74, h73, h72, h71, h70]; ring
    rw [h79, e78, p17, p0, hx, gen_pow_pow]
  refine ⟨⟨st, fresh, wV [σ (.n 65), σ (.n 66), σ (.n 13), σ (.n 14), σ (.n 16), σ (.n 6),
    σ (.n 79)]⟩, ⟨σ (.n 19), ?_, ?_, by simpa [st, hlx] using hnx,
    by simpa [st, hls] using hns, by simpa [st] using hdlen, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfs,
    ?_, hver⟩, ?_⟩
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
      show c + c = 2 * c by ring, show σ (.n 65) = _ from congrArg Prod.fst hst] at l65
    exact l65
  · rw [h69, h67, p15, p0, hx, ← pow_add, loadHolds_mul_gen_pow,
      show c + c = 2 * c by ring, show σ (.n 66) = _ from congrArg Prod.snd hst] at l66
    exact l66
  · rw [e79] at hfr
    exact hfr
  · exact congrArg wV (by
      rw [subArgs, show σ (.n 65) = _ from congrArg Prod.fst hst,
        show σ (.n 66) = _ from congrArg Prod.snd hst, p13, p14, p16, p6, e79])

end
end LeanVM.Guest.B1.Main
