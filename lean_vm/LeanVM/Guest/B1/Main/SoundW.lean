/-
  LeanVM.Guest.B1.Main.SoundW

  B1 for `main` (G:3119-3316) with its witness decoded: the seed, the statement and the witness of
  `NodeRel` as explicit functions of `main`'s valuation, the memory and the callees' witness
  functions.
-/

module

public import LeanVM.Guest.B1.Main.LoopsW
public import LeanVM.Guest.B1.Main.WritersW

/-!
# `main`, soundly, its witness decoded

`main_sound` concludes `∃ seed s w, statementDigest seed s = D ∧ NodeRel bytecode seed s w`.
`main_sound_w` names all three, for any valuation `σ` of `main`'s body and any call relation `C`
that unfolds, given the callees' contracts with their witness functions (`CalleesW`):

* `decSeed σ`: the seed's cells `fs_seed`;
* `decStmt σ rd`: the claim lists read at the tables `claim_list_digest` hashes (their lengths the
  logs of `n_x`, `n_s`), the DA claims at the roots `da_list_digest` hashes, the deferred claim at
  `defer_stmt`;
* `decWit σ rd wX wS wD wV wA`: the children `decKids` (child `c`'s statement read off the slots
  of its marks, `kidStmt`; its fresh claims at `child_fresh·g^(106c)`; its proof `wV` at its
  `verify_sub` call's words), a holder for every claim by the mark in its slot (`markOf`): a
  raw writer's (`e` below `n_raw_x`, `n_raw_x + n_raw_s`, `… + n_direct_da`) holds it by the
  signature `wX p` (`wS p`) at the table entry `p` or the matrix `wD`, a child's by the child whose
  segment of the running counts holds the mark (`kidOf`); and the batching's hints
  `wA` at `aggregate_claims`'s words.

The proof is `main_sound`'s, its existentials then shown equal to the decoders: the logs by
`gLog_gen_pow`, the cells by `readCells_of_readsAt`, the claims by `daOf_of_claimsAt`, the seed by
`digestAt_eq`, each child by `kidStmt_eq`, `decFresh_eq` and its proof's call, the slots by the
coverage table's bijection (`cover_all_w`, `cover_slot_unique`).
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Verifier LeanVM.Node

@[expose] public section

/-! ## The decoders -/

/-- The pointers and region sizes `main` hands its children's loop, the sizes the logs of
`g^Lx`, `g^Ls`, `g^Md`. -/
def frameOf (σ : Val) : Frame :=
  ⟨σ (.n 145), σ (.n 77), σ (.n 80), σ (.n 103), σ (.n 69), σ (.n 104), σ (.n 142), σ (.n 123),
    σ (.n 133), gLog (σ (.n 55)), gLog (σ (.n 56)), gLog (σ (.n 50))⟩

/-- The running count at `written[c]`, as a log. -/
def countOf (rd : Reader) (σ : Val) (c : ℕ) : ℕ := gLog (cellAt rd (σ (.n 145)) c)

/-- The child whose segment of the running counts holds the mark `g^e`. -/
def kidOf (rd : Reader) (σ : Val) (e : ℕ) : ℕ :=
  ((List.range (gLog (σ (.n 6)))).find? fun c => decide (e < countOf rd σ (c + 1))).getD 0

/-- The mark in coverage slot `s`, as a log. -/
def markOf (rd : Reader) (σ : Val) (s : ℕ) : ℕ := gLog (cellAt rd (σ (.n 103)) s)

/-- **Child `c`**: its statement read off the coverage table (`kidStmt`), its fresh claims at
`child_fresh·g^(106c)`, its proof `wV` at the words of its `verify_sub` call. -/
def decKid (rd : Reader) (σ : Val) (wV : List E → Proof) (c : ℕ) : Child :=
  ⟨kidStmt rd (frameOf σ) (gLog (σ (.n 58))) (countOf rd σ) c,
    decFresh rd (σ (.n 133) * gen ^ (106 * c)),
    wV [cellAt rd (σ (.n 123)) (2 * c), cellAt rd (σ (.n 123)) (2 * c + 1), σ (.n 63), σ (.n 64),
      σ (.n 65), σ (.n 66), σ (.n 133) * gen ^ (106 * c)]⟩

/-- The children, `n_children` of them. -/
def decKids (rd : Reader) (σ : Val) (wV : List E → Proof) : List Child :=
  (List.range (gLog (σ (.n 6)))).map (decKid rd σ wV)

/-- The holder of the leanXMSS table's claim `s`, its slot's mark `g^e`: a raw signature below
`n_raw_x`, else the child `kid e`. -/
def holdX (σ : Val) (wX : E → LeanXmss.Signature) (kid : ℕ → ℕ) (e s : ℕ) :
    Holder LeanXmss.Signature :=
  if e < gLog (σ (.n 2)) then .direct (wX (σ (.n 77) * gen ^ (4 * s))) else .child (kid e)

/-- The holder of the leanSPHINCS table's claim `s`, its slot's mark `g^e`. -/
def holdS (σ : Val) (wS : E → Sphincs.Signature) (kid : ℕ → ℕ) (e s : ℕ) :
    Holder Sphincs.Signature :=
  if e < gLog (σ (.n 2)) + gLog (σ (.n 5)) then .direct (wS (σ (.n 80) * gen ^ (4 * s)))
  else .child (kid e)

/-- The holder of DA claim `s`, its slot's mark `g^e`: the direct blob matrix, or a child. -/
def holdD (σ : Val) (wD : List E → List E → Da.Witness) (kid : ℕ → ℕ) (e _s : ℕ) :
    Holder Da.Witness :=
  if e < gLog (σ (.n 2)) + gLog (σ (.n 5)) + gLog (σ (.n 7)) then
    .direct (wD [σ (.n 66)] [σ (.n 113), σ (.n 114), σ (.n 115), σ (.n 116)])
  else .child (kid e)

/-- **The seed**: the cells `fs_seed`. -/
def decSeed (σ : Val) : Digest := digestAt (σ (.n 63)) (σ (.n 64))

/-- **The statement**: the claims at the leanXMSS and leanSPHINCS tables, `n_x` and `n_s` of
them, the `n_da` DA claims at the roots, the deferred claim at `defer_stmt`. -/
def decStmt (σ : Val) (rd : Reader) : NodeStatement :=
  ⟨⟨xmssClaims (readCells rd (σ (.n 77)) (4 * gLog (σ (.n 0)))),
    sphincsClaims (readCells rd (σ (.n 80)) (4 * gLog (σ (.n 3)))),
    (List.range (gLog (σ (.n 40)))).map (daOf rd (σ (.n 69)))⟩, decDefer rd (σ (.n 153))⟩

/-- **The witness**: the children, a holder for every claim by its slot's mark, and the
batching's hints. -/
def decWit (σ : Val) (rd : Reader) (wX : E → LeanXmss.Signature) (wS : E → Sphincs.Signature)
    (wD : List E → List E → Da.Witness) (wV : List E → Proof)
    (wA : List E → List E → BatchHints) : NodeWitness :=
  ⟨decKids rd σ wV,
    (List.range (gLog (σ (.n 0)))).map fun k => holdX σ wX (kidOf rd σ) (markOf rd σ k) k,
    (List.range (gLog (σ (.n 3)))).map fun k =>
      holdS σ wS (kidOf rd σ) (markOf rd σ (gLog (σ (.n 55)) + k)) k,
    (List.range (gLog (σ (.n 40)))).map fun k =>
      holdD σ wD (kidOf rd σ) (markOf rd σ (gLog (σ (.n 55)) + gLog (σ (.n 56)) + k)) k,
    wA [σ (.n 6), σ (.n 123), σ (.n 133), σ (.n 142), σ (.n 153)] []⟩

/-! ## `main` -/

variable {bytecode : List K} {rd : Reader}

/-- **`main`, soundly, its witness decoded** (G:3119-3316; TRIAGE #76): on a memory of a valid
execution whose public input is the digest `D`, `main`'s body under a valuation `σ` and a call
relation `C` that unfolds gives the seed `decSeed σ` and the statement `decStmt σ rd` of digest
`D`, which the witness `decWit σ rd wX wS wD wV wA` holds (`NodeRel`) for the guest `bytecode` of
`2^22` words, given the callees' contracts with the witness functions `wX`, `wS`, `wD`, `wV`,
`wA`. -/
theorem main_sound_w (hlen : bytecode.length = 2 ^ 22) (hm : MemOk rd) {C : CallRel}
    (hC : ∀ f args rets, C f args rets → ∃ (fn : Fn) (σ' : Val), coreProgram.find? f = some fn ∧
      fn.params.map σ' = args ∧ Stmt.HoldsList C rd σ' fn.body False (fun rs ↦ rs = rets))
    {wX : E → LeanXmss.Signature} {wS : E → Sphincs.Signature}
    {wD : List E → List E → Da.Witness} {wV : List E → Proof}
    {wA : List E → List E → BatchHints} (H : CalleesW bytecode rd C wX wS wD wV wA)
    {D : Digest} (hpub0 : rd 1 = some (digestScalars D).1) (hpub1 : rd g = some (digestScalars D).2)
    {σ : Val} (h : Stmt.HoldsList C rd σ Data.core0.body False (fun rs ↦ rs = [])) :
    statementDigest (decSeed σ) (decStmt σ rd) = D ∧
      NodeRel bytecode (decSeed σ) (decStmt σ rd) (decWit σ rd wX wS wD wV wA) := by
  rw [show Data.core0.body = mainBody from core0_body, mainBody, holdsList_append,
    holdsList_noRet mainPre rfl] at h
  obtain ⟨hpre, h⟩ := h
  rw [Stmt.HoldsList, holds_ite_noRet (.n 112) daBranch [] rfl rfl, holdsList_append,
    holdsList_noRet mainMid rfl] at h
  obtain ⟨hite1, hmid, h⟩ := h
  rw [Stmt.HoldsList, holds_ite_noRet (.n 155) leafT aggT rfl rfl] at h
  obtain ⟨hite2, hpost⟩ := h
  simp only [mainPre, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil,
    word_gmax, word_g16, word_g257, word_gen, word_one, word_iv0, word_iv1, word_md64] at hpre
  obtain ⟨-, c8, rc0, c12, rc1, c16, rc2, c20, rc3, c24, rc4, c28, rc5, c32, rc6, c36, rc7, -,
    c42, rc40, c46, rc41, h50, -, -, h55, h56, h57, h58, c59, rc58, -, het, -, -, -, -, -, -, -, -,
    hdl, -, -, -, -, -, -, hcx, hcs, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    c97, c98, c99, hbl, -, l100, l101, -, h104, h105, h106, h107, -, hl3, h108, h109, h110, -, hl4,
    h111, h112, -⟩ := hpre
  simp only [mainMid, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil,
    word_gen, word_one] at hmid
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h146, h147, l147,
    h148, h149, h150, -, hl5, h151, l152, he152, -, h154, h155, -⟩ := hmid
  simp only [mainPost, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil,
    word_gen, word_one] at hpost
  obtain ⟨hsd, h211, l212, he212, h213, h214, h215, l216, he216, -⟩ := hpost
  -- the counts
  obtain ⟨a0, ha0, e0⟩ := rc_const hm (by norm_num) c8 rc0
  obtain ⟨a1, ha1, e1⟩ := rc_const hm (by norm_num) c12 rc1
  obtain ⟨a2, ha2, e2⟩ := rc_const hm (by norm_num) c16 rc2
  obtain ⟨a3, ha3, e3⟩ := rc_const hm (by norm_num) c20 rc3
  obtain ⟨a4, ha4, e4⟩ := rc_const hm (by norm_num) c24 rc4
  obtain ⟨a5, ha5, e5⟩ := rc_const hm (by norm_num) c28 rc5
  obtain ⟨a6, ha6, e6⟩ := rc_const hm (by norm_num) c32 rc6
  obtain ⟨a7, ha7, e7⟩ := rc_const hm (c := 1) (by norm_num) (by rw [c36, pow_one]) rc7
  obtain ⟨a40, ha40, e40⟩ := rc_const hm (by norm_num) c42 rc40
  obtain ⟨a41, ha41, e41⟩ := rc_const hm (by norm_num) c46 rc41
  obtain ⟨t, ht, et⟩ := rc_const hm (by norm_num) c59 rc58
  have e55 : σ (.n 55) = gen ^ (a0 + a1) := by rw [h55, e0, e1, ← pow_add]
  have e56 : σ (.n 56) = gen ^ (a3 + a4) := by rw [h56, e3, e4, ← pow_add]
  have e50 : σ (.n 50) = gen ^ (a40 + a41) := by rw [h50, e40, e41, ← pow_add]
  have e57 : σ (.n 57) = gen ^ (a0 + a1 + (a3 + a4)) := by rw [h57, e55, e56, ← pow_add]
  have hT : t = a0 + a1 + (a3 + a4) + (a40 + a41) :=
    gen_pow_inj' (by omega) (by omega) (et.symm.trans (by rw [h58, e57, e50, ← pow_add]))
  -- the counts, decoded
  have dA2 : gLog (σ (.n 2)) = a2 := by rw [e2, gLog_gen_pow (by omega)]
  have dA5 : gLog (σ (.n 5)) = a5 := by rw [e5, gLog_gen_pow (by omega)]
  have dA6 : gLog (σ (.n 6)) = a6 := by rw [e6, gLog_gen_pow (by omega)]
  have dA7 : gLog (σ (.n 7)) = a7 := by rw [e7, gLog_gen_pow (by omega)]
  have dA40 : gLog (σ (.n 40)) = a40 := by rw [e40, gLog_gen_pow (by omega)]
  have dLx : gLog (σ (.n 55)) = a0 + a1 := by rw [e55, gLog_gen_pow (by omega)]
  have dLs : gLog (σ (.n 56)) = a3 + a4 := by rw [e56, gLog_gen_pow (by omega)]
  have dMd : gLog (σ (.n 50)) = a40 + a41 := by rw [e50, gLog_gen_pow (by omega)]
  have dT : gLog (σ (.n 58)) = t := by rw [et, gLog_gen_pow (by omega)]
  -- the tables
  have htab : ExpTables rd (σ (.n 65)) (σ (.n 66)) := H.exponent_tables _ _ het
  have hsq := squaresTable_of_expTables htab
  -- the declared lists
  obtain ⟨dcl, hdl16, hn40, hDCA, hdd⟩ := H.da_list_digest _ _ _ _ hdl
  have hdlen : dcl.length = a40 := gen_pow_inj' (by omega) (by omega) (hn40.symm.trans e40)
  obtain ⟨nx, hnx, hn0, csX, hlX, hRX, hdX⟩ := H.claim_list_digest _ _ _ _ _ hsq hcx
  have hnx' : a0 = nx := gen_pow_inj' (by omega) (by omega) (e0.symm.trans hn0)
  obtain ⟨ns, hns, hn3, csS, hlS, hRS, hdS⟩ := H.claim_list_digest _ _ _ _ _ hsq hcs
  have hns' : a3 = ns := gen_pow_inj' (by omega) (by omega) (e3.symm.trans hn3)
  subst hnx' hns'
  have dA0 : gLog (σ (.n 0)) = a0 := by rw [e0, gLog_gen_pow (by omega)]
  have dA3 : gLog (σ (.n 3)) = a3 := by rw [e3, gLog_gen_pow (by omega)]
  rw [← xmssListDigest_claims hlX] at hdX
  rw [← sphincsListDigest_claims hlS] at hdS
  -- the signer set
  rw [c97, c98, c99, show σ (.n 81) = _ from congrArg Prod.fst hdX,
    show σ (.n 82) = _ from congrArg Prod.snd hdX, show σ (.n 83) = _ from congrArg Prod.fst hdS,
    show σ (.n 84) = _ from congrArg Prod.snd hdS] at hbl
  have hsig := signers_compress hbl
  -- the own statement's digest
  obtain ⟨seed, sig, da, cells, hcl, hseed, hs0, hs1, hda, hcells, hown⟩ :=
    H.statement_digest _ _ _ _ _ _ _ _ hsd
  have hsg : sig = signersDigest (xmssClaims csX) (sphincsClaims csS) := by
    apply digestScalars_injective
    rw [signersDigest, ← hsig, ← loadHolds_unique hs0 l100, ← loadHolds_unique hs1 l101]
  have hdg : da = daListDigest dcl := digestScalars_injective (hda.symm.trans hdd)
  subst hsg hdg
  have hD : stmtDigestOf seed (signersDigest (xmssClaims csX) (sphincsClaims csS))
      (daListDigest dcl) cells = D := by
    apply digestScalars_injective
    rw [← hown]
    rw [h211] at l212
    rw [h215, h213, h214, one_mul] at l216
    have q0 := Option.some.inj ((load_one l212).symm.trans hpub0)
    have q1 := Option.some.inj ((load_gen l216).symm.trans hpub1)
    rw [← e_add_eq_zero_iff.mp he212, ← e_add_eq_zero_iff.mp he216, q0, q1]
  -- the seed and the statement, decoded
  have hseedD : decSeed σ = seed := digestAt_eq hseed
  have hstD : decStmt σ rd = ⟨⟨xmssClaims csX, sphincsClaims csS, dcl⟩, deferOfCells cells⟩ := by
    rw [decStmt, dA0, dA3, dA40, ← hdlen, daOf_of_claimsAt hDCA, ← hlX, ← hlS,
      readCells_of_readsAt hRX, readCells_of_readsAt hRS, decDefer, ← hcl,
      readCells_of_readsAt hcells]
  -- the raw signatures
  have raw3 := loop_soundC (C := C) (f := "__loop3")
    (ps := [σ (.n 2), σ (.n 55), σ (.n 103), σ (.n 77)]) (m := a2) (N := σ (.n 2))
    (by unfold ordG; omega) e2 (fun x hx => loop3_step_w hm hC H (M := a0 + a1) (by omega) e55 x hx)
    (by rw [h106, h105, h107] at hl3; exact hl3)
  have raw4 := loop_soundC (C := C) (f := "__loop4")
    (ps := [σ (.n 5), σ (.n 56), σ (.n 103), σ (.n 55), σ (.n 2), σ (.n 80)]) (m := a5)
    (N := σ (.n 5)) (by unfold ordG; omega) e5
    (fun x hx => loop4_step_w hm hC H (M := a3 + a4) (Lx := a0 + a1) (by omega) e56 e55 x hx)
    (by rw [h109, h108, h110] at hl4; exact hl4)
  -- the direct DA
  have hdirect : a7 = 1 → ∃ i < a40 + a41, LoadHolds rd (σ (.n 104)) i (gen ^ (a2 + a5)) ∧
      ∀ cl, DaAt rd (σ (.n 69)) i cl →
        (wD [σ (.n 66)] [σ (.n 113), σ (.n 114), σ (.n 115), σ (.n 116)]).Opens cl.1 cl.2 := by
    intro h7
    have h0 : σ (.n 112) = 0 := by rw [h112, h111, e7, h7, pow_one]; exact e_add_self gen
    have hb := hite1.2.1 h0
    simp only [daBranch, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons,
      List.map_nil] at hb
    obtain ⟨hdv, h117, hcov, q0, q1, q2, q3, -⟩ := hb
    obtain ⟨root, vd, hr, hv, hw⟩ := daOut_iff.mp (H.da_verify _ _ _ _ _ hsq hdv)
    obtain ⟨i, M, hM, hi, hsl, hmk, hrd⟩ := H.cover_da_root _ _ _ _ _ _ _ _ hcov
    have hMM : M = a40 + a41 := gen_pow_inj' (by omega) (by omega) (hsl.symm.trans e50)
    subst hMM
    refine ⟨i, hi, ?_, fun cl hcl => ?_⟩
    · rw [h117, e2, e5, ← pow_add, loadHolds_mul_gen_pow, Nat.add_zero] at hmk
      exact hmk
    · have hroot : DaAt rd (σ (.n 69)) i (root, vd) := by
        unfold DaAt
        rw [← e_add_eq_zero_iff.mp q0, ← e_add_eq_zero_iff.mp q1, ← e_add_eq_zero_iff.mp q2,
          ← e_add_eq_zero_iff.mp q3, show σ (.n 113) = _ from congrArg Prod.fst hr,
          show σ (.n 114) = _ from congrArg Prod.snd hr, show σ (.n 115) = _ from congrArg Prod.fst hv,
          show σ (.n 116) = _ from congrArg Prod.snd hv] at hrd
        exact hrd
      rw [daAt_unique hcl hroot]
      exact hw
  -- the children
  let F : Frame := ⟨σ (.n 145), σ (.n 77), σ (.n 80), σ (.n 103), σ (.n 69), σ (.n 104),
    σ (.n 142), σ (.n 123), σ (.n 133), a0 + a1, a3 + a4, a40 + a41⟩
  have hFr : frameOf σ = F := by rw [frameOf, dLx, dLs, dMd]
  have hkids := loop_soundC (C := C) (f := "__loop5")
    (ps := [σ (.n 6), F.written, F.lxT, F.cover, σ (.n 55), σ (.n 66), F.spT, σ (.n 56), F.carried,
      F.daR, F.daC, σ (.n 50), σ (.n 63), σ (.n 64), F.cpi, σ (.n 65), F.cfresh]) (m := a6)
    (N := σ (.n 6)) (by unfold ordG; omega) e6
    (fun x hx => loop5_step_w (F := F) hC H e55 e56 e50 (by show a0 + a1 < 2 ^ 33; omega)
      (by show a3 + a4 < 2 ^ 33; omega) (by show a40 + a41 < 2 ^ 33; omega) hseed htab x hx)
    (by rw [h149, h148, h150] at hl5; exact hl5)
  obtain ⟨chs, hchl, hch⟩ := exists_list (P := fun c ch => ChildAt bytecode rd F seed c ch ∧
    ch.proof = wV (subArgs (statementDigest seed ch.statement) (σ (.n 63)) (σ (.n 64))
      (σ (.n 65)) (σ (.n 66)) F.cfresh c)) (m := a6) (fun j hj => hkids j hj j rfl)
  have hch' : ∀ c (hc : c < chs.length), ChildAt bytecode rd F seed c chs[c] :=
    fun c hc => (hch c hc).1
  have hb0 : LoadHolds rd F.written 0 (gen ^ (a2 + a5 + a7)) := by
    rw [h147, h146, e2, e5, e7, ← pow_add, ← pow_add] at l147
    exact l147
  have hbase : ∀ c ≤ chs.length, LoadHolds rd F.written c (gen ^ counts (a2 + a5 + a7) chs c) := by
    intro c hc
    induction c with
    | zero => simpa [counts] using hb0
    | succ c ih =>
      obtain ⟨base, hw0, hw1, -⟩ := hch' c (by omega)
      have := loadHolds_unique hw0 (ih (by omega))
      rw [this, ← pow_add] at hw1
      rw [counts_succ _ _ _ (by omega), nOf]
      exact hw1
  have hnOf : ∀ c (hc : c < chs.length), nOf chs[c] ≤ 2 ^ 18 := by
    intro c hc
    obtain ⟨-, -, -, h1, h2, h3, -⟩ := hch' c hc
    rw [nOf]; omega
  have hfin : counts (a2 + a5 + a7) chs chs.length = t := by
    rw [h151, e6, loadHolds_mul_gen_pow, Nat.add_zero, e_add_eq_zero_iff.mp he152, et,
      ← hchl] at l152
    have := counts_le (a2 + a5 + a7) chs hnOf chs.length le_rfl
    exact gen_pow_inj' (by omega) (by omega) (loadHolds_unique (hbase chs.length le_rfl) l152)
  have hmono : Monotone (counts (a2 + a5 + a7) chs) :=
    monotone_nat_of_le_succ (counts_mono (a2 + a5 + a7) chs)
  -- the running counts, decoded
  have hcnt : ∀ c ≤ chs.length, countOf rd σ c = counts (a2 + a5 + a7) chs c := by
    intro c hc
    have := hmono hc
    show gLog (cellAt rd F.written c) = _
    rw [cellAt_of_load (hbase c hc), gLog_gen_pow (by omega)]
  have hkidOf : ∀ e c, c < chs.length → counts (a2 + a5 + a7) chs c ≤ e →
      e < counts (a2 + a5 + a7) chs (c + 1) → kidOf rd σ e = c := by
    intro e c hc h1 h2
    have hf : (List.range chs.length).find? (fun c => decide (e < countOf rd σ (c + 1))) =
        some c := by
      rw [List.find?_range_eq_some]
      refine ⟨?_, List.mem_range.mpr hc, fun j hj => ?_⟩
      · rw [hcnt (c + 1) (by omega)]; exact decide_eq_true h2
      · rw [hcnt (j + 1) (by omega)]
        have := hmono (show j + 1 ≤ c by omega)
        simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, not_lt]
        omega
    rw [kidOf, dA6, ← hchl, hf, Option.getD_some]
  -- the coverage
  have hdaC : F.daC = F.cover * gen ^ (F.Lx + F.Ls) := by
    show σ (.n 104) = σ (.n 103) * gen ^ (a0 + a1 + (a3 + a4))
    rw [h104, e57]
  have hFt : F.Lx + F.Ls + F.Md = t := by
    show a0 + a1 + (a3 + a4) + (a40 + a41) = t; omega
  have hw := writers_good_w (F := F) (seed := seed) (chs := chs) (a2 := a2) (a5 := a5) (a7 := a7)
    (hX := holdX σ wX (kidOf rd σ)) (hS := holdS σ wS (kidOf rd σ))
    (hD := holdD σ wD (kidOf rd σ)) hdaC
    (fun i hi => by
      obtain ⟨s, hs, hl, a, b, c, d, hr, hv⟩ := raw3 i hi
      refine ⟨s, hs, hl, ?_⟩
      rw [holdX, dA2]
      simp only [hi, ↓reduceIte]
      show xmssVerify _ _ _ = true
      rwa [entryX_of_reads hr])
    (fun j hj => by
      obtain ⟨s, hs, hl, a, b, c, d, hr, hv⟩ := raw4 j hj
      rw [e2, ← pow_add] at hl
      refine ⟨s, hs, hl, ?_⟩
      rw [holdS, dA2, dA5]
      simp only [show a2 + j < a2 + a5 by omega, ↓reduceIte]
      show sphincsVerify _ _ _ = true
      rwa [entryS_of_reads hr])
    ha7
    (fun h7 => by
      obtain ⟨i, hi, hl, hw⟩ := hdirect h7
      refine ⟨i, hi, hl, fun cl hcl => ?_⟩
      rw [holdD, dA2, dA5, dA7]
      simp only [show a2 + a5 < a2 + a5 + a7 by omega, ↓reduceIte]
      exact hw cl hcl)
    hch' hbase
    (fun e c hc h1 h2 s => by
      have hb : a2 + a5 + a7 ≤ e := by
        have := hmono (Nat.zero_le c)
        rw [show counts (a2 + a5 + a7) chs 0 = a2 + a5 + a7 by simp [counts]] at this
        omega
      rw [holdX, holdS, holdD, dA2, dA5, dA7, hkidOf e c hc h1 h2]
      simp only [show ¬ e < a2 by omega, show ¬ e < a2 + a5 by omega,
        show ¬ e < a2 + a5 + a7 by omega, ↓reduceIte, and_self])
  have hw' : ∀ e < t, ∃ s < t, LoadHolds rd F.cover s (gen ^ e) ∧
      SlotGoodW rd F chs (holdX σ wX (kidOf rd σ)) (holdS σ wS (kidOf rd σ))
        (holdD σ wD (kidOf rd σ)) e s := fun e he => by
    obtain ⟨s, hs, hl, hg⟩ := hw e (by rw [hfin]; exact he)
    exact ⟨s, by omega, hl, hg⟩
  have hplace : ∀ e < t, ∃ s < t, LoadHolds rd F.cover s (gen ^ e) := fun e he => by
    obtain ⟨s, hs, hl, -⟩ := hw' e he
    exact ⟨s, hs, hl⟩
  have hgood := cover_all_w (T := t) (by omega) hw'
  have hslot : ∀ e < t, ∀ s < t, LoadHolds rd F.cover s (gen ^ e) → slotOf rd F.cover t e = s :=
    fun e he s hs hl => slotOf_eq hs (cellAt_of_load hl) fun s' hs' hl' =>
      cover_slot_unique (by omega) hplace he hs' hs hl' (cellAt_of_load hl)
  -- the children, decoded
  have hkidEq : ∀ c (hc : c < chs.length), decKid rd σ wV c = chs[c] := by
    intro c hc
    obtain ⟨⟨base, hw0, -, -, -, -, hXc, hSc, hDc, h22, h28, hcar, hp0, hp1, hfs, hfr, -⟩,
      hprf⟩ := hch c hc
    have hb := loadHolds_unique hw0 (hbase c (by omega))
    subst hb
    have hsucc := counts_succ (a2 + a5 + a7) chs c hc
    have hlast := hmono (show c + 1 ≤ chs.length by omega)
    rw [nOf] at hsucc
    have e1 : kidStmt rd (frameOf σ) (gLog (σ (.n 58))) (countOf rd σ) c = chs[c].statement := by
      rw [hFr, dT]
      refine kidStmt_eq hdaC (by omega) (hcnt c (by omega)) ?_ ?_ hXc hSc hDc h22 h28 hcar
      · rw [hcnt (c + 1) (by omega), hsucc]
      · intro j hj s hs hl
        exact hslot _ (by omega) s hs hl
    have e2 : decFresh rd (σ (.n 133) * gen ^ (106 * c)) = chs[c].fresh := decFresh_eq hfs hfr
    have q0 : cellAt rd (σ (.n 123)) (2 * c) = _ := cellAt_of_load hp0
    have q1 : cellAt rd (σ (.n 123)) (2 * c + 1) = _ := cellAt_of_load hp1
    have e3 : wV [cellAt rd (σ (.n 123)) (2 * c), cellAt rd (σ (.n 123)) (2 * c + 1), σ (.n 63),
        σ (.n 64), σ (.n 65), σ (.n 66), σ (.n 133) * gen ^ (106 * c)] = chs[c].proof := by
      rw [hprf, subArgs, q0, q1]
    rw [decKid, e1, e2, e3]
  have hkidsD : decKids rd σ wV = chs := by
    apply List.ext_getElem (by simp [decKids, dA6, hchl])
    intro c h1 h2
    simp only [decKids, List.getElem_map, List.getElem_range]
    exact hkidEq c h2
  -- the holders
  have hmark : ∀ s < t, ∃ e < t, markOf rd σ s = e ∧
      SlotGoodW rd F chs (holdX σ wX (kidOf rd σ)) (holdS σ wS (kidOf rd σ))
        (holdD σ wD (kidOf rd σ)) e s := by
    intro s hs
    obtain ⟨e, he, hl, hg⟩ := hgood s hs
    refine ⟨e, he, ?_, hg⟩
    show gLog (cellAt rd F.cover s) = e
    rw [cellAt_of_load hl, gLog_gen_pow (by omega)]
  have hhX : List.Forall₂ (XmssHeld chs) (xmssClaims csX)
      ((List.range a0).map fun k => holdX σ wX (kidOf rd σ) (markOf rd σ k) k) := by
    apply forall₂_of_getElem (by simp [(xmssClaims_spec a0 csX hlX).1])
    intro k h1 h2
    have hk' : k < a0 := by rwa [(xmssClaims_spec a0 csX hlX).1] at h1
    have hent : (xmssClaims csX)[k] = entryX rd F.lxT k := by
      rw [(xmssClaims_spec a0 csX hlX).2.1 k h1, entryX, cellAt_eq_getD hRX (by omega),
        cellAt_eq_getD hRX (by omega), cellAt_eq_getD hRX (by omega),
        cellAt_eq_getD hRX (by omega)]
    obtain ⟨e, he, hme, hg⟩ := hmark k (by omega)
    simp only [List.getElem_map, List.getElem_range]
    rw [hent, hme]
    obtain ⟨g1, -, -⟩ := hg
    exact g1 (by show k < a0 + a1; omega)
  have hhS : List.Forall₂ (SphincsHeld chs) (sphincsClaims csS)
      ((List.range a3).map fun k => holdS σ wS (kidOf rd σ) (markOf rd σ (F.Lx + k)) k) := by
    apply forall₂_of_getElem (by simp [(sphincsClaims_spec a3 csS hlS).1])
    intro k h1 h2
    have hk' : k < a3 := by rwa [(sphincsClaims_spec a3 csS hlS).1] at h1
    have hent : (sphincsClaims csS)[k] = entryS rd F.spT k := by
      rw [(sphincsClaims_spec a3 csS hlS).2.1 k h1, entryS, cellAt_eq_getD hRS (by omega),
        cellAt_eq_getD hRS (by omega), cellAt_eq_getD hRS (by omega),
        cellAt_eq_getD hRS (by omega)]
    obtain ⟨e, he, hme, hg⟩ := hmark (F.Lx + k) (by show a0 + a1 + k < t; omega)
    obtain ⟨-, g2, -⟩ := hg
    have := g2 (by omega) (by show a0 + a1 + k < a0 + a1 + (a3 + a4); omega)
    rw [Nat.add_sub_cancel_left] at this
    simp only [List.getElem_map, List.getElem_range]
    rw [hent, hme]
    exact this
  have hhD : List.Forall₂ (DaHeld chs) dcl
      ((List.range dcl.length).map fun k =>
        holdD σ wD (kidOf rd σ) (markOf rd σ (F.Lx + F.Ls + k)) k) := by
    apply forall₂_of_getElem (by simp)
    intro k h1 h2
    obtain ⟨e, he, hme, hg⟩ := hmark (F.Lx + F.Ls + k)
      (by show a0 + a1 + (a3 + a4) + k < t; omega)
    obtain ⟨-, -, g3⟩ := hg
    have := g3 (Nat.le_add_right _ _)
    rw [Nat.add_sub_cancel_left] at this
    simp only [List.getElem_map, List.getElem_range]
    rw [hme]
    exact this dcl[k] (daAt_of_claimsAt hDCA k h1)
  have hwD : decWit σ rd wX wS wD wV wA = ⟨chs,
      (List.range a0).map fun k => holdX σ wX (kidOf rd σ) (markOf rd σ k) k,
      (List.range a3).map fun k => holdS σ wS (kidOf rd σ) (markOf rd σ (F.Lx + k)) k,
      (List.range dcl.length).map fun k =>
        holdD σ wD (kidOf rd σ) (markOf rd σ (F.Lx + F.Ls + k)) k,
      wA [σ (.n 6), σ (.n 123), σ (.n 133), σ (.n 142), σ (.n 153)] []⟩ := by
    rw [decWit, hkidsD, dA0, dA3, dA40, ← hdlen, dLx, dLs]
  have hkidsOk : ∀ c ∈ chs, c.statement.defer.Shaped bytecode ∧
      verifyDeferred bytecode seed (statementDigest seed c.statement) c.fresh c.proof = true := by
    intro c hc
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hc
    obtain ⟨-, -, -, -, -, -, -, -, -, h22, h28, -, -, -, -, -, hv⟩ := hch' k hk
    exact ⟨(deferredShaped_iff hlen _).mpr ⟨h22, h28⟩, hv⟩
  have hdig : statementDigest seed ⟨⟨xmssClaims csX, sphincsClaims csS, dcl⟩, deferOfCells cells⟩ =
      D := by
    rw [statementDigest_eq, cells_deferOfCells hcl]; exact hD
  rw [hseedD, hstD, hwD]
  refine ⟨hdig, ?_⟩
  -- the deferred claim
  by_cases ha60 : a6 = 0
  · -- a leaf
    have hnil : chs = [] := List.eq_nil_of_length_eq_zero (by omega)
    have h0 : σ (.n 155) = 0 := by
      rw [h155, h154, e6, ha60, pow_zero]; exact e_add_self 1
    have hl := hite2.2.1 h0
    rw [leafT, Stmt.HoldsList, Stmt.Holds, holdsList_append, holdsList_append, holdsList_append,
      holdsList_range_flatten 22 (zeroStores 159 0) (fun _ => rfl),
      holdsList_range_flatten 28 (zeroStores 181 23) (fun _ => rfl)] at hl
    simp only [zeroStores, Stmt.HoldsList, Stmt.Holds, Atom.Holds, word_zero] at hl
    obtain ⟨-, hz1, -, hz2, -⟩ := hl
    have hz : ∀ k (h : k < cells.length), k < 22 → cells[k] = 0 := fun k h hk => by
      obtain ⟨hc, hl, -⟩ := hz1 k hk
      rw [hc, Nat.zero_add] at hl
      exact loadHolds_unique (hcells k h) hl
    have hz' : ∀ k (h : 23 + k < cells.length), k < 28 → cells[23 + k] = 0 := fun k h hk => by
      obtain ⟨hc, hl, -⟩ := hz2 k hk
      rw [hc] at hl
      exact loadHolds_unique (hcells (23 + k) h) hl
    refine ⟨(deferredShaped_iff hlen _).mpr (length_deferOfCells hcl), hkidsOk, hhX, hhS, hhD, ?_⟩
    simp only [hnil, ↓reduceIte]
    rw [DeferredClaim.AtZero, hlen, Nat.log2_two_pow, show 2 * blake2sR1csLogSize = 28 from rfl]
    refine ⟨List.ext_getElem (by simp [deferOfCells, hcl]) fun k h1 h2 => ?_,
      List.ext_getElem (by simp [deferOfCells, hcl]) fun k h1 h2 => ?_⟩
    · simp only [deferOfCells, List.getElem_take, List.getElem_replicate]
      exact hz k _ (by simpa [deferOfCells, hcl] using h1)
    · simp only [deferOfCells, List.getElem_take, List.getElem_drop, List.getElem_replicate]
      exact hz' k _ (by simpa [deferOfCells, hcl] using h1)
  · -- the batching
    have hne : σ (.n 155) ≠ 0 := by
      rw [h155, h154, e6]
      intro h0
      have := (gen_pow_eq_one_iff (by omega)).mp (e_add_eq_zero_iff.mp h0)
      omega
    have ha := hite2.2.2 hne
    simp only [aggT, Stmt.HoldsList, Stmt.Holds, List.map_cons, List.map_nil] at ha
    obtain ⟨n_g, pis, fresh, carried, dp, hargs, -, hbat⟩ := H.aggregate_claims _ _ ha.1
    simp only [List.cons.injEq, and_true] at hargs
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hargs
    let cs : List ChildClaims := chs.map fun c => ⟨statementDigest seed c.statement, c.fresh,
      c.statement.defer⟩
    have hchs : chs ≠ [] := fun hc => ha60 (by rw [← hchl, hc, List.length_nil])
    obtain ⟨d, hbd, hd22, hd28, hdc⟩ := hbat cs (by simpa [cs] using hchs)
      (by simp [cs, hchl]; omega) (by simp [cs, hchl, e6])
      (fun c hc => by
        simp only [cs, List.length_map] at hc
        obtain ⟨-, -, -, -, -, -, -, -, -, h22, h28, hcar, hp0, hp1, hfs, hfr, -⟩ := hch' c hc
        simp only [cs, List.getElem_map]
        exact ⟨hp0, hp1, hfs, hfr, h22, h28, hcar⟩)
    have hcd : cells = d.cells := readsAt_unique hcells hdc (by
      simp [hcl, DeferredClaim.cells, hd22, hd28])
    refine ⟨(deferredShaped_iff hlen _).mpr (length_deferOfCells hcl), hkidsOk, hhX, hhS, hhD, ?_⟩
    simp only [hchs, ↓reduceIte]
    rw [hcd, deferOfCells_cells hd22 hd28]
    exact hbd

end
end LeanVM.Guest.B1.Main
