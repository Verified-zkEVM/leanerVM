/-
  LeanVM.Guest.B1.Main.CalleesWM

  What `main` assumes of its callees over a hash model, for any call relation and with the hash
  witnesses given as functions of the call's words (`CalleesW` over a `HashModel`).
-/

module

public import LeanVM.Guest.B1.Main.CalleesW
public import LeanVM.Guest.B1.Digest.StatementM
public import LeanVM.Guest.B1.Da.NamedM
public import LeanVM.Guest.Value.NodeSome

/-!
# The callees of `main`, with their witnesses, over a hash model

`CalleesW.lean` over a hash model `M` (`Value.HashModel`): the calls are those of a call relation
`C` whose calls unfold under `M.sem` (`UnfoldsB`), and every hash a callee concludes is answered
by `M.H` (pattern E of `docs/roadmap/w2-guest-model.md`):

* the signatures verify with the model's hash (`XmssOutM`, `SphincsOutM`:
  `xmssVerifyWith M.H … = some true`);
* `statement_digest`, the claim lists and the DA list hash to answered digests
  (`Digest.stmtDigestOfWith M.H`, `M.H`, `daListDigestWith M.H`);
* the blob matrix opens over the model with the guest's padding digests (`Digest.DaOutM`);
* the child proof's deferring verifier accepts over the model (`verifyDeferredWith M.H`);
* the batching closes from the chain state `s0` over the model (`MeaningAggWM`,
  `batchWith M.H s0`).

The hash-free outcomes (`exponent_tables`, `cover_da_root`) are `CalleesW`'s.

The vocabulary for `main`'s body under `S` is here too: `holdsB_ite_noRet`,
`holdsListB_range_flatten` (the `B` forms of `holds_ite_noRet`, `holdsList_range_flatten`), and the
signer set's one block over the model (`signers_compress_model`).
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Verifier LeanVM.Node

@[expose] public section

/-! ## Blocks under any semantics -/

section Blocks

variable {S : BlakeSem} {C : CallRel} {rd : Reader} {σ : Val}

/-- A forward branch whose blocks have no `ret` holds under `S`, then its continuation
(`holds_ite_noRet`). -/
theorem holdsB_ite_noRet (c : V) (z n : List Stmt) (hz : Stmt.noRetList z = true)
    (hn : Stmt.noRetList n = true) (next : Prop) (kret : List E → Prop) :
    Stmt.HoldsB S C rd σ (.ite c z n) next kret ↔
      (IsInK (σ c) ∧ (σ c = 0 → Stmt.HoldsListB S C rd σ z True kret) ∧
        (σ c ≠ 0 → Stmt.HoldsListB S C rd σ n True kret)) ∧ next := by
  rw [holdsB_noRet (.ite c z n) (by simp [Stmt.noRet, hz, hn]) next kret]
  rfl

/-- Blocks without a return, one per index below `n`, hold under `S` exactly when each does
(`holdsList_range_flatten`). -/
theorem holdsListB_range_flatten (n : ℕ) (blk : ℕ → List Stmt)
    (h : ∀ i, Stmt.noRetList (blk i) = true) (next : Prop) (kret : List E → Prop) :
    Stmt.HoldsListB S C rd σ ((List.range n).map blk).flatten next kret ↔
      (∀ i < n, Stmt.HoldsListB S C rd σ (blk i) True kret) ∧ next := by
  rw [holdsListB_flatten _ (fun b hb => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hb
    exact h i)]
  simp only [List.mem_map, List.mem_range, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]

end Blocks

/-- **A call is its callee's body under `S`** (`Unfolds` under `S`): a call of `C` holds at a
valuation of the callee's body under `S` and `C`. -/
abbrev UnfoldsB (S : BlakeSem) (rd : Reader) (C : CallRel) : Prop :=
  ∀ f args rets, C f args rets → ∃ (fn : Fn) (σ' : Val), coreProgram.find? f = some fn ∧
    fn.params.map σ' = args ∧ Stmt.HoldsListB S C rd σ' fn.body False (fun rs ↦ rs = rets)

/-- At the deployed semantics `UnfoldsB` is `Unfolds`. -/
theorem unfoldsB_deployed {rd : Reader} {C : CallRel} : UnfoldsB blakeDeployed rd C ↔ Unfolds rd C := by
  simp only [UnfoldsB, Unfolds, holdsListB_deployed]

/-! ## Hashes over a model -/

section Hashes

variable {M : HashModel}

/-- **The signer set's block over a model** (`signers_compress`): one checked row of two digests'
cells under the IV, the final 64-byte block, answers the hash of their bytes. -/
theorem signers_compress_model {a b : Digest} {o0 o1 : E}
    (hc : M.sem.check ![(digestScalars a).1, (digestScalars a).2, (digestScalars b).1,
      (digestScalars b).2] ivCells.1 ivCells.2 o0 o1 (metadataCell 64 true)) :
    ∃ d, M.H (digestBytes a ++ digestBytes b) = some d ∧ (o0, o1) = digestScalars d := by
  obtain ⟨d, hd, e⟩ := HashModel.one_block hc
  refine ⟨d, ?_, e⟩
  rw [← hd, digestBytes_eq, digestBytes_eq]
  simp [blockBytes, List.append_assoc]

/-- The leanXMSS list digest of decoded claims over a model is the hash of their cells
(`xmssListDigest_claims`). -/
theorem xmssListDigestWith_claims {cs : List E} {n : ℕ} (hlen : cs.length = 4 * n) :
    xmssListDigestWith M.H (xmssClaims cs) = M.H (cs.flatMap cellBytes) := by
  rw [xmssListDigestWith, (xmssClaims_spec n cs hlen).2.2]

/-- The leanSPHINCS list digest of decoded claims over a model is the hash of their cells. -/
theorem sphincsListDigestWith_claims {cs : List E} {n : ℕ} (hlen : cs.length = 4 * n) :
    sphincsListDigestWith M.H (sphincsClaims cs) = M.H (cs.flatMap cellBytes) := by
  rw [sphincsListDigestWith, (sphincsClaims_spec n cs hlen).2.2]

/-- The signer set's digest from its two answered list digests and its answered block. -/
theorem signersDigestWith_of {H : List UInt8 → Option Digest} {xs : List XmssClaim}
    {ss : List SphincsClaim} {dx ds d : Digest} (hx : xmssListDigestWith H xs = some dx)
    (hs : sphincsListDigestWith H ss = some ds) (h : H (digestBytes dx ++ digestBytes ds) = some d) :
    signersDigestWith H xs ss = some d := by
  simp only [signersDigestWith, hx, hs, Option.bind_eq_bind, Option.bind_some]
  exact h

end Hashes

/-! ## The outcomes over a model -/

/-- The DA padding cell's digest the guest bakes (`Digest.padCellD`, D5), as LeanDA's. -/
abbrev daPadCell : LeanDa.Digest := Da.toBytes Digest.padCellD

/-- The DA padding row's digest the guest bakes (`Digest.padRowD`, D5), as LeanDA's. -/
abbrev daPadRow : LeanDa.Digest := Da.toBytes Digest.padRowD

/-- **What `verify_lean_xmss(p)` establishes over a model for the signature `sig`**
(`Sig.XmssOut`): the four words at `p` are a leanXMSS claim that `sig` verifies with the model's
answered hash. -/
def XmssOutM (M : HashModel) (rd : Reader) (p : E) (sig : LeanXmss.Signature) : Prop :=
  ∃ a b c d, ReadsAt rd p [a, b, c, d] ∧
    xmssVerifyWith M.H (xmssOf a b c d).1 (xmssOf a b c d).2 sig = some true

/-- **What `verify_sig_lean_sphincs(p)` establishes over a model for the signature `sig`**
(`Sig.SphincsOut`). -/
def SphincsOutM (M : HashModel) (rd : Reader) (p : E) (sig : Sphincs.Signature) : Prop :=
  ∃ a b c d, ReadsAt rd p [a, b, c, d] ∧
    sphincsVerifyWith M.H (sphincsOf a b c d).1 (sphincsOf a b c d).2 sig = some true

/-- **`aggregate_claims` over a model, its hints named** (`MeaningAggW`): the batching from the
chain state `s0` closes over the model's hash. -/
def MeaningAggWM (M : HashModel) (s0 : Digest) (rd : Reader) (args rets : List E)
    (hints : BatchHints) : Prop :=
  ∃ n_g pis fresh carried dp, args = [n_g, pis, fresh, carried, dp] ∧ rets = [] ∧
    ∀ cs : List ChildClaims, cs ≠ [] → cs.length ≤ 16 → n_g = gen ^ cs.length →
      ChildClaimsAt rd pis fresh carried cs →
      ∃ d : DeferredClaim, batchWith M.H s0 cs hints = some (some d) ∧
        d.bytecodePoint.length = 22 ∧ d.matrixPoint.length = 28 ∧ ReadsAt rd dp d.cells

/-- **The callees of `main` over a hash model, with their witnesses named** (`CalleesW` over
`M`): for each function another group proves, a call of `C` implies its meaning over the model on
the memory `rd`, the hash witnesses the values of `wX`, `wS`, `wD`, `wV` and `wA` at the call's
words; `verify_sub` for the guest `bytecode`, the batching from `s0`. -/
structure CalleesWM (M : HashModel) (s0 : Digest) (bytecode : List K) (rd : Reader) (C : CallRel)
    (wX : E → LeanXmss.Signature) (wS : E → Sphincs.Signature)
    (wD : List E → List E → Da.Witness) (wV : List E → Proof)
    (wA : List E → List E → BatchHints) : Prop where
  exponent_tables : ∀ p q, C "exponent_tables" [] [p, q] → ExpTables rd p q
  verify_lean_xmss : ∀ p, C "verify_lean_xmss" [p] [] → XmssOutM M rd p (wX p)
  verify_sig_lean_sphincs : ∀ p, C "verify_sig_lean_sphincs" [p] [] → SphincsOutM M rd p (wS p)
  statement_digest : ∀ seed0 seed1 sigp da0 da1 dp d0 d1,
    C "statement_digest" [seed0, seed1, sigp, da0, da1, dp] [d0, d1] →
      ∃ (seed sig da : Digest) (cells : List E), cells.length = 53 ∧
        (seed0, seed1) = digestScalars seed ∧ LoadHolds rd sigp 0 (digestScalars sig).1 ∧
        LoadHolds rd sigp 1 (digestScalars sig).2 ∧ (da0, da1) = digestScalars da ∧
        ReadsAt rd dp cells ∧
        ∃ pi, Digest.stmtDigestOfWith M.H seed sig da cells = some pi ∧ (d0, d1) = digestScalars pi
  claim_list_digest : ∀ p n_g gsq d0 d1, SquaresTable rd gsq →
    C "claim_list_digest" [p, n_g, gsq] [d0, d1] →
      ∃ n < 2 ^ 16, n_g = gen ^ n ∧ ∃ cs : List E, cs.length = 4 * n ∧ ReadsAt rd p cs ∧
        ∃ d, M.H (cs.flatMap cellBytes) = some d ∧ (d0, d1) = digestScalars d
  child_claim_list_digest : ∀ entries cover base origin limit n_g gsq d0 d1, SquaresTable rd gsq →
    C "child_claim_list_digest" [entries, cover, base, origin, limit, n_g, gsq] [d0, d1] →
      ∃ n < 2 ^ 16, n_g = gen ^ n ∧ ∃ (off : ℕ → ℕ) (cs : List E), cs.length = 4 * n ∧
        ChildReads rd entries cover base origin limit off cs n ∧
        ∃ d, M.H (cs.flatMap cellBytes) = some d ∧ (d0, d1) = digestScalars d
  da_list_digest : ∀ roots n_g d0 d1, C "da_list_digest" [roots, n_g] [d0, d1] →
      ∃ claims : List DaClaim, claims.length ≤ 16 ∧ n_g = gen ^ claims.length ∧
        DaClaimsAt rd roots claims ∧
        ∃ d, daListDigestWith M.H claims = some d ∧ (d0, d1) = digestScalars d
  cover_da_root : ∀ roots cover nslots mark r0 r1 r2 r3,
    C "cover_da_root" [roots, cover, nslots, mark] [r0, r1, r2, r3] →
      ∃ i M, M < 2 ^ 33 ∧ i < M ∧ nslots = gen ^ M ∧ LoadHolds rd (cover * gen ^ i) 0 mark ∧
        ReadsAt rd (roots * gen ^ (4 * i)) [r0, r1, r2, r3]
  da_verify : ∀ gsq r0 r1 v0 v1, SquaresTable rd gsq → C "da_verify" [gsq] [r0, r1, v0, v1] →
      Digest.DaOutM M rd gsq r0 r1 v0 v1 (wD [gsq] [r0, r1, v0, v1])
  verify_sub : ∀ pi0 pi1 iv0 iv1 glp gsq out, ExpTables rd glp gsq →
    C "verify_sub" [pi0, pi1, iv0, iv1, glp, gsq, out] [] →
      ∃ (pi iv : Digest) (fresh : FixedClaims), (pi0, pi1) = digestScalars pi ∧
        (iv0, iv1) = digestScalars iv ∧ FreshShaped fresh ∧ ReadsAt rd out (fixedCells fresh) ∧
        verifyDeferredWith M.H bytecode iv pi fresh (wV [pi0, pi1, iv0, iv1, glp, gsq, out]) =
          some true
  aggregate_claims : ∀ args rets, C "aggregate_claims" args rets →
      MeaningAggWM M s0 rd args rets (wA args rets)

end
end LeanVM.Guest.B1.Main
