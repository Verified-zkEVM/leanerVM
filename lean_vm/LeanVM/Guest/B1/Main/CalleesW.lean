/-
  LeanVM.Guest.B1.Main.CalleesW

  What `main` assumes of its callees, for any call relation and with the hash witnesses given as
  functions of the call's words: the signatures, the blob matrix, the child proofs and the
  batching's hints.
-/

module

public import LeanVM.Guest.B1.Main.AggregateSpec
public import LeanVM.Guest.B1.Sig.XmssOut
public import LeanVM.Guest.B1.Sig.SphincsOut
public import LeanVM.Guest.B1.Da.Verify

/-!
# The callees of `main`, with their witnesses

`Callees bytecode rd` states each callee's soundness on `coreProgram.Rel rd` with its witnesses
existential. `CalleesW bytecode rd C wX wS wD wV wA` states the same for a call relation `C`,
with each witness the value of a function of the call's words:

* `verify_lean_xmss(p)`: the signature `wX p` verifies the claim at `p` (`Sig.XmssOut`);
* `verify_sig_lean_sphincs(p)`: the same of `wS p` (`Sig.SphincsOut`);
* `da_verify(g_squares)`: the blob matrix `wD args rets` opens to the returned root and vector
  digest (`DaOut`);
* `verify_sub(pi, iv, tables, out)`: the deferring verifier accepts the proof `wV args`;
* `aggregate_claims`: the batching closes with the hints `wA args rets` (`MeaningAggW`);

and every other callee as in `Callees`, with `exponent_tables`, which `main_sound` reads off
`coreProgram.Rel` (`exponent_tables_iff`), among them. `Unfolds rd C` says a call of `C` is its
callee's body under `C` at some valuation, as `coreProgram.Rel rd` (`rel_iff`) and the located
relation (`Core.relL_iff`) are: it unfolds the loop helpers `main` proves itself.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Verifier LeanVM.Node

@[expose] public section

/-- **A call is its callee's body**: a call of `C` holds at a valuation of the callee's body
under `C`. -/
abbrev Unfolds (rd : Reader) (C : CallRel) : Prop :=
  ∀ f args rets, C f args rets → ∃ (fn : Fn) (σ' : Val), coreProgram.find? f = some fn ∧
    fn.params.map σ' = args ∧ Stmt.HoldsList C rd σ' fn.body False (fun rs ↦ rs = rets)

/-- **The callees of `main`, with their witnesses named**: for each function another group proves,
a call of `C` implies its meaning on the memory `rd`, the hash witnesses the values of `wX`,
`wS`, `wD`, `wV` and `wA` at the call's words; `verify_sub` for the guest `bytecode`. -/
structure CalleesW (bytecode : List K) (rd : Reader) (C : CallRel)
    (wX : E → LeanXmss.Signature) (wS : E → Sphincs.Signature)
    (wD : List E → List E → Da.Witness) (wV : List E → Proof)
    (wA : List E → List E → BatchHints) : Prop where
  exponent_tables : ∀ p q, C "exponent_tables" [] [p, q] → ExpTables rd p q
  verify_lean_xmss : ∀ p, C "verify_lean_xmss" [p] [] → Sig.XmssOut rd p (wX p)
  verify_sig_lean_sphincs : ∀ p, C "verify_sig_lean_sphincs" [p] [] → Sig.SphincsOut rd p (wS p)
  statement_digest : ∀ seed0 seed1 sigp da0 da1 dp d0 d1,
    C "statement_digest" [seed0, seed1, sigp, da0, da1, dp] [d0, d1] →
      ∃ (seed sig da : Digest) (cells : List E), cells.length = 53 ∧
        (seed0, seed1) = digestScalars seed ∧ LoadHolds rd sigp 0 (digestScalars sig).1 ∧
        LoadHolds rd sigp 1 (digestScalars sig).2 ∧ (da0, da1) = digestScalars da ∧
        ReadsAt rd dp cells ∧ (d0, d1) = digestScalars (stmtDigestOf seed sig da cells)
  claim_list_digest : ∀ p n_g gsq d0 d1, SquaresTable rd gsq →
    C "claim_list_digest" [p, n_g, gsq] [d0, d1] →
      ∃ n < 2 ^ 16, n_g = gen ^ n ∧ ∃ cs : List E, cs.length = 4 * n ∧ ReadsAt rd p cs ∧
        (d0, d1) = digestScalars (blake2sBytes (cs.flatMap cellBytes))
  child_claim_list_digest : ∀ entries cover base origin limit n_g gsq d0 d1, SquaresTable rd gsq →
    C "child_claim_list_digest" [entries, cover, base, origin, limit, n_g, gsq] [d0, d1] →
      ∃ n < 2 ^ 16, n_g = gen ^ n ∧ ∃ (off : ℕ → ℕ) (cs : List E), cs.length = 4 * n ∧
        ChildReads rd entries cover base origin limit off cs n ∧
        (d0, d1) = digestScalars (blake2sBytes (cs.flatMap cellBytes))
  da_list_digest : ∀ roots n_g d0 d1, C "da_list_digest" [roots, n_g] [d0, d1] →
      ∃ claims : List DaClaim, claims.length ≤ 16 ∧ n_g = gen ^ claims.length ∧
        DaClaimsAt rd roots claims ∧ (d0, d1) = digestScalars (daListDigest claims)
  cover_da_root : ∀ roots cover nslots mark r0 r1 r2 r3,
    C "cover_da_root" [roots, cover, nslots, mark] [r0, r1, r2, r3] →
      ∃ i M, M < 2 ^ 33 ∧ i < M ∧ nslots = gen ^ M ∧ LoadHolds rd (cover * gen ^ i) 0 mark ∧
        ReadsAt rd (roots * gen ^ (4 * i)) [r0, r1, r2, r3]
  da_verify : ∀ gsq r0 r1 v0 v1, SquaresTable rd gsq → C "da_verify" [gsq] [r0, r1, v0, v1] →
      DaOut rd gsq r0 r1 v0 v1 (wD [gsq] [r0, r1, v0, v1])
  verify_sub : ∀ pi0 pi1 s0 s1 glp gsq out, ExpTables rd glp gsq →
    C "verify_sub" [pi0, pi1, s0, s1, glp, gsq, out] [] →
      ∃ (pi iv : Digest) (fresh : FixedClaims), (pi0, pi1) = digestScalars pi ∧
        (s0, s1) = digestScalars iv ∧ FreshShaped fresh ∧ ReadsAt rd out (fixedCells fresh) ∧
        verifyDeferred bytecode iv pi fresh (wV [pi0, pi1, s0, s1, glp, gsq, out]) = true
  aggregate_claims : ∀ args rets, C "aggregate_claims" args rets →
      MeaningAggW rd args rets (wA args rets)

end
end LeanVM.Guest.B1.Main
