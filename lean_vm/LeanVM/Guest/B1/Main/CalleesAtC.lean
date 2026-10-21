/-
  LeanVM.Guest.B1.Main.CalleesAtC

  What `main`'s placed completeness over an answered hash assumes of the functions it calls:
  `CalleesAt` under a semantics `S`, each digest a callee returns answered by `H`.
-/

module

public import LeanVM.Guest.B1.Main.CalleesAt
public import LeanVM.Guest.B1.Main.WeightLoopS
public import LeanVM.Guest.B1.Main.CalleesWM
public import LeanVM.Guest.B1.Sig.Model.Sphincs
public import LeanVM.Guest.B1.Sig.Model.Xmss

/-!
# The callees of `main` over an answered hash

`CalleesAt.lean`'s preconditions with each digest the callee returns answered by `H`
(`ClPreAtC`, `CclPreAtC`, `SdPreAtC`, `DaListPreAtC`; `CoverPreAt` and `DaVerifyPreAt` hash
nothing), the signatures verifying with `H`'s answers (`Meaning_verify_lean_xmssWith`,
`Meaning_verify_sig_lean_sphincsWith`), the blob matrix opening with `H` and the guest's padding
digests (`Da.Witness.OpensWith H daPadCell daPadRow`), and `CalleesAtC S H`: `CalleesAt` under
`S`, every tree valid under `S` (`CompleteRelBS S`, `CompleteAtWS S`) at these preconditions,
within the same bounds `Bd`; `verify_sub` for every run in `VsGood` at the weight hypotheses under
`S` (`VerifySub.VsStatOkS S`).
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest.B1 (CompleteRelBS CompleteAtBS Returns LowDef Meaning_verify_lean_xmssWith
  Meaning_verify_sig_lean_sphincsWith)
open LeanVM.Guest.B1.Digest (SquaresAt CellsAt)

@[expose] public section

variable (H : List UInt8 → Option Digest)

/-- `claim_list_digest`'s precondition over `H` (`ClPreAt`): the claims' digest answered. -/
def ClPreAtC (cs : List E) (rd : Reader) : List E → List E → Prop
  | [ptr, ng, gsq], [d0, d1] => SquaresAt rd gsq ∧ ∃ n < 2 ^ 16, ng = gen ^ n ∧
      cs.length = 4 * n ∧ CellsAt rd ptr cs ∧ (∀ c ∈ cs, IsCanonical128 c) ∧
        ∃ d, H (cs.flatMap cellBytes) = some d ∧ (d0, d1) = digestScalars d
  | _, _ => False

/-- `child_claim_list_digest`'s precondition over `H` (`CclPreAt`). -/
def CclPreAtC (off : ℕ → ℕ) (cs : List E) (rd : Reader) : List E → List E → Prop
  | [entries, cover, base, origin, limit, ng, gsq], [d0, d1] => SquaresAt rd gsq ∧
      (∃ L ≤ 2 ^ 16, limit = gen ^ L) ∧ ∃ n < 2 ^ 16, ng = gen ^ n ∧
        cs.length = 4 * n ∧ Digest.ChildReads rd entries cover base origin limit off cs n ∧
        (∀ c ∈ cs, IsCanonical128 c) ∧
          ∃ d, H (cs.flatMap cellBytes) = some d ∧ (d0, d1) = digestScalars d
  | _, _ => False

/-- `statement_digest`'s precondition over `H` (`SdPreAt`): the statement's digest answered. -/
def SdPreAtC (sig : Digest) (cells : List E) (rd : Reader) : List E → List E → Prop
  | [seed0, seed1, sigp, da0, da1, dp], [d0, d1] => ∃ (seed da : Digest),
      cells.length = Digest.deferStmtCells ∧ (seed0, seed1) = digestScalars seed ∧
      LoadHolds rd sigp 0 (digestScalars sig).1 ∧ LoadHolds rd sigp 1 (digestScalars sig).2 ∧
      (da0, da1) = digestScalars da ∧ CellsAt rd dp cells ∧
      ∃ pd, Digest.stmtDigestOfWith H seed sig da cells = some pd ∧ (d0, d1) = digestScalars pd
  | _, _ => False

/-- `da_list_digest`'s precondition over `H` (`DaListPreAt`): the list's digest answered. -/
def DaListPreAtC (claims : List DaClaim) (rd : Reader) : List E → List E → Prop
  | [roots, ng], [d0, d1] => claims.length ≤ 16 ∧ ng = gen ^ claims.length ∧
      LeanVM.Guest.B1.DaClaimsAt rd roots claims ∧
        ∃ d, daListDigestWith H claims = some d ∧ (d0, d1) = digestScalars d
  | _, _ => False

/-- A completeness under `S` within the weights at every frame weight, at the weights `w θ`
(`CompleteAtW.reindex`). -/
theorem CompleteAtWS.reindex {S : BlakeSem} {fs : String → ℕ} {cert : String → V → ℕ} {κ : ℕ}
    {f : String} {Lin : Layout} {args : List E} {Out : List E → Layout → Prop} {B : ℕ}
    {Bw : (String → ℕ) → ℕ}
    (h : CompleteAtWS S fs cert (fun θ : String → ℕ => θ) κ f Lin args Out B Bw) {Θ : Type}
    (w : Θ → String → ℕ) :
    CompleteAtWS S fs cert w κ f Lin args Out B fun θ => Bw (w θ) := fun fp =>
  let ⟨n, Lown, rets, Lout, ho, hW, hd, hn, hr⟩ := h fp
  ⟨n, Lown, rets, Lout, ho, hW, hd, hn, fun rd hl hm =>
    let ⟨t, a, b, c, d, e, f', g, hwt⟩ := hr rd hl hm
    ⟨t, a, b, c, d, e, f', g, fun θ => hwt (w θ)⟩⟩

/-- **The callees of `main` other groups prove, complete under `S` over the answered hash `H`**,
uniformly and placed at `κ`, by trees within `Bd` (`CalleesAt` over `S` and `H`). -/
structure CalleesAtC (S : BlakeSem) (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ)
    (VsGood : VerifySub.VsData → Prop) (Bd : CalleeBounds) : Prop where
  verify_lean_xmss :
    CompleteRelBS S fs cert κ "verify_lean_xmss" (Meaning_verify_lean_xmssWith H) Bd.xmss
  verify_sig_lean_sphincs : CompleteRelBS S fs cert κ "verify_sig_lean_sphincs"
    (Meaning_verify_sig_lean_sphincsWith H) Bd.sphincs
  statement_digest : ∀ sig cells,
    CompleteRelBS S fs cert κ "statement_digest" (SdPreAtC H sig cells) Bd.sd
  da_list_digest : ∀ claims,
    CompleteRelBS S fs cert κ "da_list_digest" (DaListPreAtC H claims) (Bd.daList claims.length)
  cover_da_root : ∀ i, CompleteRelBS S fs cert κ "cover_da_root" (CoverPreAt i) Bd.cover
  claim_list_digest : ∀ cs,
    CompleteRelBS S fs cert κ "claim_list_digest" (ClPreAtC H cs) (Bd.cl (cs.length / 4))
  child_claim_list_digest : ∀ off cs,
    CompleteRelBS S fs cert κ "child_claim_list_digest" (CclPreAtC H off cs) (Bd.ccl (cs.length / 4))
  da_verify : ∀ (wt : Da.Witness) (root vd : Digest), wt.OpensWith H daPadCell daPadRow root vd →
    ∀ (args rets : List E) (Lin : Layout),
    (∀ rd, LowDef κ rd → MemL rd Lin → DaVerifyPreAt root vd rd args rets) →
    CompleteAtWS S fs cert (fun θ : String → ℕ => θ) κ "da_verify" Lin args (Returns rets)
      (Bd.daVerify wt.rows.length) fun θ => Bd.daVerifyW θ wt.rows.length
  verify_sub : ∀ D, VsGood D → ∀ lpA sqA outA : ℕ, ∀ {Θ : Type} (w : Θ → String → ℕ)
    (c : Θ → VerifySub.VsStat), (∀ θ, VerifySub.VsStatOkS S (w θ) (c θ)) →
    CompleteAtWS S fs cert w κ "verify_sub"
    (VerifySub.vsExtL lpA sqA outA D) [(digestScalars D.pi).1, (digestScalars D.pi).2,
      (digestScalars D.seed).1, (digestScalars D.seed).2, ofK (gpow lpA), ofK (gpow sqA),
      ofK (gpow outA)] (Returns []) Bd.vs fun θ => Bd.vsW (w θ) (c θ)

end
end LeanVM.Guest.B1.Main
