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
public import LeanVM.Guest.B1.Comp.Digest.SmallAtC
public import LeanVM.Guest.B1.Comp.Digest.ChildListAtC
public import LeanVM.Guest.B1.Comp.VerifySub.Data

/-!
# The callees of `main` over an answered hash

`CalleesAt.lean`'s preconditions with each digest the callee returns answered by `H`
(B1's `Digest.ClPreAtC`, `Digest.CclPreAtC`, `Digest.SdPreAtC`, `Digest.DaListPreAtC`; `CoverPreAt` and `DaVerifyPreAt` hash
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
open LeanVM.Guest.B1.Digest (SquaresAt CellsAt SdPreAtC DaListPreAtC ClPreAtC CclPreAtC)

@[expose] public section

variable (H : List UInt8 → Option Digest)

/-- The caller's words `verify_sub` reads at a run record `R` of the run `D` (`vsExtL`; B1's
`vsExtLC`): the exponent tables and `defer_out`'s cells at the run record's fixed claims. -/
def vsExtLR (lpA sqA outA : ℕ) (D : VerifySub.VsData) (R : VerifySub.VsRunC) : Layout :=
  VerifySub.expL lpA sqA ++ [(outA, Node.fixedCells (R.fresh D))]

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
    (VsGood : VerifySub.VsData → VerifySub.VsRunC → Prop) (Bd : CalleeBounds) : Prop where
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
  verify_sub : ∀ D R, VsGood D R → ∀ lpA sqA outA : ℕ, ∀ {Θ : Type} (w : Θ → String → ℕ)
    (c : Θ → VerifySub.VsStat), (∀ θ, VerifySub.VsStatOkS S (w θ) (c θ)) →
    CompleteAtWS S fs cert w κ "verify_sub"
    (vsExtLR lpA sqA outA D R) [(digestScalars D.pi).1, (digestScalars D.pi).2,
      (digestScalars D.seed).1, (digestScalars D.seed).2, ofK (gpow lpA), ofK (gpow sqA),
      ofK (gpow outA)] (Returns []) Bd.vs fun θ => Bd.vsW (w θ) (c θ)

end
end LeanVM.Guest.B1.Main
