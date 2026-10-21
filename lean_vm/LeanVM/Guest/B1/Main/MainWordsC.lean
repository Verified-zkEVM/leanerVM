/-
  LeanVM.Guest.B1.Main.MainWordsC

  What `main`'s callees need of its words at `fp` under a semantics `S`, over an answered hash
  `Ha` (`MainWordsOk` over `S` and `Ha`).
-/

module

public import LeanVM.Guest.B1.Main.MainWords
public import LeanVM.Guest.B1.Main.AggSoundM
public import LeanVM.Guest.B1.Main.ChildrenAtC
public import LeanVM.Guest.B1.Main.TablesAtS

/-!
# `main`'s words over an answered hash

`MainWordsOkC S Ha`: `MainWords.lean`'s `MainWordsOk` with the callees' preconditions over `Ha`
(`DaListPreAtC`, `ClPreAtC`, `SdPreAtC`, the signatures with `Ha`'s answers, the blob matrix
opening with `Ha` and the guest's padding digests), the signer set's row under `S`, the children's
iterations `ChildWordsOkC S Ha`, and the batching closing over `Ha` from the guest's baked start
`aggSeedD`.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest.B1 (LowDef bufL Meaning_verify_lean_xmssWith Meaning_verify_sig_lean_sphincsWith)

@[expose] public section

variable {S : BlakeSem}

variable (fs : String → ℕ)

variable (S) in
/-- **What `main`'s callees need of its words at `fp`**, on every memory holding `mainIn` and
defined below `2^κ`, the children's runs of the deferring verifier in `VsGood`. -/
structure MainWordsOkC (Ha : List UInt8 → Option Digest) (κ : ℕ) (VsGood : VerifySub.VsData → Prop) (fp : ℕ) (W : MainWords) :
    Prop where
  total : W.total ≤ 65535
  nc : W.nc ≤ 16
  rd1 : W.rd ≤ 1
  da : W.da ≤ 16
  ud : W.ud ≤ 257
  dau : W.da + W.ud ≤ 257
  rx : W.rx ≤ 65535
  rs : W.rs ≤ 65535
  decl : 0 < W.dx + W.ds + W.da
  lens : W.bufs.map List.length = W.sizes
  daList : ∃ claims : List DaClaim, claims.length = W.da ∧ ∀ rd, LowDef κ rd → MemL rd (mainIn fs fp W) →
    DaListPreAtC Ha claims rd [mainPtr fs fp W 0, gen ^ W.da]
      [(digestScalars W.daDig).1, (digestScalars W.daDig).2]
  xList : ∃ cs : List E, cs.length = 4 * W.dx ∧ ∀ rd, LowDef κ rd → MemL rd (mainIn fs fp W) →
    ClPreAtC Ha cs rd [mainPtr fs fp W 1, gen ^ W.dx, ofK (gpow (mainExpBase fs fp W + 34))]
      [(digestScalars W.xDig).1, (digestScalars W.xDig).2]
  sList : ∃ cs : List E, cs.length = 4 * W.ds ∧ ∀ rd, LowDef κ rd → MemL rd (mainIn fs fp W) →
    ClPreAtC Ha cs rd [mainPtr fs fp W 2, gen ^ W.ds, ofK (gpow (mainExpBase fs fp W + 34))]
      [(digestScalars W.sDig).1, (digestScalars W.sDig).2]
  sig : S.check ![(digestScalars W.xDig).1, (digestScalars W.xDig).2, (digestScalars W.sDig).1,
    (digestScalars W.sDig).2] ivCells.1 ivCells.2 (digestScalars W.sigDig).1
    (digestScalars W.sigDig).2 (metadataCell 64 true)
  xSlot : ∀ c < W.rx, W.slX c < W.dx + W.ux
  xMark : ∀ c < W.rx, CellL (mainIn fs fp W) (mainBase fs fp W 4 + W.slX c) (gen ^ c)
  xSig : ∀ c < W.rx, ∀ rd, LowDef κ rd → MemL rd (mainIn fs fp W) →
    Meaning_verify_lean_xmssWith Ha rd [mainPtr fs fp W 1 * gen ^ (4 * W.slX c)] []
  sSlot : ∀ c < W.rs, W.slS c < W.ds + W.us
  sMark : ∀ c < W.rs, CellL (mainIn fs fp W) (mainBase fs fp W 4 + (W.dx + W.ux + W.slS c))
    (gen ^ W.rx * gen ^ c)
  sSig : ∀ c < W.rs, ∀ rd, LowDef κ rd → MemL rd (mainIn fs fp W) →
    Meaning_verify_sig_lean_sphincsWith Ha rd [mainPtr fs fp W 2 * gen ^ (4 * W.slS c)] []
  daVerify : W.rd = 1 → ∃ (wt : Da.Witness) (root vd : Digest), wt.OpensWith Ha daPadCell daPadRow root vd ∧ wt.rows.length = W.drows ∧
    ∀ rd, LowDef κ rd → MemL rd (mainIn fs fp W) → DaVerifyPreAt root vd rd [ofK (gpow (mainExpBase fs fp W + 34))] [W.dr.1, W.dr.2.1, W.dr.2.2.1, W.dr.2.2.2]
  daCover : W.rd = 1 → ∃ i, ∀ rd, LowDef κ rd → MemL rd (mainIn fs fp W) →
    CoverPreAt i rd [mainPtr fs fp W 0, mainPtr fs fp W 4 * (gen ^ W.dx * gen ^ W.ux *
      (gen ^ W.ds * gen ^ W.us)), gen ^ W.da * gen ^ W.ud, gen ^ W.rx * gen ^ W.rs]
      [W.dr.1, W.dr.2.1, W.dr.2.2.1, W.dr.2.2.2]
  written0 : CellL (mainIn fs fp W) (mainBase fs fp W 8 + 0) (gen ^ W.rx * gen ^ W.rs * gen ^ W.rd)
  writtenN : CellL (mainIn fs fp W) (mainBase fs fp W 8 + W.nc)
    (gen ^ W.dx * gen ^ W.ux * (gen ^ W.ds * gen ^ W.us) * (gen ^ W.da * gen ^ W.ud))
  children : ∀ c < W.nc, ChildWordsOkC S Ha κ VsGood (mainIn fs fp W) (mainBase fs fp W 8)
    (mainBase fs fp W 5) (mainPtr fs fp W 1) (mainPtr fs fp W 4) (gen ^ W.dx * gen ^ W.ux)
    (ofK (gpow (mainExpBase fs fp W + 34))) (mainPtr fs fp W 2) (gen ^ W.ds * gen ^ W.us)
    (mainPtr fs fp W 7) (mainPtr fs fp W 0)
    (mainPtr fs fp W 4 * (gen ^ W.dx * gen ^ W.ux * (gen ^ W.ds * gen ^ W.us)))
    (gen ^ W.da * gen ^ W.ud) (digestScalars W.seed).1 (digestScalars W.seed).2
    (ofK (gpow (mainExpBase fs fp W))) (mainPtr fs fp W 6) W.seed c (W.child c)
  leaf : W.nc = 0 → W.dTab = List.replicate 22 0 ++ [W.lbv] ++ List.replicate 28 0 ++ [W.lmA, W.lmB]
  agg : W.nc ≠ 0 → ∃ (cs : List ChildClaims) (h : BatchHints) (d : DeferredClaim),
    cs.length = W.nc ∧ batchWith (m := Option) Ha aggSeedD cs h = some (some d) ∧ h.bytecodeRounds.length = 22 ∧
    h.matrixRounds.length = 28 ∧ (∀ c ∈ cs, FreshShaped c.fresh ∧
      c.carried.bytecodePoint.length = 22 ∧ c.carried.matrixPoint.length = 28) ∧
    W.cpiTab = cs.flatMap (fun c => [(digestScalars c.publicInput).1, (digestScalars c.publicInput).2]) ∧
    W.frTab = cs.flatMap (fun c => fixedCells c.fresh) ∧ W.carTab = cs.flatMap (fun c => c.carried.cells) ∧
    W.dTab = d.cells
  stmt : ∃ sig cells, ∀ rd, LowDef κ rd → MemL rd (mainIn fs fp W) →
    SdPreAtC Ha sig cells rd [(digestScalars W.seed).1, (digestScalars W.seed).2,
      mainPtr fs fp W 3, (digestScalars W.daDig).1, (digestScalars W.daDig).2, mainPtr fs fp W 9]
      [(digestScalars W.stDig).1, (digestScalars W.stDig).2]

end
end LeanVM.Guest.B1.Main
