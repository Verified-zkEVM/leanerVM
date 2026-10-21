/-
  LeanVM.Guest.B1.Comp.Whir.Loc.OsCallees

  The callees of `open_stacked` over a completeness model (`Whir/OsCallees.lean`)
-/

module

public import LeanVM.Guest.B1.Whir.OsCallees
public import LeanVM.Guest.B1.UniformS
public import LeanVM.Guest.B1.Comp.Whir.OsCapC
public import LeanVM.Guest.B1.Comp.Opening
public import LeanVM.Guest.B1.Comp.FiatShamir
public import LeanVM.Guest.B1.Comp.Grind
public import LeanVM.Guest.B1.Comp.OpeningOod

/-!
# The callees of `open_stacked` over a completeness model (`Whir/OsCallees.lean`)
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Main (MemL RegionL)
open LeanVM.E2E.Complete
open LeanVM.Protocol.Compile (Bytes)
open LeanVM.Protocol (Digest)

@[expose] public section

variable {Ht : Bytes → Digest} {CM : CompModel}

/-- `opening_ood_point`'s meaning without its states' run, over a completeness model (`OodPointPre`,
the squeezes answered by the model). -/
def OodPointPreC (CM : CompModel) (rd : Reader) : List E → List E → Prop
  | [fs0, fs1, point, ng], rets =>
      ∃ m < ordG, 2 * m + 2 < ordG ∧ ng = gen ^ m ∧
        ((m = 0 ∧ rets = [fs0, fs1]) ∨
          (0 < m ∧ ∃ cv rs cv', (fs0, fs1) = digestScalars cv ∧ RunsToM CM.hm (Prog.sampleN m) cv [] rs cv' ∧
            ReadsAt rd point rs ∧ rets = [(digestScalars cv').1, (digestScalars cv').2]))
  | _, _ => False

/-- `grind_check`'s meaning without its frame run, over a completeness model (`GrindPre`, the
squeeze and the absorb answered by the model). -/
def GrindPreC (CM : CompModel) (_rd : Reader) : List E → List E → Prop
  | [s0, s1, nonce, ng], rets =>
      rets = [] ∧ ∃ m < ordG, m ≤ 64 ∧ ng = gen ^ m ∧ ∃ cv base d, (s0, s1) = digestScalars cv ∧
        CM.H (digestBytes cv ++ blockOf 0 3) = some base ∧ CM.H (digestBytes base ++ blockOf nonce 4) = some d ∧
        powOk m nonce d = true
  | _, _ => False

/-- `OsDecodeAt` on disjoint layouts. -/
def OsDecodeAtDC (CM : CompModel) (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) (d : ℕ) (name : String) : Prop :=
  ∀ (w pos ptrs : E) (Lin : Main.Layout) (fp : ℕ),
    (∀ rd, LowDef k rd → MemL rd Lin → ∀ j < 192 / d,
      LoadHolds rd pos j (eOfNat ((eToNat w >>> (j * d)) % 2 ^ d)) ∧
        LoadHolds rd ptrs j (ofK (Parameters.gpow (fp + cert name (.n 3))) * gen ^ (j * d))) →
    ∃ Lown : Main.Layout, Within (dqRunL cert name fp w ++ Lown) fp (fs name) ∧
      DisjL (dqRunL cert name fp w ++ Lown) ∧
      ∀ rd, LowDef k rd → MemL rd (dqRunL cert name fp w ++ Lown ++ Lin) →
        RelAtInB CM.sem coreProgram fs cert rd (RegionL Lin) (RegionL (dqRunL cert name fp w)) fp (fs name) name
          [w, pos, ptrs] []

/-- `CompleteRelB` with a bound depending on the arguments. -/
def CompleteRelBAC (CM : CompModel) (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) (f : String)
    (Pre : Reader → List E → List E → Prop) (B : List E → ℕ) : Prop :=
  ∀ (args rets : List E) (Lin : Main.Layout), (∀ rd, LowDef k rd → MemL rd Lin → Pre rd args rets) →
    CompleteAtBS CM.sem fs cert k f Lin args (Returns rets) (B args)

/-- `OsFinalMsgAtD` by bounded trees. -/
def OsFinalMsgAtBC (CM : CompModel) (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) (name : String) (n : ℕ)
    (B : List E → ℕ) : Prop :=
  ∀ (args rets : List E) (Lin : Main.Layout), (∀ rd, MemL rd Lin → MeaningOpeningFinalMessageComp CM n rd args rets) →
    CompleteAtBS CM.sem fs cert k name Lin args (Returns rets) (B args)

/-- `OsRowWeightsAtD` by bounded trees. -/
def OsRowWeightsAtBC (CM : CompModel) (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) (name : String) (folds rev : ℕ)
    (B : List E → ℕ) : Prop :=
  ∀ (args rets : List E) (Lin : Main.Layout), (∀ rd, MemL rd Lin → MeaningOpeningRowWeights folds rev rd args rets) →
    CompleteAtBS CM.sem fs cert k name Lin args (Returns rets) (B args)

/-- `OsFoldFinalAtD` by bounded trees. -/
def OsFoldFinalAtBC (CM : CompModel) (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) (name : String) (n : ℕ)
    (B : List E → ℕ) : Prop :=
  ∀ (args rets : List E) (Lin : Main.Layout), (∀ rd, MemL rd Lin → MeaningFoldFinalMsg n rd args rets) →
    CompleteAtBS CM.sem fs cert k name Lin args (Returns rets) (B args)

/-- `OsDecodeAtDC CM`, its tree `fs name` words (the decoder calls nothing). -/
def OsDecodeAtBC (CM : CompModel) (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) (d : ℕ) (name : String) : Prop :=
  OsDecodeAtDC CM fs cert k d name

/-- **The callees of `open_stacked` from group 1, by bounded trees**, each with its bound. -/
structure OsCalleesAtBC (CM : CompModel) (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) : Type where
  foldB : List E → ℕ
  fold : CompleteRelBAC CM fs cert k "opening_fold" (MeaningOpeningFoldComp CM) foldB
  canonicalB : List E → ℕ
  canonical : CompleteRelBAC CM fs cert k "assert_canonical" (fun _ args rets => MeaningAssertCanonical args rets)
    canonicalB
  oodB : List E → ℕ
  ood : CompleteRelBAC CM fs cert k "opening_ood_point" (OodPointPreC CM) oodB
  grindB : List E → ℕ
  grind : CompleteRelBAC CM fs cert k "grind_check" (GrindPreC CM) grindB
  finalMsg4B : List E → ℕ
  finalMsg4 : OsFinalMsgAtBC CM fs cert k "opening_final_message__L4" 4 finalMsg4B
  finalMsg8B : List E → ℕ
  finalMsg8 : OsFinalMsgAtBC CM fs cert k "opening_final_message__L8" 8 finalMsg8B
  finalMsg16B : List E → ℕ
  finalMsg16 : OsFinalMsgAtBC CM fs cert k "opening_final_message__L16" 16 finalMsg16B
  finalMsg32B : List E → ℕ
  finalMsg32 : OsFinalMsgAtBC CM fs cert k "opening_final_message__L32" 32 finalMsg32B
  rowWeights4B : List E → ℕ
  rowWeights4 : OsRowWeightsAtBC CM fs cert k "opening_row_weights__L4_L0" 4 0 rowWeights4B
  rowWeights6B : List E → ℕ
  rowWeights6 : OsRowWeightsAtBC CM fs cert k "opening_row_weights__L6_L1" 6 1 rowWeights6B
  foldFinal2B : List E → ℕ
  foldFinal2 : OsFoldFinalAtBC CM fs cert k "fold_final_msg__L2" 2 foldFinal2B
  foldFinal3B : List E → ℕ
  foldFinal3 : OsFoldFinalAtBC CM fs cert k "fold_final_msg__L3" 3 foldFinal3B
  foldFinal4B : List E → ℕ
  foldFinal4 : OsFoldFinalAtBC CM fs cert k "fold_final_msg__L4" 4 foldFinal4B
  foldFinal5B : List E → ℕ
  foldFinal5 : OsFoldFinalAtBC CM fs cert k "fold_final_msg__L5" 5 foldFinal5B
  decode : ∀ p ∈ osDqNames, OsDecodeAtBC CM fs cert k p.1 p.2

end
end LeanVM.Guest.B1
