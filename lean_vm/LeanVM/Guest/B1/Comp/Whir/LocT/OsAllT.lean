/-
  LeanVM.Guest.B1.Comp.Whir.LocT.OsAllT

  `open_stacked` over every completeness model, its tree loading the stream words it reads and
  decoding to the run's openings: `CompleteOpenAtBCL` at `main`'s frame sizes and certificates.
-/

module

public import LeanVM.Guest.B1.Comp.Whir.LocT.OsInstAllT
public import LeanVM.Guest.B1.Comp.Whir.Loc.OsAllC

/-!
# `open_stacked` in tree form over every completeness model

`open_stacked_completeAtBCL_of`, `open_stacked_completeAtBCL_b2c`: `open_stacked_completeAtBC_of`,
`open_stacked_completeAtBC_b2c` in tree form (`CompleteOpenAtBCL … (CapAgreesC CM) … OsQ`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub
open LeanVM.E2E.Complete

@[expose] public section

/-- **`open_stacked` in tree form over every completeness model**, at frame sizes agreeing with
`fsOf` but at `main`, at the caps' agreement over the model, within the deployed bound. -/
theorem open_stacked_completeAtBCL_of (CM : CompModel) (fs : String → ℕ) (h : FsAgree fs) (cert : String → V → ℕ)
    (k : ℕ) (hc : G1Certs fs cert) (hq : OsOqFits fs cert) :
    CompleteOpenAtBCL CM fs cert k (CapAgreesC CM) (osBop fs (osCalleesMaxOf fs h cert k hc) (osPureSizes fs)) OsQ := by
  rw [← osBopC_eq CM fs h cert k hc]
  exact open_stacked_completeAtBCL fs cert k (osCalleesAtBCOf CM fs h cert k hc) (osCalleesMaxOfC CM fs h cert k hc) hq
    (osPureSizesC CM fs)

/-- **`open_stacked` in tree form over every completeness model at `main`'s frame sizes and
certificates**: `CalleesOpenC`'s field, its tree loading the words it reads and decoding to the
openings. -/
theorem open_stacked_completeAtBCL_b2c (CM : CompModel) :
    CompleteOpenAtBCL CM B2C.fs B2C.cert 16 (CapAgreesC CM) B2C.calleesHyps_b2c.Bop OsQ :=
  open_stacked_completeAtBCL_of CM B2C.fs B2C.fsAgree_fs B2C.cert 16 B2C.g1Certs B2C.osOqFits

end
end LeanVM.Guest.B1
