/-
  LeanVM.Guest.B1.Comp.VerifySub.Seed

  `verify_sub`'s seed compression over a completeness model.
-/

module

public import LeanVM.Guest.B1.Comp.Da.Tree
public import LeanVM.Guest.B1.VerifySub.CFront

/-!
# The seed over a completeness model

`compress_seed` (`VerifySub/CFront.lean`) over a `CompModel`: the seed's and the statement's
digests, one final block under the IV, check under `CM.sem` into the model's answer for their
bytes (`pair_comp`). At `CompModel.deployed` it is `compress_seed` (`compress_seed_of_comp`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.E2E.Complete

@[expose] public section

/-- **The seed's compression over a completeness model** (`compress_seed`). -/
theorem compress_seed_comp (CM : CompModel) {seed pi d : Digest}
    (hd : CM.H (digestBytes seed ++ digestBytes pi) = some d) :
    CM.sem.check ![(digestScalars seed).1, (digestScalars seed).2, (digestScalars pi).1,
      (digestScalars pi).2] ivCells.1 ivCells.2 (digestScalars d).1 (digestScalars d).2
      (metadataCell 64 true) :=
  Digest.pair_comp CM hd

/-- The deployed `compress_seed`, from the model's at `CompModel.deployed`. -/
theorem compress_seed_of_comp (seed pi : Digest) :
    CompressCells ![(digestScalars seed).1, (digestScalars seed).2, (digestScalars pi).1,
      (digestScalars pi).2] ivCells.1 ivCells.2
      (digestScalars (blake2sBytes (digestBytes seed ++ digestBytes pi))).1
      (digestScalars (blake2sBytes (digestBytes seed ++ digestBytes pi))).2
      (metadataCell 64 true) :=
  compress_seed_comp CompModel.deployed rfl

end
end LeanVM.Guest.B1.VerifySub
