import LeanVM.Cost.Extractor.Lane

/-!
# Probe: the additive NTT, as compiled on the chain

`novelFwd` and `novelInv` (`Protocol/Extraction/Extractor.lean` §4) are compiled on demand in
`Cost/Extractor/Lane.lean` (`laneEncodedDistinctC`): `novelFwd.c216` (its stages `novelFwdStage.c218`,
twiddles `novelTwiddles.c219`), and `novelInv` inlined into `toNovelFast.c244` (its fold's closure
`toNovelFast.c244.lam0`, stages `novelInvStage.c246`); bounded in `Cost/Bounds/FastPath.lean`
(`novelFwd_cost`, `novelInv_cost`). Here: their values and prices on small inputs.
-/

namespace LeanVMTests.Cost.ProbeNtt

open LeanVM.Cost LeanVM.Cost.Library LeanVM.Parameters LeanVM.Extraction

def run (deps : List (ℕ × Term)) (i : ℕ) (args : List MachineValue) : Option (MachineValue × ℕ) :=
  evaluateFunctionBody (MachineProgram.ofList deps) 1000000 i args

def coeffs (κ : ℕ) : Array K := Array.ofFn fun v : Fin (2 ^ κ) ↦ K.ofBits (v.val * 2654435761 % 1000003)

#guard (run Auto.LeanVM.Extraction.novelFwd.c216.costDeps Auto.LeanVM.Extraction.novelFwd.c216.costIdx
    [MachineEncoding.encodeValue (4 : ℕ), MachineEncoding.encodeValue (1 : ℕ),
      MachineEncoding.encodeValue (coeffs 4)]).map (·.1) ==
  some (MachineEncoding.encodeValue (novelFwd 4 1 (coeffs 4)))

/-- The forward transform's price at `κ`, `R = 1`. -/
def fwdPrice (κ : ℕ) : ℕ :=
  ((run Auto.LeanVM.Extraction.novelFwd.c216.costDeps Auto.LeanVM.Extraction.novelFwd.c216.costIdx
    [MachineEncoding.encodeValue κ, MachineEncoding.encodeValue (1 : ℕ),
      MachineEncoding.encodeValue (coeffs κ)]).map (·.2)).getD 0

/-- The inverse transform's price at `κ` (the fold over the stages). -/
def invPrice (κ : ℕ) : ℕ :=
  ((run (Auto.LeanVM.Extraction.Fast.toNovelFast.c244.lam0.costDeps ++ listFoldl.costDeps) listFoldl.costIdx
    [.closure Auto.LeanVM.Extraction.Fast.toNovelFast.c244.lam0.costIdx [MachineEncoding.encodeValue κ],
      MachineEncoding.encodeValue (coeffs κ), MachineEncoding.encodeValue (List.range κ)]).map (·.2)).getD 0

#guard (run (Auto.LeanVM.Extraction.Fast.toNovelFast.c244.lam0.costDeps ++ listFoldl.costDeps) listFoldl.costIdx
    [.closure Auto.LeanVM.Extraction.Fast.toNovelFast.c244.lam0.costIdx [MachineEncoding.encodeValue (4 : ℕ)],
      MachineEncoding.encodeValue (coeffs 4), MachineEncoding.encodeValue (List.range 4)]).map (·.1) ==
  some (MachineEncoding.encodeValue (novelInv 4 (coeffs 4)))

#eval (List.range 4).map fun j ↦ let κ := 4 + 2 * j; (κ, fwdPrice κ, invPrice κ, κ * 2 ^ (κ + 1))

end LeanVMTests.Cost.ProbeNtt
