/-
  LeanVM.Guest.B1.KeccakGkr.LayerHolds

  `keccak_layer`'s four specializations meet `MeaningKeccakLayer`.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.LayerProof
public import LeanVM.Guest.B1.KeccakGkr.LayerWeight0
public import LeanVM.Guest.B1.KeccakGkr.LayerBody254
public import LeanVM.Guest.B1.KeccakGkr.LayerBody255
public import LeanVM.Guest.B1.KeccakGkr.LayerBody256
public import LeanVM.Guest.B1.KeccakGkr.LayerBody257

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

theorem find_layer254 : coreProgram.find? "keccak_layer__L1_L0" = some Data.core254 :=
  Program.find?_of_indexOf? (j := 254) (by decide +kernel) rfl
theorem find_layer255 : coreProgram.find? "keccak_layer__L1_L1" = some Data.core255 :=
  Program.find?_of_indexOf? (j := 255) (by decide +kernel) rfl
theorem find_layer256 : coreProgram.find? "keccak_layer__L0_L0" = some Data.core256 :=
  Program.find?_of_indexOf? (j := 256) (by decide +kernel) rfl
theorem find_layer257 : coreProgram.find? "keccak_layer__L0_L1" = some Data.core257 :=
  Program.find?_of_indexOf? (j := 257) (by decide +kernel) rfl

/-- **`keccak_layer`**, given the later claims' weight section. -/
theorem keccak_layer_holds_of (hW0 : WeightOk 0) : keccak_layer_Spec := by
  intro first hf odd ho rd args rets h
  interval_cases first <;> interval_cases odd
  · exact layer_sound (first := 0) (odd := 0) (by decide) (by decide) hW0 find_layer256
      layer_body256 rfl rd args rets h
  · exact layer_sound (first := 0) (odd := 1) (by decide) (by decide) hW0 find_layer257
      layer_body257 rfl rd args rets h
  · exact layer_sound (first := 1) (odd := 0) (by decide) (by decide) weightOk_one find_layer254
      layer_body254 rfl rd args rets h
  · exact layer_sound (first := 1) (odd := 1) (by decide) (by decide) weightOk_one find_layer255
      layer_body255 rfl rd args rets h

/-- **`keccak_layer`** (G:2480-2725; TRIAGE #60): its four specializations compute their
meanings. -/
theorem keccak_layer_holds : keccak_layer_Spec := keccak_layer_holds_of weightOk_zero

end
end LeanVM.Guest.B1.VerifySub
