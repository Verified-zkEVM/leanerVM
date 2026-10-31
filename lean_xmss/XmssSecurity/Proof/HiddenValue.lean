module

public import XmssSecurity.Proof.EvalDistEq
public import XmssSecurity.Proof.IdealStatement
public import VCVio.OracleComp.Constructions.SampleableType

@[expose] public section

open OracleComp ENNReal

namespace XmssSecurity.HiddenValue

noncomputable local instance : SampleableType Digest :=
  SampleableType.ofFintype Digest

theorem card_digest : Fintype.card Digest = 2 ^ digestBits := by
  simp

theorem uniform_digest_point_probability (target : Digest) :
    Pr{let x ← $ᵗ Digest}[x = target] =
      ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  rw [SampleableType.prEvent_uniformSample_eq_singleton, card_digest]

end XmssSecurity.HiddenValue
