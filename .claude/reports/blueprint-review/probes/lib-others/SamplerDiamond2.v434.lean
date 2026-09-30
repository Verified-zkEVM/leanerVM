import LeanerVM.Protocol.Field

/-!
Probe `SamplerDiamond2`: with `LeanerVM.Protocol.Field` imported, two samplers on `K` are in
scope, leanerVM's and the one instance search derives from Mathlib's `FinEnum (BitVec n)`.
Are they the same term up to definitional unfolding?
-/

open LeanerVM.Parameters LeanerVM.Protocol OracleComp

#synth SampleableType K

-- the computations are definitionally equal
example :
    (instSampleableTypeK).selectElem = (FinEnum.SampleableType K).selectElem := rfl

-- hence so are the instances (the law fields are proofs)
example : (instSampleableTypeK : SampleableType K) = FinEnum.SampleableType K := rfl
