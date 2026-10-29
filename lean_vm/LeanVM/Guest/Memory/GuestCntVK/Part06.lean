module

public import LeanVM.Guest.Memory.GuestCntVK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvkstaticRange_302 : kvkStaticRange 302 1 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_303 : kvkStaticRange 303 1 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvksplit_304_0 : noTopRet ((Data.core304.body.drop 0).take 1320) = true ∧
    blockR (kvklookJ 304) (kvkomLookJ 304) false [(.n 217, 0), (.n 218, 14), (.n 367, 56), (.n 554, 0), (.n 555, 6), (.n 644, 45), (.n 831, 0), (.n 832, 4), (.n 904, 28), (.n 1091, 0), (.n 1092, 3), (.n 1157, 21), (.n 1242, 0), (.n 1243, 2), (.n 1303, 16), (.n 2012, 0), (.n 2013, 56), (.n 2025, 0), (.n 2026, 22), (.n 2140, 0), (.n 2141, 14), (.n 2153, 0), (.n 2154, 10), (.n 2220, 0), (.n 2221, 8)] Data.core304.params Data.core304.name ((Data.core304.body.drop 0).take 1320)
      ([], []) = some (⟨4684, []⟩, []) ∧
    blockEnv false [(.n 217, 0), (.n 218, 14), (.n 367, 56), (.n 554, 0), (.n 555, 6), (.n 644, 45), (.n 831, 0), (.n 832, 4), (.n 904, 28), (.n 1091, 0), (.n 1092, 3), (.n 1157, 21), (.n 1242, 0), (.n 1243, 2), (.n 1303, 16), (.n 2012, 0), (.n 2013, 56), (.n 2025, 0), (.n 2026, 22), (.n 2140, 0), (.n 2141, 14), (.n 2153, 0), (.n 2154, 10), (.n 2220, 0), (.n 2221, 8)] Data.core304.params ([], []) ((Data.core304.body.drop 0).take 1320) = ([(.n 1303, 16), (.n 1243, 2), (.n 1242, 0), (.n 1157, 21), (.n 1092, 3), (.n 1091, 0), (.n 904, 28), (.n 832, 4), (.n 831, 0), (.n 644, 45), (.n 555, 6), (.n 554, 0), (.n 367, 56), (.n 218, 14), (.n 217, 0)], []) := by
  decide +kernel

end
end LeanVM.Guest
