module

public import LeanVM.Guest.Memory.GuestCntVK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvkstaticRange_309 : kvkStaticRange 309 1 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_310 : kvkStaticRange 310 1 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvksplit_311_0 : noTopRet ((Data.core311.body.drop 0).take 1320) = true ∧
    blockR (kvklookJ 311) (kvkomLookJ 311) false [(.n 217, 0), (.n 218, 10), (.n 330, 37), (.n 517, 0), (.n 518, 5), (.n 600, 38), (.n 787, 0), (.n 788, 4), (.n 857, 25), (.n 1044, 0), (.n 1045, 3), (.n 1108, 19), (.n 1193, 0), (.n 1194, 2), (.n 1253, 15), (.n 1962, 0), (.n 1963, 37), (.n 2101, 0), (.n 2102, 19), (.n 2114, 0), (.n 2115, 12), (.n 2205, 0), (.n 2206, 9), (.n 2272, 0), (.n 2273, 7)] Data.core311.params Data.core311.name ((Data.core311.body.drop 0).take 1320)
      ([], []) = some (⟨3867, []⟩, []) ∧
    blockEnv false [(.n 217, 0), (.n 218, 10), (.n 330, 37), (.n 517, 0), (.n 518, 5), (.n 600, 38), (.n 787, 0), (.n 788, 4), (.n 857, 25), (.n 1044, 0), (.n 1045, 3), (.n 1108, 19), (.n 1193, 0), (.n 1194, 2), (.n 1253, 15), (.n 1962, 0), (.n 1963, 37), (.n 2101, 0), (.n 2102, 19), (.n 2114, 0), (.n 2115, 12), (.n 2205, 0), (.n 2206, 9), (.n 2272, 0), (.n 2273, 7)] Data.core311.params ([], []) ((Data.core311.body.drop 0).take 1320) = ([(.n 1253, 15), (.n 1194, 2), (.n 1193, 0), (.n 1108, 19), (.n 1045, 3), (.n 1044, 0), (.n 857, 25), (.n 788, 4), (.n 787, 0), (.n 600, 38), (.n 518, 5), (.n 517, 0), (.n 330, 37), (.n 218, 10), (.n 217, 0)], []) := by
  decide +kernel

end
end LeanVM.Guest
