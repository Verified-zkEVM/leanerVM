module

public import LeanVM.Guest.Memory.GuestCntVD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvdsplit_322_1111 : noTopRet ((Data.core322.body.drop 1111).take 1111) = true ∧
    blockR (kvdlookJ 322) (kvdomLookJ 322) false [(.n 217, 0), (.n 218, 8), (.n 311, 28), (.n 498, 0), (.n 499, 5), (.n 575, 32), (.n 762, 0), (.n 763, 3), (.n 830, 23), (.n 1017, 0), (.n 1018, 3), (.n 1080, 18), (.n 1267, 0), (.n 1268, 2), (.n 1327, 15), (.n 1412, 0), (.n 1413, 2), (.n 1469, 12), (.n 2198, 0), (.n 2199, 28), (.n 2211, 0), (.n 2212, 16), (.n 2224, 0), (.n 2225, 11), (.n 2321, 0), (.n 2322, 9), (.n 2334, 0), (.n 2335, 7), (.n 2383, 0), (.n 2384, 6)] Data.core322.params Data.core322.name ((Data.core322.body.drop 1111).take 1111)
      ([(.n 1080, 18), (.n 1018, 3), (.n 1017, 0), (.n 830, 23), (.n 763, 3), (.n 762, 0), (.n 575, 32), (.n 499, 5), (.n 498, 0), (.n 311, 28), (.n 218, 8), (.n 217, 0)], []) = some (⟨3747, []⟩, []) ∧
    blockEnv false [(.n 217, 0), (.n 218, 8), (.n 311, 28), (.n 498, 0), (.n 499, 5), (.n 575, 32), (.n 762, 0), (.n 763, 3), (.n 830, 23), (.n 1017, 0), (.n 1018, 3), (.n 1080, 18), (.n 1267, 0), (.n 1268, 2), (.n 1327, 15), (.n 1412, 0), (.n 1413, 2), (.n 1469, 12), (.n 2198, 0), (.n 2199, 28), (.n 2211, 0), (.n 2212, 16), (.n 2224, 0), (.n 2225, 11), (.n 2321, 0), (.n 2322, 9), (.n 2334, 0), (.n 2335, 7), (.n 2383, 0), (.n 2384, 6)] Data.core322.params ([(.n 1080, 18), (.n 1018, 3), (.n 1017, 0), (.n 830, 23), (.n 763, 3), (.n 762, 0), (.n 575, 32), (.n 499, 5), (.n 498, 0), (.n 311, 28), (.n 218, 8), (.n 217, 0)], []) ((Data.core322.body.drop 1111).take 1111) = ([(.n 2225, 11), (.n 2224, 0), (.n 2212, 16), (.n 2211, 0), (.n 2199, 28), (.n 2198, 0), (.n 1469, 12), (.n 1413, 2), (.n 1412, 0), (.n 1327, 15), (.n 1268, 2), (.n 1267, 0), (.n 1080, 18), (.n 1018, 3), (.n 1017, 0), (.n 830, 23), (.n 763, 3), (.n 762, 0), (.n 575, 32), (.n 499, 5), (.n 498, 0), (.n 311, 28), (.n 218, 8), (.n 217, 0)], []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kvdsplit_322_2222 : blockR (kvdlookJ 322) (kvdomLookJ 322) false [(.n 217, 0), (.n 218, 8), (.n 311, 28), (.n 498, 0), (.n 499, 5), (.n 575, 32), (.n 762, 0), (.n 763, 3), (.n 830, 23), (.n 1017, 0), (.n 1018, 3), (.n 1080, 18), (.n 1267, 0), (.n 1268, 2), (.n 1327, 15), (.n 1412, 0), (.n 1413, 2), (.n 1469, 12), (.n 2198, 0), (.n 2199, 28), (.n 2211, 0), (.n 2212, 16), (.n 2224, 0), (.n 2225, 11), (.n 2321, 0), (.n 2322, 9), (.n 2334, 0), (.n 2335, 7), (.n 2383, 0), (.n 2384, 6)] Data.core322.params Data.core322.name (Data.core322.body.drop 2222)
    ([(.n 2225, 11), (.n 2224, 0), (.n 2212, 16), (.n 2211, 0), (.n 2199, 28), (.n 2198, 0), (.n 1469, 12), (.n 1413, 2), (.n 1412, 0), (.n 1327, 15), (.n 1268, 2), (.n 1267, 0), (.n 1080, 18), (.n 1018, 3), (.n 1017, 0), (.n 830, 23), (.n 763, 3), (.n 762, 0), (.n 575, 32), (.n 499, 5), (.n 498, 0), (.n 311, 28), (.n 218, 8), (.n 217, 0)], []) = some (⟨276, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_323 : kvdStaticRange 323 25 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_348 : kvdStaticRange 348 23 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_371 : kvdStaticRange 371 30 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_401 : kvdStaticRange 401 24 := by
  unfold kvdStaticRange; decide +kernel

end
end LeanVM.Guest
