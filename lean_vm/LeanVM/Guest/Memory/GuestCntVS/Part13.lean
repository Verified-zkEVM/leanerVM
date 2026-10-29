module

public import LeanVM.Guest.Memory.GuestCntVS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvssplit_319_1111 : noTopRet ((Data.core316.body.drop 1111).take 1111) = true ∧
    blockR (kvslookJ 319) (kvsomLookJ 319) false [(.n 217, 0), (.n 218, 8), (.n 311, 28), (.n 498, 0), (.n 499, 5), (.n 575, 32), (.n 762, 0), (.n 763, 3), (.n 830, 23), (.n 1017, 0), (.n 1018, 3), (.n 1080, 18), (.n 1267, 0), (.n 1268, 2), (.n 1327, 15), (.n 1412, 0), (.n 1413, 2), (.n 1469, 12), (.n 2198, 0), (.n 2199, 28), (.n 2211, 0), (.n 2212, 16), (.n 2224, 0), (.n 2225, 11), (.n 2321, 0), (.n 2322, 9), (.n 2334, 0), (.n 2335, 7), (.n 2383, 0), (.n 2384, 6)] Data.core316.params Data.core316.name ((Data.core316.body.drop 1111).take 1111)
      ([(.n 1080, 18), (.n 1018, 3), (.n 1017, 0), (.n 830, 23), (.n 763, 3), (.n 762, 0), (.n 575, 32), (.n 499, 5), (.n 498, 0), (.n 311, 28), (.n 218, 8), (.n 217, 0)], []) = some (⟨2116, []⟩, []) ∧
    blockEnv false [(.n 217, 0), (.n 218, 8), (.n 311, 28), (.n 498, 0), (.n 499, 5), (.n 575, 32), (.n 762, 0), (.n 763, 3), (.n 830, 23), (.n 1017, 0), (.n 1018, 3), (.n 1080, 18), (.n 1267, 0), (.n 1268, 2), (.n 1327, 15), (.n 1412, 0), (.n 1413, 2), (.n 1469, 12), (.n 2198, 0), (.n 2199, 28), (.n 2211, 0), (.n 2212, 16), (.n 2224, 0), (.n 2225, 11), (.n 2321, 0), (.n 2322, 9), (.n 2334, 0), (.n 2335, 7), (.n 2383, 0), (.n 2384, 6)] Data.core316.params ([(.n 1080, 18), (.n 1018, 3), (.n 1017, 0), (.n 830, 23), (.n 763, 3), (.n 762, 0), (.n 575, 32), (.n 499, 5), (.n 498, 0), (.n 311, 28), (.n 218, 8), (.n 217, 0)], []) ((Data.core316.body.drop 1111).take 1111) = ([(.n 2225, 11), (.n 2224, 0), (.n 2212, 16), (.n 2211, 0), (.n 2199, 28), (.n 2198, 0), (.n 1469, 12), (.n 1413, 2), (.n 1412, 0), (.n 1327, 15), (.n 1268, 2), (.n 1267, 0), (.n 1080, 18), (.n 1018, 3), (.n 1017, 0), (.n 830, 23), (.n 763, 3), (.n 762, 0), (.n 575, 32), (.n 499, 5), (.n 498, 0), (.n 311, 28), (.n 218, 8), (.n 217, 0)], []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kvssplit_319_2222 : blockR (kvslookJ 319) (kvsomLookJ 319) false [(.n 217, 0), (.n 218, 8), (.n 311, 28), (.n 498, 0), (.n 499, 5), (.n 575, 32), (.n 762, 0), (.n 763, 3), (.n 830, 23), (.n 1017, 0), (.n 1018, 3), (.n 1080, 18), (.n 1267, 0), (.n 1268, 2), (.n 1327, 15), (.n 1412, 0), (.n 1413, 2), (.n 1469, 12), (.n 2198, 0), (.n 2199, 28), (.n 2211, 0), (.n 2212, 16), (.n 2224, 0), (.n 2225, 11), (.n 2321, 0), (.n 2322, 9), (.n 2334, 0), (.n 2335, 7), (.n 2383, 0), (.n 2384, 6)] Data.core316.params Data.core316.name (Data.core316.body.drop 2222)
    ([(.n 2225, 11), (.n 2224, 0), (.n 2212, 16), (.n 2211, 0), (.n 2199, 28), (.n 2198, 0), (.n 1469, 12), (.n 1413, 2), (.n 1412, 0), (.n 1327, 15), (.n 1268, 2), (.n 1267, 0), (.n 1080, 18), (.n 1018, 3), (.n 1017, 0), (.n 830, 23), (.n 763, 3), (.n 762, 0), (.n 575, 32), (.n 499, 5), (.n 498, 0), (.n 311, 28), (.n 218, 8), (.n 217, 0)], []) = some (⟨232, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_320 : kvsStaticRange 320 25 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_345 : kvsStaticRange 345 23 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_368 : kvsStaticRange 368 25 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_393 : kvsStaticRange 393 22 := by
  unfold kvsStaticRange; decide +kernel

end
end LeanVM.Guest
