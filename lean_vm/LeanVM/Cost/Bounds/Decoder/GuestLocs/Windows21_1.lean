module

public import LeanVM.Cost.Decoder.GuestTables

/-!
# Bound: the guest's frame cells, function `21`'s windows `24` to `47`, by evaluation

Function `21` (`verify_sig_lean_sphincs`, `93` windows, `69213` cells, the table's
largest) evaluated by windows, in `4` modules of their own (`GuestTablesBounds.lean` combines them
through `List.all_flatten`).
-/

namespace LeanVM.Cost.Bounds

open LeanVM.Guest

public section

/-- Function `21`'s frame cells, windows `24` to `47`, are below `2^20`. -/
theorem guestLocsWindows21_1_lt :
    [Data.cert21_w24_0,
    Data.cert21_w25_0,
    Data.cert21_w26_0,
    Data.cert21_w27_0,
    Data.cert21_w28_0,
    Data.cert21_w29_0,
    Data.cert21_w30_0,
    Data.cert21_w31_0,
    Data.cert21_w32_0,
    Data.cert21_w33_0,
    Data.cert21_w34_0,
    Data.cert21_w35_0,
    Data.cert21_w36_0,
    Data.cert21_w37_0,
    Data.cert21_w38_0,
    Data.cert21_w39_0,
    Data.cert21_w40_0,
    Data.cert21_w41_0,
    Data.cert21_w42_0,
    Data.cert21_w43_0,
    Data.cert21_w44_0,
    Data.cert21_w45_0,
    Data.cert21_w46_0,
    Data.cert21_w47_0].all (fun w ↦ w.all (· < 2 ^ 20)) = true := by
  decide +kernel

end

end LeanVM.Cost.Bounds
