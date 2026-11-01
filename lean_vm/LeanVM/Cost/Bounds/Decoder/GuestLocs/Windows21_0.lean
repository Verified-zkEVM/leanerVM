module

public import LeanVM.Cost.Decoder.GuestTables

/-!
# Bound: the guest's frame cells, function `21`'s windows `0` to `23`, by evaluation

Function `21` (`verify_sig_lean_sphincs`, `93` windows, `69213` cells, the table's
largest) evaluated by windows, in `4` modules of their own (`GuestTablesBounds.lean` combines them
through `List.all_flatten`).
-/

namespace LeanVM.Cost.Bounds

open LeanVM.Guest

public section

/-- Function `21`'s frame cells, windows `0` to `23`, are below `2^20`. -/
theorem guestLocsWindows21_0_lt :
    [Data.cert21_w0_0,
    Data.cert21_w1_0,
    Data.cert21_w2_0,
    Data.cert21_w3_0,
    Data.cert21_w4_0,
    Data.cert21_w5_0,
    Data.cert21_w6_0,
    Data.cert21_w7_0,
    Data.cert21_w8_0,
    Data.cert21_w9_0,
    Data.cert21_w10_0,
    Data.cert21_w11_0,
    Data.cert21_w12_0,
    Data.cert21_w13_0,
    Data.cert21_w14_0,
    Data.cert21_w15_0,
    Data.cert21_w16_0,
    Data.cert21_w17_0,
    Data.cert21_w18_0,
    Data.cert21_w19_0,
    Data.cert21_w20_0,
    Data.cert21_w21_0,
    Data.cert21_w22_0,
    Data.cert21_w23_0].all (fun w ↦ w.all (· < 2 ^ 20)) = true := by
  decide +kernel

end

end LeanVM.Cost.Bounds
