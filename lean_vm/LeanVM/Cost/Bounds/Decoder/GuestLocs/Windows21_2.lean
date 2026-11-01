module

public import LeanVM.Cost.Decoder.GuestTables

/-!
# Bound: the guest's frame cells, function `21`'s windows `48` to `71`, by evaluation

Function `21` (`verify_sig_lean_sphincs`, `93` windows, `69213` cells, the table's
largest) evaluated by windows, in `4` modules of their own (`GuestTablesBounds.lean` combines them
through `List.all_flatten`).
-/

namespace LeanVM.Cost.Bounds

open LeanVM.Guest

public section

/-- Function `21`'s frame cells, windows `48` to `71`, are below `2^20`. -/
theorem guestLocsWindows21_2_lt :
    [Data.cert21_w48_0,
    Data.cert21_w49_0,
    Data.cert21_w50_0,
    Data.cert21_w51_0,
    Data.cert21_w52_0,
    Data.cert21_w53_0,
    Data.cert21_w54_0,
    Data.cert21_w55_0,
    Data.cert21_w56_0,
    Data.cert21_w57_0,
    Data.cert21_w58_0,
    Data.cert21_w59_0,
    Data.cert21_w60_0,
    Data.cert21_w61_0,
    Data.cert21_w62_0,
    Data.cert21_w63_0,
    Data.cert21_w64_0,
    Data.cert21_w65_0,
    Data.cert21_w66_0,
    Data.cert21_w67_0,
    Data.cert21_w68_0,
    Data.cert21_w69_0,
    Data.cert21_w70_0,
    Data.cert21_w71_0].all (fun w ↦ w.all (· < 2 ^ 20)) = true := by
  decide +kernel

end

end LeanVM.Cost.Bounds
