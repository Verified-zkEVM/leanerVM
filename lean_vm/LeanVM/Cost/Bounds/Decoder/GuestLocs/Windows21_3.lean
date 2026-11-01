module

public import LeanVM.Cost.Decoder.GuestTables

/-!
# Bound: the guest's frame cells, function `21`'s windows `72` to `92`, by evaluation

Function `21` (`verify_sig_lean_sphincs`, `93` windows, `69213` cells, the table's
largest) evaluated by windows, in `4` modules of their own (`GuestTablesBounds.lean` combines them
through `List.all_flatten`).
-/

namespace LeanVM.Cost.Bounds

open LeanVM.Guest

public section

/-- Function `21`'s frame cells, windows `72` to `92`, are below `2^20`. -/
theorem guestLocsWindows21_3_lt :
    [Data.cert21_w72_0,
    Data.cert21_w73_0,
    Data.cert21_w74_0,
    Data.cert21_w75_0,
    Data.cert21_w76_0,
    Data.cert21_w77_0,
    Data.cert21_w78_0,
    Data.cert21_w79_0,
    Data.cert21_w80_0,
    Data.cert21_w81_0,
    Data.cert21_w82_0,
    Data.cert21_w83_0,
    Data.cert21_w84_0,
    Data.cert21_w85_0,
    Data.cert21_w86_0,
    Data.cert21_w87_0,
    Data.cert21_w88_0,
    Data.cert21_w89_0,
    Data.cert21_w90_0,
    Data.cert21_w91_0,
    Data.cert21_w92_0].all (fun w ↦ w.all (· < 2 ^ 20)) = true := by
  decide +kernel

end

end LeanVM.Cost.Bounds
