/-
  LeanVM.Guest.B1.Opening.QueriesBody2

  The bodies of a quarter of `opening_queries`' specializations and of their loop helpers are the
  templates (kernel evaluation), and so their soundness.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesMain

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier

@[expose] public section

set_option maxRecDepth 100000 in
theorem oqBody_433 : Data.core433.body = oqMainT ⟨1, 64, 10, 8⟩ 0 "__loop365" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_835 : Data.core835.body = oqLoop1T ⟨1, 64, 10, 8⟩ 0 "__loop365" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L18_L8` is sound. -/
theorem oqSound_433 (rd : Reader) (cap flags lam lamN qptrs wp nG : E) (rets : List E)
    (hbits : ∀ N, nG = gen ^ N → N < ordG → QueryBitsBool rd qptrs (oqCount 0 1 N) 18)
    (h : coreProgram.Rel rd "opening_queries__L0_L1_L64_L32_L18_L8" [cap, flags, lam, lamN, qptrs, wp, nG] rets) :
    MeaningOpeningQueries 0 1 64 18 8 rd [cap, flags, lam, lamN, qptrs, wp, nG] rets :=
  oqMain1_sound (s := ⟨1, 64, 10, 8⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (hodd := (by decide : 0 ≤ 1))
    (Program.find?_of_indexOf? (j := 433) (by decide +kernel) rfl) rfl oqBody_433
    (Program.find?_of_indexOf? (j := 835) (by decide +kernel) rfl) rfl oqBody_835 hbits h

set_option maxRecDepth 100000 in
theorem oqBody_551 : Data.core551.body = oqMainT ⟨1, 64, 13, 7⟩ 0 "__loop386" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_861 : Data.core861.body = oqLoop1T ⟨1, 64, 13, 7⟩ 0 "__loop386" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L20_L7` is sound. -/
theorem oqSound_551 (rd : Reader) (cap flags lam lamN qptrs wp nG : E) (rets : List E)
    (hbits : ∀ N, nG = gen ^ N → N < ordG → QueryBitsBool rd qptrs (oqCount 0 1 N) 20)
    (h : coreProgram.Rel rd "opening_queries__L0_L1_L64_L32_L20_L7" [cap, flags, lam, lamN, qptrs, wp, nG] rets) :
    MeaningOpeningQueries 0 1 64 20 7 rd [cap, flags, lam, lamN, qptrs, wp, nG] rets :=
  oqMain1_sound (s := ⟨1, 64, 13, 7⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (hodd := (by decide : 0 ≤ 1))
    (Program.find?_of_indexOf? (j := 551) (by decide +kernel) rfl) rfl oqBody_551
    (Program.find?_of_indexOf? (j := 861) (by decide +kernel) rfl) rfl oqBody_861 hbits h

set_option maxRecDepth 100000 in
theorem oqBody_487 : Data.core487.body = oqMainT ⟨1, 64, 13, 8⟩ 0 "__loop374" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_847 : Data.core847.body = oqLoop1T ⟨1, 64, 13, 8⟩ 0 "__loop374" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L21_L8` is sound. -/
theorem oqSound_487 (rd : Reader) (cap flags lam lamN qptrs wp nG : E) (rets : List E)
    (hbits : ∀ N, nG = gen ^ N → N < ordG → QueryBitsBool rd qptrs (oqCount 0 1 N) 21)
    (h : coreProgram.Rel rd "opening_queries__L0_L1_L64_L32_L21_L8" [cap, flags, lam, lamN, qptrs, wp, nG] rets) :
    MeaningOpeningQueries 0 1 64 21 8 rd [cap, flags, lam, lamN, qptrs, wp, nG] rets :=
  oqMain1_sound (s := ⟨1, 64, 13, 8⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (hodd := (by decide : 0 ≤ 1))
    (Program.find?_of_indexOf? (j := 487) (by decide +kernel) rfl) rfl oqBody_487
    (Program.find?_of_indexOf? (j := 847) (by decide +kernel) rfl) rfl oqBody_847 hbits h

set_option maxRecDepth 100000 in
theorem oqBody_586 : Data.core586.body = oqMainT ⟨1, 64, 16, 7⟩ 0 "__loop391" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_866 : Data.core866.body = oqLoop1T ⟨1, 64, 16, 7⟩ 0 "__loop391" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L23_L7` is sound. -/
theorem oqSound_586 (rd : Reader) (cap flags lam lamN qptrs wp nG : E) (rets : List E)
    (hbits : ∀ N, nG = gen ^ N → N < ordG → QueryBitsBool rd qptrs (oqCount 0 1 N) 23)
    (h : coreProgram.Rel rd "opening_queries__L0_L1_L64_L32_L23_L7" [cap, flags, lam, lamN, qptrs, wp, nG] rets) :
    MeaningOpeningQueries 0 1 64 23 7 rd [cap, flags, lam, lamN, qptrs, wp, nG] rets :=
  oqMain1_sound (s := ⟨1, 64, 16, 7⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (hodd := (by decide : 0 ≤ 1))
    (Program.find?_of_indexOf? (j := 586) (by decide +kernel) rfl) rfl oqBody_586
    (Program.find?_of_indexOf? (j := 866) (by decide +kernel) rfl) rfl oqBody_866 hbits h

set_option maxRecDepth 100000 in
theorem oqBody_755 : Data.core755.body = oqMainT ⟨1, 64, 20, 6⟩ 0 "__loop414" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_892 : Data.core892.body = oqLoop1T ⟨1, 64, 20, 6⟩ 0 "__loop414" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L26_L6` is sound. -/
theorem oqSound_755 (rd : Reader) (cap flags lam lamN qptrs wp nG : E) (rets : List E)
    (hbits : ∀ N, nG = gen ^ N → N < ordG → QueryBitsBool rd qptrs (oqCount 0 1 N) 26)
    (h : coreProgram.Rel rd "opening_queries__L0_L1_L64_L32_L26_L6" [cap, flags, lam, lamN, qptrs, wp, nG] rets) :
    MeaningOpeningQueries 0 1 64 26 6 rd [cap, flags, lam, lamN, qptrs, wp, nG] rets :=
  oqMain1_sound (s := ⟨1, 64, 20, 6⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (hodd := (by decide : 0 ≤ 1))
    (Program.find?_of_indexOf? (j := 755) (by decide +kernel) rfl) rfl oqBody_755
    (Program.find?_of_indexOf? (j := 892) (by decide +kernel) rfl) rfl oqBody_892 hbits h

set_option maxRecDepth 100000 in
theorem oqBody_643 : Data.core643.body = oqMainT ⟨1, 64, 15, 7⟩ 1 "__loop400" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_876 : Data.core876.body = oqLoop1T ⟨1, 64, 15, 7⟩ 1 "__loop400" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L22_L7` is sound. -/
theorem oqSound_643 (rd : Reader) (cap flags lam lamN qptrs wp nG : E) (rets : List E)
    (hbits : ∀ N, nG = gen ^ N → N < ordG → QueryBitsBool rd qptrs (oqCount 1 1 N) 22)
    (h : coreProgram.Rel rd "opening_queries__L1_L1_L64_L32_L22_L7" [cap, flags, lam, lamN, qptrs, wp, nG] rets) :
    MeaningOpeningQueries 1 1 64 22 7 rd [cap, flags, lam, lamN, qptrs, wp, nG] rets :=
  oqMain1_sound (s := ⟨1, 64, 15, 7⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (hodd := (by decide : 1 ≤ 1))
    (Program.find?_of_indexOf? (j := 643) (by decide +kernel) rfl) rfl oqBody_643
    (Program.find?_of_indexOf? (j := 876) (by decide +kernel) rfl) rfl oqBody_876 hbits h

set_option maxRecDepth 100000 in
theorem oqBody_665 : Data.core665.body = oqMainT ⟨1, 64, 17, 7⟩ 1 "__loop402" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_878 : Data.core878.body = oqLoop1T ⟨1, 64, 17, 7⟩ 1 "__loop402" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L24_L7` is sound. -/
theorem oqSound_665 (rd : Reader) (cap flags lam lamN qptrs wp nG : E) (rets : List E)
    (hbits : ∀ N, nG = gen ^ N → N < ordG → QueryBitsBool rd qptrs (oqCount 1 1 N) 24)
    (h : coreProgram.Rel rd "opening_queries__L1_L1_L64_L32_L24_L7" [cap, flags, lam, lamN, qptrs, wp, nG] rets) :
    MeaningOpeningQueries 1 1 64 24 7 rd [cap, flags, lam, lamN, qptrs, wp, nG] rets :=
  oqMain1_sound (s := ⟨1, 64, 17, 7⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (hodd := (by decide : 1 ≤ 1))
    (Program.find?_of_indexOf? (j := 665) (by decide +kernel) rfl) rfl oqBody_665
    (Program.find?_of_indexOf? (j := 878) (by decide +kernel) rfl) rfl oqBody_878 hbits h

set_option maxRecDepth 100000 in
theorem oqBody_556 : Data.core556.body = oqMainT ⟨0, 16, 12, 4⟩ 0 "__loop387" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_862 : Data.core862.body = oqLoop0T ⟨0, 16, 12, 4⟩ "__loop387" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L16_L4` is sound. -/
theorem oqSound_556 (rd : Reader) (cap flags lam lamN qptrs wp nG : E) (rets : List E)
    (hbits : ∀ N, nG = gen ^ N → N < ordG → QueryBitsBool rd qptrs (oqCount 0 0 N) 16)
    (h : coreProgram.Rel rd "opening_queries__L0_L0_L16_L24_L16_L4" [cap, flags, lam, lamN, qptrs, wp, nG] rets) :
    MeaningOpeningQueries 0 0 16 16 4 rd [cap, flags, lam, lamN, qptrs, wp, nG] rets :=
  oqMain0_sound (s := ⟨0, 16, 12, 4⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) 
    (Program.find?_of_indexOf? (j := 556) (by decide +kernel) rfl) rfl oqBody_556
    (Program.find?_of_indexOf? (j := 862) (by decide +kernel) rfl) rfl oqBody_862 hbits h

set_option maxRecDepth 100000 in
theorem oqBody_455 : Data.core455.body = oqMainT ⟨0, 16, 12, 5⟩ 0 "__loop370" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_841 : Data.core841.body = oqLoop0T ⟨0, 16, 12, 5⟩ "__loop370" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L17_L5` is sound. -/
theorem oqSound_455 (rd : Reader) (cap flags lam lamN qptrs wp nG : E) (rets : List E)
    (hbits : ∀ N, nG = gen ^ N → N < ordG → QueryBitsBool rd qptrs (oqCount 0 0 N) 17)
    (h : coreProgram.Rel rd "opening_queries__L0_L0_L16_L24_L17_L5" [cap, flags, lam, lamN, qptrs, wp, nG] rets) :
    MeaningOpeningQueries 0 0 16 17 5 rd [cap, flags, lam, lamN, qptrs, wp, nG] rets :=
  oqMain0_sound (s := ⟨0, 16, 12, 5⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) 
    (Program.find?_of_indexOf? (j := 455) (by decide +kernel) rfl) rfl oqBody_455
    (Program.find?_of_indexOf? (j := 841) (by decide +kernel) rfl) rfl oqBody_841 hbits h

set_option maxRecDepth 100000 in
theorem oqBody_452 : Data.core452.body = oqMainT ⟨0, 16, 12, 6⟩ 0 "__loop369" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_840 : Data.core840.body = oqLoop0T ⟨0, 16, 12, 6⟩ "__loop369" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L18_L6` is sound. -/
theorem oqSound_452 (rd : Reader) (cap flags lam lamN qptrs wp nG : E) (rets : List E)
    (hbits : ∀ N, nG = gen ^ N → N < ordG → QueryBitsBool rd qptrs (oqCount 0 0 N) 18)
    (h : coreProgram.Rel rd "opening_queries__L0_L0_L16_L24_L18_L6" [cap, flags, lam, lamN, qptrs, wp, nG] rets) :
    MeaningOpeningQueries 0 0 16 18 6 rd [cap, flags, lam, lamN, qptrs, wp, nG] rets :=
  oqMain0_sound (s := ⟨0, 16, 12, 6⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) 
    (Program.find?_of_indexOf? (j := 452) (by decide +kernel) rfl) rfl oqBody_452
    (Program.find?_of_indexOf? (j := 840) (by decide +kernel) rfl) rfl oqBody_840 hbits h

set_option maxRecDepth 100000 in
theorem oqBody_605 : Data.core605.body = oqMainT ⟨0, 16, 16, 4⟩ 0 "__loop396" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_872 : Data.core872.body = oqLoop0T ⟨0, 16, 16, 4⟩ "__loop396" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L20_L4` is sound. -/
theorem oqSound_605 (rd : Reader) (cap flags lam lamN qptrs wp nG : E) (rets : List E)
    (hbits : ∀ N, nG = gen ^ N → N < ordG → QueryBitsBool rd qptrs (oqCount 0 0 N) 20)
    (h : coreProgram.Rel rd "opening_queries__L0_L0_L16_L24_L20_L4" [cap, flags, lam, lamN, qptrs, wp, nG] rets) :
    MeaningOpeningQueries 0 0 16 20 4 rd [cap, flags, lam, lamN, qptrs, wp, nG] rets :=
  oqMain0_sound (s := ⟨0, 16, 16, 4⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) 
    (Program.find?_of_indexOf? (j := 605) (by decide +kernel) rfl) rfl oqBody_605
    (Program.find?_of_indexOf? (j := 872) (by decide +kernel) rfl) rfl oqBody_872 hbits h

set_option maxRecDepth 100000 in
theorem oqBody_519 : Data.core519.body = oqMainT ⟨0, 16, 16, 5⟩ 0 "__loop382" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_857 : Data.core857.body = oqLoop0T ⟨0, 16, 16, 5⟩ "__loop382" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L21_L5` is sound. -/
theorem oqSound_519 (rd : Reader) (cap flags lam lamN qptrs wp nG : E) (rets : List E)
    (hbits : ∀ N, nG = gen ^ N → N < ordG → QueryBitsBool rd qptrs (oqCount 0 0 N) 21)
    (h : coreProgram.Rel rd "opening_queries__L0_L0_L16_L24_L21_L5" [cap, flags, lam, lamN, qptrs, wp, nG] rets) :
    MeaningOpeningQueries 0 0 16 21 5 rd [cap, flags, lam, lamN, qptrs, wp, nG] rets :=
  oqMain0_sound (s := ⟨0, 16, 16, 5⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) 
    (Program.find?_of_indexOf? (j := 519) (by decide +kernel) rfl) rfl oqBody_519
    (Program.find?_of_indexOf? (j := 857) (by decide +kernel) rfl) rfl oqBody_857 hbits h

set_option maxRecDepth 100000 in
theorem oqBody_517 : Data.core517.body = oqMainT ⟨0, 16, 16, 6⟩ 0 "__loop381" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_856 : Data.core856.body = oqLoop0T ⟨0, 16, 16, 6⟩ "__loop381" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L22_L6` is sound. -/
theorem oqSound_517 (rd : Reader) (cap flags lam lamN qptrs wp nG : E) (rets : List E)
    (hbits : ∀ N, nG = gen ^ N → N < ordG → QueryBitsBool rd qptrs (oqCount 0 0 N) 22)
    (h : coreProgram.Rel rd "opening_queries__L0_L0_L16_L24_L22_L6" [cap, flags, lam, lamN, qptrs, wp, nG] rets) :
    MeaningOpeningQueries 0 0 16 22 6 rd [cap, flags, lam, lamN, qptrs, wp, nG] rets :=
  oqMain0_sound (s := ⟨0, 16, 16, 6⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) 
    (Program.find?_of_indexOf? (j := 517) (by decide +kernel) rfl) rfl oqBody_517
    (Program.find?_of_indexOf? (j := 856) (by decide +kernel) rfl) rfl oqBody_856 hbits h

set_option maxRecDepth 100000 in
theorem oqBody_678 : Data.core678.body = oqMainT ⟨0, 16, 18, 6⟩ 0 "__loop404" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_881 : Data.core881.body = oqLoop0T ⟨0, 16, 18, 6⟩ "__loop404" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L24_L6` is sound. -/
theorem oqSound_678 (rd : Reader) (cap flags lam lamN qptrs wp nG : E) (rets : List E)
    (hbits : ∀ N, nG = gen ^ N → N < ordG → QueryBitsBool rd qptrs (oqCount 0 0 N) 24)
    (h : coreProgram.Rel rd "opening_queries__L0_L0_L16_L24_L24_L6" [cap, flags, lam, lamN, qptrs, wp, nG] rets) :
    MeaningOpeningQueries 0 0 16 24 6 rd [cap, flags, lam, lamN, qptrs, wp, nG] rets :=
  oqMain0_sound (s := ⟨0, 16, 18, 6⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) 
    (Program.find?_of_indexOf? (j := 678) (by decide +kernel) rfl) rfl oqBody_678
    (Program.find?_of_indexOf? (j := 881) (by decide +kernel) rfl) rfl oqBody_881 hbits h

end
end LeanVM.Guest.B1
