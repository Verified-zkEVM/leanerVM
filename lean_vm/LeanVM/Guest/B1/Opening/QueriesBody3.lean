/-
  LeanVM.Guest.B1.Opening.QueriesBody3

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
theorem oqBody_542 : Data.core542.body = oqMainT ⟨1, 64, 12, 7⟩ 0 "__loop385" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_860 : Data.core860.body = oqLoop1T ⟨1, 64, 12, 7⟩ 0 "__loop385" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L19_L7` is sound. -/
theorem oqSound_542 (rd : Reader) (cap flags lam lamN qptrs wp nG : E) (rets : List E)
    (hbits : ∀ N, nG = gen ^ N → N < ordG → QueryBitsBool rd qptrs (oqCount 0 1 N) 19)
    (h : coreProgram.Rel rd "opening_queries__L0_L1_L64_L32_L19_L7" [cap, flags, lam, lamN, qptrs, wp, nG] rets) :
    MeaningOpeningQueries 0 1 64 19 7 rd [cap, flags, lam, lamN, qptrs, wp, nG] rets :=
  oqMain1_sound (s := ⟨1, 64, 12, 7⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (hodd := (by decide : 0 ≤ 1))
    (Program.find?_of_indexOf? (j := 542) (by decide +kernel) rfl) rfl oqBody_542
    (Program.find?_of_indexOf? (j := 860) (by decide +kernel) rfl) rfl oqBody_860 hbits h

set_option maxRecDepth 100000 in
theorem oqBody_468 : Data.core468.body = oqMainT ⟨1, 64, 12, 8⟩ 0 "__loop371" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_843 : Data.core843.body = oqLoop1T ⟨1, 64, 12, 8⟩ 0 "__loop371" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L20_L8` is sound. -/
theorem oqSound_468 (rd : Reader) (cap flags lam lamN qptrs wp nG : E) (rets : List E)
    (hbits : ∀ N, nG = gen ^ N → N < ordG → QueryBitsBool rd qptrs (oqCount 0 1 N) 20)
    (h : coreProgram.Rel rd "opening_queries__L0_L1_L64_L32_L20_L8" [cap, flags, lam, lamN, qptrs, wp, nG] rets) :
    MeaningOpeningQueries 0 1 64 20 8 rd [cap, flags, lam, lamN, qptrs, wp, nG] rets :=
  oqMain1_sound (s := ⟨1, 64, 12, 8⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (hodd := (by decide : 0 ≤ 1))
    (Program.find?_of_indexOf? (j := 468) (by decide +kernel) rfl) rfl oqBody_468
    (Program.find?_of_indexOf? (j := 843) (by decide +kernel) rfl) rfl oqBody_843 hbits h

set_option maxRecDepth 100000 in
theorem oqBody_710 : Data.core710.body = oqMainT ⟨1, 64, 16, 6⟩ 0 "__loop409" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_886 : Data.core886.body = oqLoop1T ⟨1, 64, 16, 6⟩ 0 "__loop409" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L22_L6` is sound. -/
theorem oqSound_710 (rd : Reader) (cap flags lam lamN qptrs wp nG : E) (rets : List E)
    (hbits : ∀ N, nG = gen ^ N → N < ordG → QueryBitsBool rd qptrs (oqCount 0 1 N) 22)
    (h : coreProgram.Rel rd "opening_queries__L0_L1_L64_L32_L22_L6" [cap, flags, lam, lamN, qptrs, wp, nG] rets) :
    MeaningOpeningQueries 0 1 64 22 6 rd [cap, flags, lam, lamN, qptrs, wp, nG] rets :=
  oqMain1_sound (s := ⟨1, 64, 16, 6⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (hodd := (by decide : 0 ≤ 1))
    (Program.find?_of_indexOf? (j := 710) (by decide +kernel) rfl) rfl oqBody_710
    (Program.find?_of_indexOf? (j := 886) (by decide +kernel) rfl) rfl oqBody_886 hbits h

set_option maxRecDepth 100000 in
theorem oqBody_732 : Data.core732.body = oqMainT ⟨1, 64, 18, 6⟩ 0 "__loop411" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_888 : Data.core888.body = oqLoop1T ⟨1, 64, 18, 6⟩ 0 "__loop411" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L24_L6` is sound. -/
theorem oqSound_732 (rd : Reader) (cap flags lam lamN qptrs wp nG : E) (rets : List E)
    (hbits : ∀ N, nG = gen ^ N → N < ordG → QueryBitsBool rd qptrs (oqCount 0 1 N) 24)
    (h : coreProgram.Rel rd "opening_queries__L0_L1_L64_L32_L24_L6" [cap, flags, lam, lamN, qptrs, wp, nG] rets) :
    MeaningOpeningQueries 0 1 64 24 6 rd [cap, flags, lam, lamN, qptrs, wp, nG] rets :=
  oqMain1_sound (s := ⟨1, 64, 18, 6⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (hodd := (by decide : 0 ≤ 1))
    (Program.find?_of_indexOf? (j := 732) (by decide +kernel) rfl) rfl oqBody_732
    (Program.find?_of_indexOf? (j := 888) (by decide +kernel) rfl) rfl oqBody_888 hbits h

set_option maxRecDepth 100000 in
theorem oqBody_614 : Data.core614.body = oqMainT ⟨1, 64, 12, 7⟩ 1 "__loop397" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_873 : Data.core873.body = oqLoop1T ⟨1, 64, 12, 7⟩ 1 "__loop397" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L19_L7` is sound. -/
theorem oqSound_614 (rd : Reader) (cap flags lam lamN qptrs wp nG : E) (rets : List E)
    (hbits : ∀ N, nG = gen ^ N → N < ordG → QueryBitsBool rd qptrs (oqCount 1 1 N) 19)
    (h : coreProgram.Rel rd "opening_queries__L1_L1_L64_L32_L19_L7" [cap, flags, lam, lamN, qptrs, wp, nG] rets) :
    MeaningOpeningQueries 1 1 64 19 7 rd [cap, flags, lam, lamN, qptrs, wp, nG] rets :=
  oqMain1_sound (s := ⟨1, 64, 12, 7⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (hodd := (by decide : 1 ≤ 1))
    (Program.find?_of_indexOf? (j := 614) (by decide +kernel) rfl) rfl oqBody_614
    (Program.find?_of_indexOf? (j := 873) (by decide +kernel) rfl) rfl oqBody_873 hbits h

set_option maxRecDepth 100000 in
theorem oqBody_501 : Data.core501.body = oqMainT ⟨1, 64, 14, 8⟩ 1 "__loop377" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_851 : Data.core851.body = oqLoop1T ⟨1, 64, 14, 8⟩ 1 "__loop377" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L22_L8` is sound. -/
theorem oqSound_501 (rd : Reader) (cap flags lam lamN qptrs wp nG : E) (rets : List E)
    (hbits : ∀ N, nG = gen ^ N → N < ordG → QueryBitsBool rd qptrs (oqCount 1 1 N) 22)
    (h : coreProgram.Rel rd "opening_queries__L1_L1_L64_L32_L22_L8" [cap, flags, lam, lamN, qptrs, wp, nG] rets) :
    MeaningOpeningQueries 1 1 64 22 8 rd [cap, flags, lam, lamN, qptrs, wp, nG] rets :=
  oqMain1_sound (s := ⟨1, 64, 14, 8⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (hodd := (by decide : 1 ≤ 1))
    (Program.find?_of_indexOf? (j := 501) (by decide +kernel) rfl) rfl oqBody_501
    (Program.find?_of_indexOf? (j := 851) (by decide +kernel) rfl) rfl oqBody_851 hbits h

set_option maxRecDepth 100000 in
theorem oqBody_676 : Data.core676.body = oqMainT ⟨1, 64, 18, 7⟩ 1 "__loop403" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_880 : Data.core880.body = oqLoop1T ⟨1, 64, 18, 7⟩ 1 "__loop403" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L25_L7` is sound. -/
theorem oqSound_676 (rd : Reader) (cap flags lam lamN qptrs wp nG : E) (rets : List E)
    (hbits : ∀ N, nG = gen ^ N → N < ordG → QueryBitsBool rd qptrs (oqCount 1 1 N) 25)
    (h : coreProgram.Rel rd "opening_queries__L1_L1_L64_L32_L25_L7" [cap, flags, lam, lamN, qptrs, wp, nG] rets) :
    MeaningOpeningQueries 1 1 64 25 7 rd [cap, flags, lam, lamN, qptrs, wp, nG] rets :=
  oqMain1_sound (s := ⟨1, 64, 18, 7⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (hodd := (by decide : 1 ≤ 1))
    (Program.find?_of_indexOf? (j := 676) (by decide +kernel) rfl) rfl oqBody_676
    (Program.find?_of_indexOf? (j := 880) (by decide +kernel) rfl) rfl oqBody_880 hbits h

set_option maxRecDepth 100000 in
theorem oqBody_439 : Data.core439.body = oqMainT ⟨0, 16, 11, 5⟩ 0 "__loop367" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_837 : Data.core837.body = oqLoop0T ⟨0, 16, 11, 5⟩ "__loop367" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L16_L5` is sound. -/
theorem oqSound_439 (rd : Reader) (cap flags lam lamN qptrs wp nG : E) (rets : List E)
    (hbits : ∀ N, nG = gen ^ N → N < ordG → QueryBitsBool rd qptrs (oqCount 0 0 N) 16)
    (h : coreProgram.Rel rd "opening_queries__L0_L0_L16_L24_L16_L5" [cap, flags, lam, lamN, qptrs, wp, nG] rets) :
    MeaningOpeningQueries 0 0 16 16 5 rd [cap, flags, lam, lamN, qptrs, wp, nG] rets :=
  oqMain0_sound (s := ⟨0, 16, 11, 5⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) 
    (Program.find?_of_indexOf? (j := 439) (by decide +kernel) rfl) rfl oqBody_439
    (Program.find?_of_indexOf? (j := 837) (by decide +kernel) rfl) rfl oqBody_837 hbits h

set_option maxRecDepth 100000 in
theorem oqBody_436 : Data.core436.body = oqMainT ⟨0, 16, 11, 6⟩ 0 "__loop366" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_836 : Data.core836.body = oqLoop0T ⟨0, 16, 11, 6⟩ "__loop366" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L17_L6` is sound. -/
theorem oqSound_436 (rd : Reader) (cap flags lam lamN qptrs wp nG : E) (rets : List E)
    (hbits : ∀ N, nG = gen ^ N → N < ordG → QueryBitsBool rd qptrs (oqCount 0 0 N) 17)
    (h : coreProgram.Rel rd "opening_queries__L0_L0_L16_L24_L17_L6" [cap, flags, lam, lamN, qptrs, wp, nG] rets) :
    MeaningOpeningQueries 0 0 16 17 6 rd [cap, flags, lam, lamN, qptrs, wp, nG] rets :=
  oqMain0_sound (s := ⟨0, 16, 11, 6⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) 
    (Program.find?_of_indexOf? (j := 436) (by decide +kernel) rfl) rfl oqBody_436
    (Program.find?_of_indexOf? (j := 836) (by decide +kernel) rfl) rfl oqBody_836 hbits h

set_option maxRecDepth 100000 in
theorem oqBody_591 : Data.core591.body = oqMainT ⟨0, 16, 15, 4⟩ 0 "__loop392" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_867 : Data.core867.body = oqLoop0T ⟨0, 16, 15, 4⟩ "__loop392" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L19_L4` is sound. -/
theorem oqSound_591 (rd : Reader) (cap flags lam lamN qptrs wp nG : E) (rets : List E)
    (hbits : ∀ N, nG = gen ^ N → N < ordG → QueryBitsBool rd qptrs (oqCount 0 0 N) 19)
    (h : coreProgram.Rel rd "opening_queries__L0_L0_L16_L24_L19_L4" [cap, flags, lam, lamN, qptrs, wp, nG] rets) :
    MeaningOpeningQueries 0 0 16 19 4 rd [cap, flags, lam, lamN, qptrs, wp, nG] rets :=
  oqMain0_sound (s := ⟨0, 16, 15, 4⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) 
    (Program.find?_of_indexOf? (j := 591) (by decide +kernel) rfl) rfl oqBody_591
    (Program.find?_of_indexOf? (j := 867) (by decide +kernel) rfl) rfl oqBody_867 hbits h

set_option maxRecDepth 100000 in
theorem oqBody_505 : Data.core505.body = oqMainT ⟨0, 16, 15, 5⟩ 0 "__loop379" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_853 : Data.core853.body = oqLoop0T ⟨0, 16, 15, 5⟩ "__loop379" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L20_L5` is sound. -/
theorem oqSound_505 (rd : Reader) (cap flags lam lamN qptrs wp nG : E) (rets : List E)
    (hbits : ∀ N, nG = gen ^ N → N < ordG → QueryBitsBool rd qptrs (oqCount 0 0 N) 20)
    (h : coreProgram.Rel rd "opening_queries__L0_L0_L16_L24_L20_L5" [cap, flags, lam, lamN, qptrs, wp, nG] rets) :
    MeaningOpeningQueries 0 0 16 20 5 rd [cap, flags, lam, lamN, qptrs, wp, nG] rets :=
  oqMain0_sound (s := ⟨0, 16, 15, 5⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) 
    (Program.find?_of_indexOf? (j := 505) (by decide +kernel) rfl) rfl oqBody_505
    (Program.find?_of_indexOf? (j := 853) (by decide +kernel) rfl) rfl oqBody_853 hbits h

set_option maxRecDepth 100000 in
theorem oqBody_503 : Data.core503.body = oqMainT ⟨0, 16, 15, 6⟩ 0 "__loop378" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_852 : Data.core852.body = oqLoop0T ⟨0, 16, 15, 6⟩ "__loop378" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L21_L6` is sound. -/
theorem oqSound_503 (rd : Reader) (cap flags lam lamN qptrs wp nG : E) (rets : List E)
    (hbits : ∀ N, nG = gen ^ N → N < ordG → QueryBitsBool rd qptrs (oqCount 0 0 N) 21)
    (h : coreProgram.Rel rd "opening_queries__L0_L0_L16_L24_L21_L6" [cap, flags, lam, lamN, qptrs, wp, nG] rets) :
    MeaningOpeningQueries 0 0 16 21 6 rd [cap, flags, lam, lamN, qptrs, wp, nG] rets :=
  oqMain0_sound (s := ⟨0, 16, 15, 6⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) 
    (Program.find?_of_indexOf? (j := 503) (by decide +kernel) rfl) rfl oqBody_503
    (Program.find?_of_indexOf? (j := 852) (by decide +kernel) rfl) rfl oqBody_852 hbits h

set_option maxRecDepth 100000 in
theorem oqBody_680 : Data.core680.body = oqMainT ⟨0, 16, 18, 5⟩ 0 "__loop405" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_882 : Data.core882.body = oqLoop0T ⟨0, 16, 18, 5⟩ "__loop405" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L23_L5` is sound. -/
theorem oqSound_680 (rd : Reader) (cap flags lam lamN qptrs wp nG : E) (rets : List E)
    (hbits : ∀ N, nG = gen ^ N → N < ordG → QueryBitsBool rd qptrs (oqCount 0 0 N) 23)
    (h : coreProgram.Rel rd "opening_queries__L0_L0_L16_L24_L23_L5" [cap, flags, lam, lamN, qptrs, wp, nG] rets) :
    MeaningOpeningQueries 0 0 16 23 5 rd [cap, flags, lam, lamN, qptrs, wp, nG] rets :=
  oqMain0_sound (s := ⟨0, 16, 18, 5⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) 
    (Program.find?_of_indexOf? (j := 680) (by decide +kernel) rfl) rfl oqBody_680
    (Program.find?_of_indexOf? (j := 882) (by decide +kernel) rfl) rfl oqBody_882 hbits h

set_option maxRecDepth 100000 in
theorem oqBody_757 : Data.core757.body = oqMainT ⟨0, 16, 20, 5⟩ 0 "__loop415" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem oqBody_893 : Data.core893.body = oqLoop0T ⟨0, 16, 20, 5⟩ "__loop415" :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L25_L5` is sound. -/
theorem oqSound_757 (rd : Reader) (cap flags lam lamN qptrs wp nG : E) (rets : List E)
    (hbits : ∀ N, nG = gen ^ N → N < ordG → QueryBitsBool rd qptrs (oqCount 0 0 N) 25)
    (h : coreProgram.Rel rd "opening_queries__L0_L0_L16_L24_L25_L5" [cap, flags, lam, lamN, qptrs, wp, nG] rets) :
    MeaningOpeningQueries 0 0 16 25 5 rd [cap, flags, lam, lamN, qptrs, wp, nG] rets :=
  oqMain0_sound (s := ⟨0, 16, 20, 5⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) 
    (Program.find?_of_indexOf? (j := 757) (by decide +kernel) rfl) rfl oqBody_757
    (Program.find?_of_indexOf? (j := 893) (by decide +kernel) rfl) rfl oqBody_893 hbits h

end
end LeanVM.Guest.B1
