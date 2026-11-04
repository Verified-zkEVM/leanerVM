/-
  LeanVM.Guest.B1.Bits.QueryWindowsData

  The 45 specializations of `decode_query_windows` are their template, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Bits.QueryWindowsT
public import LeanVM.Guest.CoreData

/-!
# `decode_query_windows`' specializations

`queryWindowsShapes`: the deployed `(name, depth, cap depth)`; `queryWindows_data`: each is found
in the core IR with the parameters `0 .. 3` and the body `qwBody d cd` (`stmtsEqb_sound`, one
kernel evaluation each).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

set_option maxRecDepth 100000 in
theorem qw_L14_L5 : QwIs "decode_query_windows__L14_L5" (qwBody 14 5) :=
  ⟨Data.core852, Program.find?_of_indexOf? (j := 852) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L15_L5 : QwIs "decode_query_windows__L15_L5" (qwBody 15 5) :=
  ⟨Data.core850, Program.find?_of_indexOf? (j := 850) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L16_L4 : QwIs "decode_query_windows__L16_L4" (qwBody 16 4) :=
  ⟨Data.core898, Program.find?_of_indexOf? (j := 898) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L16_L5 : QwIs "decode_query_windows__L16_L5" (qwBody 16 5) :=
  ⟨Data.core858, Program.find?_of_indexOf? (j := 858) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L16_L6 : QwIs "decode_query_windows__L16_L6" (qwBody 16 6) :=
  ⟨Data.core848, Program.find?_of_indexOf? (j := 848) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L17_L4 : QwIs "decode_query_windows__L17_L4" (qwBody 17 4) :=
  ⟨Data.core902, Program.find?_of_indexOf? (j := 902) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L17_L5 : QwIs "decode_query_windows__L17_L5" (qwBody 17 5) :=
  ⟨Data.core864, Program.find?_of_indexOf? (j := 864) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L17_L6 : QwIs "decode_query_windows__L17_L6" (qwBody 17 6) :=
  ⟨Data.core856, Program.find?_of_indexOf? (j := 856) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L17_L8 : QwIs "decode_query_windows__L17_L8" (qwBody 17 8) :=
  ⟨Data.core846, Program.find?_of_indexOf? (j := 846) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L18_L4 : QwIs "decode_query_windows__L18_L4" (qwBody 18 4) :=
  ⟨Data.core890, Program.find?_of_indexOf? (j := 890) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L18_L5 : QwIs "decode_query_windows__L18_L5" (qwBody 18 5) :=
  ⟨Data.core870, Program.find?_of_indexOf? (j := 870) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L18_L6 : QwIs "decode_query_windows__L18_L6" (qwBody 18 6) :=
  ⟨Data.core862, Program.find?_of_indexOf? (j := 862) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L18_L7 : QwIs "decode_query_windows__L18_L7" (qwBody 18 7) :=
  ⟨Data.core892, Program.find?_of_indexOf? (j := 892) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L18_L8 : QwIs "decode_query_windows__L18_L8" (qwBody 18 8) :=
  ⟨Data.core854, Program.find?_of_indexOf? (j := 854) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L19_L4 : QwIs "decode_query_windows__L19_L4" (qwBody 19 4) :=
  ⟨Data.core908, Program.find?_of_indexOf? (j := 908) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L19_L5 : QwIs "decode_query_windows__L19_L5" (qwBody 19 5) :=
  ⟨Data.core876, Program.find?_of_indexOf? (j := 876) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L19_L6 : QwIs "decode_query_windows__L19_L6" (qwBody 19 6) :=
  ⟨Data.core868, Program.find?_of_indexOf? (j := 868) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L19_L7 : QwIs "decode_query_windows__L19_L7" (qwBody 19 7) :=
  ⟨Data.core894, Program.find?_of_indexOf? (j := 894) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L19_L8 : QwIs "decode_query_windows__L19_L8" (qwBody 19 8) :=
  ⟨Data.core860, Program.find?_of_indexOf? (j := 860) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L20_L4 : QwIs "decode_query_windows__L20_L4" (qwBody 20 4) :=
  ⟨Data.core916, Program.find?_of_indexOf? (j := 916) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L20_L5 : QwIs "decode_query_windows__L20_L5" (qwBody 20 5) :=
  ⟨Data.core882, Program.find?_of_indexOf? (j := 882) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L20_L6 : QwIs "decode_query_windows__L20_L6" (qwBody 20 6) :=
  ⟨Data.core874, Program.find?_of_indexOf? (j := 874) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L20_L7 : QwIs "decode_query_windows__L20_L7" (qwBody 20 7) :=
  ⟨Data.core896, Program.find?_of_indexOf? (j := 896) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L20_L8 : QwIs "decode_query_windows__L20_L8" (qwBody 20 8) :=
  ⟨Data.core866, Program.find?_of_indexOf? (j := 866) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L21_L4 : QwIs "decode_query_windows__L21_L4" (qwBody 21 4) :=
  ⟨Data.core930, Program.find?_of_indexOf? (j := 930) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L21_L5 : QwIs "decode_query_windows__L21_L5" (qwBody 21 5) :=
  ⟨Data.core888, Program.find?_of_indexOf? (j := 888) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L21_L6 : QwIs "decode_query_windows__L21_L6" (qwBody 21 6) :=
  ⟨Data.core880, Program.find?_of_indexOf? (j := 880) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L21_L7 : QwIs "decode_query_windows__L21_L7" (qwBody 21 7) :=
  ⟨Data.core900, Program.find?_of_indexOf? (j := 900) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L21_L8 : QwIs "decode_query_windows__L21_L8" (qwBody 21 8) :=
  ⟨Data.core872, Program.find?_of_indexOf? (j := 872) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L22_L4 : QwIs "decode_query_windows__L22_L4" (qwBody 22 4) :=
  ⟨Data.core945, Program.find?_of_indexOf? (j := 945) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L22_L5 : QwIs "decode_query_windows__L22_L5" (qwBody 22 5) :=
  ⟨Data.core914, Program.find?_of_indexOf? (j := 914) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L22_L6 : QwIs "decode_query_windows__L22_L6" (qwBody 22 6) :=
  ⟨Data.core886, Program.find?_of_indexOf? (j := 886) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L22_L7 : QwIs "decode_query_windows__L22_L7" (qwBody 22 7) :=
  ⟨Data.core904, Program.find?_of_indexOf? (j := 904) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L22_L8 : QwIs "decode_query_windows__L22_L8" (qwBody 22 8) :=
  ⟨Data.core878, Program.find?_of_indexOf? (j := 878) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L23_L5 : QwIs "decode_query_windows__L23_L5" (qwBody 23 5) :=
  ⟨Data.core928, Program.find?_of_indexOf? (j := 928) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L23_L6 : QwIs "decode_query_windows__L23_L6" (qwBody 23 6) :=
  ⟨Data.core912, Program.find?_of_indexOf? (j := 912) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L23_L7 : QwIs "decode_query_windows__L23_L7" (qwBody 23 7) :=
  ⟨Data.core906, Program.find?_of_indexOf? (j := 906) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L23_L8 : QwIs "decode_query_windows__L23_L8" (qwBody 23 8) :=
  ⟨Data.core884, Program.find?_of_indexOf? (j := 884) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L24_L5 : QwIs "decode_query_windows__L24_L5" (qwBody 24 5) :=
  ⟨Data.core939, Program.find?_of_indexOf? (j := 939) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L24_L6 : QwIs "decode_query_windows__L24_L6" (qwBody 24 6) :=
  ⟨Data.core926, Program.find?_of_indexOf? (j := 926) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L24_L7 : QwIs "decode_query_windows__L24_L7" (qwBody 24 7) :=
  ⟨Data.core910, Program.find?_of_indexOf? (j := 910) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L25_L5 : QwIs "decode_query_windows__L25_L5" (qwBody 25 5) :=
  ⟨Data.core943, Program.find?_of_indexOf? (j := 943) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L25_L6 : QwIs "decode_query_windows__L25_L6" (qwBody 25 6) :=
  ⟨Data.core937, Program.find?_of_indexOf? (j := 937) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L25_L7 : QwIs "decode_query_windows__L25_L7" (qwBody 25 7) :=
  ⟨Data.core924, Program.find?_of_indexOf? (j := 924) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem qw_L26_L6 : QwIs "decode_query_windows__L26_L6" (qwBody 26 6) :=
  ⟨Data.core941, Program.find?_of_indexOf? (j := 941) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

/-- **Every deployed specialization is its template.** -/
theorem queryWindows_data : ∀ p ∈ queryWindowsShapes, QwIs p.1 (qwBody p.2.1 p.2.2) := by
  intro p hp
  simp only [queryWindowsShapes, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [qw_L14_L5, qw_L15_L5, qw_L16_L4, qw_L16_L5, qw_L16_L6, qw_L17_L4, qw_L17_L5, qw_L17_L6, qw_L17_L8, qw_L18_L4, qw_L18_L5, qw_L18_L6, qw_L18_L7, qw_L18_L8, qw_L19_L4, qw_L19_L5, qw_L19_L6, qw_L19_L7, qw_L19_L8, qw_L20_L4, qw_L20_L5, qw_L20_L6, qw_L20_L7, qw_L20_L8, qw_L21_L4, qw_L21_L5, qw_L21_L6, qw_L21_L7, qw_L21_L8, qw_L22_L4, qw_L22_L5, qw_L22_L6, qw_L22_L7, qw_L22_L8, qw_L23_L5, qw_L23_L6, qw_L23_L7, qw_L23_L8, qw_L24_L5, qw_L24_L6, qw_L24_L7, qw_L25_L5, qw_L25_L6, qw_L25_L7, qw_L26_L6]

end
end LeanVM.Guest.B1
