/-
  LeanVM.Guest.B1.Comp.Whir.LocT.QueriesAtSpecT1

  `opening_queries` placed at its compiled shapes over a completeness model, by trees decoding to the openings (`Loc/QueriesAtSpec1.lean`)
-/

module

public import LeanVM.Guest.B1.Whir.QueriesAtSpec1
public import LeanVM.Guest.B1.Comp.Whir.LocT.OqQueriesT

/-!
# `opening_queries` placed at its compiled shapes over a completeness model, by trees decoding to the openings (`Loc/QueriesAtSpec1.lean`)
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Protocol.Verifier
open LeanVM.E2E.Complete
open LeanVM.Guest.Located (oqLookup)
open LeanVM.Protocol.Compile (Bytes)
open LeanVM.Protocol (Digest)

@[expose] public section

variable {Ht : Bytes → Digest} {CM : CompModel}

set_option maxRecDepth 100000 in
theorem oq_completeAtBT_L0_L16_L6_L15_L5C (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ)
    (hfit : cert "__loop434" (.n (oqP 0 16 6)) + 4 * 10 ≤ fs "__loop434") :
    OqCompleteAtBCT CM Ht fs cert k 0 16 15 5 "opening_queries__L0_L16_L6_L15_L5" fun n => fs "opening_queries__L0_L16_L6_L15_L5" + (n + 1) + (n + 1) * fs "__loop434" := by
  have hlk : oqLookup "opening_queries__L0_L16_L6_L15_L5" = some ("__loop434", 0, 16, 6, 10, 5) := by decide +kernel
  refine ⟨"__loop434", 6, hlk, ?_⟩
  intro n hn Lin cap flags qw qbp rew leaf pos sibs wts qwV dbpV hleaf hq hsl hans hlin hreg
  have hf := Program.find?_of_indexOf? (P := coreProgram) (n := "opening_queries__L0_L16_L6_L15_L5") (f := Data.core587) (j := 587) (by decide +kernel) rfl
  have hlf := Program.find?_of_indexOf? (P := coreProgram) (n := "__loop434") (f := Data.core979) (j := 979) (by decide +kernel) rfl
  exact opening_queries_completeAtCT (Ht := Ht) (CM := CM) fs cert k (base := 0) (I := 16) (blocks := 6) (pd := 10) (cd := 5)
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    hf rfl (stmtsEqb_sound (by decide +kernel)) (by rw [Program.loop_of_find? hf]; decide +kernel)
    hlf rfl (stmtsEqb_sound (by decide +kernel))
    ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
    (by rw [Program.loop_of_find? hlf]; decide +kernel)
    (cellsOk_of (j := 588) (by decide +kernel) (by decide +kernel))
    (cellsOk_of (j := 980) (by decide +kernel) (by decide +kernel)) (mem_osDecNames_loop hlk) hfit hn hleaf hq hsl hans hlin hreg

set_option maxRecDepth 100000 in
theorem oq_completeAtBT_L0_L16_L6_L16_L5C (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ)
    (hfit : cert "__loop438" (.n (oqP 0 16 6)) + 4 * 11 ≤ fs "__loop438") :
    OqCompleteAtBCT CM Ht fs cert k 0 16 16 5 "opening_queries__L0_L16_L6_L16_L5" fun n => fs "opening_queries__L0_L16_L6_L16_L5" + (n + 1) + (n + 1) * fs "__loop438" := by
  have hlk : oqLookup "opening_queries__L0_L16_L6_L16_L5" = some ("__loop438", 0, 16, 6, 11, 5) := by decide +kernel
  refine ⟨"__loop438", 6, hlk, ?_⟩
  intro n hn Lin cap flags qw qbp rew leaf pos sibs wts qwV dbpV hleaf hq hsl hans hlin hreg
  have hf := Program.find?_of_indexOf? (P := coreProgram) (n := "opening_queries__L0_L16_L6_L16_L5") (f := Data.core601) (j := 601) (by decide +kernel) rfl
  have hlf := Program.find?_of_indexOf? (P := coreProgram) (n := "__loop438") (f := Data.core985) (j := 985) (by decide +kernel) rfl
  exact opening_queries_completeAtCT (Ht := Ht) (CM := CM) fs cert k (base := 0) (I := 16) (blocks := 6) (pd := 11) (cd := 5)
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    hf rfl (stmtsEqb_sound (by decide +kernel)) (by rw [Program.loop_of_find? hf]; decide +kernel)
    hlf rfl (stmtsEqb_sound (by decide +kernel))
    ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
    (by rw [Program.loop_of_find? hlf]; decide +kernel)
    (cellsOk_of (j := 602) (by decide +kernel) (by decide +kernel))
    (cellsOk_of (j := 986) (by decide +kernel) (by decide +kernel)) (mem_osDecNames_loop hlk) hfit hn hleaf hq hsl hans hlin hreg

set_option maxRecDepth 100000 in
theorem oq_completeAtBT_L0_L16_L6_L17_L4C (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ)
    (hfit : cert "__loop462" (.n (oqP 0 16 6)) + 4 * 13 ≤ fs "__loop462") :
    OqCompleteAtBCT CM Ht fs cert k 0 16 17 4 "opening_queries__L0_L16_L6_L17_L4" fun n => fs "opening_queries__L0_L16_L6_L17_L4" + (n + 1) + (n + 1) * fs "__loop462" := by
  have hlk : oqLookup "opening_queries__L0_L16_L6_L17_L4" = some ("__loop462", 0, 16, 6, 13, 4) := by decide +kernel
  refine ⟨"__loop462", 6, hlk, ?_⟩
  intro n hn Lin cap flags qw qbp rew leaf pos sibs wts qwV dbpV hleaf hq hsl hans hlin hreg
  have hf := Program.find?_of_indexOf? (P := coreProgram) (n := "opening_queries__L0_L16_L6_L17_L4") (f := Data.core719) (j := 719) (by decide +kernel) rfl
  have hlf := Program.find?_of_indexOf? (P := coreProgram) (n := "__loop462") (f := Data.core1014) (j := 1014) (by decide +kernel) rfl
  exact opening_queries_completeAtCT (Ht := Ht) (CM := CM) fs cert k (base := 0) (I := 16) (blocks := 6) (pd := 13) (cd := 4)
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    hf rfl (stmtsEqb_sound (by decide +kernel)) (by rw [Program.loop_of_find? hf]; decide +kernel)
    hlf rfl (stmtsEqb_sound (by decide +kernel))
    ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
    (by rw [Program.loop_of_find? hlf]; decide +kernel)
    (cellsOk_of (j := 720) (by decide +kernel) (by decide +kernel))
    (cellsOk_of (j := 1015) (by decide +kernel) (by decide +kernel)) (mem_osDecNames_loop hlk) hfit hn hleaf hq hsl hans hlin hreg

set_option maxRecDepth 100000 in
theorem oq_completeAtBT_L0_L16_L6_L17_L6C (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ)
    (hfit : cert "__loop437" (.n (oqP 0 16 6)) + 4 * 11 ≤ fs "__loop437") :
    OqCompleteAtBCT CM Ht fs cert k 0 16 17 6 "opening_queries__L0_L16_L6_L17_L6" fun n => fs "opening_queries__L0_L16_L6_L17_L6" + (n + 1) + (n + 1) * fs "__loop437" := by
  have hlk : oqLookup "opening_queries__L0_L16_L6_L17_L6" = some ("__loop437", 0, 16, 6, 11, 6) := by decide +kernel
  refine ⟨"__loop437", 6, hlk, ?_⟩
  intro n hn Lin cap flags qw qbp rew leaf pos sibs wts qwV dbpV hleaf hq hsl hans hlin hreg
  have hf := Program.find?_of_indexOf? (P := coreProgram) (n := "opening_queries__L0_L16_L6_L17_L6") (f := Data.core599) (j := 599) (by decide +kernel) rfl
  have hlf := Program.find?_of_indexOf? (P := coreProgram) (n := "__loop437") (f := Data.core984) (j := 984) (by decide +kernel) rfl
  exact opening_queries_completeAtCT (Ht := Ht) (CM := CM) fs cert k (base := 0) (I := 16) (blocks := 6) (pd := 11) (cd := 6)
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    hf rfl (stmtsEqb_sound (by decide +kernel)) (by rw [Program.loop_of_find? hf]; decide +kernel)
    hlf rfl (stmtsEqb_sound (by decide +kernel))
    ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
    (by rw [Program.loop_of_find? hlf]; decide +kernel)
    (cellsOk_of (j := 600) (by decide +kernel) (by decide +kernel))
    (cellsOk_of (j := 985) (by decide +kernel) (by decide +kernel)) (mem_osDecNames_loop hlk) hfit hn hleaf hq hsl hans hlin hreg

set_option maxRecDepth 100000 in
theorem oq_completeAtBT_L0_L16_L6_L18_L5C (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ)
    (hfit : cert "__loop444" (.n (oqP 0 16 6)) + 4 * 13 ≤ fs "__loop444") :
    OqCompleteAtBCT CM Ht fs cert k 0 16 18 5 "opening_queries__L0_L16_L6_L18_L5" fun n => fs "opening_queries__L0_L16_L6_L18_L5" + (n + 1) + (n + 1) * fs "__loop444" := by
  have hlk : oqLookup "opening_queries__L0_L16_L6_L18_L5" = some ("__loop444", 0, 16, 6, 13, 5) := by decide +kernel
  refine ⟨"__loop444", 6, hlk, ?_⟩
  intro n hn Lin cap flags qw qbp rew leaf pos sibs wts qwV dbpV hleaf hq hsl hans hlin hreg
  have hf := Program.find?_of_indexOf? (P := coreProgram) (n := "opening_queries__L0_L16_L6_L18_L5") (f := Data.core629) (j := 629) (by decide +kernel) rfl
  have hlf := Program.find?_of_indexOf? (P := coreProgram) (n := "__loop444") (f := Data.core993) (j := 993) (by decide +kernel) rfl
  exact opening_queries_completeAtCT (Ht := Ht) (CM := CM) fs cert k (base := 0) (I := 16) (blocks := 6) (pd := 13) (cd := 5)
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    hf rfl (stmtsEqb_sound (by decide +kernel)) (by rw [Program.loop_of_find? hf]; decide +kernel)
    hlf rfl (stmtsEqb_sound (by decide +kernel))
    ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
    (by rw [Program.loop_of_find? hlf]; decide +kernel)
    (cellsOk_of (j := 630) (by decide +kernel) (by decide +kernel))
    (cellsOk_of (j := 994) (by decide +kernel) (by decide +kernel)) (mem_osDecNames_loop hlk) hfit hn hleaf hq hsl hans hlin hreg

set_option maxRecDepth 100000 in
theorem oq_completeAtBT_L0_L16_L6_L19_L4C (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ)
    (hfit : cert "__loop465" (.n (oqP 0 16 6)) + 4 * 15 ≤ fs "__loop465") :
    OqCompleteAtBCT CM Ht fs cert k 0 16 19 4 "opening_queries__L0_L16_L6_L19_L4" fun n => fs "opening_queries__L0_L16_L6_L19_L4" + (n + 1) + (n + 1) * fs "__loop465" := by
  have hlk : oqLookup "opening_queries__L0_L16_L6_L19_L4" = some ("__loop465", 0, 16, 6, 15, 4) := by decide +kernel
  refine ⟨"__loop465", 6, hlk, ?_⟩
  intro n hn Lin cap flags qw qbp rew leaf pos sibs wts qwV dbpV hleaf hq hsl hans hlin hreg
  have hf := Program.find?_of_indexOf? (P := coreProgram) (n := "opening_queries__L0_L16_L6_L19_L4") (f := Data.core742) (j := 742) (by decide +kernel) rfl
  have hlf := Program.find?_of_indexOf? (P := coreProgram) (n := "__loop465") (f := Data.core1017) (j := 1017) (by decide +kernel) rfl
  exact opening_queries_completeAtCT (Ht := Ht) (CM := CM) fs cert k (base := 0) (I := 16) (blocks := 6) (pd := 15) (cd := 4)
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    hf rfl (stmtsEqb_sound (by decide +kernel)) (by rw [Program.loop_of_find? hf]; decide +kernel)
    hlf rfl (stmtsEqb_sound (by decide +kernel))
    ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
    (by rw [Program.loop_of_find? hlf]; decide +kernel)
    (cellsOk_of (j := 743) (by decide +kernel) (by decide +kernel))
    (cellsOk_of (j := 1018) (by decide +kernel) (by decide +kernel)) (mem_osDecNames_loop hlk) hfit hn hleaf hq hsl hans hlin hreg

set_option maxRecDepth 100000 in
theorem oq_completeAtBT_L0_L16_L6_L19_L6C (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ)
    (hfit : cert "__loop443" (.n (oqP 0 16 6)) + 4 * 13 ≤ fs "__loop443") :
    OqCompleteAtBCT CM Ht fs cert k 0 16 19 6 "opening_queries__L0_L16_L6_L19_L6" fun n => fs "opening_queries__L0_L16_L6_L19_L6" + (n + 1) + (n + 1) * fs "__loop443" := by
  have hlk : oqLookup "opening_queries__L0_L16_L6_L19_L6" = some ("__loop443", 0, 16, 6, 13, 6) := by decide +kernel
  refine ⟨"__loop443", 6, hlk, ?_⟩
  intro n hn Lin cap flags qw qbp rew leaf pos sibs wts qwV dbpV hleaf hq hsl hans hlin hreg
  have hf := Program.find?_of_indexOf? (P := coreProgram) (n := "opening_queries__L0_L16_L6_L19_L6") (f := Data.core627) (j := 627) (by decide +kernel) rfl
  have hlf := Program.find?_of_indexOf? (P := coreProgram) (n := "__loop443") (f := Data.core992) (j := 992) (by decide +kernel) rfl
  exact opening_queries_completeAtCT (Ht := Ht) (CM := CM) fs cert k (base := 0) (I := 16) (blocks := 6) (pd := 13) (cd := 6)
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    hf rfl (stmtsEqb_sound (by decide +kernel)) (by rw [Program.loop_of_find? hf]; decide +kernel)
    hlf rfl (stmtsEqb_sound (by decide +kernel))
    ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
    (by rw [Program.loop_of_find? hlf]; decide +kernel)
    (cellsOk_of (j := 628) (by decide +kernel) (by decide +kernel))
    (cellsOk_of (j := 993) (by decide +kernel) (by decide +kernel)) (mem_osDecNames_loop hlk) hfit hn hleaf hq hsl hans hlin hreg

set_option maxRecDepth 100000 in
theorem oq_completeAtBT_L0_L16_L6_L20_L5C (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ)
    (hfit : cert "__loop450" (.n (oqP 0 16 6)) + 4 * 15 ≤ fs "__loop450") :
    OqCompleteAtBCT CM Ht fs cert k 0 16 20 5 "opening_queries__L0_L16_L6_L20_L5" fun n => fs "opening_queries__L0_L16_L6_L20_L5" + (n + 1) + (n + 1) * fs "__loop450" := by
  have hlk : oqLookup "opening_queries__L0_L16_L6_L20_L5" = some ("__loop450", 0, 16, 6, 15, 5) := by decide +kernel
  refine ⟨"__loop450", 6, hlk, ?_⟩
  intro n hn Lin cap flags qw qbp rew leaf pos sibs wts qwV dbpV hleaf hq hsl hans hlin hreg
  have hf := Program.find?_of_indexOf? (P := coreProgram) (n := "opening_queries__L0_L16_L6_L20_L5") (f := Data.core657) (j := 657) (by decide +kernel) rfl
  have hlf := Program.find?_of_indexOf? (P := coreProgram) (n := "__loop450") (f := Data.core1001) (j := 1001) (by decide +kernel) rfl
  exact opening_queries_completeAtCT (Ht := Ht) (CM := CM) fs cert k (base := 0) (I := 16) (blocks := 6) (pd := 15) (cd := 5)
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    hf rfl (stmtsEqb_sound (by decide +kernel)) (by rw [Program.loop_of_find? hf]; decide +kernel)
    hlf rfl (stmtsEqb_sound (by decide +kernel))
    ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
    (by rw [Program.loop_of_find? hlf]; decide +kernel)
    (cellsOk_of (j := 658) (by decide +kernel) (by decide +kernel))
    (cellsOk_of (j := 1002) (by decide +kernel) (by decide +kernel)) (mem_osDecNames_loop hlk) hfit hn hleaf hq hsl hans hlin hreg

set_option maxRecDepth 100000 in
theorem oq_completeAtBT_L0_L16_L6_L21_L4C (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ)
    (hfit : cert "__loop473" (.n (oqP 0 16 6)) + 4 * 17 ≤ fs "__loop473") :
    OqCompleteAtBCT CM Ht fs cert k 0 16 21 4 "opening_queries__L0_L16_L6_L21_L4" fun n => fs "opening_queries__L0_L16_L6_L21_L4" + (n + 1) + (n + 1) * fs "__loop473" := by
  have hlk : oqLookup "opening_queries__L0_L16_L6_L21_L4" = some ("__loop473", 0, 16, 6, 17, 4) := by decide +kernel
  refine ⟨"__loop473", 6, hlk, ?_⟩
  intro n hn Lin cap flags qw qbp rew leaf pos sibs wts qwV dbpV hleaf hq hsl hans hlin hreg
  have hf := Program.find?_of_indexOf? (P := coreProgram) (n := "opening_queries__L0_L16_L6_L21_L4") (f := Data.core828) (j := 828) (by decide +kernel) rfl
  have hlf := Program.find?_of_indexOf? (P := coreProgram) (n := "__loop473") (f := Data.core1027) (j := 1027) (by decide +kernel) rfl
  exact opening_queries_completeAtCT (Ht := Ht) (CM := CM) fs cert k (base := 0) (I := 16) (blocks := 6) (pd := 17) (cd := 4)
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    hf rfl (stmtsEqb_sound (by decide +kernel)) (by rw [Program.loop_of_find? hf]; decide +kernel)
    hlf rfl (stmtsEqb_sound (by decide +kernel))
    ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
    (by rw [Program.loop_of_find? hlf]; decide +kernel)
    (cellsOk_of (j := 829) (by decide +kernel) (by decide +kernel))
    (cellsOk_of (j := 1028) (by decide +kernel) (by decide +kernel)) (mem_osDecNames_loop hlk) hfit hn hleaf hq hsl hans hlin hreg

set_option maxRecDepth 100000 in
theorem oq_completeAtBT_L0_L16_L6_L21_L6C (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ)
    (hfit : cert "__loop449" (.n (oqP 0 16 6)) + 4 * 15 ≤ fs "__loop449") :
    OqCompleteAtBCT CM Ht fs cert k 0 16 21 6 "opening_queries__L0_L16_L6_L21_L6" fun n => fs "opening_queries__L0_L16_L6_L21_L6" + (n + 1) + (n + 1) * fs "__loop449" := by
  have hlk : oqLookup "opening_queries__L0_L16_L6_L21_L6" = some ("__loop449", 0, 16, 6, 15, 6) := by decide +kernel
  refine ⟨"__loop449", 6, hlk, ?_⟩
  intro n hn Lin cap flags qw qbp rew leaf pos sibs wts qwV dbpV hleaf hq hsl hans hlin hreg
  have hf := Program.find?_of_indexOf? (P := coreProgram) (n := "opening_queries__L0_L16_L6_L21_L6") (f := Data.core655) (j := 655) (by decide +kernel) rfl
  have hlf := Program.find?_of_indexOf? (P := coreProgram) (n := "__loop449") (f := Data.core1000) (j := 1000) (by decide +kernel) rfl
  exact opening_queries_completeAtCT (Ht := Ht) (CM := CM) fs cert k (base := 0) (I := 16) (blocks := 6) (pd := 15) (cd := 6)
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    hf rfl (stmtsEqb_sound (by decide +kernel)) (by rw [Program.loop_of_find? hf]; decide +kernel)
    hlf rfl (stmtsEqb_sound (by decide +kernel))
    ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
    (by rw [Program.loop_of_find? hlf]; decide +kernel)
    (cellsOk_of (j := 656) (by decide +kernel) (by decide +kernel))
    (cellsOk_of (j := 1001) (by decide +kernel) (by decide +kernel)) (mem_osDecNames_loop hlk) hfit hn hleaf hq hsl hans hlin hreg

set_option maxRecDepth 100000 in
theorem oq_completeAtBT_L0_L16_L6_L22_L5C (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ)
    (hfit : cert "__loop468" (.n (oqP 0 16 6)) + 4 * 17 ≤ fs "__loop468") :
    OqCompleteAtBCT CM Ht fs cert k 0 16 22 5 "opening_queries__L0_L16_L6_L22_L5" fun n => fs "opening_queries__L0_L16_L6_L22_L5" + (n + 1) + (n + 1) * fs "__loop468" := by
  have hlk : oqLookup "opening_queries__L0_L16_L6_L22_L5" = some ("__loop468", 0, 16, 6, 17, 5) := by decide +kernel
  refine ⟨"__loop468", 6, hlk, ?_⟩
  intro n hn Lin cap flags qw qbp rew leaf pos sibs wts qwV dbpV hleaf hq hsl hans hlin hreg
  have hf := Program.find?_of_indexOf? (P := coreProgram) (n := "opening_queries__L0_L16_L6_L22_L5") (f := Data.core753) (j := 753) (by decide +kernel) rfl
  have hlf := Program.find?_of_indexOf? (P := coreProgram) (n := "__loop468") (f := Data.core1021) (j := 1021) (by decide +kernel) rfl
  exact opening_queries_completeAtCT (Ht := Ht) (CM := CM) fs cert k (base := 0) (I := 16) (blocks := 6) (pd := 17) (cd := 5)
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    hf rfl (stmtsEqb_sound (by decide +kernel)) (by rw [Program.loop_of_find? hf]; decide +kernel)
    hlf rfl (stmtsEqb_sound (by decide +kernel))
    ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
    (by rw [Program.loop_of_find? hlf]; decide +kernel)
    (cellsOk_of (j := 754) (by decide +kernel) (by decide +kernel))
    (cellsOk_of (j := 1022) (by decide +kernel) (by decide +kernel)) (mem_osDecNames_loop hlk) hfit hn hleaf hq hsl hans hlin hreg

set_option maxRecDepth 100000 in
theorem oq_completeAtBT_L0_L16_L6_L23_L5C (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ)
    (hfit : cert "__loop472" (.n (oqP 0 16 6)) + 4 * 18 ≤ fs "__loop472") :
    OqCompleteAtBCT CM Ht fs cert k 0 16 23 5 "opening_queries__L0_L16_L6_L23_L5" fun n => fs "opening_queries__L0_L16_L6_L23_L5" + (n + 1) + (n + 1) * fs "__loop472" := by
  have hlk : oqLookup "opening_queries__L0_L16_L6_L23_L5" = some ("__loop472", 0, 16, 6, 18, 5) := by decide +kernel
  refine ⟨"__loop472", 6, hlk, ?_⟩
  intro n hn Lin cap flags qw qbp rew leaf pos sibs wts qwV dbpV hleaf hq hsl hans hlin hreg
  have hf := Program.find?_of_indexOf? (P := coreProgram) (n := "opening_queries__L0_L16_L6_L23_L5") (f := Data.core825) (j := 825) (by decide +kernel) rfl
  have hlf := Program.find?_of_indexOf? (P := coreProgram) (n := "__loop472") (f := Data.core1026) (j := 1026) (by decide +kernel) rfl
  exact opening_queries_completeAtCT (Ht := Ht) (CM := CM) fs cert k (base := 0) (I := 16) (blocks := 6) (pd := 18) (cd := 5)
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    hf rfl (stmtsEqb_sound (by decide +kernel)) (by rw [Program.loop_of_find? hf]; decide +kernel)
    hlf rfl (stmtsEqb_sound (by decide +kernel))
    ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
    (by rw [Program.loop_of_find? hlf]; decide +kernel)
    (cellsOk_of (j := 826) (by decide +kernel) (by decide +kernel))
    (cellsOk_of (j := 1027) (by decide +kernel) (by decide +kernel)) (mem_osDecNames_loop hlk) hfit hn hleaf hq hsl hans hlin hreg

set_option maxRecDepth 100000 in
theorem oq_completeAtBT_L0_L16_L6_L24_L5C (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ)
    (hfit : cert "__loop480" (.n (oqP 0 16 6)) + 4 * 19 ≤ fs "__loop480") :
    OqCompleteAtBCT CM Ht fs cert k 0 16 24 5 "opening_queries__L0_L16_L6_L24_L5" fun n => fs "opening_queries__L0_L16_L6_L24_L5" + (n + 1) + (n + 1) * fs "__loop480" := by
  have hlk : oqLookup "opening_queries__L0_L16_L6_L24_L5" = some ("__loop480", 0, 16, 6, 19, 5) := by decide +kernel
  refine ⟨"__loop480", 6, hlk, ?_⟩
  intro n hn Lin cap flags qw qbp rew leaf pos sibs wts qwV dbpV hleaf hq hsl hans hlin hreg
  have hf := Program.find?_of_indexOf? (P := coreProgram) (n := "opening_queries__L0_L16_L6_L24_L5") (f := Data.core890) (j := 890) (by decide +kernel) rfl
  have hlf := Program.find?_of_indexOf? (P := coreProgram) (n := "__loop480") (f := Data.core1034) (j := 1034) (by decide +kernel) rfl
  exact opening_queries_completeAtCT (Ht := Ht) (CM := CM) fs cert k (base := 0) (I := 16) (blocks := 6) (pd := 19) (cd := 5)
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    hf rfl (stmtsEqb_sound (by decide +kernel)) (by rw [Program.loop_of_find? hf]; decide +kernel)
    hlf rfl (stmtsEqb_sound (by decide +kernel))
    ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
    (by rw [Program.loop_of_find? hlf]; decide +kernel)
    (cellsOk_of (j := 891) (by decide +kernel) (by decide +kernel))
    (cellsOk_of (j := 1035) (by decide +kernel) (by decide +kernel)) (mem_osDecNames_loop hlk) hfit hn hleaf hq hsl hans hlin hreg

set_option maxRecDepth 100000 in
theorem oq_completeAtBT_L0_L16_L6_L25_L5C (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ)
    (hfit : cert "__loop482" (.n (oqP 0 16 6)) + 4 * 20 ≤ fs "__loop482") :
    OqCompleteAtBCT CM Ht fs cert k 0 16 25 5 "opening_queries__L0_L16_L6_L25_L5" fun n => fs "opening_queries__L0_L16_L6_L25_L5" + (n + 1) + (n + 1) * fs "__loop482" := by
  have hlk : oqLookup "opening_queries__L0_L16_L6_L25_L5" = some ("__loop482", 0, 16, 6, 20, 5) := by decide +kernel
  refine ⟨"__loop482", 6, hlk, ?_⟩
  intro n hn Lin cap flags qw qbp rew leaf pos sibs wts qwV dbpV hleaf hq hsl hans hlin hreg
  have hf := Program.find?_of_indexOf? (P := coreProgram) (n := "opening_queries__L0_L16_L6_L25_L5") (f := Data.core902) (j := 902) (by decide +kernel) rfl
  have hlf := Program.find?_of_indexOf? (P := coreProgram) (n := "__loop482") (f := Data.core1037) (j := 1037) (by decide +kernel) rfl
  exact opening_queries_completeAtCT (Ht := Ht) (CM := CM) fs cert k (base := 0) (I := 16) (blocks := 6) (pd := 20) (cd := 5)
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    hf rfl (stmtsEqb_sound (by decide +kernel)) (by rw [Program.loop_of_find? hf]; decide +kernel)
    hlf rfl (stmtsEqb_sound (by decide +kernel))
    ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
    (by rw [Program.loop_of_find? hlf]; decide +kernel)
    (cellsOk_of (j := 903) (by decide +kernel) (by decide +kernel))
    (cellsOk_of (j := 1038) (by decide +kernel) (by decide +kernel)) (mem_osDecNames_loop hlk) hfit hn hleaf hq hsl hans hlin hreg

set_option maxRecDepth 100000 in
theorem oq_completeAtBT_L1_L64_L8_L18_L7C (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ)
    (hfit : cert "__loop457" (.n (oqP 1 64 8)) + 4 * 11 ≤ fs "__loop457") :
    OqCompleteAtBCT CM Ht fs cert k 1 64 18 7 "opening_queries__L1_L64_L8_L18_L7" fun n => fs "opening_queries__L1_L64_L8_L18_L7" + (n + 1) + (n + 1) * fs "__loop457" := by
  have hlk : oqLookup "opening_queries__L1_L64_L8_L18_L7" = some ("__loop457", 1, 64, 8, 11, 7) := by decide +kernel
  refine ⟨"__loop457", 8, hlk, ?_⟩
  intro n hn Lin cap flags qw qbp rew leaf pos sibs wts qwV dbpV hleaf hq hsl hans hlin hreg
  have hf := Program.find?_of_indexOf? (P := coreProgram) (n := "opening_queries__L1_L64_L8_L18_L7") (f := Data.core684) (j := 684) (by decide +kernel) rfl
  have hlf := Program.find?_of_indexOf? (P := coreProgram) (n := "__loop457") (f := Data.core1009) (j := 1009) (by decide +kernel) rfl
  exact opening_queries_completeAtCT (Ht := Ht) (CM := CM) fs cert k (base := 1) (I := 64) (blocks := 8) (pd := 11) (cd := 7)
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    hf rfl (stmtsEqb_sound (by decide +kernel)) (by rw [Program.loop_of_find? hf]; decide +kernel)
    hlf rfl (stmtsEqb_sound (by decide +kernel))
    ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
    (by rw [Program.loop_of_find? hlf]; decide +kernel)
    (cellsOk_of (j := 685) (by decide +kernel) (by decide +kernel))
    (cellsOk_of (j := 1010) (by decide +kernel) (by decide +kernel)) (mem_osDecNames_loop hlk) hfit hn hleaf hq hsl hans hlin hreg

set_option maxRecDepth 100000 in
theorem oq_completeAtBT_L1_L64_L8_L19_L7C (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ)
    (hfit : cert "__loop458" (.n (oqP 1 64 8)) + 4 * 12 ≤ fs "__loop458") :
    OqCompleteAtBCT CM Ht fs cert k 1 64 19 7 "opening_queries__L1_L64_L8_L19_L7" fun n => fs "opening_queries__L1_L64_L8_L19_L7" + (n + 1) + (n + 1) * fs "__loop458" := by
  have hlk : oqLookup "opening_queries__L1_L64_L8_L19_L7" = some ("__loop458", 1, 64, 8, 12, 7) := by decide +kernel
  refine ⟨"__loop458", 8, hlk, ?_⟩
  intro n hn Lin cap flags qw qbp rew leaf pos sibs wts qwV dbpV hleaf hq hsl hans hlin hreg
  have hf := Program.find?_of_indexOf? (P := coreProgram) (n := "opening_queries__L1_L64_L8_L19_L7") (f := Data.core693) (j := 693) (by decide +kernel) rfl
  have hlf := Program.find?_of_indexOf? (P := coreProgram) (n := "__loop458") (f := Data.core1010) (j := 1010) (by decide +kernel) rfl
  exact opening_queries_completeAtCT (Ht := Ht) (CM := CM) fs cert k (base := 1) (I := 64) (blocks := 8) (pd := 12) (cd := 7)
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    hf rfl (stmtsEqb_sound (by decide +kernel)) (by rw [Program.loop_of_find? hf]; decide +kernel)
    hlf rfl (stmtsEqb_sound (by decide +kernel))
    ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
    (by rw [Program.loop_of_find? hlf]; decide +kernel)
    (cellsOk_of (j := 694) (by decide +kernel) (by decide +kernel))
    (cellsOk_of (j := 1011) (by decide +kernel) (by decide +kernel)) (mem_osDecNames_loop hlk) hfit hn hleaf hq hsl hans hlin hreg

set_option maxRecDepth 100000 in
theorem oq_completeAtBT_L1_L64_L8_L20_L6C (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ)
    (hfit : cert "__loop474" (.n (oqP 1 64 8)) + 4 * 14 ≤ fs "__loop474") :
    OqCompleteAtBCT CM Ht fs cert k 1 64 20 6 "opening_queries__L1_L64_L8_L20_L6" fun n => fs "opening_queries__L1_L64_L8_L20_L6" + (n + 1) + (n + 1) * fs "__loop474" := by
  have hlk : oqLookup "opening_queries__L1_L64_L8_L20_L6" = some ("__loop474", 1, 64, 8, 14, 6) := by decide +kernel
  refine ⟨"__loop474", 8, hlk, ?_⟩
  intro n hn Lin cap flags qw qbp rew leaf pos sibs wts qwV dbpV hleaf hq hsl hans hlin hreg
  have hf := Program.find?_of_indexOf? (P := coreProgram) (n := "opening_queries__L1_L64_L8_L20_L6") (f := Data.core837) (j := 837) (by decide +kernel) rfl
  have hlf := Program.find?_of_indexOf? (P := coreProgram) (n := "__loop474") (f := Data.core1028) (j := 1028) (by decide +kernel) rfl
  exact opening_queries_completeAtCT (Ht := Ht) (CM := CM) fs cert k (base := 1) (I := 64) (blocks := 8) (pd := 14) (cd := 6)
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    hf rfl (stmtsEqb_sound (by decide +kernel)) (by rw [Program.loop_of_find? hf]; decide +kernel)
    hlf rfl (stmtsEqb_sound (by decide +kernel))
    ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
    (by rw [Program.loop_of_find? hlf]; decide +kernel)
    (cellsOk_of (j := 838) (by decide +kernel) (by decide +kernel))
    (cellsOk_of (j := 1029) (by decide +kernel) (by decide +kernel)) (mem_osDecNames_loop hlk) hfit hn hleaf hq hsl hans hlin hreg

set_option maxRecDepth 100000 in
theorem oq_completeAtBT_L1_L64_L8_L20_L8C (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ)
    (hfit : cert "__loop442" (.n (oqP 1 64 8)) + 4 * 12 ≤ fs "__loop442") :
    OqCompleteAtBCT CM Ht fs cert k 1 64 20 8 "opening_queries__L1_L64_L8_L20_L8" fun n => fs "opening_queries__L1_L64_L8_L20_L8" + (n + 1) + (n + 1) * fs "__loop442" := by
  have hlk : oqLookup "opening_queries__L1_L64_L8_L20_L8" = some ("__loop442", 1, 64, 8, 12, 8) := by decide +kernel
  refine ⟨"__loop442", 8, hlk, ?_⟩
  intro n hn Lin cap flags qw qbp rew leaf pos sibs wts qwV dbpV hleaf hq hsl hans hlin hreg
  have hf := Program.find?_of_indexOf? (P := coreProgram) (n := "opening_queries__L1_L64_L8_L20_L8") (f := Data.core625) (j := 625) (by decide +kernel) rfl
  have hlf := Program.find?_of_indexOf? (P := coreProgram) (n := "__loop442") (f := Data.core991) (j := 991) (by decide +kernel) rfl
  exact opening_queries_completeAtCT (Ht := Ht) (CM := CM) fs cert k (base := 1) (I := 64) (blocks := 8) (pd := 12) (cd := 8)
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    hf rfl (stmtsEqb_sound (by decide +kernel)) (by rw [Program.loop_of_find? hf]; decide +kernel)
    hlf rfl (stmtsEqb_sound (by decide +kernel))
    ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
    (by rw [Program.loop_of_find? hlf]; decide +kernel)
    (cellsOk_of (j := 626) (by decide +kernel) (by decide +kernel))
    (cellsOk_of (j := 992) (by decide +kernel) (by decide +kernel)) (mem_osDecNames_loop hlk) hfit hn hleaf hq hsl hans hlin hreg

set_option maxRecDepth 100000 in
theorem oq_completeAtBT_L1_L64_L8_L21_L7C (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ)
    (hfit : cert "__loop461" (.n (oqP 1 64 8)) + 4 * 14 ≤ fs "__loop461") :
    OqCompleteAtBCT CM Ht fs cert k 1 64 21 7 "opening_queries__L1_L64_L8_L21_L7" fun n => fs "opening_queries__L1_L64_L8_L21_L7" + (n + 1) + (n + 1) * fs "__loop461" := by
  have hlk : oqLookup "opening_queries__L1_L64_L8_L21_L7" = some ("__loop461", 1, 64, 8, 14, 7) := by decide +kernel
  refine ⟨"__loop461", 8, hlk, ?_⟩
  intro n hn Lin cap flags qw qbp rew leaf pos sibs wts qwV dbpV hleaf hq hsl hans hlin hreg
  have hf := Program.find?_of_indexOf? (P := coreProgram) (n := "opening_queries__L1_L64_L8_L21_L7") (f := Data.core714) (j := 714) (by decide +kernel) rfl
  have hlf := Program.find?_of_indexOf? (P := coreProgram) (n := "__loop461") (f := Data.core1013) (j := 1013) (by decide +kernel) rfl
  exact opening_queries_completeAtCT (Ht := Ht) (CM := CM) fs cert k (base := 1) (I := 64) (blocks := 8) (pd := 14) (cd := 7)
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    hf rfl (stmtsEqb_sound (by decide +kernel)) (by rw [Program.loop_of_find? hf]; decide +kernel)
    hlf rfl (stmtsEqb_sound (by decide +kernel))
    ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
    (by rw [Program.loop_of_find? hlf]; decide +kernel)
    (cellsOk_of (j := 715) (by decide +kernel) (by decide +kernel))
    (cellsOk_of (j := 1014) (by decide +kernel) (by decide +kernel)) (mem_osDecNames_loop hlk) hfit hn hleaf hq hsl hans hlin hreg

set_option maxRecDepth 100000 in
theorem oq_completeAtBT_L1_L64_L8_L22_L6C (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ)
    (hfit : cert "__loop476" (.n (oqP 1 64 8)) + 4 * 16 ≤ fs "__loop476") :
    OqCompleteAtBCT CM Ht fs cert k 1 64 22 6 "opening_queries__L1_L64_L8_L22_L6" fun n => fs "opening_queries__L1_L64_L8_L22_L6" + (n + 1) + (n + 1) * fs "__loop476" := by
  have hlk : oqLookup "opening_queries__L1_L64_L8_L22_L6" = some ("__loop476", 1, 64, 8, 16, 6) := by decide +kernel
  refine ⟨"__loop476", 8, hlk, ?_⟩
  intro n hn Lin cap flags qw qbp rew leaf pos sibs wts qwV dbpV hleaf hq hsl hans hlin hreg
  have hf := Program.find?_of_indexOf? (P := coreProgram) (n := "opening_queries__L1_L64_L8_L22_L6") (f := Data.core855) (j := 855) (by decide +kernel) rfl
  have hlf := Program.find?_of_indexOf? (P := coreProgram) (n := "__loop476") (f := Data.core1030) (j := 1030) (by decide +kernel) rfl
  exact opening_queries_completeAtCT (Ht := Ht) (CM := CM) fs cert k (base := 1) (I := 64) (blocks := 8) (pd := 16) (cd := 6)
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    hf rfl (stmtsEqb_sound (by decide +kernel)) (by rw [Program.loop_of_find? hf]; decide +kernel)
    hlf rfl (stmtsEqb_sound (by decide +kernel))
    ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
    (by rw [Program.loop_of_find? hlf]; decide +kernel)
    (cellsOk_of (j := 856) (by decide +kernel) (by decide +kernel))
    (cellsOk_of (j := 1031) (by decide +kernel) (by decide +kernel)) (mem_osDecNames_loop hlk) hfit hn hleaf hq hsl hans hlin hreg

set_option maxRecDepth 100000 in
theorem oq_completeAtBT_L1_L64_L8_L22_L8C (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ)
    (hfit : cert "__loop448" (.n (oqP 1 64 8)) + 4 * 14 ≤ fs "__loop448") :
    OqCompleteAtBCT CM Ht fs cert k 1 64 22 8 "opening_queries__L1_L64_L8_L22_L8" fun n => fs "opening_queries__L1_L64_L8_L22_L8" + (n + 1) + (n + 1) * fs "__loop448" := by
  have hlk : oqLookup "opening_queries__L1_L64_L8_L22_L8" = some ("__loop448", 1, 64, 8, 14, 8) := by decide +kernel
  refine ⟨"__loop448", 8, hlk, ?_⟩
  intro n hn Lin cap flags qw qbp rew leaf pos sibs wts qwV dbpV hleaf hq hsl hans hlin hreg
  have hf := Program.find?_of_indexOf? (P := coreProgram) (n := "opening_queries__L1_L64_L8_L22_L8") (f := Data.core653) (j := 653) (by decide +kernel) rfl
  have hlf := Program.find?_of_indexOf? (P := coreProgram) (n := "__loop448") (f := Data.core999) (j := 999) (by decide +kernel) rfl
  exact opening_queries_completeAtCT (Ht := Ht) (CM := CM) fs cert k (base := 1) (I := 64) (blocks := 8) (pd := 14) (cd := 8)
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    hf rfl (stmtsEqb_sound (by decide +kernel)) (by rw [Program.loop_of_find? hf]; decide +kernel)
    hlf rfl (stmtsEqb_sound (by decide +kernel))
    ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
    (by rw [Program.loop_of_find? hlf]; decide +kernel)
    (cellsOk_of (j := 654) (by decide +kernel) (by decide +kernel))
    (cellsOk_of (j := 1000) (by decide +kernel) (by decide +kernel)) (mem_osDecNames_loop hlk) hfit hn hleaf hq hsl hans hlin hreg

set_option maxRecDepth 100000 in
theorem oq_completeAtBT_L1_L64_L8_L23_L7C (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ)
    (hfit : cert "__loop464" (.n (oqP 1 64 8)) + 4 * 16 ≤ fs "__loop464") :
    OqCompleteAtBCT CM Ht fs cert k 1 64 23 7 "opening_queries__L1_L64_L8_L23_L7" fun n => fs "opening_queries__L1_L64_L8_L23_L7" + (n + 1) + (n + 1) * fs "__loop464" := by
  have hlk : oqLookup "opening_queries__L1_L64_L8_L23_L7" = some ("__loop464", 1, 64, 8, 16, 7) := by decide +kernel
  refine ⟨"__loop464", 8, hlk, ?_⟩
  intro n hn Lin cap flags qw qbp rew leaf pos sibs wts qwV dbpV hleaf hq hsl hans hlin hreg
  have hf := Program.find?_of_indexOf? (P := coreProgram) (n := "opening_queries__L1_L64_L8_L23_L7") (f := Data.core737) (j := 737) (by decide +kernel) rfl
  have hlf := Program.find?_of_indexOf? (P := coreProgram) (n := "__loop464") (f := Data.core1016) (j := 1016) (by decide +kernel) rfl
  exact opening_queries_completeAtCT (Ht := Ht) (CM := CM) fs cert k (base := 1) (I := 64) (blocks := 8) (pd := 16) (cd := 7)
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    hf rfl (stmtsEqb_sound (by decide +kernel)) (by rw [Program.loop_of_find? hf]; decide +kernel)
    hlf rfl (stmtsEqb_sound (by decide +kernel))
    ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
    (by rw [Program.loop_of_find? hlf]; decide +kernel)
    (cellsOk_of (j := 738) (by decide +kernel) (by decide +kernel))
    (cellsOk_of (j := 1017) (by decide +kernel) (by decide +kernel)) (mem_osDecNames_loop hlk) hfit hn hleaf hq hsl hans hlin hreg

set_option maxRecDepth 100000 in
theorem oq_completeAtBT_L1_L64_L8_L24_L6C (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ)
    (hfit : cert "__loop478" (.n (oqP 1 64 8)) + 4 * 18 ≤ fs "__loop478") :
    OqCompleteAtBCT CM Ht fs cert k 1 64 24 6 "opening_queries__L1_L64_L8_L24_L6" fun n => fs "opening_queries__L1_L64_L8_L24_L6" + (n + 1) + (n + 1) * fs "__loop478" := by
  have hlk : oqLookup "opening_queries__L1_L64_L8_L24_L6" = some ("__loop478", 1, 64, 8, 18, 6) := by decide +kernel
  refine ⟨"__loop478", 8, hlk, ?_⟩
  intro n hn Lin cap flags qw qbp rew leaf pos sibs wts qwV dbpV hleaf hq hsl hans hlin hreg
  have hf := Program.find?_of_indexOf? (P := coreProgram) (n := "opening_queries__L1_L64_L8_L24_L6") (f := Data.core877) (j := 877) (by decide +kernel) rfl
  have hlf := Program.find?_of_indexOf? (P := coreProgram) (n := "__loop478") (f := Data.core1032) (j := 1032) (by decide +kernel) rfl
  exact opening_queries_completeAtCT (Ht := Ht) (CM := CM) fs cert k (base := 1) (I := 64) (blocks := 8) (pd := 18) (cd := 6)
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    hf rfl (stmtsEqb_sound (by decide +kernel)) (by rw [Program.loop_of_find? hf]; decide +kernel)
    hlf rfl (stmtsEqb_sound (by decide +kernel))
    ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
    (by rw [Program.loop_of_find? hlf]; decide +kernel)
    (cellsOk_of (j := 878) (by decide +kernel) (by decide +kernel))
    (cellsOk_of (j := 1033) (by decide +kernel) (by decide +kernel)) (mem_osDecNames_loop hlk) hfit hn hleaf hq hsl hans hlin hreg

set_option maxRecDepth 100000 in
theorem oq_completeAtBT_L1_L64_L8_L25_L6C (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ)
    (hfit : cert "__loop479" (.n (oqP 1 64 8)) + 4 * 19 ≤ fs "__loop479") :
    OqCompleteAtBCT CM Ht fs cert k 1 64 25 6 "opening_queries__L1_L64_L8_L25_L6" fun n => fs "opening_queries__L1_L64_L8_L25_L6" + (n + 1) + (n + 1) * fs "__loop479" := by
  have hlk : oqLookup "opening_queries__L1_L64_L8_L25_L6" = some ("__loop479", 1, 64, 8, 19, 6) := by decide +kernel
  refine ⟨"__loop479", 8, hlk, ?_⟩
  intro n hn Lin cap flags qw qbp rew leaf pos sibs wts qwV dbpV hleaf hq hsl hans hlin hreg
  have hf := Program.find?_of_indexOf? (P := coreProgram) (n := "opening_queries__L1_L64_L8_L25_L6") (f := Data.core888) (j := 888) (by decide +kernel) rfl
  have hlf := Program.find?_of_indexOf? (P := coreProgram) (n := "__loop479") (f := Data.core1033) (j := 1033) (by decide +kernel) rfl
  exact opening_queries_completeAtCT (Ht := Ht) (CM := CM) fs cert k (base := 1) (I := 64) (blocks := 8) (pd := 19) (cd := 6)
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    hf rfl (stmtsEqb_sound (by decide +kernel)) (by rw [Program.loop_of_find? hf]; decide +kernel)
    hlf rfl (stmtsEqb_sound (by decide +kernel))
    ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
    (by rw [Program.loop_of_find? hlf]; decide +kernel)
    (cellsOk_of (j := 889) (by decide +kernel) (by decide +kernel))
    (cellsOk_of (j := 1034) (by decide +kernel) (by decide +kernel)) (mem_osDecNames_loop hlk) hfit hn hleaf hq hsl hans hlin hreg

set_option maxRecDepth 100000 in
theorem oq_completeAtBT_L1_L64_L8_L26_L6C (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ)
    (hfit : cert "__loop481" (.n (oqP 1 64 8)) + 4 * 20 ≤ fs "__loop481") :
    OqCompleteAtBCT CM Ht fs cert k 1 64 26 6 "opening_queries__L1_L64_L8_L26_L6" fun n => fs "opening_queries__L1_L64_L8_L26_L6" + (n + 1) + (n + 1) * fs "__loop481" := by
  have hlk : oqLookup "opening_queries__L1_L64_L8_L26_L6" = some ("__loop481", 1, 64, 8, 20, 6) := by decide +kernel
  refine ⟨"__loop481", 8, hlk, ?_⟩
  intro n hn Lin cap flags qw qbp rew leaf pos sibs wts qwV dbpV hleaf hq hsl hans hlin hreg
  have hf := Program.find?_of_indexOf? (P := coreProgram) (n := "opening_queries__L1_L64_L8_L26_L6") (f := Data.core900) (j := 900) (by decide +kernel) rfl
  have hlf := Program.find?_of_indexOf? (P := coreProgram) (n := "__loop481") (f := Data.core1036) (j := 1036) (by decide +kernel) rfl
  exact opening_queries_completeAtCT (Ht := Ht) (CM := CM) fs cert k (base := 1) (I := 64) (blocks := 8) (pd := 20) (cd := 6)
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    hf rfl (stmtsEqb_sound (by decide +kernel)) (by rw [Program.loop_of_find? hf]; decide +kernel)
    hlf rfl (stmtsEqb_sound (by decide +kernel))
    ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
    (by rw [Program.loop_of_find? hlf]; decide +kernel)
    (cellsOk_of (j := 901) (by decide +kernel) (by decide +kernel))
    (cellsOk_of (j := 1037) (by decide +kernel) (by decide +kernel)) (mem_osDecNames_loop hlk) hfit hn hleaf hq hsl hans hlin hreg

end
end LeanVM.Guest.B1
