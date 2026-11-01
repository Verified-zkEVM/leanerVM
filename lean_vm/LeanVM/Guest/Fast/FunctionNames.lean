module

public import LeanVM.Guest.Core

/-!
# The functions the decoder reads frames of, numbered

The decoder reads the witness off the frames of the functions that checked it, through a frame
map keyed by the function's name (`FrameMap`, `B1/Main/Frames.lean`). Its readers, made
programs of the cost machine, key it by a number instead (`NFrames`): the frame map `V` is read
as `fun k ↦ V (decoderFunctionName k)`.

* `decoderFunctionNames`: the `152` functions, each once (`decoderFunctionNames_nodup`): `main`
  (`0`); `main`'s callees whose witness is read: `verify_lean_xmss` (`1`),
  `verify_sig_lean_sphincs` (`2`), `da_verify` (`3`), `verify_sub` (`4`), `aggregate_claims` (`5`);
  `da_verify`'s callees (`6 ..< 12`); `open_stacked`'s 28 specializations (`openStackedBase + m`,
  `openNames`); the 56 `opening_queries` specializations (`openingQueriesBase + j`) and their loop
  helpers (`openingQueriesLoopBase + j`), in the order of `openingQueriesLoops`
  (`Fast/FunctionNamesCheck.lean` checks the last three against their name functions);
* `decoderFunctionName k`, `decoderFunctionIndex f`: the name of number `k` (`""` past the
  table) and the number of name `f` (`none` off the table), inverse on the table
  (`decoderFunctionIndex_name`, `decoderFunctionIndex_eq_some`). A frame map keyed by name is
  re-keyed by `decoderFunctionName`; an entry table keyed by name, by `decoderFunctionIndex`.
-/

namespace LeanVM.Guest.Fast

open LeanVM.Parameters LeanVM.Guest.Core

@[expose] public section

/-- A frame map keyed by the numbers of `decoderFunctionNames`. -/
abbrev NFrames : Type := ℕ → List E → List E → Val

/-- **The functions the decoder reads frames of.** -/
def decoderFunctionNames : List String := [
    "main",  -- 0
    "verify_lean_xmss",  -- 1
    "verify_sig_lean_sphincs",  -- 2
    "da_verify",  -- 3
    "verify_sub",  -- 4
    "aggregate_claims",  -- 5
    "da_verify_column__L1",  -- 6
    "da_verify_column__L0",  -- 7
    "__loop415",  -- 8
    "__loop417",  -- 9
    "da_vector_cell",  -- 10
    "da_verify_cell",  -- 11
    "open_stacked__L0",  -- 12
    "open_stacked__L1",  -- 13
    "open_stacked__L2",  -- 14
    "open_stacked__L3",  -- 15
    "open_stacked__L4",  -- 16
    "open_stacked__L5",  -- 17
    "open_stacked__L6",  -- 18
    "open_stacked__L7",  -- 19
    "open_stacked__L8",  -- 20
    "open_stacked__L9",  -- 21
    "open_stacked__L10",  -- 22
    "open_stacked__L11",  -- 23
    "open_stacked__L12",  -- 24
    "open_stacked__L13",  -- 25
    "open_stacked__L14",  -- 26
    "open_stacked__L15",  -- 27
    "open_stacked__L16",  -- 28
    "open_stacked__L17",  -- 29
    "open_stacked__L18",  -- 30
    "open_stacked__L19",  -- 31
    "open_stacked__L20",  -- 32
    "open_stacked__L21",  -- 33
    "open_stacked__L22",  -- 34
    "open_stacked__L23",  -- 35
    "open_stacked__L24",  -- 36
    "open_stacked__L25",  -- 37
    "open_stacked__L26",  -- 38
    "open_stacked__L27",  -- 39
    "opening_queries__L0_L1_L64_L32_L17_L8",  -- 40
    "opening_queries__L0_L1_L64_L32_L19_L8",  -- 41
    "opening_queries__L0_L1_L64_L32_L21_L6",  -- 42
    "opening_queries__L0_L1_L64_L32_L22_L7",  -- 43
    "opening_queries__L0_L1_L64_L32_L24_L7",  -- 44
    "opening_queries__L1_L1_L64_L32_L20_L7",  -- 45
    "opening_queries__L1_L1_L64_L32_L23_L7",  -- 46
    "opening_queries__L0_L0_L16_L24_L14_L5",  -- 47
    "opening_queries__L0_L0_L16_L24_L16_L6",  -- 48
    "opening_queries__L0_L0_L16_L24_L18_L4",  -- 49
    "opening_queries__L0_L0_L16_L24_L19_L5",  -- 50
    "opening_queries__L0_L0_L16_L24_L20_L6",  -- 51
    "opening_queries__L0_L0_L16_L24_L22_L4",  -- 52
    "opening_queries__L0_L0_L16_L24_L23_L6",  -- 53
    "opening_queries__L0_L1_L64_L32_L18_L7",  -- 54
    "opening_queries__L0_L1_L64_L32_L20_L6",  -- 55
    "opening_queries__L0_L1_L64_L32_L21_L7",  -- 56
    "opening_queries__L0_L1_L64_L32_L23_L6",  -- 57
    "opening_queries__L0_L1_L64_L32_L25_L6",  -- 58
    "opening_queries__L1_L1_L64_L32_L21_L7",  -- 59
    "opening_queries__L1_L1_L64_L32_L23_L8",  -- 60
    "opening_queries__L0_L0_L16_L24_L15_L5",  -- 61
    "opening_queries__L0_L0_L16_L24_L17_L4",  -- 62
    "opening_queries__L0_L0_L16_L24_L18_L5",  -- 63
    "opening_queries__L0_L0_L16_L24_L19_L6",  -- 64
    "opening_queries__L0_L0_L16_L24_L21_L4",  -- 65
    "opening_queries__L0_L0_L16_L24_L22_L5",  -- 66
    "opening_queries__L0_L0_L16_L24_L24_L5",  -- 67
    "opening_queries__L0_L1_L64_L32_L18_L8",  -- 68
    "opening_queries__L0_L1_L64_L32_L20_L7",  -- 69
    "opening_queries__L0_L1_L64_L32_L21_L8",  -- 70
    "opening_queries__L0_L1_L64_L32_L23_L7",  -- 71
    "opening_queries__L0_L1_L64_L32_L26_L6",  -- 72
    "opening_queries__L1_L1_L64_L32_L22_L7",  -- 73
    "opening_queries__L1_L1_L64_L32_L24_L7",  -- 74
    "opening_queries__L0_L0_L16_L24_L16_L4",  -- 75
    "opening_queries__L0_L0_L16_L24_L17_L5",  -- 76
    "opening_queries__L0_L0_L16_L24_L18_L6",  -- 77
    "opening_queries__L0_L0_L16_L24_L20_L4",  -- 78
    "opening_queries__L0_L0_L16_L24_L21_L5",  -- 79
    "opening_queries__L0_L0_L16_L24_L22_L6",  -- 80
    "opening_queries__L0_L0_L16_L24_L24_L6",  -- 81
    "opening_queries__L0_L1_L64_L32_L19_L7",  -- 82
    "opening_queries__L0_L1_L64_L32_L20_L8",  -- 83
    "opening_queries__L0_L1_L64_L32_L22_L6",  -- 84
    "opening_queries__L0_L1_L64_L32_L24_L6",  -- 85
    "opening_queries__L1_L1_L64_L32_L19_L7",  -- 86
    "opening_queries__L1_L1_L64_L32_L22_L8",  -- 87
    "opening_queries__L1_L1_L64_L32_L25_L7",  -- 88
    "opening_queries__L0_L0_L16_L24_L16_L5",  -- 89
    "opening_queries__L0_L0_L16_L24_L17_L6",  -- 90
    "opening_queries__L0_L0_L16_L24_L19_L4",  -- 91
    "opening_queries__L0_L0_L16_L24_L20_L5",  -- 92
    "opening_queries__L0_L0_L16_L24_L21_L6",  -- 93
    "opening_queries__L0_L0_L16_L24_L23_L5",  -- 94
    "opening_queries__L0_L0_L16_L24_L25_L5",  -- 95
    "__loop359",  -- 96
    "__loop366",  -- 97
    "__loop406",  -- 98
    "__loop388",  -- 99
    "__loop391",  -- 100
    "__loop396",  -- 101
    "__loop399",  -- 102
    "__loop362",  -- 103
    "__loop360",  -- 104
    "__loop381",  -- 105
    "__loop374",  -- 106
    "__loop373",  -- 107
    "__loop414",  -- 108
    "__loop392",  -- 109
    "__loop382",  -- 110
    "__loop405",  -- 111
    "__loop386",  -- 112
    "__loop408",  -- 113
    "__loop410",  -- 114
    "__loop397",  -- 115
    "__loop378",  -- 116
    "__loop361",  -- 117
    "__loop387",  -- 118
    "__loop371",  -- 119
    "__loop370",  -- 120
    "__loop404",  -- 121
    "__loop393",  -- 122
    "__loop411",  -- 123
    "__loop363",  -- 124
    "__loop384",  -- 125
    "__loop372",  -- 126
    "__loop389",  -- 127
    "__loop412",  -- 128
    "__loop398",  -- 129
    "__loop400",  -- 130
    "__loop385",  -- 131
    "__loop368",  -- 132
    "__loop367",  -- 133
    "__loop394",  -- 134
    "__loop380",  -- 135
    "__loop379",  -- 136
    "__loop402",  -- 137
    "__loop383",  -- 138
    "__loop369",  -- 139
    "__loop407",  -- 140
    "__loop409",  -- 141
    "__loop395",  -- 142
    "__loop375",  -- 143
    "__loop401",  -- 144
    "__loop365",  -- 145
    "__loop364",  -- 146
    "__loop390",  -- 147
    "__loop377",  -- 148
    "__loop376",  -- 149
    "__loop403",  -- 150
    "__loop413"  -- 151
  ]

/-- The number of functions. -/
def decoderFunctionCount : ℕ := 152

/-- `open_stacked__L{m}` is `openStackedBase + m`. -/
def openStackedBase : ℕ := 12

/-- `opening_queries` specialization `j` (of `openingQueriesLoops`) is `openingQueriesBase + j`. -/
def openingQueriesBase : ℕ := 40

/-- Its loop helper is `openingQueriesLoopBase + j`. -/
def openingQueriesLoopBase : ℕ := 96

/-- **The name of function `k`** (`""` past the table). -/
def decoderFunctionName (k : ℕ) : String := decoderFunctionNames.getD k ""

/-- **The number of the function named `f`** (`none` off the table). -/
def decoderFunctionIndex (f : String) : Option ℕ :=
  (List.range decoderFunctionCount).find? fun k ↦ decoderFunctionName k == f

theorem decoderFunctionNames_length : decoderFunctionNames.length = decoderFunctionCount := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem decoderFunctionNames_nodup : decoderFunctionNames.Nodup := by decide +kernel

/-- **The names are distinct.** -/
theorem decoderFunctionName_inj {j k : ℕ} (hj : j < decoderFunctionCount)
    (hk : k < decoderFunctionCount) (h : decoderFunctionName j = decoderFunctionName k) :
    j = k := by
  unfold decoderFunctionName at h
  rw [List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ hk] at h
  exact (decoderFunctionNames_nodup.getElem_inj_iff).mp h

theorem decoderFunctionIndex_eq_some {f : String} {k : ℕ} :
    decoderFunctionIndex f = some k ↔ k < decoderFunctionCount ∧ decoderFunctionName k = f := by
  constructor
  · intro h
    have hm := List.mem_range.mp (List.mem_of_find?_eq_some h)
    exact ⟨hm, by simpa using List.find?_some h⟩
  · rintro ⟨hk, rfl⟩
    rw [decoderFunctionIndex, List.find?_eq_some_iff_getElem]
    refine ⟨by simp, k, by simpa using hk, by simp, fun j hj ↦ ?_⟩
    simp only [List.getElem_range]
    cases e : (decoderFunctionName j == decoderFunctionName k)
    · rfl
    have hjk : j = k := decoderFunctionName_inj (by omega) hk (by simp at e; exact e)
    omega

/-! ## The fixed names -/

theorem name_main : decoderFunctionName 0 = "main" := rfl
theorem name_verify_lean_xmss : decoderFunctionName 1 = "verify_lean_xmss" := rfl
theorem name_verify_sig_lean_sphincs : decoderFunctionName 2 = "verify_sig_lean_sphincs" := rfl
theorem name_da_verify : decoderFunctionName 3 = "da_verify" := rfl
theorem name_verify_sub : decoderFunctionName 4 = "verify_sub" := rfl
theorem name_aggregate_claims : decoderFunctionName 5 = "aggregate_claims" := rfl
theorem name_da_verify_column_L1 : decoderFunctionName 6 = "da_verify_column__L1" := rfl
theorem name_da_verify_column_L0 : decoderFunctionName 7 = "da_verify_column__L0" := rfl
theorem name_loop415 : decoderFunctionName 8 = "__loop415" := rfl
theorem name_loop417 : decoderFunctionName 9 = "__loop417" := rfl
theorem name_da_vector_cell : decoderFunctionName 10 = "da_vector_cell" := rfl
theorem name_da_verify_cell : decoderFunctionName 11 = "da_verify_cell" := rfl

/-- **Number and name are inverse** on the table. -/
theorem decoderFunctionIndex_name {k : ℕ} (hk : k < decoderFunctionCount) :
    decoderFunctionIndex (decoderFunctionName k) = some k :=
  decoderFunctionIndex_eq_some.mpr ⟨hk, rfl⟩

end
end LeanVM.Guest.Fast
