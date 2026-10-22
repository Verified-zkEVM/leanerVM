/-
  LeanVM.Guest.B1.Comp.Whir.LoadsT.OsInjZ

  The functions `open_stacked`'s callees other than `opening_queries` and its loop helpers reach,
  closed under calls, by kernel evaluation.
-/

module

public import LeanVM.Guest.Located.VerifySub
public import LeanVM.Guest.Memory.SizeTotal

/-!
# The functions the other callees reach

`osInjNames`: `opening_queries`' specializations and their loop helpers. `osInjZ`: the functions
`open_stacked`'s other callees reach; their bodies call only functions of `osInjZ`
(`osInjZ_callsIn`), none of `osInjNames` (`osInjZ_notMem`). Checked over the program in chunks.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.Located LeanVM.Guest.B1.VerifySub

@[expose] public section

/-- `opening_queries`' specializations and their loop helpers. -/
def osInjNames : List String := oqTable.map (·.1) ++ oqTable.map (·.2.1)

/-! ## The functions the other callees reach -/

/-- The functions `open_stacked`'s callees outside `osInjNames` reach. -/
def osInjZ : List String :=
  ["__loop6", "__loop9", "__loop102", "__loop103", "__loop104", "__loop105", "__loop106", "__loop107",
    "__loop108", "__loop109", "__loop110", "__loop111", "__loop112", "__loop113", "__loop114", "__loop115",
    "__loop116", "__loop117", "__loop118", "__loop119", "__loop120", "__loop121", "__loop122", "__loop123",
    "__loop124", "__loop125", "__loop126", "__loop127", "__loop128", "__loop129", "__loop130", "__loop131",
    "__loop132", "__loop133", "__loop134", "__loop135", "__loop136", "__loop137", "__loop138", "__loop139",
    "__loop140", "__loop141", "__loop142", "__loop143", "__loop144", "__loop145", "__loop146", "__loop147",
    "__loop148", "__loop149", "__loop150", "__loop151", "__loop152", "__loop153", "__loop154", "__loop155",
    "__loop156", "__loop157", "__loop158", "__loop159", "__loop160", "__loop161", "__loop162", "__loop163",
    "__loop164", "__loop165", "__loop166", "__loop167", "__loop168", "__loop169", "__loop170", "__loop171",
    "__loop172", "__loop173", "__loop174", "__loop175", "__loop176", "__loop177", "__loop178", "__loop179",
    "__loop180", "__loop181", "__loop182", "__loop183", "__loop184", "__loop185", "__loop186", "__loop187",
    "__loop188", "__loop189", "__loop190", "__loop191", "__loop192", "__loop193", "__loop194", "__loop195",
    "__loop196", "__loop197", "__loop198", "__loop199", "__loop200", "__loop201", "__loop202", "__loop203",
    "__loop204", "__loop205", "__loop206", "__loop207", "__loop208", "__loop209", "__loop210", "__loop211",
    "__loop212", "__loop213", "__loop214", "__loop215", "__loop216", "__loop217", "__loop218", "__loop219",
    "__loop220", "__loop221", "__loop222", "__loop223", "__loop224", "__loop225", "__loop226", "__loop227",
    "__loop228", "__loop229", "__loop230", "__loop231", "__loop232", "__loop233", "__loop234", "__loop235",
    "__loop236", "__loop237", "__loop238", "__loop239", "__loop240", "__loop241", "__loop242", "__loop243",
    "__loop244", "__loop245", "__loop246", "__loop247", "__loop248", "__loop249", "__loop250", "__loop251",
    "__loop252", "__loop253", "__loop254", "__loop255", "__loop256", "__loop257", "__loop258", "__loop259",
    "__loop260", "__loop261", "__loop262", "__loop263", "__loop264", "__loop265", "__loop266", "__loop267",
    "__loop268", "__loop269", "__loop270", "__loop271", "__loop272", "__loop273", "__loop274", "__loop275",
    "__loop276", "__loop277", "__loop278", "__loop279", "__loop280", "__loop281", "__loop282", "__loop283",
    "__loop284", "__loop285", "__loop286", "__loop287", "__loop288", "__loop289", "__loop290", "__loop291",
    "__loop292", "__loop293", "__loop294", "__loop295", "__loop296", "__loop297", "__loop298", "__loop299",
    "__loop300", "__loop301", "__loop302", "__loop303", "__loop304", "__loop305", "__loop306", "__loop307",
    "__loop308", "__loop309", "__loop310", "__loop311", "__loop312", "__loop313", "__loop314", "__loop315",
    "__loop316", "__loop317", "__loop318", "__loop319", "__loop320", "__loop321", "__loop322", "__loop323",
    "__loop324", "__loop325", "__loop326", "__loop327", "__loop328", "__loop329", "__loop330", "__loop331",
    "__loop332", "__loop333", "__loop334", "__loop335", "__loop336", "__loop337", "__loop338", "__loop339",
    "__loop340", "__loop341", "__loop342", "__loop343", "__loop344", "__loop345", "__loop346", "__loop347",
    "__loop348", "__loop349", "__loop350", "__loop351", "__loop352", "__loop353", "__loop354", "__loop355",
    "__loop356", "__loop357", "__loop358", "__loop359", "__loop360", "__loop361", "__loop362", "__loop363",
    "__loop364", "__loop365", "__loop366", "__loop367", "__loop368", "__loop369", "__loop370", "__loop371",
    "__loop372", "__loop373", "__loop429", "__loop431", "__loop433", "__loop454", "__loop456",
    "assert_canonical", "decode_query_bits__L14", "decode_query_bits__L15", "decode_query_bits__L16",
    "decode_query_bits__L17", "decode_query_bits__L18", "decode_query_bits__L19", "decode_query_bits__L20",
    "decode_query_bits__L21", "decode_query_bits__L22", "decode_query_bits__L23", "decode_query_bits__L24",
    "decode_query_bits__L25", "decode_query_bits__L26", "fold_final_msg__L2", "fold_final_msg__L3",
    "fold_final_msg__L4", "fold_final_msg__L5", "grind_check", "opening_final_message__L16",
    "opening_final_message__L32", "opening_final_message__L4", "opening_final_message__L8", "opening_fold",
    "opening_ood_point", "opening_row_weights__L4_L0", "opening_row_weights__L6_L1", "verify_merkle_cap__L4",
    "verify_merkle_cap__L5", "verify_merkle_cap__L6", "verify_merkle_cap__L7", "verify_merkle_cap__L8"]

/-- A function's calls stay in `osInjZ` if it is in it. -/
def osInjZOk (fn : Fn) : Bool := !(osInjZ.contains fn.name) || (Stmt.blockCallees fn.body).all osInjZ.contains

set_option maxRecDepth 100000 in
theorem osInjZ_ok0 : ((coreProgram.drop 0).take 100).all osInjZOk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem osInjZ_ok100 : ((coreProgram.drop 100).take 100).all osInjZOk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem osInjZ_ok200 : ((coreProgram.drop 200).take 100).all osInjZOk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem osInjZ_ok300 : ((coreProgram.drop 300).take 100).all osInjZOk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem osInjZ_ok400 : ((coreProgram.drop 400).take 100).all osInjZOk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem osInjZ_ok500 : ((coreProgram.drop 500).take 100).all osInjZOk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem osInjZ_ok600 : ((coreProgram.drop 600).take 100).all osInjZOk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem osInjZ_ok700 : ((coreProgram.drop 700).take 100).all osInjZOk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem osInjZ_ok800 : ((coreProgram.drop 800).take 100).all osInjZOk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem osInjZ_ok900 : ((coreProgram.drop 900).take 100).all osInjZOk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem osInjZ_ok1000 : ((coreProgram.drop 1000).take 100).all osInjZOk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem osInjZ_not : osInjZ.all (fun f => !osInjNames.contains f) = true := by decide +kernel

theorem osInjZ_ok_mem {fn : Fn} (h : fn ∈ coreProgram) : osInjZOk fn = true := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem h
  have hl := coreProgram_length
  have chunk : ∀ a, a ≤ i → i < a + 100 → ((coreProgram.drop a).take 100).all osInjZOk = true →
      osInjZOk coreProgram[i] = true := fun a h1 h2 hc => by
    have hm : coreProgram[i] ∈ (coreProgram.drop a).take 100 := by
      rw [List.mem_iff_getElem]
      refine ⟨i - a, by simp; omega, ?_⟩
      simp only [List.getElem_take, List.getElem_drop]
      congr 1; omega
    exact List.all_eq_true.mp hc _ hm
  have hq : i / 100 ≤ 10 := by omega
  interval_cases hq' : i / 100
  · exact chunk 0 (by omega) (by omega) osInjZ_ok0
  · exact chunk 100 (by omega) (by omega) osInjZ_ok100
  · exact chunk 200 (by omega) (by omega) osInjZ_ok200
  · exact chunk 300 (by omega) (by omega) osInjZ_ok300
  · exact chunk 400 (by omega) (by omega) osInjZ_ok400
  · exact chunk 500 (by omega) (by omega) osInjZ_ok500
  · exact chunk 600 (by omega) (by omega) osInjZ_ok600
  · exact chunk 700 (by omega) (by omega) osInjZ_ok700
  · exact chunk 800 (by omega) (by omega) osInjZ_ok800
  · exact chunk 900 (by omega) (by omega) osInjZ_ok900
  · exact chunk 1000 (by omega) (by omega) osInjZ_ok1000

/-- **`osInjZ` is closed under calls.** -/
theorem osInjZ_callsIn : CallsIn coreProgram (· ∈ osInjZ) := by
  refine callsIn_of_callees fun f hf fn hfn g hg => ?_
  have h' : List.find? (fun g ↦ g.name == f) coreProgram = some fn := hfn
  have hmem := List.mem_of_find?_eq_some h'
  have hname : fn.name = f := by simpa using List.find?_some h'
  have hok := osInjZ_ok_mem hmem
  simp only [osInjZOk, hname, Bool.or_eq_true, Bool.not_true,
    List.contains_iff_mem.mpr hf] at hok
  rcases hok with h | h
  · exact absurd h (by simp)
  · exact List.contains_iff_mem.mp (List.all_eq_true.mp h g hg)

theorem osInjZ_notMem {f : String} (h : f ∈ osInjZ) : f ∉ osInjNames := by
  have := List.all_eq_true.mp osInjZ_not f h
  simpa using this

end
end LeanVM.Guest.B1
