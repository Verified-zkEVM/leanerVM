/-
  LeanVM.Guest.B1.Whir.StackedInstM1

  The `open_stacked` specializations of `Whir/StackedInst1.lean` are sound under a hash model.
-/

module

public import LeanVM.Guest.B1.Whir.StackedSoundM
public import LeanVM.Guest.B1.Whir.StackedInst1
public import LeanVM.Guest.B1.Whir.QueriesSpecM

/-!
# `open_stacked` at its candidates under a hash model (1)

For each candidate of `Whir/StackedInst1.lean`: its configuration's facts (`osCfgOk_…`, as
there), its callees' meanings under the model (`OsCalleesM`: the specialized callees' generic
lemmas, the hash-free ones by transfer), and `open_stacked_model` at them.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Protocol.Verifier
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Guest.B1.VerifySub

@[expose] public section

/-- The callees of `open_stacked__L7` under a hash model. -/
theorem osCalleesM_7 (M : HashModel) (rd : Reader) : OsCalleesM M rd osCfg7 where
  lv := fun i hi => by
    have : i < 4 := hi
    interval_cases i
    · exact ⟨fun a r h => (opening_row_weights_L6_L1_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L7_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L1_L64_L8_L18_L7_model hn hq h, fun a r h => (decode_query_bits_L18_iffB rd a r).mp h,
        ⟨Data.core682, os_sq_find_7_0, rfl, os_sq_body_7_0⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L6_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L17_L6_model hn hq h, fun a r h => (decode_query_bits_L17_iffB rd a r).mp h,
        ⟨Data.core685, os_sq_find_7_1, rfl, os_sq_body_7_1⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L5_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L16_L5_model hn hq h, fun a r h => (decode_query_bits_L16_iffB rd a r).mp h,
        ⟨Data.core686, os_sq_find_7_2, rfl, os_sq_body_7_2⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L5_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L15_L5_model hn hq h, fun a r h => (decode_query_bits_L15_iffB rd a r).mp h,
        ⟨Data.core687, os_sq_find_7_3, rfl, os_sq_body_7_3⟩⟩
  fin := fun a r h => opening_final_message_L16_model rd a r h
  ff := fun a r h => (fold_final_msg_L4_iffB rd a r).mp h
  res := fun i hi => by
    have : i < 4 := hi
    interval_cases i
    exacts [⟨Data.core688, os_res_find_7_0, rfl, os_res_body_7_0⟩, ⟨Data.core689, os_res_find_7_1, rfl, os_res_body_7_1⟩, ⟨Data.core690, os_res_find_7_2, rfl, os_res_body_7_2⟩, ⟨Data.core691, os_res_find_7_3, rfl, os_res_body_7_3⟩]

/-- **`open_stacked__L7`** (`μ = 22`, `r = 2`) is sound under a hash model. -/
theorem open_stacked_L7_model {M : HashModel} {rd : Reader} {root : Digest}
    {fs0 fs1 target root0 root1 cur : E} {rets : List E} (hroot : (root0, root1) = digestScalars root)
    (h : coreProgram.RelB M.sem rd "open_stacked__L7" [fs0, fs1, target, root0, root1, cur] rets) :
    OpenOutM M rd 22 2 root fs0 fs1 target cur rets :=
  open_stacked_model osCfgOk_7 os_find_7 rfl os_body_7 (osCalleesM_7 M rd) hroot h

/-- The callees of `open_stacked__L8` under a hash model. -/
theorem osCalleesM_8 (M : HashModel) (rd : Reader) : OsCalleesM M rd osCfg8 where
  lv := fun i hi => by
    have : i < 4 := hi
    interval_cases i
    · exact ⟨fun a r h => (opening_row_weights_L6_L1_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L7_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L1_L64_L8_L19_L7_model hn hq h, fun a r h => (decode_query_bits_L19_iffB rd a r).mp h,
        ⟨Data.core692, os_sq_find_8_0, rfl, os_sq_body_8_0⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L6_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L18_L6_model hn hq h, fun a r h => (decode_query_bits_L18_iffB rd a r).mp h,
        ⟨Data.core694, os_sq_find_8_1, rfl, os_sq_body_8_1⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L5_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L17_L5_model hn hq h, fun a r h => (decode_query_bits_L17_iffB rd a r).mp h,
        ⟨Data.core695, os_sq_find_8_2, rfl, os_sq_body_8_2⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L5_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L16_L5_model hn hq h, fun a r h => (decode_query_bits_L16_iffB rd a r).mp h,
        ⟨Data.core696, os_sq_find_8_3, rfl, os_sq_body_8_3⟩⟩
  fin := fun a r h => opening_final_message_L32_model rd a r h
  ff := fun a r h => (fold_final_msg_L5_iffB rd a r).mp h
  res := fun i hi => by
    have : i < 4 := hi
    interval_cases i
    exacts [⟨Data.core697, os_res_find_8_0, rfl, os_res_body_8_0⟩, ⟨Data.core698, os_res_find_8_1, rfl, os_res_body_8_1⟩, ⟨Data.core699, os_res_find_8_2, rfl, os_res_body_8_2⟩, ⟨Data.core700, os_res_find_8_3, rfl, os_res_body_8_3⟩]

/-- **`open_stacked__L8`** (`μ = 23`, `r = 2`) is sound under a hash model. -/
theorem open_stacked_L8_model {M : HashModel} {rd : Reader} {root : Digest}
    {fs0 fs1 target root0 root1 cur : E} {rets : List E} (hroot : (root0, root1) = digestScalars root)
    (h : coreProgram.RelB M.sem rd "open_stacked__L8" [fs0, fs1, target, root0, root1, cur] rets) :
    OpenOutM M rd 23 2 root fs0 fs1 target cur rets :=
  open_stacked_model osCfgOk_8 os_find_8 rfl os_body_8 (osCalleesM_8 M rd) hroot h

/-- The callees of `open_stacked__L9` under a hash model. -/
theorem osCalleesM_9 (M : HashModel) (rd : Reader) : OsCalleesM M rd osCfg9 where
  lv := fun i hi => by
    have : i < 5 := hi
    interval_cases i
    · exact ⟨fun a r h => (opening_row_weights_L6_L1_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L7_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L1_L64_L8_L20_L7_model hn hq h, fun a r h => (decode_query_bits_L20_iffB rd a r).mp h,
        ⟨Data.core701, os_sq_find_9_0, rfl, os_sq_body_9_0⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L6_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L19_L6_model hn hq h, fun a r h => (decode_query_bits_L19_iffB rd a r).mp h,
        ⟨Data.core703, os_sq_find_9_1, rfl, os_sq_body_9_1⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L5_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L18_L5_model hn hq h, fun a r h => (decode_query_bits_L18_iffB rd a r).mp h,
        ⟨Data.core704, os_sq_find_9_2, rfl, os_sq_body_9_2⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L5_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L17_L5_model hn hq h, fun a r h => (decode_query_bits_L17_iffB rd a r).mp h,
        ⟨Data.core705, os_sq_find_9_3, rfl, os_sq_body_9_3⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L4_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L16_L4_model hn hq h, fun a r h => (decode_query_bits_L16_iffB rd a r).mp h,
        ⟨Data.core706, os_sq_find_9_4, rfl, os_sq_body_9_4⟩⟩
  fin := fun a r h => opening_final_message_L4_model rd a r h
  ff := fun a r h => (fold_final_msg_L2_iffB rd a r).mp h
  res := fun i hi => by
    have : i < 5 := hi
    interval_cases i
    exacts [⟨Data.core708, os_res_find_9_0, rfl, os_res_body_9_0⟩, ⟨Data.core709, os_res_find_9_1, rfl, os_res_body_9_1⟩, ⟨Data.core710, os_res_find_9_2, rfl, os_res_body_9_2⟩, ⟨Data.core711, os_res_find_9_3, rfl, os_res_body_9_3⟩, ⟨Data.core712, os_res_find_9_4, rfl, os_res_body_9_4⟩]

/-- **`open_stacked__L9`** (`μ = 24`, `r = 2`) is sound under a hash model. -/
theorem open_stacked_L9_model {M : HashModel} {rd : Reader} {root : Digest}
    {fs0 fs1 target root0 root1 cur : E} {rets : List E} (hroot : (root0, root1) = digestScalars root)
    (h : coreProgram.RelB M.sem rd "open_stacked__L9" [fs0, fs1, target, root0, root1, cur] rets) :
    OpenOutM M rd 24 2 root fs0 fs1 target cur rets :=
  open_stacked_model osCfgOk_9 os_find_9 rfl os_body_9 (osCalleesM_9 M rd) hroot h

/-- The callees of `open_stacked__L10` under a hash model. -/
theorem osCalleesM_10 (M : HashModel) (rd : Reader) : OsCalleesM M rd osCfg10 where
  lv := fun i hi => by
    have : i < 5 := hi
    interval_cases i
    · exact ⟨fun a r h => (opening_row_weights_L6_L1_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L7_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L1_L64_L8_L21_L7_model hn hq h, fun a r h => (decode_query_bits_L21_iffB rd a r).mp h,
        ⟨Data.core713, os_sq_find_10_0, rfl, os_sq_body_10_0⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L6_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L20_L6_model hn hq h, fun a r h => (decode_query_bits_L20_iffB rd a r).mp h,
        ⟨Data.core715, os_sq_find_10_1, rfl, os_sq_body_10_1⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L5_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L19_L5_model hn hq h, fun a r h => (decode_query_bits_L19_iffB rd a r).mp h,
        ⟨Data.core716, os_sq_find_10_2, rfl, os_sq_body_10_2⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L5_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L18_L5_model hn hq h, fun a r h => (decode_query_bits_L18_iffB rd a r).mp h,
        ⟨Data.core717, os_sq_find_10_3, rfl, os_sq_body_10_3⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L4_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L17_L4_model hn hq h, fun a r h => (decode_query_bits_L17_iffB rd a r).mp h,
        ⟨Data.core718, os_sq_find_10_4, rfl, os_sq_body_10_4⟩⟩
  fin := fun a r h => opening_final_message_L8_model rd a r h
  ff := fun a r h => (fold_final_msg_L3_iffB rd a r).mp h
  res := fun i hi => by
    have : i < 5 := hi
    interval_cases i
    exacts [⟨Data.core720, os_res_find_10_0, rfl, os_res_body_10_0⟩, ⟨Data.core721, os_res_find_10_1, rfl, os_res_body_10_1⟩, ⟨Data.core722, os_res_find_10_2, rfl, os_res_body_10_2⟩, ⟨Data.core723, os_res_find_10_3, rfl, os_res_body_10_3⟩, ⟨Data.core724, os_res_find_10_4, rfl, os_res_body_10_4⟩]

/-- **`open_stacked__L10`** (`μ = 25`, `r = 2`) is sound under a hash model. -/
theorem open_stacked_L10_model {M : HashModel} {rd : Reader} {root : Digest}
    {fs0 fs1 target root0 root1 cur : E} {rets : List E} (hroot : (root0, root1) = digestScalars root)
    (h : coreProgram.RelB M.sem rd "open_stacked__L10" [fs0, fs1, target, root0, root1, cur] rets) :
    OpenOutM M rd 25 2 root fs0 fs1 target cur rets :=
  open_stacked_model osCfgOk_10 os_find_10 rfl os_body_10 (osCalleesM_10 M rd) hroot h

/-- The callees of `open_stacked__L11` under a hash model. -/
theorem osCalleesM_11 (M : HashModel) (rd : Reader) : OsCalleesM M rd osCfg11 where
  lv := fun i hi => by
    have : i < 5 := hi
    interval_cases i
    · exact ⟨fun a r h => (opening_row_weights_L6_L1_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L7_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L1_L64_L8_L22_L7_model hn hq h, fun a r h => (decode_query_bits_L22_iffB rd a r).mp h,
        ⟨Data.core725, os_sq_find_11_0, rfl, os_sq_body_11_0⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L6_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L21_L6_model hn hq h, fun a r h => (decode_query_bits_L21_iffB rd a r).mp h,
        ⟨Data.core727, os_sq_find_11_1, rfl, os_sq_body_11_1⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L5_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L20_L5_model hn hq h, fun a r h => (decode_query_bits_L20_iffB rd a r).mp h,
        ⟨Data.core728, os_sq_find_11_2, rfl, os_sq_body_11_2⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L5_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L19_L5_model hn hq h, fun a r h => (decode_query_bits_L19_iffB rd a r).mp h,
        ⟨Data.core729, os_sq_find_11_3, rfl, os_sq_body_11_3⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L4_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L18_L4_model hn hq h, fun a r h => (decode_query_bits_L18_iffB rd a r).mp h,
        ⟨Data.core730, os_sq_find_11_4, rfl, os_sq_body_11_4⟩⟩
  fin := fun a r h => opening_final_message_L16_model rd a r h
  ff := fun a r h => (fold_final_msg_L4_iffB rd a r).mp h
  res := fun i hi => by
    have : i < 5 := hi
    interval_cases i
    exacts [⟨Data.core731, os_res_find_11_0, rfl, os_res_body_11_0⟩, ⟨Data.core732, os_res_find_11_1, rfl, os_res_body_11_1⟩, ⟨Data.core733, os_res_find_11_2, rfl, os_res_body_11_2⟩, ⟨Data.core734, os_res_find_11_3, rfl, os_res_body_11_3⟩, ⟨Data.core735, os_res_find_11_4, rfl, os_res_body_11_4⟩]

/-- **`open_stacked__L11`** (`μ = 26`, `r = 2`) is sound under a hash model. -/
theorem open_stacked_L11_model {M : HashModel} {rd : Reader} {root : Digest}
    {fs0 fs1 target root0 root1 cur : E} {rets : List E} (hroot : (root0, root1) = digestScalars root)
    (h : coreProgram.RelB M.sem rd "open_stacked__L11" [fs0, fs1, target, root0, root1, cur] rets) :
    OpenOutM M rd 26 2 root fs0 fs1 target cur rets :=
  open_stacked_model osCfgOk_11 os_find_11 rfl os_body_11 (osCalleesM_11 M rd) hroot h

/-- The callees of `open_stacked__L12` under a hash model. -/
theorem osCalleesM_12 (M : HashModel) (rd : Reader) : OsCalleesM M rd osCfg12 where
  lv := fun i hi => by
    have : i < 5 := hi
    interval_cases i
    · exact ⟨fun a r h => (opening_row_weights_L6_L1_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L7_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L1_L64_L8_L23_L7_model hn hq h, fun a r h => (decode_query_bits_L23_iffB rd a r).mp h,
        ⟨Data.core736, os_sq_find_12_0, rfl, os_sq_body_12_0⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L6_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L22_L6_model hn hq h, fun a r h => (decode_query_bits_L22_iffB rd a r).mp h,
        ⟨Data.core738, os_sq_find_12_1, rfl, os_sq_body_12_1⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L5_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L21_L5_model hn hq h, fun a r h => (decode_query_bits_L21_iffB rd a r).mp h,
        ⟨Data.core739, os_sq_find_12_2, rfl, os_sq_body_12_2⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L5_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L20_L5_model hn hq h, fun a r h => (decode_query_bits_L20_iffB rd a r).mp h,
        ⟨Data.core740, os_sq_find_12_3, rfl, os_sq_body_12_3⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L4_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L19_L4_model hn hq h, fun a r h => (decode_query_bits_L19_iffB rd a r).mp h,
        ⟨Data.core741, os_sq_find_12_4, rfl, os_sq_body_12_4⟩⟩
  fin := fun a r h => opening_final_message_L32_model rd a r h
  ff := fun a r h => (fold_final_msg_L5_iffB rd a r).mp h
  res := fun i hi => by
    have : i < 5 := hi
    interval_cases i
    exacts [⟨Data.core743, os_res_find_12_0, rfl, os_res_body_12_0⟩, ⟨Data.core744, os_res_find_12_1, rfl, os_res_body_12_1⟩, ⟨Data.core745, os_res_find_12_2, rfl, os_res_body_12_2⟩, ⟨Data.core746, os_res_find_12_3, rfl, os_res_body_12_3⟩, ⟨Data.core747, os_res_find_12_4, rfl, os_res_body_12_4⟩]

/-- **`open_stacked__L12`** (`μ = 27`, `r = 2`) is sound under a hash model. -/
theorem open_stacked_L12_model {M : HashModel} {rd : Reader} {root : Digest}
    {fs0 fs1 target root0 root1 cur : E} {rets : List E} (hroot : (root0, root1) = digestScalars root)
    (h : coreProgram.RelB M.sem rd "open_stacked__L12" [fs0, fs1, target, root0, root1, cur] rets) :
    OpenOutM M rd 27 2 root fs0 fs1 target cur rets :=
  open_stacked_model osCfgOk_12 os_find_12 rfl os_body_12 (osCalleesM_12 M rd) hroot h

/-- The callees of `open_stacked__L13` under a hash model. -/
theorem osCalleesM_13 (M : HashModel) (rd : Reader) : OsCalleesM M rd osCfg13 where
  lv := fun i hi => by
    have : i < 6 := hi
    interval_cases i
    · exact ⟨fun a r h => (opening_row_weights_L6_L1_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L7_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L1_L64_L8_L24_L7_model hn hq h, fun a r h => (decode_query_bits_L24_iffB rd a r).mp h,
        ⟨Data.core748, os_sq_find_13_0, rfl, os_sq_body_13_0⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L6_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L23_L6_model hn hq h, fun a r h => (decode_query_bits_L23_iffB rd a r).mp h,
        ⟨Data.core750, os_sq_find_13_1, rfl, os_sq_body_13_1⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L5_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L22_L5_model hn hq h, fun a r h => (decode_query_bits_L22_iffB rd a r).mp h,
        ⟨Data.core752, os_sq_find_13_2, rfl, os_sq_body_13_2⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L5_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L21_L5_model hn hq h, fun a r h => (decode_query_bits_L21_iffB rd a r).mp h,
        ⟨Data.core754, os_sq_find_13_3, rfl, os_sq_body_13_3⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L4_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L20_L4_model hn hq h, fun a r h => (decode_query_bits_L20_iffB rd a r).mp h,
        ⟨Data.core755, os_sq_find_13_4, rfl, os_sq_body_13_4⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L4_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L19_L4_model hn hq h, fun a r h => (decode_query_bits_L19_iffB rd a r).mp h,
        ⟨Data.core757, os_sq_find_13_5, rfl, os_sq_body_13_5⟩⟩
  fin := fun a r h => opening_final_message_L4_model rd a r h
  ff := fun a r h => (fold_final_msg_L2_iffB rd a r).mp h
  res := fun i hi => by
    have : i < 6 := hi
    interval_cases i
    exacts [⟨Data.core758, os_res_find_13_0, rfl, os_res_body_13_0⟩, ⟨Data.core759, os_res_find_13_1, rfl, os_res_body_13_1⟩, ⟨Data.core760, os_res_find_13_2, rfl, os_res_body_13_2⟩, ⟨Data.core761, os_res_find_13_3, rfl, os_res_body_13_3⟩, ⟨Data.core762, os_res_find_13_4, rfl, os_res_body_13_4⟩, ⟨Data.core763, os_res_find_13_5, rfl, os_res_body_13_5⟩]

/-- **`open_stacked__L13`** (`μ = 28`, `r = 2`) is sound under a hash model. -/
theorem open_stacked_L13_model {M : HashModel} {rd : Reader} {root : Digest}
    {fs0 fs1 target root0 root1 cur : E} {rets : List E} (hroot : (root0, root1) = digestScalars root)
    (h : coreProgram.RelB M.sem rd "open_stacked__L13" [fs0, fs1, target, root0, root1, cur] rets) :
    OpenOutM M rd 28 2 root fs0 fs1 target cur rets :=
  open_stacked_model osCfgOk_13 os_find_13 rfl os_body_13 (osCalleesM_13 M rd) hroot h

end
end LeanVM.Guest.B1
