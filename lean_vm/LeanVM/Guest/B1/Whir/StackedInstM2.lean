/-
  LeanVM.Guest.B1.Whir.StackedInstM2

  The `open_stacked` specializations of `Whir/StackedInst2.lean` are sound under a hash model.
-/

module

public import LeanVM.Guest.B1.Whir.StackedSoundM
public import LeanVM.Guest.B1.Whir.StackedInst2
public import LeanVM.Guest.B1.Whir.QueriesSpecM

/-!
# `open_stacked` at its candidates under a hash model (2)

For each candidate of `Whir/StackedInst2.lean`: its configuration's facts (`osCfgOk_…`, as
there), its callees' meanings under the model (`OsCalleesM`: the specialized callees' generic
lemmas, the hash-free ones by transfer), and `open_stacked_model` at them.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Protocol.Verifier
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Guest.B1.VerifySub

@[expose] public section

/-- The callees of `open_stacked__L14` under a hash model. -/
theorem osCalleesM_14 (M : HashModel) (rd : Reader) : OsCalleesM M rd osCfg14 where
  lv := fun i hi => by
    have : i < 4 := hi
    interval_cases i
    · exact ⟨fun a r h => (opening_row_weights_L6_L1_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L7_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L1_L64_L8_L19_L7_model hn hq h, fun a r h => (decode_query_bits_L19_iffB rd a r).mp h,
        ⟨Data.core764, os_sq_find_14_0, rfl, os_sq_body_14_0⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L6_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L18_L6_model hn hq h, fun a r h => (decode_query_bits_L18_iffB rd a r).mp h,
        ⟨Data.core765, os_sq_find_14_1, rfl, os_sq_body_14_1⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L5_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L17_L5_model hn hq h, fun a r h => (decode_query_bits_L17_iffB rd a r).mp h,
        ⟨Data.core766, os_sq_find_14_2, rfl, os_sq_body_14_2⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L5_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L16_L5_model hn hq h, fun a r h => (decode_query_bits_L16_iffB rd a r).mp h,
        ⟨Data.core767, os_sq_find_14_3, rfl, os_sq_body_14_3⟩⟩
  fin := fun a r h => opening_final_message_L16_model rd a r h
  ff := fun a r h => (fold_final_msg_L4_iffB rd a r).mp h
  res := fun i hi => by
    have : i < 4 := hi
    interval_cases i
    exacts [⟨Data.core768, os_res_find_14_0, rfl, os_res_body_14_0⟩, ⟨Data.core769, os_res_find_14_1, rfl, os_res_body_14_1⟩, ⟨Data.core770, os_res_find_14_2, rfl, os_res_body_14_2⟩, ⟨Data.core771, os_res_find_14_3, rfl, os_res_body_14_3⟩]

/-- **`open_stacked__L14`** (`μ = 22`, `r = 3`) is sound under a hash model. -/
theorem open_stacked_L14_model {M : HashModel} {rd : Reader} {root : Digest}
    {fs0 fs1 target root0 root1 cur : E} {rets : List E} (hroot : (root0, root1) = digestScalars root)
    (h : coreProgram.RelB M.sem rd "open_stacked__L14" [fs0, fs1, target, root0, root1, cur] rets) :
    OpenOutM M rd 22 3 root fs0 fs1 target cur rets :=
  open_stacked_model osCfgOk_14 os_find_14 rfl os_body_14 (osCalleesM_14 M rd) hroot h

/-- The callees of `open_stacked__L15` under a hash model. -/
theorem osCalleesM_15 (M : HashModel) (rd : Reader) : OsCalleesM M rd osCfg15 where
  lv := fun i hi => by
    have : i < 4 := hi
    interval_cases i
    · exact ⟨fun a r h => (opening_row_weights_L6_L1_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L7_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L1_L64_L8_L20_L7_model hn hq h, fun a r h => (decode_query_bits_L20_iffB rd a r).mp h,
        ⟨Data.core772, os_sq_find_15_0, rfl, os_sq_body_15_0⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L6_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L19_L6_model hn hq h, fun a r h => (decode_query_bits_L19_iffB rd a r).mp h,
        ⟨Data.core773, os_sq_find_15_1, rfl, os_sq_body_15_1⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L5_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L18_L5_model hn hq h, fun a r h => (decode_query_bits_L18_iffB rd a r).mp h,
        ⟨Data.core774, os_sq_find_15_2, rfl, os_sq_body_15_2⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L5_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L17_L5_model hn hq h, fun a r h => (decode_query_bits_L17_iffB rd a r).mp h,
        ⟨Data.core775, os_sq_find_15_3, rfl, os_sq_body_15_3⟩⟩
  fin := fun a r h => opening_final_message_L32_model rd a r h
  ff := fun a r h => (fold_final_msg_L5_iffB rd a r).mp h
  res := fun i hi => by
    have : i < 4 := hi
    interval_cases i
    exacts [⟨Data.core776, os_res_find_15_0, rfl, os_res_body_15_0⟩, ⟨Data.core777, os_res_find_15_1, rfl, os_res_body_15_1⟩, ⟨Data.core778, os_res_find_15_2, rfl, os_res_body_15_2⟩, ⟨Data.core779, os_res_find_15_3, rfl, os_res_body_15_3⟩]

/-- **`open_stacked__L15`** (`μ = 23`, `r = 3`) is sound under a hash model. -/
theorem open_stacked_L15_model {M : HashModel} {rd : Reader} {root : Digest}
    {fs0 fs1 target root0 root1 cur : E} {rets : List E} (hroot : (root0, root1) = digestScalars root)
    (h : coreProgram.RelB M.sem rd "open_stacked__L15" [fs0, fs1, target, root0, root1, cur] rets) :
    OpenOutM M rd 23 3 root fs0 fs1 target cur rets :=
  open_stacked_model osCfgOk_15 os_find_15 rfl os_body_15 (osCalleesM_15 M rd) hroot h

/-- The callees of `open_stacked__L16` under a hash model. -/
theorem osCalleesM_16 (M : HashModel) (rd : Reader) : OsCalleesM M rd osCfg16 where
  lv := fun i hi => by
    have : i < 5 := hi
    interval_cases i
    · exact ⟨fun a r h => (opening_row_weights_L6_L1_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L7_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L1_L64_L8_L21_L7_model hn hq h, fun a r h => (decode_query_bits_L21_iffB rd a r).mp h,
        ⟨Data.core780, os_sq_find_16_0, rfl, os_sq_body_16_0⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L6_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L20_L6_model hn hq h, fun a r h => (decode_query_bits_L20_iffB rd a r).mp h,
        ⟨Data.core781, os_sq_find_16_1, rfl, os_sq_body_16_1⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L5_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L19_L5_model hn hq h, fun a r h => (decode_query_bits_L19_iffB rd a r).mp h,
        ⟨Data.core782, os_sq_find_16_2, rfl, os_sq_body_16_2⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L5_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L18_L5_model hn hq h, fun a r h => (decode_query_bits_L18_iffB rd a r).mp h,
        ⟨Data.core783, os_sq_find_16_3, rfl, os_sq_body_16_3⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L4_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L17_L4_model hn hq h, fun a r h => (decode_query_bits_L17_iffB rd a r).mp h,
        ⟨Data.core784, os_sq_find_16_4, rfl, os_sq_body_16_4⟩⟩
  fin := fun a r h => opening_final_message_L4_model rd a r h
  ff := fun a r h => (fold_final_msg_L2_iffB rd a r).mp h
  res := fun i hi => by
    have : i < 5 := hi
    interval_cases i
    exacts [⟨Data.core785, os_res_find_16_0, rfl, os_res_body_16_0⟩, ⟨Data.core786, os_res_find_16_1, rfl, os_res_body_16_1⟩, ⟨Data.core787, os_res_find_16_2, rfl, os_res_body_16_2⟩, ⟨Data.core788, os_res_find_16_3, rfl, os_res_body_16_3⟩, ⟨Data.core789, os_res_find_16_4, rfl, os_res_body_16_4⟩]

/-- **`open_stacked__L16`** (`μ = 24`, `r = 3`) is sound under a hash model. -/
theorem open_stacked_L16_model {M : HashModel} {rd : Reader} {root : Digest}
    {fs0 fs1 target root0 root1 cur : E} {rets : List E} (hroot : (root0, root1) = digestScalars root)
    (h : coreProgram.RelB M.sem rd "open_stacked__L16" [fs0, fs1, target, root0, root1, cur] rets) :
    OpenOutM M rd 24 3 root fs0 fs1 target cur rets :=
  open_stacked_model osCfgOk_16 os_find_16 rfl os_body_16 (osCalleesM_16 M rd) hroot h

/-- The callees of `open_stacked__L17` under a hash model. -/
theorem osCalleesM_17 (M : HashModel) (rd : Reader) : OsCalleesM M rd osCfg17 where
  lv := fun i hi => by
    have : i < 5 := hi
    interval_cases i
    · exact ⟨fun a r h => (opening_row_weights_L6_L1_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L7_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L1_L64_L8_L22_L7_model hn hq h, fun a r h => (decode_query_bits_L22_iffB rd a r).mp h,
        ⟨Data.core790, os_sq_find_17_0, rfl, os_sq_body_17_0⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L6_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L21_L6_model hn hq h, fun a r h => (decode_query_bits_L21_iffB rd a r).mp h,
        ⟨Data.core791, os_sq_find_17_1, rfl, os_sq_body_17_1⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L5_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L20_L5_model hn hq h, fun a r h => (decode_query_bits_L20_iffB rd a r).mp h,
        ⟨Data.core792, os_sq_find_17_2, rfl, os_sq_body_17_2⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L5_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L19_L5_model hn hq h, fun a r h => (decode_query_bits_L19_iffB rd a r).mp h,
        ⟨Data.core793, os_sq_find_17_3, rfl, os_sq_body_17_3⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L4_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L18_L4_model hn hq h, fun a r h => (decode_query_bits_L18_iffB rd a r).mp h,
        ⟨Data.core794, os_sq_find_17_4, rfl, os_sq_body_17_4⟩⟩
  fin := fun a r h => opening_final_message_L8_model rd a r h
  ff := fun a r h => (fold_final_msg_L3_iffB rd a r).mp h
  res := fun i hi => by
    have : i < 5 := hi
    interval_cases i
    exacts [⟨Data.core795, os_res_find_17_0, rfl, os_res_body_17_0⟩, ⟨Data.core796, os_res_find_17_1, rfl, os_res_body_17_1⟩, ⟨Data.core797, os_res_find_17_2, rfl, os_res_body_17_2⟩, ⟨Data.core798, os_res_find_17_3, rfl, os_res_body_17_3⟩, ⟨Data.core799, os_res_find_17_4, rfl, os_res_body_17_4⟩]

/-- **`open_stacked__L17`** (`μ = 25`, `r = 3`) is sound under a hash model. -/
theorem open_stacked_L17_model {M : HashModel} {rd : Reader} {root : Digest}
    {fs0 fs1 target root0 root1 cur : E} {rets : List E} (hroot : (root0, root1) = digestScalars root)
    (h : coreProgram.RelB M.sem rd "open_stacked__L17" [fs0, fs1, target, root0, root1, cur] rets) :
    OpenOutM M rd 25 3 root fs0 fs1 target cur rets :=
  open_stacked_model osCfgOk_17 os_find_17 rfl os_body_17 (osCalleesM_17 M rd) hroot h

/-- The callees of `open_stacked__L18` under a hash model. -/
theorem osCalleesM_18 (M : HashModel) (rd : Reader) : OsCalleesM M rd osCfg18 where
  lv := fun i hi => by
    have : i < 5 := hi
    interval_cases i
    · exact ⟨fun a r h => (opening_row_weights_L6_L1_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L7_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L1_L64_L8_L23_L7_model hn hq h, fun a r h => (decode_query_bits_L23_iffB rd a r).mp h,
        ⟨Data.core800, os_sq_find_18_0, rfl, os_sq_body_18_0⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L6_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L22_L6_model hn hq h, fun a r h => (decode_query_bits_L22_iffB rd a r).mp h,
        ⟨Data.core801, os_sq_find_18_1, rfl, os_sq_body_18_1⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L5_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L21_L5_model hn hq h, fun a r h => (decode_query_bits_L21_iffB rd a r).mp h,
        ⟨Data.core802, os_sq_find_18_2, rfl, os_sq_body_18_2⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L5_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L20_L5_model hn hq h, fun a r h => (decode_query_bits_L20_iffB rd a r).mp h,
        ⟨Data.core803, os_sq_find_18_3, rfl, os_sq_body_18_3⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L4_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L19_L4_model hn hq h, fun a r h => (decode_query_bits_L19_iffB rd a r).mp h,
        ⟨Data.core804, os_sq_find_18_4, rfl, os_sq_body_18_4⟩⟩
  fin := fun a r h => opening_final_message_L16_model rd a r h
  ff := fun a r h => (fold_final_msg_L4_iffB rd a r).mp h
  res := fun i hi => by
    have : i < 5 := hi
    interval_cases i
    exacts [⟨Data.core805, os_res_find_18_0, rfl, os_res_body_18_0⟩, ⟨Data.core806, os_res_find_18_1, rfl, os_res_body_18_1⟩, ⟨Data.core807, os_res_find_18_2, rfl, os_res_body_18_2⟩, ⟨Data.core808, os_res_find_18_3, rfl, os_res_body_18_3⟩, ⟨Data.core809, os_res_find_18_4, rfl, os_res_body_18_4⟩]

/-- **`open_stacked__L18`** (`μ = 26`, `r = 3`) is sound under a hash model. -/
theorem open_stacked_L18_model {M : HashModel} {rd : Reader} {root : Digest}
    {fs0 fs1 target root0 root1 cur : E} {rets : List E} (hroot : (root0, root1) = digestScalars root)
    (h : coreProgram.RelB M.sem rd "open_stacked__L18" [fs0, fs1, target, root0, root1, cur] rets) :
    OpenOutM M rd 26 3 root fs0 fs1 target cur rets :=
  open_stacked_model osCfgOk_18 os_find_18 rfl os_body_18 (osCalleesM_18 M rd) hroot h

/-- The callees of `open_stacked__L19` under a hash model. -/
theorem osCalleesM_19 (M : HashModel) (rd : Reader) : OsCalleesM M rd osCfg19 where
  lv := fun i hi => by
    have : i < 5 := hi
    interval_cases i
    · exact ⟨fun a r h => (opening_row_weights_L6_L1_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L7_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L1_L64_L8_L24_L7_model hn hq h, fun a r h => (decode_query_bits_L24_iffB rd a r).mp h,
        ⟨Data.core810, os_sq_find_19_0, rfl, os_sq_body_19_0⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L6_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L23_L6_model hn hq h, fun a r h => (decode_query_bits_L23_iffB rd a r).mp h,
        ⟨Data.core811, os_sq_find_19_1, rfl, os_sq_body_19_1⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L5_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L22_L5_model hn hq h, fun a r h => (decode_query_bits_L22_iffB rd a r).mp h,
        ⟨Data.core812, os_sq_find_19_2, rfl, os_sq_body_19_2⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L5_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L21_L5_model hn hq h, fun a r h => (decode_query_bits_L21_iffB rd a r).mp h,
        ⟨Data.core813, os_sq_find_19_3, rfl, os_sq_body_19_3⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L4_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L20_L4_model hn hq h, fun a r h => (decode_query_bits_L20_iffB rd a r).mp h,
        ⟨Data.core814, os_sq_find_19_4, rfl, os_sq_body_19_4⟩⟩
  fin := fun a r h => opening_final_message_L32_model rd a r h
  ff := fun a r h => (fold_final_msg_L5_iffB rd a r).mp h
  res := fun i hi => by
    have : i < 5 := hi
    interval_cases i
    exacts [⟨Data.core815, os_res_find_19_0, rfl, os_res_body_19_0⟩, ⟨Data.core816, os_res_find_19_1, rfl, os_res_body_19_1⟩, ⟨Data.core817, os_res_find_19_2, rfl, os_res_body_19_2⟩, ⟨Data.core818, os_res_find_19_3, rfl, os_res_body_19_3⟩, ⟨Data.core819, os_res_find_19_4, rfl, os_res_body_19_4⟩]

/-- **`open_stacked__L19`** (`μ = 27`, `r = 3`) is sound under a hash model. -/
theorem open_stacked_L19_model {M : HashModel} {rd : Reader} {root : Digest}
    {fs0 fs1 target root0 root1 cur : E} {rets : List E} (hroot : (root0, root1) = digestScalars root)
    (h : coreProgram.RelB M.sem rd "open_stacked__L19" [fs0, fs1, target, root0, root1, cur] rets) :
    OpenOutM M rd 27 3 root fs0 fs1 target cur rets :=
  open_stacked_model osCfgOk_19 os_find_19 rfl os_body_19 (osCalleesM_19 M rd) hroot h

/-- The callees of `open_stacked__L20` under a hash model. -/
theorem osCalleesM_20 (M : HashModel) (rd : Reader) : OsCalleesM M rd osCfg20 where
  lv := fun i hi => by
    have : i < 6 := hi
    interval_cases i
    · exact ⟨fun a r h => (opening_row_weights_L6_L1_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L7_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L1_L64_L8_L25_L7_model hn hq h, fun a r h => (decode_query_bits_L25_iffB rd a r).mp h,
        ⟨Data.core820, os_sq_find_20_0, rfl, os_sq_body_20_0⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L6_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L24_L6_model hn hq h, fun a r h => (decode_query_bits_L24_iffB rd a r).mp h,
        ⟨Data.core822, os_sq_find_20_1, rfl, os_sq_body_20_1⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L5_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L23_L5_model hn hq h, fun a r h => (decode_query_bits_L23_iffB rd a r).mp h,
        ⟨Data.core824, os_sq_find_20_2, rfl, os_sq_body_20_2⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L5_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L22_L5_model hn hq h, fun a r h => (decode_query_bits_L22_iffB rd a r).mp h,
        ⟨Data.core826, os_sq_find_20_3, rfl, os_sq_body_20_3⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L4_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L21_L4_model hn hq h, fun a r h => (decode_query_bits_L21_iffB rd a r).mp h,
        ⟨Data.core827, os_sq_find_20_4, rfl, os_sq_body_20_4⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L4_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L20_L4_model hn hq h, fun a r h => (decode_query_bits_L20_iffB rd a r).mp h,
        ⟨Data.core829, os_sq_find_20_5, rfl, os_sq_body_20_5⟩⟩
  fin := fun a r h => opening_final_message_L4_model rd a r h
  ff := fun a r h => (fold_final_msg_L2_iffB rd a r).mp h
  res := fun i hi => by
    have : i < 6 := hi
    interval_cases i
    exacts [⟨Data.core830, os_res_find_20_0, rfl, os_res_body_20_0⟩, ⟨Data.core831, os_res_find_20_1, rfl, os_res_body_20_1⟩, ⟨Data.core832, os_res_find_20_2, rfl, os_res_body_20_2⟩, ⟨Data.core833, os_res_find_20_3, rfl, os_res_body_20_3⟩, ⟨Data.core834, os_res_find_20_4, rfl, os_res_body_20_4⟩, ⟨Data.core835, os_res_find_20_5, rfl, os_res_body_20_5⟩]

/-- **`open_stacked__L20`** (`μ = 28`, `r = 3`) is sound under a hash model. -/
theorem open_stacked_L20_model {M : HashModel} {rd : Reader} {root : Digest}
    {fs0 fs1 target root0 root1 cur : E} {rets : List E} (hroot : (root0, root1) = digestScalars root)
    (h : coreProgram.RelB M.sem rd "open_stacked__L20" [fs0, fs1, target, root0, root1, cur] rets) :
    OpenOutM M rd 28 3 root fs0 fs1 target cur rets :=
  open_stacked_model osCfgOk_20 os_find_20 rfl os_body_20 (osCalleesM_20 M rd) hroot h

end
end LeanVM.Guest.B1
