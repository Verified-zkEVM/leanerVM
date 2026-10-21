/-
  LeanVM.Guest.B1.Whir.StackedInstM3

  The `open_stacked` specializations of `Whir/StackedInst3.lean` are sound under a hash model.
-/

module

public import LeanVM.Guest.B1.Whir.StackedSoundM
public import LeanVM.Guest.B1.Whir.StackedInst3
public import LeanVM.Guest.B1.Whir.QueriesSpecM

/-!
# `open_stacked` at its candidates under a hash model (3)

For each candidate of `Whir/StackedInst3.lean`: its configuration's facts (`osCfgOk_…`, as
there), its callees' meanings under the model (`OsCalleesM`: the specialized callees' generic
lemmas, the hash-free ones by transfer), and `open_stacked_model` at them.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Protocol.Verifier
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Guest.B1.VerifySub

@[expose] public section

/-- The callees of `open_stacked__L21` under a hash model. -/
theorem osCalleesM_21 (M : HashModel) (rd : Reader) : OsCalleesM M rd osCfg21 where
  lv := fun i hi => by
    have : i < 4 := hi
    interval_cases i
    · exact ⟨fun a r h => (opening_row_weights_L6_L1_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L6_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L1_L64_L8_L20_L6_model hn hq h, fun a r h => (decode_query_bits_L20_iffB rd a r).mp h,
        ⟨Data.core836, os_sq_find_21_0, rfl, os_sq_body_21_0⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L5_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L19_L5_model hn hq h, fun a r h => (decode_query_bits_L19_iffB rd a r).mp h,
        ⟨Data.core838, os_sq_find_21_1, rfl, os_sq_body_21_1⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L5_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L18_L5_model hn hq h, fun a r h => (decode_query_bits_L18_iffB rd a r).mp h,
        ⟨Data.core839, os_sq_find_21_2, rfl, os_sq_body_21_2⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L5_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L17_L5_model hn hq h, fun a r h => (decode_query_bits_L17_iffB rd a r).mp h,
        ⟨Data.core840, os_sq_find_21_3, rfl, os_sq_body_21_3⟩⟩
  fin := fun a r h => opening_final_message_L16_model rd a r h
  ff := fun a r h => (fold_final_msg_L4_iffB rd a r).mp h
  res := fun i hi => by
    have : i < 4 := hi
    interval_cases i
    exacts [⟨Data.core841, os_res_find_21_0, rfl, os_res_body_21_0⟩, ⟨Data.core842, os_res_find_21_1, rfl, os_res_body_21_1⟩, ⟨Data.core843, os_res_find_21_2, rfl, os_res_body_21_2⟩, ⟨Data.core844, os_res_find_21_3, rfl, os_res_body_21_3⟩]

/-- **`open_stacked__L21`** (`μ = 22`, `r = 4`) is sound under a hash model. -/
theorem open_stacked_L21_model {M : HashModel} {rd : Reader} {root : Digest}
    {fs0 fs1 target root0 root1 cur : E} {rets : List E} (hroot : (root0, root1) = digestScalars root)
    (h : coreProgram.RelB M.sem rd "open_stacked__L21" [fs0, fs1, target, root0, root1, cur] rets) :
    OpenOutM M rd 22 4 root fs0 fs1 target cur rets :=
  open_stacked_model osCfgOk_21 os_find_21 rfl os_body_21 (osCalleesM_21 M rd) hroot h

/-- The callees of `open_stacked__L22` under a hash model. -/
theorem osCalleesM_22 (M : HashModel) (rd : Reader) : OsCalleesM M rd osCfg22 where
  lv := fun i hi => by
    have : i < 4 := hi
    interval_cases i
    · exact ⟨fun a r h => (opening_row_weights_L6_L1_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L6_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L1_L64_L8_L21_L6_model hn hq h, fun a r h => (decode_query_bits_L21_iffB rd a r).mp h,
        ⟨Data.core845, os_sq_find_22_0, rfl, os_sq_body_22_0⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L5_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L20_L5_model hn hq h, fun a r h => (decode_query_bits_L20_iffB rd a r).mp h,
        ⟨Data.core847, os_sq_find_22_1, rfl, os_sq_body_22_1⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L5_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L19_L5_model hn hq h, fun a r h => (decode_query_bits_L19_iffB rd a r).mp h,
        ⟨Data.core848, os_sq_find_22_2, rfl, os_sq_body_22_2⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L5_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L18_L5_model hn hq h, fun a r h => (decode_query_bits_L18_iffB rd a r).mp h,
        ⟨Data.core849, os_sq_find_22_3, rfl, os_sq_body_22_3⟩⟩
  fin := fun a r h => opening_final_message_L32_model rd a r h
  ff := fun a r h => (fold_final_msg_L5_iffB rd a r).mp h
  res := fun i hi => by
    have : i < 4 := hi
    interval_cases i
    exacts [⟨Data.core850, os_res_find_22_0, rfl, os_res_body_22_0⟩, ⟨Data.core851, os_res_find_22_1, rfl, os_res_body_22_1⟩, ⟨Data.core852, os_res_find_22_2, rfl, os_res_body_22_2⟩, ⟨Data.core853, os_res_find_22_3, rfl, os_res_body_22_3⟩]

/-- **`open_stacked__L22`** (`μ = 23`, `r = 4`) is sound under a hash model. -/
theorem open_stacked_L22_model {M : HashModel} {rd : Reader} {root : Digest}
    {fs0 fs1 target root0 root1 cur : E} {rets : List E} (hroot : (root0, root1) = digestScalars root)
    (h : coreProgram.RelB M.sem rd "open_stacked__L22" [fs0, fs1, target, root0, root1, cur] rets) :
    OpenOutM M rd 23 4 root fs0 fs1 target cur rets :=
  open_stacked_model osCfgOk_22 os_find_22 rfl os_body_22 (osCalleesM_22 M rd) hroot h

/-- The callees of `open_stacked__L23` under a hash model. -/
theorem osCalleesM_23 (M : HashModel) (rd : Reader) : OsCalleesM M rd osCfg23 where
  lv := fun i hi => by
    have : i < 5 := hi
    interval_cases i
    · exact ⟨fun a r h => (opening_row_weights_L6_L1_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L6_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L1_L64_L8_L22_L6_model hn hq h, fun a r h => (decode_query_bits_L22_iffB rd a r).mp h,
        ⟨Data.core854, os_sq_find_23_0, rfl, os_sq_body_23_0⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L5_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L21_L5_model hn hq h, fun a r h => (decode_query_bits_L21_iffB rd a r).mp h,
        ⟨Data.core856, os_sq_find_23_1, rfl, os_sq_body_23_1⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L5_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L20_L5_model hn hq h, fun a r h => (decode_query_bits_L20_iffB rd a r).mp h,
        ⟨Data.core857, os_sq_find_23_2, rfl, os_sq_body_23_2⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L5_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L19_L5_model hn hq h, fun a r h => (decode_query_bits_L19_iffB rd a r).mp h,
        ⟨Data.core858, os_sq_find_23_3, rfl, os_sq_body_23_3⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L4_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L18_L4_model hn hq h, fun a r h => (decode_query_bits_L18_iffB rd a r).mp h,
        ⟨Data.core859, os_sq_find_23_4, rfl, os_sq_body_23_4⟩⟩
  fin := fun a r h => opening_final_message_L4_model rd a r h
  ff := fun a r h => (fold_final_msg_L2_iffB rd a r).mp h
  res := fun i hi => by
    have : i < 5 := hi
    interval_cases i
    exacts [⟨Data.core860, os_res_find_23_0, rfl, os_res_body_23_0⟩, ⟨Data.core861, os_res_find_23_1, rfl, os_res_body_23_1⟩, ⟨Data.core862, os_res_find_23_2, rfl, os_res_body_23_2⟩, ⟨Data.core863, os_res_find_23_3, rfl, os_res_body_23_3⟩, ⟨Data.core864, os_res_find_23_4, rfl, os_res_body_23_4⟩]

/-- **`open_stacked__L23`** (`μ = 24`, `r = 4`) is sound under a hash model. -/
theorem open_stacked_L23_model {M : HashModel} {rd : Reader} {root : Digest}
    {fs0 fs1 target root0 root1 cur : E} {rets : List E} (hroot : (root0, root1) = digestScalars root)
    (h : coreProgram.RelB M.sem rd "open_stacked__L23" [fs0, fs1, target, root0, root1, cur] rets) :
    OpenOutM M rd 24 4 root fs0 fs1 target cur rets :=
  open_stacked_model osCfgOk_23 os_find_23 rfl os_body_23 (osCalleesM_23 M rd) hroot h

/-- The callees of `open_stacked__L24` under a hash model. -/
theorem osCalleesM_24 (M : HashModel) (rd : Reader) : OsCalleesM M rd osCfg24 where
  lv := fun i hi => by
    have : i < 5 := hi
    interval_cases i
    · exact ⟨fun a r h => (opening_row_weights_L6_L1_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L6_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L1_L64_L8_L23_L6_model hn hq h, fun a r h => (decode_query_bits_L23_iffB rd a r).mp h,
        ⟨Data.core865, os_sq_find_24_0, rfl, os_sq_body_24_0⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L5_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L22_L5_model hn hq h, fun a r h => (decode_query_bits_L22_iffB rd a r).mp h,
        ⟨Data.core867, os_sq_find_24_1, rfl, os_sq_body_24_1⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L5_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L21_L5_model hn hq h, fun a r h => (decode_query_bits_L21_iffB rd a r).mp h,
        ⟨Data.core868, os_sq_find_24_2, rfl, os_sq_body_24_2⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L5_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L20_L5_model hn hq h, fun a r h => (decode_query_bits_L20_iffB rd a r).mp h,
        ⟨Data.core869, os_sq_find_24_3, rfl, os_sq_body_24_3⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L4_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L19_L4_model hn hq h, fun a r h => (decode_query_bits_L19_iffB rd a r).mp h,
        ⟨Data.core870, os_sq_find_24_4, rfl, os_sq_body_24_4⟩⟩
  fin := fun a r h => opening_final_message_L8_model rd a r h
  ff := fun a r h => (fold_final_msg_L3_iffB rd a r).mp h
  res := fun i hi => by
    have : i < 5 := hi
    interval_cases i
    exacts [⟨Data.core871, os_res_find_24_0, rfl, os_res_body_24_0⟩, ⟨Data.core872, os_res_find_24_1, rfl, os_res_body_24_1⟩, ⟨Data.core873, os_res_find_24_2, rfl, os_res_body_24_2⟩, ⟨Data.core874, os_res_find_24_3, rfl, os_res_body_24_3⟩, ⟨Data.core875, os_res_find_24_4, rfl, os_res_body_24_4⟩]

/-- **`open_stacked__L24`** (`μ = 25`, `r = 4`) is sound under a hash model. -/
theorem open_stacked_L24_model {M : HashModel} {rd : Reader} {root : Digest}
    {fs0 fs1 target root0 root1 cur : E} {rets : List E} (hroot : (root0, root1) = digestScalars root)
    (h : coreProgram.RelB M.sem rd "open_stacked__L24" [fs0, fs1, target, root0, root1, cur] rets) :
    OpenOutM M rd 25 4 root fs0 fs1 target cur rets :=
  open_stacked_model osCfgOk_24 os_find_24 rfl os_body_24 (osCalleesM_24 M rd) hroot h

/-- The callees of `open_stacked__L25` under a hash model. -/
theorem osCalleesM_25 (M : HashModel) (rd : Reader) : OsCalleesM M rd osCfg25 where
  lv := fun i hi => by
    have : i < 5 := hi
    interval_cases i
    · exact ⟨fun a r h => (opening_row_weights_L6_L1_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L6_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L1_L64_L8_L24_L6_model hn hq h, fun a r h => (decode_query_bits_L24_iffB rd a r).mp h,
        ⟨Data.core876, os_sq_find_25_0, rfl, os_sq_body_25_0⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L5_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L23_L5_model hn hq h, fun a r h => (decode_query_bits_L23_iffB rd a r).mp h,
        ⟨Data.core878, os_sq_find_25_1, rfl, os_sq_body_25_1⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L5_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L22_L5_model hn hq h, fun a r h => (decode_query_bits_L22_iffB rd a r).mp h,
        ⟨Data.core879, os_sq_find_25_2, rfl, os_sq_body_25_2⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L5_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L21_L5_model hn hq h, fun a r h => (decode_query_bits_L21_iffB rd a r).mp h,
        ⟨Data.core880, os_sq_find_25_3, rfl, os_sq_body_25_3⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L4_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L20_L4_model hn hq h, fun a r h => (decode_query_bits_L20_iffB rd a r).mp h,
        ⟨Data.core881, os_sq_find_25_4, rfl, os_sq_body_25_4⟩⟩
  fin := fun a r h => opening_final_message_L16_model rd a r h
  ff := fun a r h => (fold_final_msg_L4_iffB rd a r).mp h
  res := fun i hi => by
    have : i < 5 := hi
    interval_cases i
    exacts [⟨Data.core882, os_res_find_25_0, rfl, os_res_body_25_0⟩, ⟨Data.core883, os_res_find_25_1, rfl, os_res_body_25_1⟩, ⟨Data.core884, os_res_find_25_2, rfl, os_res_body_25_2⟩, ⟨Data.core885, os_res_find_25_3, rfl, os_res_body_25_3⟩, ⟨Data.core886, os_res_find_25_4, rfl, os_res_body_25_4⟩]

/-- **`open_stacked__L25`** (`μ = 26`, `r = 4`) is sound under a hash model. -/
theorem open_stacked_L25_model {M : HashModel} {rd : Reader} {root : Digest}
    {fs0 fs1 target root0 root1 cur : E} {rets : List E} (hroot : (root0, root1) = digestScalars root)
    (h : coreProgram.RelB M.sem rd "open_stacked__L25" [fs0, fs1, target, root0, root1, cur] rets) :
    OpenOutM M rd 26 4 root fs0 fs1 target cur rets :=
  open_stacked_model osCfgOk_25 os_find_25 rfl os_body_25 (osCalleesM_25 M rd) hroot h

/-- The callees of `open_stacked__L26` under a hash model. -/
theorem osCalleesM_26 (M : HashModel) (rd : Reader) : OsCalleesM M rd osCfg26 where
  lv := fun i hi => by
    have : i < 5 := hi
    interval_cases i
    · exact ⟨fun a r h => (opening_row_weights_L6_L1_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L6_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L1_L64_L8_L25_L6_model hn hq h, fun a r h => (decode_query_bits_L25_iffB rd a r).mp h,
        ⟨Data.core887, os_sq_find_26_0, rfl, os_sq_body_26_0⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L5_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L24_L5_model hn hq h, fun a r h => (decode_query_bits_L24_iffB rd a r).mp h,
        ⟨Data.core889, os_sq_find_26_1, rfl, os_sq_body_26_1⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L5_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L23_L5_model hn hq h, fun a r h => (decode_query_bits_L23_iffB rd a r).mp h,
        ⟨Data.core891, os_sq_find_26_2, rfl, os_sq_body_26_2⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L5_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L22_L5_model hn hq h, fun a r h => (decode_query_bits_L22_iffB rd a r).mp h,
        ⟨Data.core892, os_sq_find_26_3, rfl, os_sq_body_26_3⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L4_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L21_L4_model hn hq h, fun a r h => (decode_query_bits_L21_iffB rd a r).mp h,
        ⟨Data.core893, os_sq_find_26_4, rfl, os_sq_body_26_4⟩⟩
  fin := fun a r h => opening_final_message_L32_model rd a r h
  ff := fun a r h => (fold_final_msg_L5_iffB rd a r).mp h
  res := fun i hi => by
    have : i < 5 := hi
    interval_cases i
    exacts [⟨Data.core894, os_res_find_26_0, rfl, os_res_body_26_0⟩, ⟨Data.core895, os_res_find_26_1, rfl, os_res_body_26_1⟩, ⟨Data.core896, os_res_find_26_2, rfl, os_res_body_26_2⟩, ⟨Data.core897, os_res_find_26_3, rfl, os_res_body_26_3⟩, ⟨Data.core898, os_res_find_26_4, rfl, os_res_body_26_4⟩]

/-- **`open_stacked__L26`** (`μ = 27`, `r = 4`) is sound under a hash model. -/
theorem open_stacked_L26_model {M : HashModel} {rd : Reader} {root : Digest}
    {fs0 fs1 target root0 root1 cur : E} {rets : List E} (hroot : (root0, root1) = digestScalars root)
    (h : coreProgram.RelB M.sem rd "open_stacked__L26" [fs0, fs1, target, root0, root1, cur] rets) :
    OpenOutM M rd 27 4 root fs0 fs1 target cur rets :=
  open_stacked_model osCfgOk_26 os_find_26 rfl os_body_26 (osCalleesM_26 M rd) hroot h

/-- The callees of `open_stacked__L27` under a hash model. -/
theorem osCalleesM_27 (M : HashModel) (rd : Reader) : OsCalleesM M rd osCfg27 where
  lv := fun i hi => by
    have : i < 6 := hi
    interval_cases i
    · exact ⟨fun a r h => (opening_row_weights_L6_L1_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L6_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L1_L64_L8_L26_L6_model hn hq h, fun a r h => (decode_query_bits_L26_iffB rd a r).mp h,
        ⟨Data.core899, os_sq_find_27_0, rfl, os_sq_body_27_0⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L5_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L25_L5_model hn hq h, fun a r h => (decode_query_bits_L25_iffB rd a r).mp h,
        ⟨Data.core901, os_sq_find_27_1, rfl, os_sq_body_27_1⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L5_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L24_L5_model hn hq h, fun a r h => (decode_query_bits_L24_iffB rd a r).mp h,
        ⟨Data.core903, os_sq_find_27_2, rfl, os_sq_body_27_2⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L5_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L23_L5_model hn hq h, fun a r h => (decode_query_bits_L23_iffB rd a r).mp h,
        ⟨Data.core904, os_sq_find_27_3, rfl, os_sq_body_27_3⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L4_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L22_L4_model hn hq h, fun a r h => (decode_query_bits_L22_iffB rd a r).mp h,
        ⟨Data.core905, os_sq_find_27_4, rfl, os_sq_body_27_4⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L4_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L21_L4_model hn hq h, fun a r h => (decode_query_bits_L21_iffB rd a r).mp h,
        ⟨Data.core907, os_sq_find_27_5, rfl, os_sq_body_27_5⟩⟩
  fin := fun a r h => opening_final_message_L4_model rd a r h
  ff := fun a r h => (fold_final_msg_L2_iffB rd a r).mp h
  res := fun i hi => by
    have : i < 6 := hi
    interval_cases i
    exacts [⟨Data.core908, os_res_find_27_0, rfl, os_res_body_27_0⟩, ⟨Data.core909, os_res_find_27_1, rfl, os_res_body_27_1⟩, ⟨Data.core910, os_res_find_27_2, rfl, os_res_body_27_2⟩, ⟨Data.core911, os_res_find_27_3, rfl, os_res_body_27_3⟩, ⟨Data.core912, os_res_find_27_4, rfl, os_res_body_27_4⟩, ⟨Data.core913, os_res_find_27_5, rfl, os_res_body_27_5⟩]

/-- **`open_stacked__L27`** (`μ = 28`, `r = 4`) is sound under a hash model. -/
theorem open_stacked_L27_model {M : HashModel} {rd : Reader} {root : Digest}
    {fs0 fs1 target root0 root1 cur : E} {rets : List E} (hroot : (root0, root1) = digestScalars root)
    (h : coreProgram.RelB M.sem rd "open_stacked__L27" [fs0, fs1, target, root0, root1, cur] rets) :
    OpenOutM M rd 28 4 root fs0 fs1 target cur rets :=
  open_stacked_model osCfgOk_27 os_find_27 rfl os_body_27 (osCalleesM_27 M rd) hroot h

end
end LeanVM.Guest.B1
