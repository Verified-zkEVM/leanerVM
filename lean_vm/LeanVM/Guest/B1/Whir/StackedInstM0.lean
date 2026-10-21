/-
  LeanVM.Guest.B1.Whir.StackedInstM0

  The `open_stacked` specializations of `Whir/StackedInst0.lean` are sound under a hash model.
-/

module

public import LeanVM.Guest.B1.Whir.StackedSoundM
public import LeanVM.Guest.B1.Whir.StackedInst0
public import LeanVM.Guest.B1.Whir.QueriesSpecM

/-!
# `open_stacked` at its candidates under a hash model (0)

For each candidate of `Whir/StackedInst0.lean`: its configuration's facts (`osCfgOk_…`, as
there), its callees' meanings under the model (`OsCalleesM`: the specialized callees' generic
lemmas, the hash-free ones by transfer), and `open_stacked_model` at them.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Protocol.Verifier
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Guest.B1.VerifySub

@[expose] public section

/-- The callees of `open_stacked__L0` under a hash model. -/
theorem osCalleesM_0 (M : HashModel) (rd : Reader) : OsCalleesM M rd osCfg0 where
  lv := fun i hi => by
    have : i < 4 := hi
    interval_cases i
    · exact ⟨fun a r h => (opening_row_weights_L6_L1_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L8_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L1_L64_L8_L17_L8_model hn hq h, fun a r h => (decode_query_bits_L17_iffB rd a r).mp h,
        ⟨Data.core577, os_sq_find_0_0, rfl, os_sq_body_0_0⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L6_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L16_L6_model hn hq h, fun a r h => (decode_query_bits_L16_iffB rd a r).mp h,
        ⟨Data.core581, os_sq_find_0_1, rfl, os_sq_body_0_1⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L5_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L15_L5_model hn hq h, fun a r h => (decode_query_bits_L15_iffB rd a r).mp h,
        ⟨Data.core585, os_sq_find_0_2, rfl, os_sq_body_0_2⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L5_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L14_L5_model hn hq h, fun a r h => (decode_query_bits_L14_iffB rd a r).mp h,
        ⟨Data.core589, os_sq_find_0_3, rfl, os_sq_body_0_3⟩⟩
  fin := fun a r h => opening_final_message_L16_model rd a r h
  ff := fun a r h => (fold_final_msg_L4_iffB rd a r).mp h
  res := fun i hi => by
    have : i < 4 := hi
    interval_cases i
    exacts [⟨Data.core592, os_res_find_0_0, rfl, os_res_body_0_0⟩, ⟨Data.core593, os_res_find_0_1, rfl, os_res_body_0_1⟩, ⟨Data.core594, os_res_find_0_2, rfl, os_res_body_0_2⟩, ⟨Data.core595, os_res_find_0_3, rfl, os_res_body_0_3⟩]

/-- **`open_stacked__L0`** (`μ = 22`, `r = 1`) is sound under a hash model. -/
theorem open_stacked_L0_model {M : HashModel} {rd : Reader} {root : Digest}
    {fs0 fs1 target root0 root1 cur : E} {rets : List E} (hroot : (root0, root1) = digestScalars root)
    (h : coreProgram.RelB M.sem rd "open_stacked__L0" [fs0, fs1, target, root0, root1, cur] rets) :
    OpenOutM M rd 22 1 root fs0 fs1 target cur rets :=
  open_stacked_model osCfgOk_0 os_find_0 rfl os_body_0 (osCalleesM_0 M rd) hroot h

/-- The callees of `open_stacked__L1` under a hash model. -/
theorem osCalleesM_1 (M : HashModel) (rd : Reader) : OsCalleesM M rd osCfg1 where
  lv := fun i hi => by
    have : i < 4 := hi
    interval_cases i
    · exact ⟨fun a r h => (opening_row_weights_L6_L1_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L8_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L1_L64_L8_L18_L8_model hn hq h, fun a r h => (decode_query_bits_L18_iffB rd a r).mp h,
        ⟨Data.core596, os_sq_find_1_0, rfl, os_sq_body_1_0⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L6_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L17_L6_model hn hq h, fun a r h => (decode_query_bits_L17_iffB rd a r).mp h,
        ⟨Data.core598, os_sq_find_1_1, rfl, os_sq_body_1_1⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L5_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L16_L5_model hn hq h, fun a r h => (decode_query_bits_L16_iffB rd a r).mp h,
        ⟨Data.core600, os_sq_find_1_2, rfl, os_sq_body_1_2⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L5_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L15_L5_model hn hq h, fun a r h => (decode_query_bits_L15_iffB rd a r).mp h,
        ⟨Data.core603, os_sq_find_1_3, rfl, os_sq_body_1_3⟩⟩
  fin := fun a r h => opening_final_message_L32_model rd a r h
  ff := fun a r h => (fold_final_msg_L5_iffB rd a r).mp h
  res := fun i hi => by
    have : i < 4 := hi
    interval_cases i
    exacts [⟨Data.core605, os_res_find_1_0, rfl, os_res_body_1_0⟩, ⟨Data.core606, os_res_find_1_1, rfl, os_res_body_1_1⟩, ⟨Data.core607, os_res_find_1_2, rfl, os_res_body_1_2⟩, ⟨Data.core608, os_res_find_1_3, rfl, os_res_body_1_3⟩]

/-- **`open_stacked__L1`** (`μ = 23`, `r = 1`) is sound under a hash model. -/
theorem open_stacked_L1_model {M : HashModel} {rd : Reader} {root : Digest}
    {fs0 fs1 target root0 root1 cur : E} {rets : List E} (hroot : (root0, root1) = digestScalars root)
    (h : coreProgram.RelB M.sem rd "open_stacked__L1" [fs0, fs1, target, root0, root1, cur] rets) :
    OpenOutM M rd 23 1 root fs0 fs1 target cur rets :=
  open_stacked_model osCfgOk_1 os_find_1 rfl os_body_1 (osCalleesM_1 M rd) hroot h

/-- The callees of `open_stacked__L2` under a hash model. -/
theorem osCalleesM_2 (M : HashModel) (rd : Reader) : OsCalleesM M rd osCfg2 where
  lv := fun i hi => by
    have : i < 5 := hi
    interval_cases i
    · exact ⟨fun a r h => (opening_row_weights_L6_L1_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L8_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L1_L64_L8_L19_L8_model hn hq h, fun a r h => (decode_query_bits_L19_iffB rd a r).mp h,
        ⟨Data.core609, os_sq_find_2_0, rfl, os_sq_body_2_0⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L6_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L18_L6_model hn hq h, fun a r h => (decode_query_bits_L18_iffB rd a r).mp h,
        ⟨Data.core611, os_sq_find_2_1, rfl, os_sq_body_2_1⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L5_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L17_L5_model hn hq h, fun a r h => (decode_query_bits_L17_iffB rd a r).mp h,
        ⟨Data.core613, os_sq_find_2_2, rfl, os_sq_body_2_2⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L5_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L16_L5_model hn hq h, fun a r h => (decode_query_bits_L16_iffB rd a r).mp h,
        ⟨Data.core615, os_sq_find_2_3, rfl, os_sq_body_2_3⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L5_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L15_L5_model hn hq h, fun a r h => (decode_query_bits_L15_iffB rd a r).mp h,
        ⟨Data.core617, os_sq_find_2_4, rfl, os_sq_body_2_4⟩⟩
  fin := fun a r h => opening_final_message_L4_model rd a r h
  ff := fun a r h => (fold_final_msg_L2_iffB rd a r).mp h
  res := fun i hi => by
    have : i < 5 := hi
    interval_cases i
    exacts [⟨Data.core619, os_res_find_2_0, rfl, os_res_body_2_0⟩, ⟨Data.core620, os_res_find_2_1, rfl, os_res_body_2_1⟩, ⟨Data.core621, os_res_find_2_2, rfl, os_res_body_2_2⟩, ⟨Data.core622, os_res_find_2_3, rfl, os_res_body_2_3⟩, ⟨Data.core623, os_res_find_2_4, rfl, os_res_body_2_4⟩]

/-- **`open_stacked__L2`** (`μ = 24`, `r = 1`) is sound under a hash model. -/
theorem open_stacked_L2_model {M : HashModel} {rd : Reader} {root : Digest}
    {fs0 fs1 target root0 root1 cur : E} {rets : List E} (hroot : (root0, root1) = digestScalars root)
    (h : coreProgram.RelB M.sem rd "open_stacked__L2" [fs0, fs1, target, root0, root1, cur] rets) :
    OpenOutM M rd 24 1 root fs0 fs1 target cur rets :=
  open_stacked_model osCfgOk_2 os_find_2 rfl os_body_2 (osCalleesM_2 M rd) hroot h

/-- The callees of `open_stacked__L3` under a hash model. -/
theorem osCalleesM_3 (M : HashModel) (rd : Reader) : OsCalleesM M rd osCfg3 where
  lv := fun i hi => by
    have : i < 5 := hi
    interval_cases i
    · exact ⟨fun a r h => (opening_row_weights_L6_L1_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L8_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L1_L64_L8_L20_L8_model hn hq h, fun a r h => (decode_query_bits_L20_iffB rd a r).mp h,
        ⟨Data.core624, os_sq_find_3_0, rfl, os_sq_body_3_0⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L6_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L19_L6_model hn hq h, fun a r h => (decode_query_bits_L19_iffB rd a r).mp h,
        ⟨Data.core626, os_sq_find_3_1, rfl, os_sq_body_3_1⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L5_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L18_L5_model hn hq h, fun a r h => (decode_query_bits_L18_iffB rd a r).mp h,
        ⟨Data.core628, os_sq_find_3_2, rfl, os_sq_body_3_2⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L5_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L17_L5_model hn hq h, fun a r h => (decode_query_bits_L17_iffB rd a r).mp h,
        ⟨Data.core630, os_sq_find_3_3, rfl, os_sq_body_3_3⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L5_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L16_L5_model hn hq h, fun a r h => (decode_query_bits_L16_iffB rd a r).mp h,
        ⟨Data.core632, os_sq_find_3_4, rfl, os_sq_body_3_4⟩⟩
  fin := fun a r h => opening_final_message_L8_model rd a r h
  ff := fun a r h => (fold_final_msg_L3_iffB rd a r).mp h
  res := fun i hi => by
    have : i < 5 := hi
    interval_cases i
    exacts [⟨Data.core634, os_res_find_3_0, rfl, os_res_body_3_0⟩, ⟨Data.core635, os_res_find_3_1, rfl, os_res_body_3_1⟩, ⟨Data.core636, os_res_find_3_2, rfl, os_res_body_3_2⟩, ⟨Data.core637, os_res_find_3_3, rfl, os_res_body_3_3⟩, ⟨Data.core638, os_res_find_3_4, rfl, os_res_body_3_4⟩]

/-- **`open_stacked__L3`** (`μ = 25`, `r = 1`) is sound under a hash model. -/
theorem open_stacked_L3_model {M : HashModel} {rd : Reader} {root : Digest}
    {fs0 fs1 target root0 root1 cur : E} {rets : List E} (hroot : (root0, root1) = digestScalars root)
    (h : coreProgram.RelB M.sem rd "open_stacked__L3" [fs0, fs1, target, root0, root1, cur] rets) :
    OpenOutM M rd 25 1 root fs0 fs1 target cur rets :=
  open_stacked_model osCfgOk_3 os_find_3 rfl os_body_3 (osCalleesM_3 M rd) hroot h

/-- The callees of `open_stacked__L4` under a hash model. -/
theorem osCalleesM_4 (M : HashModel) (rd : Reader) : OsCalleesM M rd osCfg4 where
  lv := fun i hi => by
    have : i < 5 := hi
    interval_cases i
    · exact ⟨fun a r h => (opening_row_weights_L6_L1_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L8_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L1_L64_L8_L21_L8_model hn hq h, fun a r h => (decode_query_bits_L21_iffB rd a r).mp h,
        ⟨Data.core639, os_sq_find_4_0, rfl, os_sq_body_4_0⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L6_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L20_L6_model hn hq h, fun a r h => (decode_query_bits_L20_iffB rd a r).mp h,
        ⟨Data.core641, os_sq_find_4_1, rfl, os_sq_body_4_1⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L5_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L19_L5_model hn hq h, fun a r h => (decode_query_bits_L19_iffB rd a r).mp h,
        ⟨Data.core643, os_sq_find_4_2, rfl, os_sq_body_4_2⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L5_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L18_L5_model hn hq h, fun a r h => (decode_query_bits_L18_iffB rd a r).mp h,
        ⟨Data.core645, os_sq_find_4_3, rfl, os_sq_body_4_3⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L5_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L17_L5_model hn hq h, fun a r h => (decode_query_bits_L17_iffB rd a r).mp h,
        ⟨Data.core646, os_sq_find_4_4, rfl, os_sq_body_4_4⟩⟩
  fin := fun a r h => opening_final_message_L16_model rd a r h
  ff := fun a r h => (fold_final_msg_L4_iffB rd a r).mp h
  res := fun i hi => by
    have : i < 5 := hi
    interval_cases i
    exacts [⟨Data.core647, os_res_find_4_0, rfl, os_res_body_4_0⟩, ⟨Data.core648, os_res_find_4_1, rfl, os_res_body_4_1⟩, ⟨Data.core649, os_res_find_4_2, rfl, os_res_body_4_2⟩, ⟨Data.core650, os_res_find_4_3, rfl, os_res_body_4_3⟩, ⟨Data.core651, os_res_find_4_4, rfl, os_res_body_4_4⟩]

/-- **`open_stacked__L4`** (`μ = 26`, `r = 1`) is sound under a hash model. -/
theorem open_stacked_L4_model {M : HashModel} {rd : Reader} {root : Digest}
    {fs0 fs1 target root0 root1 cur : E} {rets : List E} (hroot : (root0, root1) = digestScalars root)
    (h : coreProgram.RelB M.sem rd "open_stacked__L4" [fs0, fs1, target, root0, root1, cur] rets) :
    OpenOutM M rd 26 1 root fs0 fs1 target cur rets :=
  open_stacked_model osCfgOk_4 os_find_4 rfl os_body_4 (osCalleesM_4 M rd) hroot h

/-- The callees of `open_stacked__L5` under a hash model. -/
theorem osCalleesM_5 (M : HashModel) (rd : Reader) : OsCalleesM M rd osCfg5 where
  lv := fun i hi => by
    have : i < 5 := hi
    interval_cases i
    · exact ⟨fun a r h => (opening_row_weights_L6_L1_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L8_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L1_L64_L8_L22_L8_model hn hq h, fun a r h => (decode_query_bits_L22_iffB rd a r).mp h,
        ⟨Data.core652, os_sq_find_5_0, rfl, os_sq_body_5_0⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L6_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L21_L6_model hn hq h, fun a r h => (decode_query_bits_L21_iffB rd a r).mp h,
        ⟨Data.core654, os_sq_find_5_1, rfl, os_sq_body_5_1⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L5_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L20_L5_model hn hq h, fun a r h => (decode_query_bits_L20_iffB rd a r).mp h,
        ⟨Data.core656, os_sq_find_5_2, rfl, os_sq_body_5_2⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L5_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L19_L5_model hn hq h, fun a r h => (decode_query_bits_L19_iffB rd a r).mp h,
        ⟨Data.core658, os_sq_find_5_3, rfl, os_sq_body_5_3⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L5_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L18_L5_model hn hq h, fun a r h => (decode_query_bits_L18_iffB rd a r).mp h,
        ⟨Data.core659, os_sq_find_5_4, rfl, os_sq_body_5_4⟩⟩
  fin := fun a r h => opening_final_message_L32_model rd a r h
  ff := fun a r h => (fold_final_msg_L5_iffB rd a r).mp h
  res := fun i hi => by
    have : i < 5 := hi
    interval_cases i
    exacts [⟨Data.core660, os_res_find_5_0, rfl, os_res_body_5_0⟩, ⟨Data.core661, os_res_find_5_1, rfl, os_res_body_5_1⟩, ⟨Data.core662, os_res_find_5_2, rfl, os_res_body_5_2⟩, ⟨Data.core663, os_res_find_5_3, rfl, os_res_body_5_3⟩, ⟨Data.core664, os_res_find_5_4, rfl, os_res_body_5_4⟩]

/-- **`open_stacked__L5`** (`μ = 27`, `r = 1`) is sound under a hash model. -/
theorem open_stacked_L5_model {M : HashModel} {rd : Reader} {root : Digest}
    {fs0 fs1 target root0 root1 cur : E} {rets : List E} (hroot : (root0, root1) = digestScalars root)
    (h : coreProgram.RelB M.sem rd "open_stacked__L5" [fs0, fs1, target, root0, root1, cur] rets) :
    OpenOutM M rd 27 1 root fs0 fs1 target cur rets :=
  open_stacked_model osCfgOk_5 os_find_5 rfl os_body_5 (osCalleesM_5 M rd) hroot h

/-- The callees of `open_stacked__L6` under a hash model. -/
theorem osCalleesM_6 (M : HashModel) (rd : Reader) : OsCalleesM M rd osCfg6 where
  lv := fun i hi => by
    have : i < 6 := hi
    interval_cases i
    · exact ⟨fun a r h => (opening_row_weights_L6_L1_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L8_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L1_L64_L8_L23_L8_model hn hq h, fun a r h => (decode_query_bits_L23_iffB rd a r).mp h,
        ⟨Data.core665, os_sq_find_6_0, rfl, os_sq_body_6_0⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L6_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L22_L6_model hn hq h, fun a r h => (decode_query_bits_L22_iffB rd a r).mp h,
        ⟨Data.core667, os_sq_find_6_1, rfl, os_sq_body_6_1⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L5_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L21_L5_model hn hq h, fun a r h => (decode_query_bits_L21_iffB rd a r).mp h,
        ⟨Data.core669, os_sq_find_6_2, rfl, os_sq_body_6_2⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L5_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L20_L5_model hn hq h, fun a r h => (decode_query_bits_L20_iffB rd a r).mp h,
        ⟨Data.core671, os_sq_find_6_3, rfl, os_sq_body_6_3⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L5_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L19_L5_model hn hq h, fun a r h => (decode_query_bits_L19_iffB rd a r).mp h,
        ⟨Data.core672, os_sq_find_6_4, rfl, os_sq_body_6_4⟩⟩
    · exact ⟨fun a r h => (opening_row_weights_L4_L0_iffB rd a r).mp h, fun a r h => verify_merkle_cap_L4_model rd a r h,
        fun _ _ _ _ _ _ _ _ hn hq h => opening_queries_L0_L16_L6_L18_L4_model hn hq h, fun a r h => (decode_query_bits_L18_iffB rd a r).mp h,
        ⟨Data.core673, os_sq_find_6_5, rfl, os_sq_body_6_5⟩⟩
  fin := fun a r h => opening_final_message_L4_model rd a r h
  ff := fun a r h => (fold_final_msg_L2_iffB rd a r).mp h
  res := fun i hi => by
    have : i < 6 := hi
    interval_cases i
    exacts [⟨Data.core676, os_res_find_6_0, rfl, os_res_body_6_0⟩, ⟨Data.core677, os_res_find_6_1, rfl, os_res_body_6_1⟩, ⟨Data.core678, os_res_find_6_2, rfl, os_res_body_6_2⟩, ⟨Data.core679, os_res_find_6_3, rfl, os_res_body_6_3⟩, ⟨Data.core680, os_res_find_6_4, rfl, os_res_body_6_4⟩, ⟨Data.core681, os_res_find_6_5, rfl, os_res_body_6_5⟩]

/-- **`open_stacked__L6`** (`μ = 28`, `r = 1`) is sound under a hash model. -/
theorem open_stacked_L6_model {M : HashModel} {rd : Reader} {root : Digest}
    {fs0 fs1 target root0 root1 cur : E} {rets : List E} (hroot : (root0, root1) = digestScalars root)
    (h : coreProgram.RelB M.sem rd "open_stacked__L6" [fs0, fs1, target, root0, root1, cur] rets) :
    OpenOutM M rd 28 1 root fs0 fs1 target cur rets :=
  open_stacked_model osCfgOk_6 os_find_6 rfl os_body_6 (osCalleesM_6 M rd) hroot h

end
end LeanVM.Guest.B1
