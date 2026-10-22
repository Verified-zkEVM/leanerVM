/-
  LeanVM.Guest.Memory.GuestBoundsAtB

  The words bounds of `GuestBoundsB` at frame sizes agreeing with `fsOf` but at `main`
  (`GuestBoundsAt.lean`) under any semantics of `BLAKE2S`.
-/

module

public import LeanVM.Guest.Memory.GuestBoundsAt
public import LeanVM.Guest.Memory.GuestBoundsB
public import LeanVM.Guest.Memory.SizeTransferB

/-!
# Words bounds at frame sizes agreeing with `fsOf`, under any `BLAKE2S` semantics

`GuestBoundsAt.lean`'s bounds as `TotalLeB S`/`TotalLeOnB S`, each from `GuestBoundsB`'s by
`totalLeB_transfer`/`totalLeOnB_transfer` and the same `coreProgram_callsIn_noMain`.

Made by `mkB.py` from the generated `GuestBoundsAt.lean` (W2-1's pattern, `docs/roadmap/t6-completeness.md` (removed; in git at `6ffa1d1f`)
§4.2): remake it, do not edit it, when that file is regenerated.
-/

namespace LeanVM.Guest

open LeanVM.Parameters LeanVM.Semantics Core Memory Data

@[expose] public section

variable {S : BlakeSem}

theorem verifyB_lean_xmss_totalLe_at {fs' : String → ℕ} (h : FsAgree fs') :
    TotalLeB S coreProgram fs' "verify_lean_xmss" fun _ => 1721 :=
  totalLeB_transfer coreProgram_callsIn_noMain h (by decide) verifyB_lean_xmss_totalLe

theorem verifyB_sig_lean_sphincs_totalLe_at {fs' : String → ℕ} (h : FsAgree fs') :
    TotalLeB S coreProgram fs' "verify_sig_lean_sphincs" fun _ => 3157 :=
  totalLeB_transfer coreProgram_callsIn_noMain h (by decide) verifyB_sig_lean_sphincs_totalLe

theorem statementB_digest_totalLe_at {fs' : String → ℕ} (h : FsAgree fs') :
    TotalLeB S coreProgram fs' "statement_digest" fun _ => 627 :=
  totalLeB_transfer coreProgram_callsIn_noMain h (by decide) statementB_digest_totalLe

theorem daB_list_digest_totalLe_at {fs' : String → ℕ} (h : FsAgree fs') :
    TotalLeB S coreProgram fs' "da_list_digest" fun _ => 134 :=
  totalLeB_transfer coreProgram_callsIn_noMain h (by decide) daB_list_digest_totalLe

theorem scaledB_log_L11_totalLe_at {fs' : String → ℕ} (h : FsAgree fs') :
    TotalLeB S coreProgram fs' "scaled_log__L11" fun _ => 147 :=
  totalLeB_transfer coreProgram_callsIn_noMain h (by decide) scaledB_log_L11_totalLe

theorem scaledB_log_L6_totalLe_at {fs' : String → ℕ} (h : FsAgree fs') :
    TotalLeB S coreProgram fs' "scaled_log__L6" fun _ => 147 :=
  totalLeB_transfer coreProgram_callsIn_noMain h (by decide) scaledB_log_L6_totalLe

theorem openingB_fold_totalLe_at {fs' : String → ℕ} (h : FsAgree fs') :
    TotalLeB S coreProgram fs' "opening_fold" fun _ => 68 :=
  totalLeB_transfer coreProgram_callsIn_noMain h (by decide) openingB_fold_totalLe

theorem openingB_final_message_L4_totalLe_at {fs' : String → ℕ} (h : FsAgree fs') :
    TotalLeB S coreProgram fs' "opening_final_message__L4" fun _ => 72 :=
  totalLeB_transfer coreProgram_callsIn_noMain h (by decide) openingB_final_message_L4_totalLe

theorem openingB_final_message_L8_totalLe_at {fs' : String → ℕ} (h : FsAgree fs') :
    TotalLeB S coreProgram fs' "opening_final_message__L8" fun _ => 124 :=
  totalLeB_transfer coreProgram_callsIn_noMain h (by decide) openingB_final_message_L8_totalLe

theorem openingB_final_message_L16_totalLe_at {fs' : String → ℕ} (h : FsAgree fs') :
    TotalLeB S coreProgram fs' "opening_final_message__L16" fun _ => 228 :=
  totalLeB_transfer coreProgram_callsIn_noMain h (by decide) openingB_final_message_L16_totalLe

theorem openingB_final_message_L32_totalLe_at {fs' : String → ℕ} (h : FsAgree fs') :
    TotalLeB S coreProgram fs' "opening_final_message__L32" fun _ => 436 :=
  totalLeB_transfer coreProgram_callsIn_noMain h (by decide) openingB_final_message_L32_totalLe

theorem openingB_row_weights_L4_L0_totalLe_at {fs' : String → ℕ} (h : FsAgree fs') :
    TotalLeB S coreProgram fs' "opening_row_weights__L4_L0" fun _ => 57 :=
  totalLeB_transfer coreProgram_callsIn_noMain h (by decide) openingB_row_weights_L4_L0_totalLe

theorem openingB_row_weights_L6_L1_totalLe_at {fs' : String → ℕ} (h : FsAgree fs') :
    TotalLeB S coreProgram fs' "opening_row_weights__L6_L1" fun _ => 205 :=
  totalLeB_transfer coreProgram_callsIn_noMain h (by decide) openingB_row_weights_L6_L1_totalLe

theorem foldB_final_msg_L2_totalLe_at {fs' : String → ℕ} (h : FsAgree fs') :
    TotalLeB S coreProgram fs' "fold_final_msg__L2" fun _ => 92 :=
  totalLeB_transfer coreProgram_callsIn_noMain h (by decide) foldB_final_msg_L2_totalLe

theorem foldB_final_msg_L3_totalLe_at {fs' : String → ℕ} (h : FsAgree fs') :
    TotalLeB S coreProgram fs' "fold_final_msg__L3" fun _ => 137 :=
  totalLeB_transfer coreProgram_callsIn_noMain h (by decide) foldB_final_msg_L3_totalLe

theorem foldB_final_msg_L4_totalLe_at {fs' : String → ℕ} (h : FsAgree fs') :
    TotalLeB S coreProgram fs' "fold_final_msg__L4" fun _ => 194 :=
  totalLeB_transfer coreProgram_callsIn_noMain h (by decide) foldB_final_msg_L4_totalLe

theorem foldB_final_msg_L5_totalLe_at {fs' : String → ℕ} (h : FsAgree fs') :
    TotalLeB S coreProgram fs' "fold_final_msg__L5" fun _ => 275 :=
  totalLeB_transfer coreProgram_callsIn_noMain h (by decide) foldB_final_msg_L5_totalLe

theorem daB_vector_cell_L0_totalLe_at {fs' : String → ℕ} (h : FsAgree fs') :
    TotalLeB S coreProgram fs' "da_vector_cell__L0" fun _ => 2907 :=
  totalLeB_transfer coreProgram_callsIn_noMain h (by decide) daB_vector_cell_L0_totalLe

theorem daB_vector_cell_L1_totalLe_at {fs' : String → ℕ} (h : FsAgree fs') :
    TotalLeB S coreProgram fs' "da_vector_cell__L1" fun _ => 2909 :=
  totalLeB_transfer coreProgram_callsIn_noMain h (by decide) daB_vector_cell_L1_totalLe

theorem ctB_totalLe_at {fs' : String → ℕ} (h : FsAgree fs') :
    ∀ t, t < 32 → TotalLeB S coreProgram fs' ctList[t]! fun _ => ctBound[t]! := by
  intro t ht
  refine totalLeB_transfer coreProgram_callsIn_noMain h ?_ (ctB_totalLe t ht)
  interval_cases t <;> decide

theorem loop86B_totalLeOn_at {fs' : String → ℕ} (h : FsAgree fs') :
    TotalLeOnB S coreProgram fs' "__loop86" LoopPre fun a => logG (a.getD 1 0) * 482 :=
  totalLeOnB_transfer coreProgram_callsIn_noMain h (by decide) loop86B_totalLeOn

theorem loop6B_totalLeOn_at {fs' : String → ℕ} (h : FsAgree fs') :
    TotalLeOnB S coreProgram fs' "__loop6" LoopPre fun a => logG (a.getD 1 0) * 32 :=
  totalLeOnB_transfer coreProgram_callsIn_noMain h (by decide) loop6B_totalLeOn

theorem loop9B_totalLeOn_at {fs' : String → ℕ} (h : FsAgree fs') :
    TotalLeOnB S coreProgram fs' "__loop9" LoopPre fun a => logG (a.getD 1 0) * 78 :=
  totalLeOnB_transfer coreProgram_callsIn_noMain h (by decide) loop9B_totalLeOn

end
end LeanVM.Guest
