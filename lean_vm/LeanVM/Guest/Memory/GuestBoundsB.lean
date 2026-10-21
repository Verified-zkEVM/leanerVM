/-
  LeanVM.Guest.Memory.GuestBoundsB

  The words bounds of the guest's functions at the frame sizes `fsOf` (`GuestBounds.lean`)
  under any semantics of `BLAKE2S`.
-/

module

public import LeanVM.Guest.Memory.GuestBounds
public import LeanVM.Guest.Memory.GuestWordsB
public import LeanVM.Guest.Memory.SizeTotalB

/-!
# Words bounds at the frame sizes under any `BLAKE2S` semantics

Each `TotalLe` of `GuestBounds.lean` as `TotalLeB S`, by `coreB_totalLe` on the same certificate
facts (`wfs_fsOf`, `wcertOf_of_idx`), no function left to a hand bound (`whandB_none`); the loop
helpers' bounds (`TotalLeOnB`) as there. A theorem `f_…_totalLe` is `fB_…_totalLe` here
(`verifyB_lean_xmss_totalLe`, …); at `blakeDeployed` it is the deployed one by
`totalLeB_deployed`.

Made by `mkB.py` from the generated `GuestBounds.lean` (W2-1's pattern, `docs/roadmap/t6-completeness.md`
§4.2): remake it, do not edit it, when that file is regenerated.
-/

namespace LeanVM.Guest

open LeanVM.Parameters LeanVM.Semantics Core Memory Data

@[expose] public section

variable {S : BlakeSem}

theorem whandB_none : HandOkB S coreProgram fsOf wcertOf wHandX :=
  handOkB_of fun q hq => by simp [whandJ] at hq

/-- `verify_lean_xmss`: at most 1721 words. -/
theorem verifyB_lean_xmss_totalLe : TotalLeB S coreProgram fsOf "verify_lean_xmss" fun _ => 1721 :=
  coreB_totalLe wfs_fsOf whandB_none (by rw [wcertOf_of_idx (j := 16) (by decide +kernel)]; rfl)

/-- `verify_sig_lean_sphincs`: at most 3157 words. -/
theorem verifyB_sig_lean_sphincs_totalLe : TotalLeB S coreProgram fsOf "verify_sig_lean_sphincs" fun _ => 3157 :=
  coreB_totalLe wfs_fsOf whandB_none (by rw [wcertOf_of_idx (j := 17) (by decide +kernel)]; rfl)

/-- `statement_digest`: at most 627 words. -/
theorem statementB_digest_totalLe : TotalLeB S coreProgram fsOf "statement_digest" fun _ => 627 :=
  coreB_totalLe wfs_fsOf whandB_none (by rw [wcertOf_of_idx (j := 18) (by decide +kernel)]; rfl)

/-- `da_list_digest`: at most 134 words. -/
theorem daB_list_digest_totalLe : TotalLeB S coreProgram fsOf "da_list_digest" fun _ => 134 :=
  coreB_totalLe wfs_fsOf whandB_none (by rw [wcertOf_of_idx (j := 27) (by decide +kernel)]; rfl)

/-- `scaled_log__L11`: at most 147 words. -/
theorem scaledB_log_L11_totalLe : TotalLeB S coreProgram fsOf "scaled_log__L11" fun _ => 147 :=
  coreB_totalLe wfs_fsOf whandB_none (by rw [wcertOf_of_idx (j := 461) (by decide +kernel)]; rfl)

/-- `scaled_log__L6`: at most 147 words. -/
theorem scaledB_log_L6_totalLe : TotalLeB S coreProgram fsOf "scaled_log__L6" fun _ => 147 :=
  coreB_totalLe wfs_fsOf whandB_none (by rw [wcertOf_of_idx (j := 495) (by decide +kernel)]; rfl)

/-- `opening_fold`: at most 68 words. -/
theorem openingB_fold_totalLe : TotalLeB S coreProgram fsOf "opening_fold" fun _ => 68 :=
  coreB_totalLe wfs_fsOf whandB_none (by rw [wcertOf_of_idx (j := 8) (by decide +kernel)]; rfl)

/-- `opening_final_message__L4`: at most 72 words. -/
theorem openingB_final_message_L4_totalLe : TotalLeB S coreProgram fsOf "opening_final_message__L4" fun _ => 72 :=
  coreB_totalLe wfs_fsOf whandB_none (by rw [wcertOf_of_idx (j := 616) (by decide +kernel)]; rfl)

/-- `opening_final_message__L8`: at most 124 words. -/
theorem openingB_final_message_L8_totalLe : TotalLeB S coreProgram fsOf "opening_final_message__L8" fun _ => 124 :=
  coreB_totalLe wfs_fsOf whandB_none (by rw [wcertOf_of_idx (j := 631) (by decide +kernel)]; rfl)

/-- `opening_final_message__L16`: at most 228 words. -/
theorem openingB_final_message_L16_totalLe : TotalLeB S coreProgram fsOf "opening_final_message__L16" fun _ => 228 :=
  coreB_totalLe wfs_fsOf whandB_none (by rw [wcertOf_of_idx (j := 588) (by decide +kernel)]; rfl)

/-- `opening_final_message__L32`: at most 436 words. -/
theorem openingB_final_message_L32_totalLe : TotalLeB S coreProgram fsOf "opening_final_message__L32" fun _ => 436 :=
  coreB_totalLe wfs_fsOf whandB_none (by rw [wcertOf_of_idx (j := 602) (by decide +kernel)]; rfl)

/-- `opening_row_weights__L4_L0`: at most 57 words. -/
theorem openingB_row_weights_L4_L0_totalLe : TotalLeB S coreProgram fsOf "opening_row_weights__L4_L0" fun _ => 57 :=
  coreB_totalLe wfs_fsOf whandB_none (by rw [wcertOf_of_idx (j := 582) (by decide +kernel)]; rfl)

/-- `opening_row_weights__L6_L1`: at most 205 words. -/
theorem openingB_row_weights_L6_L1_totalLe : TotalLeB S coreProgram fsOf "opening_row_weights__L6_L1" fun _ => 205 :=
  coreB_totalLe wfs_fsOf whandB_none (by rw [wcertOf_of_idx (j := 578) (by decide +kernel)]; rfl)

/-- `fold_final_msg__L2`: at most 92 words. -/
theorem foldB_final_msg_L2_totalLe : TotalLeB S coreProgram fsOf "fold_final_msg__L2" fun _ => 92 :=
  coreB_totalLe wfs_fsOf whandB_none (by rw [wcertOf_of_idx (j := 618) (by decide +kernel)]; rfl)

/-- `fold_final_msg__L3`: at most 137 words. -/
theorem foldB_final_msg_L3_totalLe : TotalLeB S coreProgram fsOf "fold_final_msg__L3" fun _ => 137 :=
  coreB_totalLe wfs_fsOf whandB_none (by rw [wcertOf_of_idx (j := 633) (by decide +kernel)]; rfl)

/-- `fold_final_msg__L4`: at most 194 words. -/
theorem foldB_final_msg_L4_totalLe : TotalLeB S coreProgram fsOf "fold_final_msg__L4" fun _ => 194 :=
  coreB_totalLe wfs_fsOf whandB_none (by rw [wcertOf_of_idx (j := 591) (by decide +kernel)]; rfl)

/-- `fold_final_msg__L5`: at most 275 words. -/
theorem foldB_final_msg_L5_totalLe : TotalLeB S coreProgram fsOf "fold_final_msg__L5" fun _ => 275 :=
  coreB_totalLe wfs_fsOf whandB_none (by rw [wcertOf_of_idx (j := 604) (by decide +kernel)]; rfl)

/-- `da_vector_cell__L0`: at most 2907 words. -/
theorem daB_vector_cell_L0_totalLe : TotalLeB S coreProgram fsOf "da_vector_cell__L0" fun _ => 2907 :=
  coreB_totalLe wfs_fsOf whandB_none (by rw [wcertOf_of_idx (j := 548) (by decide +kernel)]; rfl)

/-- `da_vector_cell__L1`: at most 2909 words. -/
theorem daB_vector_cell_L1_totalLe : TotalLeB S coreProgram fsOf "da_vector_cell__L1" fun _ => 2909 :=
  coreB_totalLe wfs_fsOf whandB_none (by rw [wcertOf_of_idx (j := 547) (by decide +kernel)]; rfl)

theorem ctB_totalLe_0 : TotalLeB S coreProgram fsOf "claims_tail__L0" fun _ => 12 :=
  coreB_totalLe wfs_fsOf whandB_none (by rw [wcertOf_of_idx (j := 463) (by decide +kernel)]; rfl)

theorem ctB_totalLe_1 : TotalLeB S coreProgram fsOf "claims_tail__L1" fun _ => 21 :=
  coreB_totalLe wfs_fsOf whandB_none (by rw [wcertOf_of_idx (j := 464) (by decide +kernel)]; rfl)

theorem ctB_totalLe_2 : TotalLeB S coreProgram fsOf "claims_tail__L2" fun _ => 29 :=
  coreB_totalLe wfs_fsOf whandB_none (by rw [wcertOf_of_idx (j := 465) (by decide +kernel)]; rfl)

theorem ctB_totalLe_3 : TotalLeB S coreProgram fsOf "claims_tail__L3" fun _ => 37 :=
  coreB_totalLe wfs_fsOf whandB_none (by rw [wcertOf_of_idx (j := 466) (by decide +kernel)]; rfl)

theorem ctB_totalLe_4 : TotalLeB S coreProgram fsOf "claims_tail__L4" fun _ => 45 :=
  coreB_totalLe wfs_fsOf whandB_none (by rw [wcertOf_of_idx (j := 467) (by decide +kernel)]; rfl)

theorem ctB_totalLe_5 : TotalLeB S coreProgram fsOf "claims_tail__L5" fun _ => 53 :=
  coreB_totalLe wfs_fsOf whandB_none (by rw [wcertOf_of_idx (j := 468) (by decide +kernel)]; rfl)

theorem ctB_totalLe_6 : TotalLeB S coreProgram fsOf "claims_tail__L6" fun _ => 61 :=
  coreB_totalLe wfs_fsOf whandB_none (by rw [wcertOf_of_idx (j := 469) (by decide +kernel)]; rfl)

theorem ctB_totalLe_7 : TotalLeB S coreProgram fsOf "claims_tail__L7" fun _ => 69 :=
  coreB_totalLe wfs_fsOf whandB_none (by rw [wcertOf_of_idx (j := 470) (by decide +kernel)]; rfl)

theorem ctB_totalLe_8 : TotalLeB S coreProgram fsOf "claims_tail__L8" fun _ => 77 :=
  coreB_totalLe wfs_fsOf whandB_none (by rw [wcertOf_of_idx (j := 471) (by decide +kernel)]; rfl)

theorem ctB_totalLe_9 : TotalLeB S coreProgram fsOf "claims_tail__L9" fun _ => 85 :=
  coreB_totalLe wfs_fsOf whandB_none (by rw [wcertOf_of_idx (j := 472) (by decide +kernel)]; rfl)

theorem ctB_totalLe_10 : TotalLeB S coreProgram fsOf "claims_tail__L10" fun _ => 93 :=
  coreB_totalLe wfs_fsOf whandB_none (by rw [wcertOf_of_idx (j := 473) (by decide +kernel)]; rfl)

theorem ctB_totalLe_11 : TotalLeB S coreProgram fsOf "claims_tail__L11" fun _ => 101 :=
  coreB_totalLe wfs_fsOf whandB_none (by rw [wcertOf_of_idx (j := 474) (by decide +kernel)]; rfl)

theorem ctB_totalLe_12 : TotalLeB S coreProgram fsOf "claims_tail__L12" fun _ => 109 :=
  coreB_totalLe wfs_fsOf whandB_none (by rw [wcertOf_of_idx (j := 475) (by decide +kernel)]; rfl)

theorem ctB_totalLe_13 : TotalLeB S coreProgram fsOf "claims_tail__L13" fun _ => 117 :=
  coreB_totalLe wfs_fsOf whandB_none (by rw [wcertOf_of_idx (j := 476) (by decide +kernel)]; rfl)

theorem ctB_totalLe_14 : TotalLeB S coreProgram fsOf "claims_tail__L14" fun _ => 125 :=
  coreB_totalLe wfs_fsOf whandB_none (by rw [wcertOf_of_idx (j := 477) (by decide +kernel)]; rfl)

theorem ctB_totalLe_15 : TotalLeB S coreProgram fsOf "claims_tail__L15" fun _ => 133 :=
  coreB_totalLe wfs_fsOf whandB_none (by rw [wcertOf_of_idx (j := 478) (by decide +kernel)]; rfl)

theorem ctB_totalLe_16 : TotalLeB S coreProgram fsOf "claims_tail__L16" fun _ => 141 :=
  coreB_totalLe wfs_fsOf whandB_none (by rw [wcertOf_of_idx (j := 479) (by decide +kernel)]; rfl)

theorem ctB_totalLe_17 : TotalLeB S coreProgram fsOf "claims_tail__L17" fun _ => 149 :=
  coreB_totalLe wfs_fsOf whandB_none (by rw [wcertOf_of_idx (j := 480) (by decide +kernel)]; rfl)

theorem ctB_totalLe_18 : TotalLeB S coreProgram fsOf "claims_tail__L18" fun _ => 157 :=
  coreB_totalLe wfs_fsOf whandB_none (by rw [wcertOf_of_idx (j := 481) (by decide +kernel)]; rfl)

theorem ctB_totalLe_19 : TotalLeB S coreProgram fsOf "claims_tail__L19" fun _ => 165 :=
  coreB_totalLe wfs_fsOf whandB_none (by rw [wcertOf_of_idx (j := 482) (by decide +kernel)]; rfl)

theorem ctB_totalLe_20 : TotalLeB S coreProgram fsOf "claims_tail__L20" fun _ => 173 :=
  coreB_totalLe wfs_fsOf whandB_none (by rw [wcertOf_of_idx (j := 483) (by decide +kernel)]; rfl)

theorem ctB_totalLe_21 : TotalLeB S coreProgram fsOf "claims_tail__L21" fun _ => 181 :=
  coreB_totalLe wfs_fsOf whandB_none (by rw [wcertOf_of_idx (j := 484) (by decide +kernel)]; rfl)

theorem ctB_totalLe_22 : TotalLeB S coreProgram fsOf "claims_tail__L22" fun _ => 189 :=
  coreB_totalLe wfs_fsOf whandB_none (by rw [wcertOf_of_idx (j := 485) (by decide +kernel)]; rfl)

theorem ctB_totalLe_23 : TotalLeB S coreProgram fsOf "claims_tail__L23" fun _ => 197 :=
  coreB_totalLe wfs_fsOf whandB_none (by rw [wcertOf_of_idx (j := 486) (by decide +kernel)]; rfl)

theorem ctB_totalLe_24 : TotalLeB S coreProgram fsOf "claims_tail__L24" fun _ => 205 :=
  coreB_totalLe wfs_fsOf whandB_none (by rw [wcertOf_of_idx (j := 487) (by decide +kernel)]; rfl)

theorem ctB_totalLe_25 : TotalLeB S coreProgram fsOf "claims_tail__L25" fun _ => 213 :=
  coreB_totalLe wfs_fsOf whandB_none (by rw [wcertOf_of_idx (j := 488) (by decide +kernel)]; rfl)

theorem ctB_totalLe_26 : TotalLeB S coreProgram fsOf "claims_tail__L26" fun _ => 221 :=
  coreB_totalLe wfs_fsOf whandB_none (by rw [wcertOf_of_idx (j := 489) (by decide +kernel)]; rfl)

theorem ctB_totalLe_27 : TotalLeB S coreProgram fsOf "claims_tail__L27" fun _ => 229 :=
  coreB_totalLe wfs_fsOf whandB_none (by rw [wcertOf_of_idx (j := 490) (by decide +kernel)]; rfl)

theorem ctB_totalLe_28 : TotalLeB S coreProgram fsOf "claims_tail__L28" fun _ => 237 :=
  coreB_totalLe wfs_fsOf whandB_none (by rw [wcertOf_of_idx (j := 491) (by decide +kernel)]; rfl)

theorem ctB_totalLe_29 : TotalLeB S coreProgram fsOf "claims_tail__L29" fun _ => 245 :=
  coreB_totalLe wfs_fsOf whandB_none (by rw [wcertOf_of_idx (j := 492) (by decide +kernel)]; rfl)

theorem ctB_totalLe_30 : TotalLeB S coreProgram fsOf "claims_tail__L30" fun _ => 253 :=
  coreB_totalLe wfs_fsOf whandB_none (by rw [wcertOf_of_idx (j := 493) (by decide +kernel)]; rfl)

theorem ctB_totalLe_31 : TotalLeB S coreProgram fsOf "claims_tail__L31" fun _ => 261 :=
  coreB_totalLe wfs_fsOf whandB_none (by rw [wcertOf_of_idx (j := 494) (by decide +kernel)]; rfl)

/-- **The claim tails' words.** -/
theorem ctB_totalLe : ∀ t, t < 32 → TotalLeB S coreProgram fsOf ctList[t]! fun _ => ctBound[t]! := by
  intro t ht
  interval_cases t
  · exact ctB_totalLe_0
  · exact ctB_totalLe_1
  · exact ctB_totalLe_2
  · exact ctB_totalLe_3
  · exact ctB_totalLe_4
  · exact ctB_totalLe_5
  · exact ctB_totalLe_6
  · exact ctB_totalLe_7
  · exact ctB_totalLe_8
  · exact ctB_totalLe_9
  · exact ctB_totalLe_10
  · exact ctB_totalLe_11
  · exact ctB_totalLe_12
  · exact ctB_totalLe_13
  · exact ctB_totalLe_14
  · exact ctB_totalLe_15
  · exact ctB_totalLe_16
  · exact ctB_totalLe_17
  · exact ctB_totalLe_18
  · exact ctB_totalLe_19
  · exact ctB_totalLe_20
  · exact ctB_totalLe_21
  · exact ctB_totalLe_22
  · exact ctB_totalLe_23
  · exact ctB_totalLe_24
  · exact ctB_totalLe_25
  · exact ctB_totalLe_26
  · exact ctB_totalLe_27
  · exact ctB_totalLe_28
  · exact ctB_totalLe_29
  · exact ctB_totalLe_30
  · exact ctB_totalLe_31

/-- `__loop86` from `g^a` to its end `g^e`, its second argument: `e - a` iterations of at most 482
words each, so at most `482` per unit of the end's exponent. -/
theorem loop86B_totalLeOn : TotalLeOnB S coreProgram fsOf "__loop86" LoopPre fun a => logG (a.getD 1 0) * 482 := by
  intro rd t args rets htn ⟨a, e, ha, he, hae, heo⟩ hv hb
  have hcf : wcertOf "__loop86" = .loop none [] ⟨482, []⟩ [] := by
    rw [wcertOf_of_idx (j := 462) (by decide +kernel)]; rfl
  have := coreB_total_le_of_loop wfs_fsOf whandB_none hcf htn hv hb ha he hae heo
    (fun _ h => (List.not_mem_nil h).elim)
  dsimp only
  rw [he, logG_spec heo]
  simp only [Aff.eval, List.map_nil, List.sum_nil, Nat.add_zero] at this
  exact this.trans (Nat.mul_le_mul_right _ (Nat.sub_le _ _))

/-- `__loop6` from `g^a` to its end `g^e`, its second argument: `e - a` iterations of at most 32
words each, so at most `32` per unit of the end's exponent. -/
theorem loop6B_totalLeOn : TotalLeOnB S coreProgram fsOf "__loop6" LoopPre fun a => logG (a.getD 1 0) * 32 := by
  intro rd t args rets htn ⟨a, e, ha, he, hae, heo⟩ hv hb
  have hcf : wcertOf "__loop6" = .loop none [] ⟨32, []⟩ [] := by
    rw [wcertOf_of_idx (j := 36) (by decide +kernel)]; rfl
  have := coreB_total_le_of_loop wfs_fsOf whandB_none hcf htn hv hb ha he hae heo
    (fun _ h => (List.not_mem_nil h).elim)
  dsimp only
  rw [he, logG_spec heo]
  simp only [Aff.eval, List.map_nil, List.sum_nil, Nat.add_zero] at this
  exact this.trans (Nat.mul_le_mul_right _ (Nat.sub_le _ _))

/-- `__loop9` from `g^a` to its end `g^e`, its second argument: `e - a` iterations of at most 78
words each, so at most `78` per unit of the end's exponent. -/
theorem loop9B_totalLeOn : TotalLeOnB S coreProgram fsOf "__loop9" LoopPre fun a => logG (a.getD 1 0) * 78 := by
  intro rd t args rets htn ⟨a, e, ha, he, hae, heo⟩ hv hb
  have hcf : wcertOf "__loop9" = .loop none [] ⟨78, []⟩ [] := by
    rw [wcertOf_of_idx (j := 39) (by decide +kernel)]; rfl
  have := coreB_total_le_of_loop wfs_fsOf whandB_none hcf htn hv hb ha he hae heo
    (fun _ h => (List.not_mem_nil h).elim)
  dsimp only
  rw [he, logG_spec heo]
  simp only [Aff.eval, List.map_nil, List.sum_nil, Nat.add_zero] at this
  exact this.trans (Nat.mul_le_mul_right _ (Nat.sub_le _ _))

end
end LeanVM.Guest
