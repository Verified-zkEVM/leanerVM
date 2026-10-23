/-
  LeanVM.Guest.B1.Tables.VtC.BGlueGen

  `verify_tables`' bus sides between the selectors and the stream reads, slice by slice
  (generated: scripts/b1c-vt/genbglue.py).
-/

module

public import LeanVM.Guest.B1.Tables.VtC.BGlue
public import LeanVM.Guest.B1.Tables.Vt.SelFw

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.B1.Fwd LeanVM.Protocol.Verifier

@[expose] public section

theorem vtB_w33 : word 8589934592 0 0 = gen ^ (34 - 1) := word_g33.trans (gen_pow_eq_ofK 33).symm

section
variable {rd : Reader} {wo : ℕ → E} {args : List E}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem vtB_glue_2404 (hl : args.length = 22)  :
    ∀ s ∈ (vtPre.drop 2404).take 3, VSH (coreProgram.Rel rd) rd (vtσ rd wo args) s := by
  exact vtB_blockR hl 2404 3 [] (by decide +kernel) (fun _ h ↦ absurd h (by simp))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem vtB_glue_2424 (hl : args.length = 22) {W : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (vtσ rd wo args (.n 14)) i (W i))  :
    ∀ s ∈ (vtPre.drop 2424).take 10, VSH (coreProgram.Rel rd) rd (vtσ rd wo args) s := by
  refine vtB_blockR hl 2424 10 [
    .atom (.load (.n 2874) (.n 14) 0),
    .atom (.load (.n 2875) (.n 14) 1),
    .atom (.load (.n 2877) (.n 14) 2)] (by decide +kernel) ?_
  intro s hs hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl
  · exact (vtB_readM hl (vtB_memAt 2424 _ (by decide +kernel)) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 2425 _ (by decide +kernel)) (by decide +kernel) (hw 1 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 2427 _ (by decide +kernel)) (by decide +kernel) (hw 2 (by norm_num))).2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem vtB_glue_2452 (hl : args.length = 22) {W : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (vtσ rd wo args (.n 14)) i (W i)) 
    (h2455 : VSH (coreProgram.Rel rd) rd (vtσ rd wo args) (.dispatch (.n 2884) vtImNames [.n 8] [.n 2908]))
    (h2456 : VSH (coreProgram.Rel rd) rd (vtσ rd wo args) (.atom (.load (.n 2908) (.n 2851) 1))) :
    ∀ s ∈ (vtPre.drop 2452).take 10, VSH (coreProgram.Rel rd) rd (vtσ rd wo args) s := by
  refine vtB_blockR hl 2452 10 [
    .atom (.load (.n 2905) (.n 14) 0),
    .dispatch (.n 2884) vtImNames [.n 8] [.n 2908],
    .atom (.load (.n 2908) (.n 2851) 1),
    .atom (.load (.n 2909) (.n 14) 1),
    .atom (.load (.n 2912) (.n 14) 2)] (by decide +kernel) ?_
  intro s hs hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl
  · exact (vtB_readM hl (vtB_memAt 2452 _ (by decide +kernel)) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact h2455
  · exact h2456
  · exact (vtB_readM hl (vtB_memAt 2457 _ (by decide +kernel)) (by decide +kernel) (hw 1 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 2460 _ (by decide +kernel)) (by decide +kernel) (hw 2 (by norm_num))).2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem vtB_glue_2471 (hl : args.length = 22) {W : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (vtσ rd wo args (.n 14)) i (W i)) 
    (h2471 : VSH (coreProgram.Rel rd) rd (vtσ rd wo args) (.atom (.load (.n 2914) (.n 16) 0)))
    (h2472 : VSH (coreProgram.Rel rd) rd (vtσ rd wo args) (.atom (.load (.n 2884) (.n 17) 0))) :
    ∀ s ∈ (vtPre.drop 2471).take 5, VSH (coreProgram.Rel rd) rd (vtσ rd wo args) s := by
  refine vtB_blockR hl 2471 5 [
    .atom (.load (.n 2914) (.n 16) 0),
    .atom (.load (.n 2884) (.n 17) 0),
    .atom (.load (.n 2924) (.n 14) 3)] (by decide +kernel) ?_
  intro s hs hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl
  · exact h2471
  · exact h2472
  · exact (vtB_readM hl (vtB_memAt 2473 _ (by decide +kernel)) (by decide +kernel) (hw 3 (by norm_num))).2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem vtB_glue_2485 (hl : args.length = 22) {W : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (vtσ rd wo args (.n 14)) i (W i)) 
    (h2485 : VSH (coreProgram.Rel rd) rd (vtσ rd wo args) (.atom (.load (.n 2927) (.n 16) 1)))
    (h2486 : VSH (coreProgram.Rel rd) rd (vtσ rd wo args) (.atom (.load (.n 2884) (.n 17) 1))) :
    ∀ s ∈ (vtPre.drop 2485).take 5, VSH (coreProgram.Rel rd) rd (vtσ rd wo args) s := by
  refine vtB_blockR hl 2485 5 [
    .atom (.load (.n 2927) (.n 16) 1),
    .atom (.load (.n 2884) (.n 17) 1),
    .atom (.load (.n 2937) (.n 14) 4)] (by decide +kernel) ?_
  intro s hs hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl
  · exact h2485
  · exact h2486
  · exact (vtB_readM hl (vtB_memAt 2487 _ (by decide +kernel)) (by decide +kernel) (hw 4 (by norm_num))).2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem vtB_glue_2499 (hl : args.length = 22) {W : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (vtσ rd wo args (.n 14)) i (W i)) 
    (h2499 : VSH (coreProgram.Rel rd) rd (vtσ rd wo args) (.atom (.load (.n 2940) (.n 16) 2)))
    (h2500 : VSH (coreProgram.Rel rd) rd (vtσ rd wo args) (.atom (.load (.n 2884) (.n 17) 2))) :
    ∀ s ∈ (vtPre.drop 2499).take 11, VSH (coreProgram.Rel rd) rd (vtσ rd wo args) s := by
  refine vtB_blockR hl 2499 11 [
    .atom (.load (.n 2940) (.n 16) 2),
    .atom (.load (.n 2884) (.n 17) 2),
    .atom (.load (.n 2950) (.n 14) 5)] (by decide +kernel) ?_
  intro s hs hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl
  · exact h2499
  · exact h2500
  · exact (vtB_readM hl (vtB_memAt 2501 _ (by decide +kernel)) (by decide +kernel) (hw 5 (by norm_num))).2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem vtB_glue_2528 (hl : args.length = 22) {W : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (vtσ rd wo args (.n 14)) i (W i)) 
    (h2531 : VSH (coreProgram.Rel rd) rd (vtσ rd wo args) (.dispatch (.n 2959) vtImNames [.n 8] [.n 2983]))
    (h2532 : VSH (coreProgram.Rel rd) rd (vtσ rd wo args) (.atom (.load (.n 2983) (.n 2851) 2))) :
    ∀ s ∈ (vtPre.drop 2528).take 58, VSH (coreProgram.Rel rd) rd (vtσ rd wo args) s := by
  refine vtB_blockR hl 2528 58 [
    .atom (.load (.n 2980) (.n 14) 0),
    .dispatch (.n 2959) vtImNames [.n 8] [.n 2983],
    .atom (.load (.n 2983) (.n 2851) 2),
    .atom (.load (.n 2984) (.n 14) 1),
    .atom (.load (.n 2987) (.n 14) 2),
    .atom (.load (.n 2989) (.n 14) 3),
    .atom (.load (.n 2993) (.n 14) 4),
    .atom (.load (.n 2997) (.n 14) 5),
    .atom (.load (.n 3001) (.n 14) 6),
    .atom (.load (.n 3005) (.n 14) 7),
    .atom (.load (.n 3009) (.n 14) 8),
    .atom (.load (.n 3013) (.n 14) 9),
    .atom (.load (.n 3017) (.n 14) 10),
    .atom (.load (.n 3021) (.n 14) 11),
    .atom (.load (.n 3025) (.n 14) 12),
    .atom (.load (.n 3029) (.n 14) 13)] (by decide +kernel) ?_
  intro s hs hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (vtB_readM hl (vtB_memAt 2528 _ (by decide +kernel)) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact h2531
  · exact h2532
  · exact (vtB_readM hl (vtB_memAt 2533 _ (by decide +kernel)) (by decide +kernel) (hw 1 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 2536 _ (by decide +kernel)) (by decide +kernel) (hw 2 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 2538 _ (by decide +kernel)) (by decide +kernel) (hw 3 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 2542 _ (by decide +kernel)) (by decide +kernel) (hw 4 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 2546 _ (by decide +kernel)) (by decide +kernel) (hw 5 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 2550 _ (by decide +kernel)) (by decide +kernel) (hw 6 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 2554 _ (by decide +kernel)) (by decide +kernel) (hw 7 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 2558 _ (by decide +kernel)) (by decide +kernel) (hw 8 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 2562 _ (by decide +kernel)) (by decide +kernel) (hw 9 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 2566 _ (by decide +kernel)) (by decide +kernel) (hw 10 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 2570 _ (by decide +kernel)) (by decide +kernel) (hw 11 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 2574 _ (by decide +kernel)) (by decide +kernel) (hw 12 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 2578 _ (by decide +kernel)) (by decide +kernel) (hw 13 (by norm_num))).2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem vtB_glue_3484 (hl : args.length = 22) {W : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (vtσ rd wo args (.n 14)) i (W i))  :
    ∀ s ∈ (vtPre.drop 3484).take 426, VSH (coreProgram.Rel rd) rd (vtσ rd wo args) s := by
  refine vtB_blockR hl 3484 426 [
    .atom (.load (.n 3986) (.n 14) 0),
    .atom (.load (.n 3989) (.n 14) 0),
    .atom (.load (.n 3993) (.n 14) 3),
    .atom (.load (.n 3997) (.n 14) 0),
    .atom (.load (.n 4003) (.n 14) 0),
    .atom (.load (.n 4009) (.n 14) 0),
    .atom (.load (.n 4016) (.n 14) 0),
    .atom (.load (.n 4019) (.n 14) 0),
    .atom (.load (.n 4023) (.n 14) 3),
    .atom (.load (.n 4029) (.n 14) 0),
    .atom (.load (.n 4035) (.n 14) 0),
    .atom (.load (.n 4041) (.n 14) 0),
    .atom (.load (.n 4049) (.n 14) 0),
    .atom (.load (.n 4052) (.n 14) 0),
    .atom (.load (.n 4056) (.n 14) 3),
    .atom (.load (.n 4062) (.n 14) 0),
    .atom (.load (.n 4070) (.n 14) 0),
    .atom (.load (.n 4073) (.n 14) 0),
    .atom (.load (.n 4077) (.n 14) 3),
    .atom (.load (.n 4083) (.n 14) 0),
    .atom (.load (.n 4089) (.n 14) 0),
    .atom (.load (.n 4095) (.n 14) 0),
    .atom (.load (.n 4103) (.n 14) 0),
    .atom (.load (.n 4106) (.n 14) 0),
    .atom (.load (.n 4110) (.n 14) 3),
    .atom (.load (.n 4116) (.n 14) 0),
    .atom (.load (.n 4122) (.n 14) 0),
    .atom (.load (.n 4128) (.n 14) 0),
    .atom (.load (.n 4136) (.n 14) 0),
    .atom (.load (.n 4139) (.n 14) 0),
    .atom (.load (.n 4143) (.n 14) 3),
    .atom (.load (.n 4149) (.n 14) 0),
    .atom (.load (.n 4155) (.n 14) 0),
    .atom (.load (.n 4161) (.n 14) 0),
    .atom (.load (.n 4167) (.n 14) 0),
    .atom (.load (.n 4173) (.n 14) 0),
    .atom (.load (.n 4179) (.n 14) 0),
    .atom (.load (.n 4185) (.n 14) 0),
    .atom (.load (.n 4191) (.n 14) 0),
    .atom (.load (.n 4197) (.n 14) 0),
    .atom (.load (.n 4203) (.n 14) 0),
    .atom (.load (.n 4209) (.n 14) 0),
    .atom (.load (.n 4215) (.n 14) 0),
    .atom (.load (.n 4221) (.n 14) 0),
    .atom (.load (.n 4227) (.n 14) 0),
    .atom (.load (.n 4231) (.n 14) 3),
    .atom (.load (.n 4235) (.n 14) 4),
    .atom (.load (.n 4241) (.n 14) 0),
    .atom (.load (.n 4245) (.n 14) 3),
    .atom (.load (.n 4249) (.n 14) 4),
    .atom (.load (.n 4255) (.n 14) 0),
    .atom (.load (.n 4259) (.n 14) 3),
    .atom (.load (.n 4263) (.n 14) 4),
    .atom (.load (.n 4269) (.n 14) 0),
    .atom (.load (.n 4273) (.n 14) 3),
    .atom (.load (.n 4277) (.n 14) 4),
    .atom (.load (.n 4283) (.n 14) 0),
    .atom (.load (.n 4287) (.n 14) 3),
    .atom (.load (.n 4291) (.n 14) 4),
    .atom (.load (.n 4297) (.n 14) 0),
    .atom (.load (.n 4301) (.n 14) 3),
    .atom (.load (.n 4305) (.n 14) 4),
    .atom (.load (.n 4311) (.n 14) 0),
    .atom (.load (.n 4315) (.n 14) 3),
    .atom (.load (.n 4319) (.n 14) 4),
    .atom (.load (.n 4325) (.n 14) 0),
    .atom (.load (.n 4329) (.n 14) 3),
    .atom (.load (.n 4333) (.n 14) 4),
    .atom (.load (.n 4339) (.n 14) 0),
    .atom (.load (.n 4343) (.n 14) 3),
    .atom (.load (.n 4349) (.n 14) 0),
    .atom (.load (.n 4353) (.n 14) 3),
    .atom (.load (.n 4357) (.n 14) 4),
    .atom (.load (.n 4363) (.n 14) 0),
    .atom (.load (.n 4367) (.n 14) 3),
    .atom (.load (.n 4371) (.n 14) 4),
    .atom (.load (.n 4377) (.n 14) 0),
    .atom (.load (.n 4381) (.n 14) 3),
    .atom (.load (.n 4385) (.n 14) 4),
    .atom (.load (.n 4391) (.n 14) 0),
    .atom (.load (.n 4395) (.n 14) 3),
    .atom (.load (.n 4399) (.n 14) 4)] (by decide +kernel) ?_
  intro s hs hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (vtB_readM hl (vtB_memAt 3484 _ (by decide +kernel)) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3487 _ (by decide +kernel)) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3491 _ (by decide +kernel)) (by decide +kernel) (hw 3 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3495 _ (by decide +kernel)) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3501 _ (by decide +kernel)) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3507 _ (by decide +kernel)) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3514 _ (by decide +kernel)) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3517 _ (by decide +kernel)) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3521 _ (by decide +kernel)) (by decide +kernel) (hw 3 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3527 _ (by decide +kernel)) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3533 _ (by decide +kernel)) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3539 _ (by decide +kernel)) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3547 _ (by decide +kernel)) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3550 _ (by decide +kernel)) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3554 _ (by decide +kernel)) (by decide +kernel) (hw 3 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3560 _ (by decide +kernel)) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3568 _ (by decide +kernel)) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3571 _ (by decide +kernel)) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3575 _ (by decide +kernel)) (by decide +kernel) (hw 3 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3581 _ (by decide +kernel)) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3587 _ (by decide +kernel)) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3593 _ (by decide +kernel)) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3601 _ (by decide +kernel)) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3604 _ (by decide +kernel)) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3608 _ (by decide +kernel)) (by decide +kernel) (hw 3 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3614 _ (by decide +kernel)) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3620 _ (by decide +kernel)) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3626 _ (by decide +kernel)) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3634 _ (by decide +kernel)) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3637 _ (by decide +kernel)) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3641 _ (by decide +kernel)) (by decide +kernel) (hw 3 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3647 _ (by decide +kernel)) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3653 _ (by decide +kernel)) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3659 _ (by decide +kernel)) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3665 _ (by decide +kernel)) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3671 _ (by decide +kernel)) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3677 _ (by decide +kernel)) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3683 _ (by decide +kernel)) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3689 _ (by decide +kernel)) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3695 _ (by decide +kernel)) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3701 _ (by decide +kernel)) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3707 _ (by decide +kernel)) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3713 _ (by decide +kernel)) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3719 _ (by decide +kernel)) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3725 _ (by decide +kernel)) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3729 _ (by decide +kernel)) (by decide +kernel) (hw 3 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3733 _ (by decide +kernel)) (by decide +kernel) (hw 4 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3739 _ (by decide +kernel)) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3743 _ (by decide +kernel)) (by decide +kernel) (hw 3 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3747 _ (by decide +kernel)) (by decide +kernel) (hw 4 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3753 _ (by decide +kernel)) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3757 _ (by decide +kernel)) (by decide +kernel) (hw 3 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3761 _ (by decide +kernel)) (by decide +kernel) (hw 4 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3767 _ (by decide +kernel)) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3771 _ (by decide +kernel)) (by decide +kernel) (hw 3 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3775 _ (by decide +kernel)) (by decide +kernel) (hw 4 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3781 _ (by decide +kernel)) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3785 _ (by decide +kernel)) (by decide +kernel) (hw 3 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3789 _ (by decide +kernel)) (by decide +kernel) (hw 4 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3795 _ (by decide +kernel)) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3799 _ (by decide +kernel)) (by decide +kernel) (hw 3 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3803 _ (by decide +kernel)) (by decide +kernel) (hw 4 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3809 _ (by decide +kernel)) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3813 _ (by decide +kernel)) (by decide +kernel) (hw 3 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3817 _ (by decide +kernel)) (by decide +kernel) (hw 4 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3823 _ (by decide +kernel)) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3827 _ (by decide +kernel)) (by decide +kernel) (hw 3 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3831 _ (by decide +kernel)) (by decide +kernel) (hw 4 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3837 _ (by decide +kernel)) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3841 _ (by decide +kernel)) (by decide +kernel) (hw 3 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3847 _ (by decide +kernel)) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3851 _ (by decide +kernel)) (by decide +kernel) (hw 3 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3855 _ (by decide +kernel)) (by decide +kernel) (hw 4 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3861 _ (by decide +kernel)) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3865 _ (by decide +kernel)) (by decide +kernel) (hw 3 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3869 _ (by decide +kernel)) (by decide +kernel) (hw 4 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3875 _ (by decide +kernel)) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3879 _ (by decide +kernel)) (by decide +kernel) (hw 3 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3883 _ (by decide +kernel)) (by decide +kernel) (hw 4 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3889 _ (by decide +kernel)) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3893 _ (by decide +kernel)) (by decide +kernel) (hw 3 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3897 _ (by decide +kernel)) (by decide +kernel) (hw 4 (by norm_num))).2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem vtB_glue_3910 (hl : args.length = 22) {W : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (vtσ rd wo args (.n 14)) i (W i)) {κ : ℕ → ℕ}
    (hbkc : ∀ b < 153, LoadHolds rd (vtσ rd wo args (.n 12)) b (gen ^ κ b))
    (hκ : ∀ b < 153, κ b < 34) {Q : ℕ → E}
    (hidx : ∀ i < 3, LoadHolds rd (vtσ rd wo args (.n 2851)) i (Q i)) 
    (hlow : ∀ i < 34, (rd (Parameters.gpow i)).isSome) :
    ∀ s ∈ (vtPre.drop 3910).take 28, VSH (coreProgram.Rel rd) rd (vtσ rd wo args) s := by
  refine vtB_blockR hl 3910 28 [
    .atom (.load (.n 4412) (.n 12) 54),
    .atom (.rangeCheck (.n 4412) (.n 4414) (.n 4415) (.n 4416) (.n 4413)),
    .atom (.load (.n 4418) (.n 14) 0),
    .atom (.load (.n 4419) (.n 14) 1),
    .atom (.load (.n 4423) (.n 14) 2),
    .atom (.load (.n 4430) (.n 12) 55),
    .atom (.rangeCheck (.n 4430) (.n 4432) (.n 4433) (.n 4434) (.n 4431)),
    .atom (.load (.n 4437) (.n 14) 0),
    .atom (.load (.n 4440) (.n 2851) 1),
    .atom (.load (.n 4441) (.n 14) 1)] (by decide +kernel) ?_
  intro s hs hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (vtB_readM hl (vtB_memAt 3910 _ (by decide +kernel)) (by decide +kernel) (hbkc 54 (by norm_num))).2
  · exact vshB_rcM hl (vtB_memAt 3912 _ (by decide +kernel)) (by simp) (K := 34)
      (vtB_readM hl (vtB_memAt 3910 _ (by decide +kernel)) (by decide +kernel) (hbkc 54 (by norm_num))).1
      (by rw [vtB_const hl (vtB_memAt 3911 (.atom (.const (.n 4413) (word 8589934592 0 0))) (by decide +kernel))]; exact vtB_w33) (hκ 54 (by norm_num)) hlow
  · exact (vtB_readM hl (vtB_memAt 3914 _ (by decide +kernel)) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3915 _ (by decide +kernel)) (by decide +kernel) (hw 1 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3919 _ (by decide +kernel)) (by decide +kernel) (hw 2 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3926 _ (by decide +kernel)) (by decide +kernel) (hbkc 55 (by norm_num))).2
  · exact vshB_rcM hl (vtB_memAt 3928 _ (by decide +kernel)) (by simp) (K := 34)
      (vtB_readM hl (vtB_memAt 3926 _ (by decide +kernel)) (by decide +kernel) (hbkc 55 (by norm_num))).1
      (by rw [vtB_const hl (vtB_memAt 3927 (.atom (.const (.n 4431) (word 8589934592 0 0))) (by decide +kernel))]; exact vtB_w33) (hκ 55 (by norm_num)) hlow
  · exact (vtB_readM hl (vtB_memAt 3931 _ (by decide +kernel)) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3934 _ (by decide +kernel)) (by decide +kernel) (hidx 1 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3935 _ (by decide +kernel)) (by decide +kernel) (hw 1 (by norm_num))).2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem vtB_glue_3947 (hl : args.length = 22) {W : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (vtσ rd wo args (.n 14)) i (W i)) {κ : ℕ → ℕ}
    (hbkc : ∀ b < 153, LoadHolds rd (vtσ rd wo args (.n 12)) b (gen ^ κ b))
    (hκ : ∀ b < 153, κ b < 34) {P : ℕ → E}
    (hpool : ∀ i < 5, LoadHolds rd (vtσ rd wo args (.n 16)) i (P i)) {Q : ℕ → E}
    (hidx : ∀ i < 3, LoadHolds rd (vtσ rd wo args (.n 2851)) i (Q i)) 
    (hlow : ∀ i < 34, (rd (Parameters.gpow i)).isSome)
    (h3947 : VSH (coreProgram.Rel rd) rd (vtσ rd wo args) (.atom (.load (.n 4444) (.n 16) 3)))
    (h3948 : VSH (coreProgram.Rel rd) rd (vtσ rd wo args) (.atom (.load (.n 4430) (.n 17) 3)))
    (h3982 : VSH (coreProgram.Rel rd) rd (vtσ rd wo args) (.atom (.keccak [.n 2921, .n 2923, .n 2934, .n 2936, .n 2947, .n 2949, .n 4451, .n 4453, .n 22, .n 23, .n 24, .n 25, .n 26] [.n 4489, .n 4490, .n 4491, .n 4492, .n 4493, .n 4494, .n 4495, .n 4496, .n 4497, .n 4498, .n 4499, .n 4500, .n 4501] false false))) :
    ∀ s ∈ (vtPre.drop 3947).take 36, VSH (coreProgram.Rel rd) rd (vtσ rd wo args) s := by
  refine vtB_blockR hl 3947 36 [
    .atom (.load (.n 4444) (.n 16) 3),
    .atom (.load (.n 4430) (.n 17) 3),
    .atom (.load (.n 4454) (.n 14) 2),
    .atom (.load (.n 4457) (.n 16) 0),
    .atom (.load (.n 4458) (.n 14) 3),
    .atom (.load (.n 4461) (.n 16) 1),
    .atom (.load (.n 4462) (.n 14) 4),
    .atom (.load (.n 4465) (.n 16) 2),
    .atom (.load (.n 4466) (.n 14) 5),
    .atom (.load (.n 4475) (.n 12) 56),
    .atom (.rangeCheck (.n 4475) (.n 4477) (.n 4478) (.n 4479) (.n 4476)),
    .atom (.load (.n 4482) (.n 14) 0),
    .atom (.load (.n 4485) (.n 2851) 2),
    .atom (.load (.n 4486) (.n 14) 1),
    .atom (.keccak [.n 2921, .n 2923, .n 2934, .n 2936, .n 2947, .n 2949, .n 4451, .n 4453, .n 22, .n 23, .n 24, .n 25, .n 26] [.n 4489, .n 4490, .n 4491, .n 4492, .n 4493, .n 4494, .n 4495, .n 4496, .n 4497, .n 4498, .n 4499, .n 4500, .n 4501] false false)] (by decide +kernel) ?_
  intro s hs hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h3947
  · exact h3948
  · exact (vtB_readM hl (vtB_memAt 3949 _ (by decide +kernel)) (by decide +kernel) (hw 2 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3952 _ (by decide +kernel)) (by decide +kernel) (hpool 0 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3953 _ (by decide +kernel)) (by decide +kernel) (hw 3 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3956 _ (by decide +kernel)) (by decide +kernel) (hpool 1 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3957 _ (by decide +kernel)) (by decide +kernel) (hw 4 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3960 _ (by decide +kernel)) (by decide +kernel) (hpool 2 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3961 _ (by decide +kernel)) (by decide +kernel) (hw 5 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3970 _ (by decide +kernel)) (by decide +kernel) (hbkc 56 (by norm_num))).2
  · exact vshB_rcM hl (vtB_memAt 3972 _ (by decide +kernel)) (by simp) (K := 34)
      (vtB_readM hl (vtB_memAt 3970 _ (by decide +kernel)) (by decide +kernel) (hbkc 56 (by norm_num))).1
      (by rw [vtB_const hl (vtB_memAt 3971 (.atom (.const (.n 4476) (word 8589934592 0 0))) (by decide +kernel))]; exact vtB_w33) (hκ 56 (by norm_num)) hlow
  · exact (vtB_readM hl (vtB_memAt 3975 _ (by decide +kernel)) (by decide +kernel) (hw 0 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3978 _ (by decide +kernel)) (by decide +kernel) (hidx 2 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3979 _ (by decide +kernel)) (by decide +kernel) (hw 1 (by norm_num))).2
  · exact h3982

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem vtB_glue_3992 (hl : args.length = 22) {W : ℕ → E}
    (hw : ∀ i < 16, LoadHolds rd (vtσ rd wo args (.n 14)) i (W i)) {κ : ℕ → ℕ}
    (hbkc : ∀ b < 153, LoadHolds rd (vtσ rd wo args (.n 12)) b (gen ^ κ b))
    (hκ : ∀ b < 153, κ b < 34) 
    (hlow : ∀ i < 34, (rd (Parameters.gpow i)).isSome)
    (h3992 : VSH (coreProgram.Rel rd) rd (vtσ rd wo args) (.atom (.load (.n 4502) (.n 16) 4)))
    (h3993 : VSH (coreProgram.Rel rd) rd (vtσ rd wo args) (.atom (.load (.n 4475) (.n 17) 4))) :
    ∀ s ∈ (vtPre.drop 3992).take 313, VSH (coreProgram.Rel rd) rd (vtσ rd wo args) s := by
  refine vtB_blockR hl 3992 313 [
    .atom (.load (.n 4502) (.n 16) 4),
    .atom (.load (.n 4475) (.n 17) 4),
    .atom (.load (.n 4512) (.n 14) 2),
    .atom (.load (.n 4515) (.n 14) 3),
    .atom (.load (.n 4519) (.n 14) 4),
    .atom (.load (.n 4523) (.n 14) 5),
    .atom (.load (.n 4527) (.n 14) 6),
    .atom (.load (.n 4531) (.n 14) 7),
    .atom (.load (.n 4535) (.n 14) 8),
    .atom (.load (.n 4539) (.n 14) 9),
    .atom (.load (.n 4543) (.n 14) 10),
    .atom (.load (.n 4547) (.n 14) 11),
    .atom (.load (.n 4551) (.n 14) 12),
    .atom (.load (.n 4555) (.n 14) 13),
    .atom (.load (.n 4563) (.n 12) 57),
    .atom (.rangeCheck (.n 4563) (.n 4565) (.n 4566) (.n 4567) (.n 4564)),
    .atom (.load (.n 4570) (.n 12) 58),
    .atom (.rangeCheck (.n 4570) (.n 4572) (.n 4573) (.n 4574) (.n 4571)),
    .atom (.load (.n 4577) (.n 12) 59),
    .atom (.rangeCheck (.n 4577) (.n 4579) (.n 4580) (.n 4581) (.n 4578)),
    .atom (.load (.n 4584) (.n 12) 60),
    .atom (.rangeCheck (.n 4584) (.n 4586) (.n 4587) (.n 4588) (.n 4585)),
    .atom (.load (.n 4591) (.n 12) 61),
    .atom (.rangeCheck (.n 4591) (.n 4593) (.n 4594) (.n 4595) (.n 4592)),
    .atom (.load (.n 4598) (.n 12) 62),
    .atom (.rangeCheck (.n 4598) (.n 4600) (.n 4601) (.n 4602) (.n 4599)),
    .atom (.load (.n 4605) (.n 12) 63),
    .atom (.rangeCheck (.n 4605) (.n 4607) (.n 4608) (.n 4609) (.n 4606)),
    .atom (.load (.n 4612) (.n 12) 64),
    .atom (.rangeCheck (.n 4612) (.n 4614) (.n 4615) (.n 4616) (.n 4613)),
    .atom (.load (.n 4619) (.n 12) 65),
    .atom (.rangeCheck (.n 4619) (.n 4621) (.n 4622) (.n 4623) (.n 4620)),
    .atom (.load (.n 4626) (.n 12) 66),
    .atom (.rangeCheck (.n 4626) (.n 4628) (.n 4629) (.n 4630) (.n 4627)),
    .atom (.load (.n 4633) (.n 12) 67),
    .atom (.rangeCheck (.n 4633) (.n 4635) (.n 4636) (.n 4637) (.n 4634)),
    .atom (.load (.n 4640) (.n 12) 68),
    .atom (.rangeCheck (.n 4640) (.n 4642) (.n 4643) (.n 4644) (.n 4641)),
    .atom (.load (.n 4647) (.n 12) 69),
    .atom (.rangeCheck (.n 4647) (.n 4649) (.n 4650) (.n 4651) (.n 4648)),
    .atom (.load (.n 4654) (.n 12) 70),
    .atom (.rangeCheck (.n 4654) (.n 4656) (.n 4657) (.n 4658) (.n 4655)),
    .atom (.load (.n 4661) (.n 12) 71),
    .atom (.rangeCheck (.n 4661) (.n 4663) (.n 4664) (.n 4665) (.n 4662)),
    .atom (.load (.n 4668) (.n 12) 72),
    .atom (.rangeCheck (.n 4668) (.n 4670) (.n 4671) (.n 4672) (.n 4669)),
    .atom (.load (.n 4675) (.n 12) 73),
    .atom (.rangeCheck (.n 4675) (.n 4677) (.n 4678) (.n 4679) (.n 4676)),
    .atom (.load (.n 4682) (.n 12) 74),
    .atom (.rangeCheck (.n 4682) (.n 4684) (.n 4685) (.n 4686) (.n 4683)),
    .atom (.load (.n 4689) (.n 12) 75),
    .atom (.rangeCheck (.n 4689) (.n 4691) (.n 4692) (.n 4693) (.n 4690)),
    .atom (.load (.n 4696) (.n 12) 76),
    .atom (.rangeCheck (.n 4696) (.n 4698) (.n 4699) (.n 4700) (.n 4697)),
    .atom (.load (.n 4703) (.n 12) 77),
    .atom (.rangeCheck (.n 4703) (.n 4705) (.n 4706) (.n 4707) (.n 4704)),
    .atom (.load (.n 4710) (.n 12) 78),
    .atom (.rangeCheck (.n 4710) (.n 4712) (.n 4713) (.n 4714) (.n 4711)),
    .atom (.load (.n 4717) (.n 12) 79),
    .atom (.rangeCheck (.n 4717) (.n 4719) (.n 4720) (.n 4721) (.n 4718)),
    .atom (.load (.n 4724) (.n 12) 80),
    .atom (.rangeCheck (.n 4724) (.n 4726) (.n 4727) (.n 4728) (.n 4725)),
    .atom (.load (.n 4731) (.n 12) 81),
    .atom (.rangeCheck (.n 4731) (.n 4733) (.n 4734) (.n 4735) (.n 4732)),
    .atom (.load (.n 4738) (.n 12) 82),
    .atom (.rangeCheck (.n 4738) (.n 4740) (.n 4741) (.n 4742) (.n 4739)),
    .atom (.load (.n 4745) (.n 12) 83),
    .atom (.rangeCheck (.n 4745) (.n 4747) (.n 4748) (.n 4749) (.n 4746)),
    .atom (.load (.n 4752) (.n 12) 84),
    .atom (.rangeCheck (.n 4752) (.n 4754) (.n 4755) (.n 4756) (.n 4753)),
    .atom (.load (.n 4759) (.n 12) 85),
    .atom (.rangeCheck (.n 4759) (.n 4761) (.n 4762) (.n 4763) (.n 4760)),
    .atom (.load (.n 4766) (.n 12) 86),
    .atom (.rangeCheck (.n 4766) (.n 4768) (.n 4769) (.n 4770) (.n 4767)),
    .atom (.load (.n 4773) (.n 12) 87),
    .atom (.rangeCheck (.n 4773) (.n 4775) (.n 4776) (.n 4777) (.n 4774)),
    .atom (.load (.n 4780) (.n 12) 88),
    .atom (.rangeCheck (.n 4780) (.n 4782) (.n 4783) (.n 4784) (.n 4781)),
    .atom (.load (.n 4787) (.n 12) 89),
    .atom (.rangeCheck (.n 4787) (.n 4789) (.n 4790) (.n 4791) (.n 4788)),
    .atom (.load (.n 4794) (.n 12) 90),
    .atom (.rangeCheck (.n 4794) (.n 4796) (.n 4797) (.n 4798) (.n 4795)),
    .atom (.load (.n 4801) (.n 12) 91),
    .atom (.rangeCheck (.n 4801) (.n 4803) (.n 4804) (.n 4805) (.n 4802)),
    .atom (.load (.n 4808) (.n 12) 92),
    .atom (.rangeCheck (.n 4808) (.n 4810) (.n 4811) (.n 4812) (.n 4809)),
    .atom (.load (.n 4815) (.n 12) 93),
    .atom (.rangeCheck (.n 4815) (.n 4817) (.n 4818) (.n 4819) (.n 4816)),
    .atom (.load (.n 4822) (.n 12) 94),
    .atom (.rangeCheck (.n 4822) (.n 4824) (.n 4825) (.n 4826) (.n 4823)),
    .atom (.load (.n 4829) (.n 12) 95),
    .atom (.rangeCheck (.n 4829) (.n 4831) (.n 4832) (.n 4833) (.n 4830)),
    .atom (.load (.n 4836) (.n 12) 96),
    .atom (.rangeCheck (.n 4836) (.n 4838) (.n 4839) (.n 4840) (.n 4837)),
    .atom (.load (.n 4843) (.n 12) 97),
    .atom (.rangeCheck (.n 4843) (.n 4845) (.n 4846) (.n 4847) (.n 4844)),
    .atom (.load (.n 4850) (.n 12) 98),
    .atom (.rangeCheck (.n 4850) (.n 4852) (.n 4853) (.n 4854) (.n 4851)),
    .atom (.load (.n 4857) (.n 12) 99),
    .atom (.rangeCheck (.n 4857) (.n 4859) (.n 4860) (.n 4861) (.n 4858)),
    .atom (.load (.n 4864) (.n 12) 100),
    .atom (.rangeCheck (.n 4864) (.n 4866) (.n 4867) (.n 4868) (.n 4865)),
    .atom (.load (.n 4871) (.n 12) 101),
    .atom (.rangeCheck (.n 4871) (.n 4873) (.n 4874) (.n 4875) (.n 4872)),
    .atom (.load (.n 4878) (.n 12) 102),
    .atom (.rangeCheck (.n 4878) (.n 4880) (.n 4881) (.n 4882) (.n 4879)),
    .atom (.load (.n 4885) (.n 12) 103),
    .atom (.rangeCheck (.n 4885) (.n 4887) (.n 4888) (.n 4889) (.n 4886)),
    .atom (.load (.n 4892) (.n 12) 104),
    .atom (.rangeCheck (.n 4892) (.n 4894) (.n 4895) (.n 4896) (.n 4893)),
    .atom (.load (.n 4899) (.n 12) 105),
    .atom (.rangeCheck (.n 4899) (.n 4901) (.n 4902) (.n 4903) (.n 4900)),
    .atom (.load (.n 4906) (.n 12) 106),
    .atom (.rangeCheck (.n 4906) (.n 4908) (.n 4909) (.n 4910) (.n 4907)),
    .atom (.load (.n 4913) (.n 12) 107),
    .atom (.rangeCheck (.n 4913) (.n 4915) (.n 4916) (.n 4917) (.n 4914))] (by decide +kernel) ?_
  intro s hs hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h3992
  · exact h3993
  · exact (vtB_readM hl (vtB_memAt 3994 _ (by decide +kernel)) (by decide +kernel) (hw 2 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 3997 _ (by decide +kernel)) (by decide +kernel) (hw 3 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 4001 _ (by decide +kernel)) (by decide +kernel) (hw 4 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 4005 _ (by decide +kernel)) (by decide +kernel) (hw 5 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 4009 _ (by decide +kernel)) (by decide +kernel) (hw 6 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 4013 _ (by decide +kernel)) (by decide +kernel) (hw 7 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 4017 _ (by decide +kernel)) (by decide +kernel) (hw 8 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 4021 _ (by decide +kernel)) (by decide +kernel) (hw 9 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 4025 _ (by decide +kernel)) (by decide +kernel) (hw 10 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 4029 _ (by decide +kernel)) (by decide +kernel) (hw 11 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 4033 _ (by decide +kernel)) (by decide +kernel) (hw 12 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 4037 _ (by decide +kernel)) (by decide +kernel) (hw 13 (by norm_num))).2
  · exact (vtB_readM hl (vtB_memAt 4045 _ (by decide +kernel)) (by decide +kernel) (hbkc 57 (by norm_num))).2
  · exact vshB_rcM hl (vtB_memAt 4047 _ (by decide +kernel)) (by simp) (K := 34)
      (vtB_readM hl (vtB_memAt 4045 _ (by decide +kernel)) (by decide +kernel) (hbkc 57 (by norm_num))).1
      (by rw [vtB_const hl (vtB_memAt 4046 (.atom (.const (.n 4564) (word 8589934592 0 0))) (by decide +kernel))]; exact vtB_w33) (hκ 57 (by norm_num)) hlow
  · exact (vtB_readM hl (vtB_memAt 4050 _ (by decide +kernel)) (by decide +kernel) (hbkc 58 (by norm_num))).2
  · exact vshB_rcM hl (vtB_memAt 4052 _ (by decide +kernel)) (by simp) (K := 34)
      (vtB_readM hl (vtB_memAt 4050 _ (by decide +kernel)) (by decide +kernel) (hbkc 58 (by norm_num))).1
      (by rw [vtB_const hl (vtB_memAt 4051 (.atom (.const (.n 4571) (word 8589934592 0 0))) (by decide +kernel))]; exact vtB_w33) (hκ 58 (by norm_num)) hlow
  · exact (vtB_readM hl (vtB_memAt 4055 _ (by decide +kernel)) (by decide +kernel) (hbkc 59 (by norm_num))).2
  · exact vshB_rcM hl (vtB_memAt 4057 _ (by decide +kernel)) (by simp) (K := 34)
      (vtB_readM hl (vtB_memAt 4055 _ (by decide +kernel)) (by decide +kernel) (hbkc 59 (by norm_num))).1
      (by rw [vtB_const hl (vtB_memAt 4056 (.atom (.const (.n 4578) (word 8589934592 0 0))) (by decide +kernel))]; exact vtB_w33) (hκ 59 (by norm_num)) hlow
  · exact (vtB_readM hl (vtB_memAt 4060 _ (by decide +kernel)) (by decide +kernel) (hbkc 60 (by norm_num))).2
  · exact vshB_rcM hl (vtB_memAt 4062 _ (by decide +kernel)) (by simp) (K := 34)
      (vtB_readM hl (vtB_memAt 4060 _ (by decide +kernel)) (by decide +kernel) (hbkc 60 (by norm_num))).1
      (by rw [vtB_const hl (vtB_memAt 4061 (.atom (.const (.n 4585) (word 8589934592 0 0))) (by decide +kernel))]; exact vtB_w33) (hκ 60 (by norm_num)) hlow
  · exact (vtB_readM hl (vtB_memAt 4065 _ (by decide +kernel)) (by decide +kernel) (hbkc 61 (by norm_num))).2
  · exact vshB_rcM hl (vtB_memAt 4067 _ (by decide +kernel)) (by simp) (K := 34)
      (vtB_readM hl (vtB_memAt 4065 _ (by decide +kernel)) (by decide +kernel) (hbkc 61 (by norm_num))).1
      (by rw [vtB_const hl (vtB_memAt 4066 (.atom (.const (.n 4592) (word 8589934592 0 0))) (by decide +kernel))]; exact vtB_w33) (hκ 61 (by norm_num)) hlow
  · exact (vtB_readM hl (vtB_memAt 4070 _ (by decide +kernel)) (by decide +kernel) (hbkc 62 (by norm_num))).2
  · exact vshB_rcM hl (vtB_memAt 4072 _ (by decide +kernel)) (by simp) (K := 34)
      (vtB_readM hl (vtB_memAt 4070 _ (by decide +kernel)) (by decide +kernel) (hbkc 62 (by norm_num))).1
      (by rw [vtB_const hl (vtB_memAt 4071 (.atom (.const (.n 4599) (word 8589934592 0 0))) (by decide +kernel))]; exact vtB_w33) (hκ 62 (by norm_num)) hlow
  · exact (vtB_readM hl (vtB_memAt 4075 _ (by decide +kernel)) (by decide +kernel) (hbkc 63 (by norm_num))).2
  · exact vshB_rcM hl (vtB_memAt 4077 _ (by decide +kernel)) (by simp) (K := 34)
      (vtB_readM hl (vtB_memAt 4075 _ (by decide +kernel)) (by decide +kernel) (hbkc 63 (by norm_num))).1
      (by rw [vtB_const hl (vtB_memAt 4076 (.atom (.const (.n 4606) (word 8589934592 0 0))) (by decide +kernel))]; exact vtB_w33) (hκ 63 (by norm_num)) hlow
  · exact (vtB_readM hl (vtB_memAt 4080 _ (by decide +kernel)) (by decide +kernel) (hbkc 64 (by norm_num))).2
  · exact vshB_rcM hl (vtB_memAt 4082 _ (by decide +kernel)) (by simp) (K := 34)
      (vtB_readM hl (vtB_memAt 4080 _ (by decide +kernel)) (by decide +kernel) (hbkc 64 (by norm_num))).1
      (by rw [vtB_const hl (vtB_memAt 4081 (.atom (.const (.n 4613) (word 8589934592 0 0))) (by decide +kernel))]; exact vtB_w33) (hκ 64 (by norm_num)) hlow
  · exact (vtB_readM hl (vtB_memAt 4085 _ (by decide +kernel)) (by decide +kernel) (hbkc 65 (by norm_num))).2
  · exact vshB_rcM hl (vtB_memAt 4087 _ (by decide +kernel)) (by simp) (K := 34)
      (vtB_readM hl (vtB_memAt 4085 _ (by decide +kernel)) (by decide +kernel) (hbkc 65 (by norm_num))).1
      (by rw [vtB_const hl (vtB_memAt 4086 (.atom (.const (.n 4620) (word 8589934592 0 0))) (by decide +kernel))]; exact vtB_w33) (hκ 65 (by norm_num)) hlow
  · exact (vtB_readM hl (vtB_memAt 4090 _ (by decide +kernel)) (by decide +kernel) (hbkc 66 (by norm_num))).2
  · exact vshB_rcM hl (vtB_memAt 4092 _ (by decide +kernel)) (by simp) (K := 34)
      (vtB_readM hl (vtB_memAt 4090 _ (by decide +kernel)) (by decide +kernel) (hbkc 66 (by norm_num))).1
      (by rw [vtB_const hl (vtB_memAt 4091 (.atom (.const (.n 4627) (word 8589934592 0 0))) (by decide +kernel))]; exact vtB_w33) (hκ 66 (by norm_num)) hlow
  · exact (vtB_readM hl (vtB_memAt 4095 _ (by decide +kernel)) (by decide +kernel) (hbkc 67 (by norm_num))).2
  · exact vshB_rcM hl (vtB_memAt 4097 _ (by decide +kernel)) (by simp) (K := 34)
      (vtB_readM hl (vtB_memAt 4095 _ (by decide +kernel)) (by decide +kernel) (hbkc 67 (by norm_num))).1
      (by rw [vtB_const hl (vtB_memAt 4096 (.atom (.const (.n 4634) (word 8589934592 0 0))) (by decide +kernel))]; exact vtB_w33) (hκ 67 (by norm_num)) hlow
  · exact (vtB_readM hl (vtB_memAt 4100 _ (by decide +kernel)) (by decide +kernel) (hbkc 68 (by norm_num))).2
  · exact vshB_rcM hl (vtB_memAt 4102 _ (by decide +kernel)) (by simp) (K := 34)
      (vtB_readM hl (vtB_memAt 4100 _ (by decide +kernel)) (by decide +kernel) (hbkc 68 (by norm_num))).1
      (by rw [vtB_const hl (vtB_memAt 4101 (.atom (.const (.n 4641) (word 8589934592 0 0))) (by decide +kernel))]; exact vtB_w33) (hκ 68 (by norm_num)) hlow
  · exact (vtB_readM hl (vtB_memAt 4105 _ (by decide +kernel)) (by decide +kernel) (hbkc 69 (by norm_num))).2
  · exact vshB_rcM hl (vtB_memAt 4107 _ (by decide +kernel)) (by simp) (K := 34)
      (vtB_readM hl (vtB_memAt 4105 _ (by decide +kernel)) (by decide +kernel) (hbkc 69 (by norm_num))).1
      (by rw [vtB_const hl (vtB_memAt 4106 (.atom (.const (.n 4648) (word 8589934592 0 0))) (by decide +kernel))]; exact vtB_w33) (hκ 69 (by norm_num)) hlow
  · exact (vtB_readM hl (vtB_memAt 4110 _ (by decide +kernel)) (by decide +kernel) (hbkc 70 (by norm_num))).2
  · exact vshB_rcM hl (vtB_memAt 4112 _ (by decide +kernel)) (by simp) (K := 34)
      (vtB_readM hl (vtB_memAt 4110 _ (by decide +kernel)) (by decide +kernel) (hbkc 70 (by norm_num))).1
      (by rw [vtB_const hl (vtB_memAt 4111 (.atom (.const (.n 4655) (word 8589934592 0 0))) (by decide +kernel))]; exact vtB_w33) (hκ 70 (by norm_num)) hlow
  · exact (vtB_readM hl (vtB_memAt 4115 _ (by decide +kernel)) (by decide +kernel) (hbkc 71 (by norm_num))).2
  · exact vshB_rcM hl (vtB_memAt 4117 _ (by decide +kernel)) (by simp) (K := 34)
      (vtB_readM hl (vtB_memAt 4115 _ (by decide +kernel)) (by decide +kernel) (hbkc 71 (by norm_num))).1
      (by rw [vtB_const hl (vtB_memAt 4116 (.atom (.const (.n 4662) (word 8589934592 0 0))) (by decide +kernel))]; exact vtB_w33) (hκ 71 (by norm_num)) hlow
  · exact (vtB_readM hl (vtB_memAt 4120 _ (by decide +kernel)) (by decide +kernel) (hbkc 72 (by norm_num))).2
  · exact vshB_rcM hl (vtB_memAt 4122 _ (by decide +kernel)) (by simp) (K := 34)
      (vtB_readM hl (vtB_memAt 4120 _ (by decide +kernel)) (by decide +kernel) (hbkc 72 (by norm_num))).1
      (by rw [vtB_const hl (vtB_memAt 4121 (.atom (.const (.n 4669) (word 8589934592 0 0))) (by decide +kernel))]; exact vtB_w33) (hκ 72 (by norm_num)) hlow
  · exact (vtB_readM hl (vtB_memAt 4125 _ (by decide +kernel)) (by decide +kernel) (hbkc 73 (by norm_num))).2
  · exact vshB_rcM hl (vtB_memAt 4127 _ (by decide +kernel)) (by simp) (K := 34)
      (vtB_readM hl (vtB_memAt 4125 _ (by decide +kernel)) (by decide +kernel) (hbkc 73 (by norm_num))).1
      (by rw [vtB_const hl (vtB_memAt 4126 (.atom (.const (.n 4676) (word 8589934592 0 0))) (by decide +kernel))]; exact vtB_w33) (hκ 73 (by norm_num)) hlow
  · exact (vtB_readM hl (vtB_memAt 4130 _ (by decide +kernel)) (by decide +kernel) (hbkc 74 (by norm_num))).2
  · exact vshB_rcM hl (vtB_memAt 4132 _ (by decide +kernel)) (by simp) (K := 34)
      (vtB_readM hl (vtB_memAt 4130 _ (by decide +kernel)) (by decide +kernel) (hbkc 74 (by norm_num))).1
      (by rw [vtB_const hl (vtB_memAt 4131 (.atom (.const (.n 4683) (word 8589934592 0 0))) (by decide +kernel))]; exact vtB_w33) (hκ 74 (by norm_num)) hlow
  · exact (vtB_readM hl (vtB_memAt 4135 _ (by decide +kernel)) (by decide +kernel) (hbkc 75 (by norm_num))).2
  · exact vshB_rcM hl (vtB_memAt 4137 _ (by decide +kernel)) (by simp) (K := 34)
      (vtB_readM hl (vtB_memAt 4135 _ (by decide +kernel)) (by decide +kernel) (hbkc 75 (by norm_num))).1
      (by rw [vtB_const hl (vtB_memAt 4136 (.atom (.const (.n 4690) (word 8589934592 0 0))) (by decide +kernel))]; exact vtB_w33) (hκ 75 (by norm_num)) hlow
  · exact (vtB_readM hl (vtB_memAt 4140 _ (by decide +kernel)) (by decide +kernel) (hbkc 76 (by norm_num))).2
  · exact vshB_rcM hl (vtB_memAt 4142 _ (by decide +kernel)) (by simp) (K := 34)
      (vtB_readM hl (vtB_memAt 4140 _ (by decide +kernel)) (by decide +kernel) (hbkc 76 (by norm_num))).1
      (by rw [vtB_const hl (vtB_memAt 4141 (.atom (.const (.n 4697) (word 8589934592 0 0))) (by decide +kernel))]; exact vtB_w33) (hκ 76 (by norm_num)) hlow
  · exact (vtB_readM hl (vtB_memAt 4145 _ (by decide +kernel)) (by decide +kernel) (hbkc 77 (by norm_num))).2
  · exact vshB_rcM hl (vtB_memAt 4147 _ (by decide +kernel)) (by simp) (K := 34)
      (vtB_readM hl (vtB_memAt 4145 _ (by decide +kernel)) (by decide +kernel) (hbkc 77 (by norm_num))).1
      (by rw [vtB_const hl (vtB_memAt 4146 (.atom (.const (.n 4704) (word 8589934592 0 0))) (by decide +kernel))]; exact vtB_w33) (hκ 77 (by norm_num)) hlow
  · exact (vtB_readM hl (vtB_memAt 4150 _ (by decide +kernel)) (by decide +kernel) (hbkc 78 (by norm_num))).2
  · exact vshB_rcM hl (vtB_memAt 4152 _ (by decide +kernel)) (by simp) (K := 34)
      (vtB_readM hl (vtB_memAt 4150 _ (by decide +kernel)) (by decide +kernel) (hbkc 78 (by norm_num))).1
      (by rw [vtB_const hl (vtB_memAt 4151 (.atom (.const (.n 4711) (word 8589934592 0 0))) (by decide +kernel))]; exact vtB_w33) (hκ 78 (by norm_num)) hlow
  · exact (vtB_readM hl (vtB_memAt 4155 _ (by decide +kernel)) (by decide +kernel) (hbkc 79 (by norm_num))).2
  · exact vshB_rcM hl (vtB_memAt 4157 _ (by decide +kernel)) (by simp) (K := 34)
      (vtB_readM hl (vtB_memAt 4155 _ (by decide +kernel)) (by decide +kernel) (hbkc 79 (by norm_num))).1
      (by rw [vtB_const hl (vtB_memAt 4156 (.atom (.const (.n 4718) (word 8589934592 0 0))) (by decide +kernel))]; exact vtB_w33) (hκ 79 (by norm_num)) hlow
  · exact (vtB_readM hl (vtB_memAt 4160 _ (by decide +kernel)) (by decide +kernel) (hbkc 80 (by norm_num))).2
  · exact vshB_rcM hl (vtB_memAt 4162 _ (by decide +kernel)) (by simp) (K := 34)
      (vtB_readM hl (vtB_memAt 4160 _ (by decide +kernel)) (by decide +kernel) (hbkc 80 (by norm_num))).1
      (by rw [vtB_const hl (vtB_memAt 4161 (.atom (.const (.n 4725) (word 8589934592 0 0))) (by decide +kernel))]; exact vtB_w33) (hκ 80 (by norm_num)) hlow
  · exact (vtB_readM hl (vtB_memAt 4165 _ (by decide +kernel)) (by decide +kernel) (hbkc 81 (by norm_num))).2
  · exact vshB_rcM hl (vtB_memAt 4167 _ (by decide +kernel)) (by simp) (K := 34)
      (vtB_readM hl (vtB_memAt 4165 _ (by decide +kernel)) (by decide +kernel) (hbkc 81 (by norm_num))).1
      (by rw [vtB_const hl (vtB_memAt 4166 (.atom (.const (.n 4732) (word 8589934592 0 0))) (by decide +kernel))]; exact vtB_w33) (hκ 81 (by norm_num)) hlow
  · exact (vtB_readM hl (vtB_memAt 4170 _ (by decide +kernel)) (by decide +kernel) (hbkc 82 (by norm_num))).2
  · exact vshB_rcM hl (vtB_memAt 4172 _ (by decide +kernel)) (by simp) (K := 34)
      (vtB_readM hl (vtB_memAt 4170 _ (by decide +kernel)) (by decide +kernel) (hbkc 82 (by norm_num))).1
      (by rw [vtB_const hl (vtB_memAt 4171 (.atom (.const (.n 4739) (word 8589934592 0 0))) (by decide +kernel))]; exact vtB_w33) (hκ 82 (by norm_num)) hlow
  · exact (vtB_readM hl (vtB_memAt 4175 _ (by decide +kernel)) (by decide +kernel) (hbkc 83 (by norm_num))).2
  · exact vshB_rcM hl (vtB_memAt 4177 _ (by decide +kernel)) (by simp) (K := 34)
      (vtB_readM hl (vtB_memAt 4175 _ (by decide +kernel)) (by decide +kernel) (hbkc 83 (by norm_num))).1
      (by rw [vtB_const hl (vtB_memAt 4176 (.atom (.const (.n 4746) (word 8589934592 0 0))) (by decide +kernel))]; exact vtB_w33) (hκ 83 (by norm_num)) hlow
  · exact (vtB_readM hl (vtB_memAt 4180 _ (by decide +kernel)) (by decide +kernel) (hbkc 84 (by norm_num))).2
  · exact vshB_rcM hl (vtB_memAt 4182 _ (by decide +kernel)) (by simp) (K := 34)
      (vtB_readM hl (vtB_memAt 4180 _ (by decide +kernel)) (by decide +kernel) (hbkc 84 (by norm_num))).1
      (by rw [vtB_const hl (vtB_memAt 4181 (.atom (.const (.n 4753) (word 8589934592 0 0))) (by decide +kernel))]; exact vtB_w33) (hκ 84 (by norm_num)) hlow
  · exact (vtB_readM hl (vtB_memAt 4185 _ (by decide +kernel)) (by decide +kernel) (hbkc 85 (by norm_num))).2
  · exact vshB_rcM hl (vtB_memAt 4187 _ (by decide +kernel)) (by simp) (K := 34)
      (vtB_readM hl (vtB_memAt 4185 _ (by decide +kernel)) (by decide +kernel) (hbkc 85 (by norm_num))).1
      (by rw [vtB_const hl (vtB_memAt 4186 (.atom (.const (.n 4760) (word 8589934592 0 0))) (by decide +kernel))]; exact vtB_w33) (hκ 85 (by norm_num)) hlow
  · exact (vtB_readM hl (vtB_memAt 4190 _ (by decide +kernel)) (by decide +kernel) (hbkc 86 (by norm_num))).2
  · exact vshB_rcM hl (vtB_memAt 4192 _ (by decide +kernel)) (by simp) (K := 34)
      (vtB_readM hl (vtB_memAt 4190 _ (by decide +kernel)) (by decide +kernel) (hbkc 86 (by norm_num))).1
      (by rw [vtB_const hl (vtB_memAt 4191 (.atom (.const (.n 4767) (word 8589934592 0 0))) (by decide +kernel))]; exact vtB_w33) (hκ 86 (by norm_num)) hlow
  · exact (vtB_readM hl (vtB_memAt 4195 _ (by decide +kernel)) (by decide +kernel) (hbkc 87 (by norm_num))).2
  · exact vshB_rcM hl (vtB_memAt 4197 _ (by decide +kernel)) (by simp) (K := 34)
      (vtB_readM hl (vtB_memAt 4195 _ (by decide +kernel)) (by decide +kernel) (hbkc 87 (by norm_num))).1
      (by rw [vtB_const hl (vtB_memAt 4196 (.atom (.const (.n 4774) (word 8589934592 0 0))) (by decide +kernel))]; exact vtB_w33) (hκ 87 (by norm_num)) hlow
  · exact (vtB_readM hl (vtB_memAt 4200 _ (by decide +kernel)) (by decide +kernel) (hbkc 88 (by norm_num))).2
  · exact vshB_rcM hl (vtB_memAt 4202 _ (by decide +kernel)) (by simp) (K := 34)
      (vtB_readM hl (vtB_memAt 4200 _ (by decide +kernel)) (by decide +kernel) (hbkc 88 (by norm_num))).1
      (by rw [vtB_const hl (vtB_memAt 4201 (.atom (.const (.n 4781) (word 8589934592 0 0))) (by decide +kernel))]; exact vtB_w33) (hκ 88 (by norm_num)) hlow
  · exact (vtB_readM hl (vtB_memAt 4205 _ (by decide +kernel)) (by decide +kernel) (hbkc 89 (by norm_num))).2
  · exact vshB_rcM hl (vtB_memAt 4207 _ (by decide +kernel)) (by simp) (K := 34)
      (vtB_readM hl (vtB_memAt 4205 _ (by decide +kernel)) (by decide +kernel) (hbkc 89 (by norm_num))).1
      (by rw [vtB_const hl (vtB_memAt 4206 (.atom (.const (.n 4788) (word 8589934592 0 0))) (by decide +kernel))]; exact vtB_w33) (hκ 89 (by norm_num)) hlow
  · exact (vtB_readM hl (vtB_memAt 4210 _ (by decide +kernel)) (by decide +kernel) (hbkc 90 (by norm_num))).2
  · exact vshB_rcM hl (vtB_memAt 4212 _ (by decide +kernel)) (by simp) (K := 34)
      (vtB_readM hl (vtB_memAt 4210 _ (by decide +kernel)) (by decide +kernel) (hbkc 90 (by norm_num))).1
      (by rw [vtB_const hl (vtB_memAt 4211 (.atom (.const (.n 4795) (word 8589934592 0 0))) (by decide +kernel))]; exact vtB_w33) (hκ 90 (by norm_num)) hlow
  · exact (vtB_readM hl (vtB_memAt 4215 _ (by decide +kernel)) (by decide +kernel) (hbkc 91 (by norm_num))).2
  · exact vshB_rcM hl (vtB_memAt 4217 _ (by decide +kernel)) (by simp) (K := 34)
      (vtB_readM hl (vtB_memAt 4215 _ (by decide +kernel)) (by decide +kernel) (hbkc 91 (by norm_num))).1
      (by rw [vtB_const hl (vtB_memAt 4216 (.atom (.const (.n 4802) (word 8589934592 0 0))) (by decide +kernel))]; exact vtB_w33) (hκ 91 (by norm_num)) hlow
  · exact (vtB_readM hl (vtB_memAt 4220 _ (by decide +kernel)) (by decide +kernel) (hbkc 92 (by norm_num))).2
  · exact vshB_rcM hl (vtB_memAt 4222 _ (by decide +kernel)) (by simp) (K := 34)
      (vtB_readM hl (vtB_memAt 4220 _ (by decide +kernel)) (by decide +kernel) (hbkc 92 (by norm_num))).1
      (by rw [vtB_const hl (vtB_memAt 4221 (.atom (.const (.n 4809) (word 8589934592 0 0))) (by decide +kernel))]; exact vtB_w33) (hκ 92 (by norm_num)) hlow
  · exact (vtB_readM hl (vtB_memAt 4225 _ (by decide +kernel)) (by decide +kernel) (hbkc 93 (by norm_num))).2
  · exact vshB_rcM hl (vtB_memAt 4227 _ (by decide +kernel)) (by simp) (K := 34)
      (vtB_readM hl (vtB_memAt 4225 _ (by decide +kernel)) (by decide +kernel) (hbkc 93 (by norm_num))).1
      (by rw [vtB_const hl (vtB_memAt 4226 (.atom (.const (.n 4816) (word 8589934592 0 0))) (by decide +kernel))]; exact vtB_w33) (hκ 93 (by norm_num)) hlow
  · exact (vtB_readM hl (vtB_memAt 4230 _ (by decide +kernel)) (by decide +kernel) (hbkc 94 (by norm_num))).2
  · exact vshB_rcM hl (vtB_memAt 4232 _ (by decide +kernel)) (by simp) (K := 34)
      (vtB_readM hl (vtB_memAt 4230 _ (by decide +kernel)) (by decide +kernel) (hbkc 94 (by norm_num))).1
      (by rw [vtB_const hl (vtB_memAt 4231 (.atom (.const (.n 4823) (word 8589934592 0 0))) (by decide +kernel))]; exact vtB_w33) (hκ 94 (by norm_num)) hlow
  · exact (vtB_readM hl (vtB_memAt 4235 _ (by decide +kernel)) (by decide +kernel) (hbkc 95 (by norm_num))).2
  · exact vshB_rcM hl (vtB_memAt 4237 _ (by decide +kernel)) (by simp) (K := 34)
      (vtB_readM hl (vtB_memAt 4235 _ (by decide +kernel)) (by decide +kernel) (hbkc 95 (by norm_num))).1
      (by rw [vtB_const hl (vtB_memAt 4236 (.atom (.const (.n 4830) (word 8589934592 0 0))) (by decide +kernel))]; exact vtB_w33) (hκ 95 (by norm_num)) hlow
  · exact (vtB_readM hl (vtB_memAt 4240 _ (by decide +kernel)) (by decide +kernel) (hbkc 96 (by norm_num))).2
  · exact vshB_rcM hl (vtB_memAt 4242 _ (by decide +kernel)) (by simp) (K := 34)
      (vtB_readM hl (vtB_memAt 4240 _ (by decide +kernel)) (by decide +kernel) (hbkc 96 (by norm_num))).1
      (by rw [vtB_const hl (vtB_memAt 4241 (.atom (.const (.n 4837) (word 8589934592 0 0))) (by decide +kernel))]; exact vtB_w33) (hκ 96 (by norm_num)) hlow
  · exact (vtB_readM hl (vtB_memAt 4245 _ (by decide +kernel)) (by decide +kernel) (hbkc 97 (by norm_num))).2
  · exact vshB_rcM hl (vtB_memAt 4247 _ (by decide +kernel)) (by simp) (K := 34)
      (vtB_readM hl (vtB_memAt 4245 _ (by decide +kernel)) (by decide +kernel) (hbkc 97 (by norm_num))).1
      (by rw [vtB_const hl (vtB_memAt 4246 (.atom (.const (.n 4844) (word 8589934592 0 0))) (by decide +kernel))]; exact vtB_w33) (hκ 97 (by norm_num)) hlow
  · exact (vtB_readM hl (vtB_memAt 4250 _ (by decide +kernel)) (by decide +kernel) (hbkc 98 (by norm_num))).2
  · exact vshB_rcM hl (vtB_memAt 4252 _ (by decide +kernel)) (by simp) (K := 34)
      (vtB_readM hl (vtB_memAt 4250 _ (by decide +kernel)) (by decide +kernel) (hbkc 98 (by norm_num))).1
      (by rw [vtB_const hl (vtB_memAt 4251 (.atom (.const (.n 4851) (word 8589934592 0 0))) (by decide +kernel))]; exact vtB_w33) (hκ 98 (by norm_num)) hlow
  · exact (vtB_readM hl (vtB_memAt 4255 _ (by decide +kernel)) (by decide +kernel) (hbkc 99 (by norm_num))).2
  · exact vshB_rcM hl (vtB_memAt 4257 _ (by decide +kernel)) (by simp) (K := 34)
      (vtB_readM hl (vtB_memAt 4255 _ (by decide +kernel)) (by decide +kernel) (hbkc 99 (by norm_num))).1
      (by rw [vtB_const hl (vtB_memAt 4256 (.atom (.const (.n 4858) (word 8589934592 0 0))) (by decide +kernel))]; exact vtB_w33) (hκ 99 (by norm_num)) hlow
  · exact (vtB_readM hl (vtB_memAt 4260 _ (by decide +kernel)) (by decide +kernel) (hbkc 100 (by norm_num))).2
  · exact vshB_rcM hl (vtB_memAt 4262 _ (by decide +kernel)) (by simp) (K := 34)
      (vtB_readM hl (vtB_memAt 4260 _ (by decide +kernel)) (by decide +kernel) (hbkc 100 (by norm_num))).1
      (by rw [vtB_const hl (vtB_memAt 4261 (.atom (.const (.n 4865) (word 8589934592 0 0))) (by decide +kernel))]; exact vtB_w33) (hκ 100 (by norm_num)) hlow
  · exact (vtB_readM hl (vtB_memAt 4265 _ (by decide +kernel)) (by decide +kernel) (hbkc 101 (by norm_num))).2
  · exact vshB_rcM hl (vtB_memAt 4267 _ (by decide +kernel)) (by simp) (K := 34)
      (vtB_readM hl (vtB_memAt 4265 _ (by decide +kernel)) (by decide +kernel) (hbkc 101 (by norm_num))).1
      (by rw [vtB_const hl (vtB_memAt 4266 (.atom (.const (.n 4872) (word 8589934592 0 0))) (by decide +kernel))]; exact vtB_w33) (hκ 101 (by norm_num)) hlow
  · exact (vtB_readM hl (vtB_memAt 4270 _ (by decide +kernel)) (by decide +kernel) (hbkc 102 (by norm_num))).2
  · exact vshB_rcM hl (vtB_memAt 4272 _ (by decide +kernel)) (by simp) (K := 34)
      (vtB_readM hl (vtB_memAt 4270 _ (by decide +kernel)) (by decide +kernel) (hbkc 102 (by norm_num))).1
      (by rw [vtB_const hl (vtB_memAt 4271 (.atom (.const (.n 4879) (word 8589934592 0 0))) (by decide +kernel))]; exact vtB_w33) (hκ 102 (by norm_num)) hlow
  · exact (vtB_readM hl (vtB_memAt 4275 _ (by decide +kernel)) (by decide +kernel) (hbkc 103 (by norm_num))).2
  · exact vshB_rcM hl (vtB_memAt 4277 _ (by decide +kernel)) (by simp) (K := 34)
      (vtB_readM hl (vtB_memAt 4275 _ (by decide +kernel)) (by decide +kernel) (hbkc 103 (by norm_num))).1
      (by rw [vtB_const hl (vtB_memAt 4276 (.atom (.const (.n 4886) (word 8589934592 0 0))) (by decide +kernel))]; exact vtB_w33) (hκ 103 (by norm_num)) hlow
  · exact (vtB_readM hl (vtB_memAt 4280 _ (by decide +kernel)) (by decide +kernel) (hbkc 104 (by norm_num))).2
  · exact vshB_rcM hl (vtB_memAt 4282 _ (by decide +kernel)) (by simp) (K := 34)
      (vtB_readM hl (vtB_memAt 4280 _ (by decide +kernel)) (by decide +kernel) (hbkc 104 (by norm_num))).1
      (by rw [vtB_const hl (vtB_memAt 4281 (.atom (.const (.n 4893) (word 8589934592 0 0))) (by decide +kernel))]; exact vtB_w33) (hκ 104 (by norm_num)) hlow
  · exact (vtB_readM hl (vtB_memAt 4285 _ (by decide +kernel)) (by decide +kernel) (hbkc 105 (by norm_num))).2
  · exact vshB_rcM hl (vtB_memAt 4287 _ (by decide +kernel)) (by simp) (K := 34)
      (vtB_readM hl (vtB_memAt 4285 _ (by decide +kernel)) (by decide +kernel) (hbkc 105 (by norm_num))).1
      (by rw [vtB_const hl (vtB_memAt 4286 (.atom (.const (.n 4900) (word 8589934592 0 0))) (by decide +kernel))]; exact vtB_w33) (hκ 105 (by norm_num)) hlow
  · exact (vtB_readM hl (vtB_memAt 4290 _ (by decide +kernel)) (by decide +kernel) (hbkc 106 (by norm_num))).2
  · exact vshB_rcM hl (vtB_memAt 4292 _ (by decide +kernel)) (by simp) (K := 34)
      (vtB_readM hl (vtB_memAt 4290 _ (by decide +kernel)) (by decide +kernel) (hbkc 106 (by norm_num))).1
      (by rw [vtB_const hl (vtB_memAt 4291 (.atom (.const (.n 4907) (word 8589934592 0 0))) (by decide +kernel))]; exact vtB_w33) (hκ 106 (by norm_num)) hlow
  · exact (vtB_readM hl (vtB_memAt 4295 _ (by decide +kernel)) (by decide +kernel) (hbkc 107 (by norm_num))).2
  · exact vshB_rcM hl (vtB_memAt 4297 _ (by decide +kernel)) (by simp) (K := 34)
      (vtB_readM hl (vtB_memAt 4295 _ (by decide +kernel)) (by decide +kernel) (hbkc 107 (by norm_num))).1
      (by rw [vtB_const hl (vtB_memAt 4296 (.atom (.const (.n 4914) (word 8589934592 0 0))) (by decide +kernel))]; exact vtB_w33) (hκ 107 (by norm_num)) hlow

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem vtB_glue_5098 (hl : args.length = 22)  :
    ∀ s ∈ (vtPre.drop 5098).take 54, VSH (coreProgram.Rel rd) rd (vtσ rd wo args) s := by
  exact vtB_blockR hl 5098 54 [] (by decide +kernel) (fun _ h ↦ absurd h (by simp))

end

end
end LeanVM.Guest.B1.Tables
