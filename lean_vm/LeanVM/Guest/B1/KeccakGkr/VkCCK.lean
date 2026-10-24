/-
  LeanVM.Guest.B1.KeccakGkr.VkCCK

  `verify_keccak`'s steps: their cores, and what the kernel checks of them.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.VkCB
public import LeanVM.Guest.B1.KeccakGkr.VkChain

/-!
# The steps' cores

`stepCore s b`: step `s` but its call (`stepT = stepCore ++ stepTailT`). `stepKer`: what the
kernel checks of it (the loads that are not stores, the residual loads' pointers), for the twelve
steps (`step_ker`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr LeanVM.Guest.B1.Fwd Finset

@[expose] public section

variable {C : CallRel} {rd : Reader} {w : ℕ → E} {σ : Val}

/-- Where step `s` starts. -/
def stepB (s : ℕ) : ℕ :=
  [488, 531, 746, 960, 1315, 1624, 1979, 2192, 2501, 2763, 3074, 3383].getD s 0

/-- The capacity step `s` passes. -/
def stepCap (s : ℕ) : List ℕ :=
  if s = 0 then [179, 180, 181, 182, 183] else (List.range 5).map fun j ↦ stepB s - 6 + j

/-- The cursor step `s ≥ 1` passes. -/
def stepCur (s : ℕ) : ℕ := if s = 0 then 0 else stepB s - 1

/-- Step `s` but its call. -/
def stepCore (s b : ℕ) : List Stmt :=
  [.atom (.load (.n b) (.n 201) (22 * s + 2)), .atom (.hint (.alloc (.n (b + 1)) 2)),
    .atom (.mul (.n (b + 2)) (.n b) (.n 17))] ++
  eqtreeT (.n (b + 2)) (.n (b + 1)) 0 (b + 3) 1 ++ flipsT s (b + 6) ++
  iotaSegT s (b + 6) (b + 6 + flipSz s * (iotaUsed s).length) (b + 1)

/-- Where step `s`'s call starts. -/
def stepT0 (s b : ℕ) : ℕ := iotaSegEnd s (b + 6 + flipSz s * (iotaUsed s).length)

theorem stepT_split (s b : ℕ) (cap : List ℕ) (cur : ℕ) (gw : ℕ → ℕ) :
    stepT s b cap cur gw = stepCore s b ++ stepTailT s (stepT0 s b) cap cur (stepT0 s b - 1) gw := rfl

/-- The pointers the flips load through, and their ranges. -/
def flipPs (s b : ℕ) : List (V × ℕ × ℕ) :=
  if s = 0 then [(.n 274, 30, 31)]
  else (.n 201, 22 * s + 3, 22 * s + 6) :: (List.range (iotaUsed s).length).flatMap fun j ↦
    [(.n (b + 6 + 46 * j), 0, 25), (.n (b + 6 + 46 * j + 1), 0, 64)]

/-- What the kernel checks of step `s`'s core. -/
def stepKer (s b : ℕ) : Prop :=
  noneIn [.load (.n b) (.n 201) (22 * s + 2)] vkSt = true ∧
  noneIn (eqtreeReads (.n (b + 2)) (.n (b + 1)) 0 (b + 3) 1) vkSt = true ∧
  (flipsT s (b + 6)).all isAtom = true ∧ canonChk [] (atomsL ([] ++ flipsT s (b + 6))) = true ∧
  (resid (atomsL (flipsT s (b + 6)))).all (ldR (flipPs s b)) = true ∧
  noneIn (resid (atomsL (flipsT s (b + 6)))) vkSt = true ∧
  (iotaSegT s (b + 6) (b + 6 + flipSz s * (iotaUsed s).length) (b + 1)).all isAtom = true ∧
  canonChk [] (atomsL ([] ++ iotaSegT s (b + 6) (b + 6 + flipSz s * (iotaUsed s).length) (b + 1)))
    = true ∧
  (resid (atomsL (iotaSegT s (b + 6) (b + 6 + flipSz s * (iotaUsed s).length) (b + 1)))).all
    (ldR [(.n (b + 1), 0, 2)]) = true ∧
  noneIn (resid (atomsL (iotaSegT s (b + 6) (b + 6 + flipSz s * (iotaUsed s).length) (b + 1))))
    vkSt = true

instance (s b : ℕ) : Decidable (stepKer s b) := by unfold stepKer; infer_instance

theorem step_ker_0 : stepKer 0 488 := by decide +kernel
theorem step_ker_1 : stepKer 1 531 := by decide +kernel
theorem step_ker_2 : stepKer 2 746 := by decide +kernel
theorem step_ker_3 : stepKer 3 960 := by decide +kernel
theorem step_ker_4 : stepKer 4 1315 := by decide +kernel
theorem step_ker_5 : stepKer 5 1624 := by decide +kernel
theorem step_ker_6 : stepKer 6 1979 := by decide +kernel
theorem step_ker_7 : stepKer 7 2192 := by decide +kernel
theorem step_ker_8 : stepKer 8 2501 := by decide +kernel
theorem step_ker_9 : stepKer 9 2763 := by decide +kernel
theorem step_ker_10 : stepKer 10 3074 := by decide +kernel
theorem step_ker_11 : stepKer 11 3383 := by decide +kernel

theorem step_ker : ∀ s < 12, stepKer s (stepB s) := by
  intro s hs
  interval_cases s
  · exact step_ker_0
  · exact step_ker_1
  · exact step_ker_2
  · exact step_ker_3
  · exact step_ker_4
  · exact step_ker_5
  · exact step_ker_6
  · exact step_ker_7
  · exact step_ker_8
  · exact step_ker_9
  · exact step_ker_10
  · exact step_ker_11

end
end LeanVM.Guest.B1.VerifySub
