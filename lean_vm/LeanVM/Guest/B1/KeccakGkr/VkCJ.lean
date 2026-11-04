/-
  LeanVM.Guest.B1.KeccakGkr.VkCJ

  What the kernel checks of `verify_keccak`'s body as a flat function: its statements, buffers,
  calls.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.VkCI
public import LeanVM.Guest.B1.KeccakGkr.VkHolds
public import LeanVM.Guest.B1.Tables.FlatAt

/-!
# The body, flat

`vkT = vkPre ++ [.ret vkVs]` (`vkT_pre`). `vkPre_kernel`: its statements are flat, it takes no
frame addresses, its nineteen buffers (`vkAllocs`); every dispatch is on `odd_g` (`.n 47`) between
two names, so its calls are `vkCalls o` at `logG odd_g = o` (`vkPre_callSF`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The inputs' check and the return but the return. -/
def vkFinPre : List Stmt := vkFinT.dropLast

/-- The returned values. -/
def vkVs : List V := [.n 3868, .n 3869, .n 3870, .n 3871, .n 3872, .n 3875, .n 3876, .n 3877]

/-- The body but its return. -/
def vkPre : List Stmt := vkHeadT ++ vkFirstT ++ vkStepsT ++ vkOutT ++ vkInT ++ vkFinPre

theorem vkFinT_pre : vkFinT = vkFinPre ++ [.ret vkVs] := stmtsEqb_sound (by decide +kernel)

theorem vkT_pre : vkT = vkPre ++ [.ret vkVs] := by
  rw [vkT, vkPre, vkFinT_pre]; simp only [List.append_assoc]

/-- The buffers. -/
def vkAllocs : List (V × (ℕ ⊕ V)) :=
  [(.n 60, .inr (.n 59)), (.n 92, .inl 5), (.n 203, .inl 286), (.n 205, .inl 30), (.n 276, .inl 62),
    (.n 384, .inl 2)] ++ (List.range 12).map (fun s ↦ (.n (stepB s + 1), .inl 2)) ++
    [(.n 1259, .inl 30)]

/-- The frame a statement sets up, a dispatch taking its `o`-th name. -/
def callSFO (o : ℕ) : Stmt → Option (Option V × String × List V × List V)
  | .dispatch _ fs args rets => some (none, fs.getD o "", args, rets)
  | s => Main.Stmt.callS s

/-- A dispatch on `odd_g` between two names. -/
def dispOddB : Stmt → Bool
  | .dispatch x fs _ _ => x == .n 47 && fs.length == 2
  | _ => true

/-- Step `s`'s call's arguments and returns. -/
def stepCall (o s : ℕ) : Option V × String × List V × List V :=
  let T := stepT0 s (stepB s)
  if s = 0 then
    (none, layerName 1 o, (stepCap s).map .n ++ [.n 200, .n 202, .n (T + 1), .n (T + 3), .n 43,
      .n 48, .n 203, .n (T + 5), .n (T - 1)], (List.range 6).map fun j ↦ .n (T + 6 + j))
  else
    (none, layerName 0 o, (stepCap s).map .n ++ [.n T, .n (T + 1), .n (stepCur s), .n (T + 3),
      .n 43, .n 48, .n (T + 5), .n (T + 9), .n (T - 1)], (List.range 6).map fun j ↦ .n (T + 10 + j))

/-- **The calls**, `odd_g = g^o`. -/
def vkCalls (o : ℕ) : List (Option V × String × List V × List V) :=
  [(some (.n 62), "__loop10", [.n 63, .n 17, .n 60, .n 65], [])] ++
    (List.range 12).map (stepCall o) ++
    [(none, "keccak_plain_rounds__L6_L0", [.n 957, .n 958, .n 959, .n 960, .n 961, .n 964,
        .n 965, .n 962, .n 193, .n 963], (List.range 7).map fun j ↦ .n (966 + j)),
      (some (.n 1243), "__loop11", [.n 1244, .n 17, .n 1246, .n 60], []),
      (none, "keccak_plain_rounds__L4_L1", [.n 966, .n 967, .n 968, .n 969, .n 970, .n 980,
        .n 982, .n 1248, .n 1249, .n 1251], (List.range 7).map fun j ↦ .n (1252 + j)),
      (none, "keccak_plain_rounds__L6_L0", [.n 1252, .n 1253, .n 1254, .n 1255, .n 1256, .n 1380,
        .n 1381, .n 1257, .n 1258, .n 1379], (List.range 7).map fun j ↦ .n (1382 + j)),
      (some (.n 3864), "__loop12", [.n 3865, .n 17, .n 3867, .n 2249], [])]

theorem vkPre_kernel :
    vkPre.all Stmt.flat = true ∧ vkPre.filterMap Main.Stmt.addrS = [] ∧
    vkPre.filterMap Main.Stmt.allocSz = vkAllocs ∧ vkPre.all dispOddB = true ∧
    vkPre.filterMap (callSFO 0) = vkCalls 0 ∧ vkPre.filterMap (callSFO 1) = vkCalls 1 := by
  decide +kernel

theorem callSF_of_dispOdd (σ : Val) {s : Stmt} (h : dispOddB s = true) :
    s.callSF σ = callSFO (logG (σ (.n 47))) s := by
  cases s with
  | dispatch x fs args rets =>
    simp only [dispOddB, Bool.and_eq_true, beq_iff_eq] at h
    rw [h.1]; rfl
  | _ => rfl

theorem vkPre_callSF (σ : Val) :
    vkPre.filterMap (Stmt.callSF σ) = vkPre.filterMap (callSFO (logG (σ (.n 47)))) :=
  List.filterMap_congr fun _ hs ↦ callSF_of_dispOdd σ (List.all_eq_true.mp vkPre_kernel.2.2.2.1 _ hs)

theorem vkPre_disp {σ : Val} {o : ℕ} (ho : o < 2) (h47 : σ (.n 47) = gen ^ o) :
    ∀ s ∈ vkPre, DispOk σ s := by
  intro s hs
  have h := List.all_eq_true.mp vkPre_kernel.2.2.2.1 s hs
  cases s with
  | dispatch x fs args rets =>
    simp only [dispOddB, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, hl⟩ := h
    exact ⟨o, by rw [hl]; exact ho, by norm_num; omega, by rw [h47, gen_pow_eq_ofK]⟩
  | _ => trivial

end
end LeanVM.Guest.B1.VerifySub
