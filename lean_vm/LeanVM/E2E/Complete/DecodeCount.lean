/-
  LeanVM.E2E.Complete.DecodeCount

  D1 of `DecodeHonest`: the children's count off `main`'s frame on the honest memory.
-/

module

public import LeanVM.E2E.Complete.DecodeMain

/-!
# The children's count, decoded

`decode_count`: on the honest memory of `main`'s retemped tree whose root valuation holds `g^n` at
word `6` (`mainVal_6` at `main`'s honest words), `gLog` of `main`'s frame at word `6` is `n`.
-/

namespace LeanVM.E2E.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-- `main`'s valuation's children count (`mainVal` at word `6`). -/
theorem mainVal_6 (fs : String → ℕ) (rd : Reader) (fp : ℕ) (W : B1.Main.MainWords) :
    B1.Main.mainVal rd (B1.Main.mainRunAt fs fp W) (.n 6) = Protocol.Verifier.gen ^ W.nc := by
  simp only [B1.Main.mainVal, B1.Main.mainRunAt]
  b1_look

/-- **D1: the children's count off `main`'s frame**, on the honest memory of `main`'s retemped
tree whose root valuation holds `g^n` at word `6`. -/
theorem decode_count {S : BlakeSem} (hB : B2C.B2HypsB S) {hdr : E × E} {rd : Reader} {T0 : Tree}
    {ν : ℕ → String → Val → V → E} {σ0 : Val} {bufs : List ℕ} {ks : List Tree}
    (hT0 : T0 = .node "main" σ0 bufs ks)
    (hH : HonestAtB S coreProgram B2C.fs B2C.H B2C.C hdr (T0.retemp coreProgram B2C.fs ν 0) B2C.cert
      rd [] [])
    {n : ℕ} (h6 : σ0 (.n 6) = Protocol.Verifier.gen ^ n) (hn : n < 2 ^ 18) :
    B1.Main.gLog (mainFrame (honest coreProgram B2C.fs B2C.H B2C.C hdr
      (T0.retemp coreProgram B2C.fs ν 0)) (.n 6)) = n := by
  have hT : T0.retemp coreProgram B2C.fs ν 0 = .node "main" (retempVal coreProgram ν 0 "main" σ0) bufs
      (Tree.retempKids coreProgram B2C.fs ν (kidPos B2C.fs coreProgram.loop 0 "main" bufs
        (ks.map (Tree.total B2C.fs))) ks) := by
    rw [hT0, retemp_node]
  have hname : (T0.retemp coreProgram B2C.fs ν 0).name = "main" := by rw [hT]; rfl
  rw [mainFrame_eq hB hname hH hT (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  rw [retempVal_uses coreProgram_fresh B1.Main.find_main (by rw [B1.Main.core0_body]; decide +kernel), h6]
  exact B1.Main.gLog_gen_pow hn

end
end LeanVM.E2E.Complete
