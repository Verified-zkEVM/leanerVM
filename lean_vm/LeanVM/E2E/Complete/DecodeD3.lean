/-
  LeanVM.E2E.Complete.DecodeD3

  D3: the children's proofs, decoded at the frames of their `verify_sub` instances.
-/

module

public import LeanVM.E2E.Complete.DecodeProof
public import LeanVM.E2E.Complete.DecodeAssembly

/-!
# The children's proofs (D3)

* `mainFrame_133`: `main`'s fresh-claims pointer off its frame;
* `vsArgsAt_inj`: distinct children's `verify_sub` calls have distinct words (their fresh-claims
  slots `cfresh·g^(106c)`).
-/

namespace LeanVM.E2E.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Protocol.Compile

@[expose] public section

/-- `main`'s fresh-claims pointer, off its frame. -/
theorem mainFrame_133 {S : BlakeSem} (hB : B2C.B2HypsB S) {hdr : E × E} {rd rd0 : Reader}
    {T0 : Memory.Tree} {ν : ℕ → String → Val → V → E} {σ0 : Val} {bufs : List ℕ}
    {ks : List Memory.Tree} (hT0 : T0 = .node "main" σ0 bufs ks)
    (hH : HonestAtB S coreProgram B2C.fs B2C.H B2C.C hdr (T0.retemp coreProgram B2C.fs ν 0) B2C.cert
      rd [] [])
    {W : B1.Main.MainWords} (hσ0 : σ0 = B1.Main.mainVal rd0 (B1.Main.mainRunAt B2C.fs 0 W)) :
    mainFrame (honest coreProgram B2C.fs B2C.H B2C.C hdr (T0.retemp coreProgram B2C.fs ν 0)) (.n 133) =
      B1.Main.mainPtr B2C.fs 0 W 6 := by
  have hTn : T0.retemp coreProgram B2C.fs ν 0 = .node "main" (retempVal coreProgram ν 0 "main" σ0) bufs
      (Memory.Tree.retempKids coreProgram B2C.fs ν (kidPos B2C.fs coreProgram.loop 0 "main" bufs
        (ks.map (Memory.Tree.total B2C.fs))) ks) := by
    rw [hT0, retemp_node]
  have hname : (T0.retemp coreProgram B2C.fs ν 0).name = "main" := by rw [hTn]; rfl
  have hm := mainFrame_vsWords_mem
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq,
    Nat.ble_eq, Nat.blt_eq] at hm
  have hu : V.n 133 ∈ Stmt.usesList (Fn.body Data.core0) := by decide +kernel
  rw [mainFrame_eqN hB hname hH hTn hm.2.2.2.2.2.1.1 hm.2.2.2.2.2.1.2 hm.2.2.2.2.2.2,
    retempVal_uses coreProgram_fresh B1.Main.find_main hu, hσ0]
  have := mainVal_vsWords B2C.fs rd0 0 W
  simp only [List.map_cons, List.map_nil, List.cons.injEq] at this
  exact this.2.2.2.2.2.1

/-- **Distinct children's `verify_sub` calls have distinct words**: their last words are their
fresh-claims slots. -/
theorem vsArgsAt_inj {κ : ℕ} {L : MemImage κ} {W : B1.Main.MainWords}
    (h133 : mainFrame L (.n 133) = B1.Main.mainPtr B2C.fs 0 W 6)
    (hb : B1.Main.mainBase B2C.fs 0 W 6 + 106 * 16 < 2 ^ 63) {c c' : ℕ} (hc : c ≤ 16) (hc' : c' ≤ 16)
    (h : vsArgsAt L c = vsArgsAt L c') : c = c' := by
  unfold vsArgsAt at h
  simp only [List.cons.injEq] at h
  have h6 := h.2.2.2.2.2.2.1
  rw [h133, B1.Main.mainPtr, B1.Main.ofK_gpow_mul_gen, B1.Main.ofK_gpow_mul_gen] at h6
  have := Parameters.gpow_injOn (show B1.Main.mainBase B2C.fs 0 W 6 + 106 * c ∈ Set.Iio (2 ^ 64 - 1) by
      simp; omega) (show B1.Main.mainBase B2C.fs 0 W 6 + 106 * c' ∈ Set.Iio (2 ^ 64 - 1) by simp; omega)
    (Parameters.ofK_injective h6)
  omega

end
end LeanVM.E2E.Complete
