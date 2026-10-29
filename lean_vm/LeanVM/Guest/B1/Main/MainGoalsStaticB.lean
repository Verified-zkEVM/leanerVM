/-
  LeanVM.Guest.B1.Main.MainGoalsStaticB

  `main`'s statically bounded callees on an honest run, within their words: the goals of
  `MainGoalsF` and `MainGoalsG` (same proofs) with the bounded lifts of `MainStaticB`.
-/

module

public import LeanVM.Guest.B1.Main.MainGoalsF
public import LeanVM.Guest.B1.Main.MainGoalsG
public import LeanVM.Guest.B1.Main.MainStaticB

/-!
# `main`'s static callees on an honest run, bounded

`MainGoalL1B` … `MainGoalStB`: `MainGoalL1` … `MainGoalSt` with `CompleteAtDTB` within the static
bounds (`SB`, `SK`, the loops' counts).
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest.B1.Digest
open LeanVM.Guest.Hints (claimCells cellsOfBytes cellOfBytes direct plan)
open LeanVM.Guest.B1 (CompleteAtD CompleteAtDTB Returns bufL completeAt_of_rel_pureBat)
open LeanVM.Guest.B1.Da (reads_of_memL exists_of_length_succ wLog)

@[expose] public section

/-! ## The goals, bounded -/

variable (fs : String → ℕ) (cert : String → V → ℕ) (fp : ℕ) (seed : Digest) (s : NodeStatement)
  (w : NodeWitness) (SB SK : String → ℕ)

def MainGoalL1B : Prop :=
  (hm fs fp seed s w).nxd ≠ 0 →
    CompleteAtDTB fs cert 16 "__loop0" (hLmain fs fp seed s w)
      [1, gen ^ (hm fs fp seed s w).nxd, (hm fs fp seed s w).a77, gen ^ (hm fs fp seed s w).nlx] (Returns []) (fun _ => True) ((hm fs fp seed s w).nxd * SK "__loop0")

def MainGoalL2B : Prop :=
  (hm fs fp seed s w).nsd ≠ 0 →
    CompleteAtDTB fs cert 16 "__loop1" (hLmain fs fp seed s w)
      [1, gen ^ (hm fs fp seed s w).nsd, (hm fs fp seed s w).a80, gen ^ (hm fs fp seed s w).nls] (Returns []) (fun _ => True) ((hm fs fp seed s w).nsd * SK "__loop1")

def MainGoalL3B : Prop :=
  (hm fs fp seed s w).nrx ≠ 0 →
    CompleteAtDTB fs cert 16 "__loop2" (hLmain fs fp seed s w)
      [1, gen ^ (hm fs fp seed s w).nrx, gen ^ ((hm fs fp seed s w).nlx + (hm fs fp seed s w).nxd), (hm fs fp seed s w).a117, (hm fs fp seed s w).a77] (Returns []) (fun _ => True)
      ((hm fs fp seed s w).nrx * SK "__loop2")

def MainGoalL4B : Prop :=
  (hm fs fp seed s w).nrs ≠ 0 →
    CompleteAtDTB fs cert 16 "__loop3" (hLmain fs fp seed s w)
      [1, gen ^ (hm fs fp seed s w).nrs, gen ^ ((hm fs fp seed s w).nls + (hm fs fp seed s w).nsd), (hm fs fp seed s w).a117, gen ^ ((hm fs fp seed s w).nlx + (hm fs fp seed s w).nxd),
        gen ^ (hm fs fp seed s w).nrx, (hm fs fp seed s w).a80, (hm fs fp seed s w).a119] (Returns []) (fun _ => True) ((hm fs fp seed s w).nrs * SK "__loop3")

def MainGoalStB : Prop :=
  CompleteAtDTB fs cert 16 "statement_digest" (hLmain fs fp seed s w)
    [(digestScalars (hm fs fp seed s w).seed).1, (digestScalars (hm fs fp seed s w).seed).2,
      (digestScalars (hm fs fp seed s w).xd).1, (digestScalars (hm fs fp seed s w).xd).2,
      (digestScalars (hm fs fp seed s w).sd).1, (digestScalars (hm fs fp seed s w).sd).2,
      (digestScalars (hm fs fp seed s w).dap).1, (digestScalars (hm fs fp seed s w).dap).2,
      (hm fs fp seed s w).a417] (Returns (B1.Digest.digestCells (hm fs fp seed s w).sdg)) (fun _ => True)
    (SB "statement_digest")

variable {fs cert fp seed s w SB SK} {bytecode : List K}

/-- **`__loop0`, `__loop1` within their static bounds.** -/
theorem mainGoalL1B (hT : TotalLeOn coreProgram fs "__loop0" LoopPre (fun a => logG (a.getD 1 0) * SK "__loop0"))
    (hl : (hm fs fp seed s w).nxd < 2 ^ 64 - 1) : MainGoalL1B fs cert fp seed s w SK := fun hne =>
  (completeAt_of_rel_pureBat mfLoop_pure (by simp [mfLoopSet]) (fun rd _ => mfL1_rel rd _ _ hne) 16
    fun rd t hn hv hb => by
      have := hT rd t _ _ hn (loopPre_gen (Nat.pos_of_ne_zero hne) hl _) hv hb
      simpa [logG_gen hl] using this).toDTB

theorem mainGoalL2B (hT : TotalLeOn coreProgram fs "__loop1" LoopPre (fun a => logG (a.getD 1 0) * SK "__loop1"))
    (hl : (hm fs fp seed s w).nsd < 2 ^ 64 - 1) : MainGoalL2B fs cert fp seed s w SK := fun hne =>
  (completeAt_of_rel_pureBat mfLoop_pure (by simp [mfLoopSet]) (fun rd _ => mfL2_rel rd _ _ hne) 16
    fun rd t hn hv hb => by
      have := hT rd t _ _ hn (loopPre_gen (Nat.pos_of_ne_zero hne) hl _) hv hb
      simpa [logG_gen hl] using this).toDTB

/-- **`statement_digest` on the claim lists' digests and the deferred claim**, a bytecode of
`2^23` words making the deferred claim `24` cells. -/
theorem mainGoalStB {bytecode : List K} (hR : NodeRel bytecode seed s w)
    (hbl : bytecode.length = 2 ^ bytecodeVars) {SB : String → ℕ}
    (hT : TotalLe coreProgram fs "statement_digest" (fun _ => SB "statement_digest")) :
    MainGoalStB fs cert fp seed s w SB := by
  have hlen : s.defer.cells.length = 24 := by
    have h1 : s.defer.bytecodePoint.length = Nat.log2 bytecode.length := hR.1
    rw [hbl, Nat.log2_two_pow] at h1
    simp [DeferredClaim.cells, h1, bytecodeVars]
  refine statement_completeAtB fs cert _ hT fun rd h => ?_
  have h9 := mf_reads fs fp seed s w h (i := 9) (by omega)
  refine ⟨s.defer.cells, hlen, h9, ?_, ?_⟩
  · intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact (digestScalars_canonical _).1 | exact (digestScalars_canonical _).2
  · exact congrArg digestCells (statementDigest_parts (digestBytes_eq_cells _)
      (digestBytes_eq_cells _) (digestBytes_eq_cells _) (digestBytes_eq_cells _) rfl hlen)

/-- **`__loop2` on an honest run.** -/
theorem mainGoalL3B (hn : NodeRel bytecode seed s w) (hl : Limits s w)
    (hc : Sig.verify_lean_xmss_complete_Spec) {SK : String → ℕ}
    (hT : TotalLeOn coreProgram fs "__loop2" LoopPre (fun a => logG (a.getD 1 0) * SK "__loop2")) :
    MainGoalL3B fs cert fp seed s w SK := by
  intro h0
  have hpos : 0 < (hRawX s w).length := Nat.pos_of_ne_zero h0
  have hb := regions_lt hl
  have hnl : (hRawX s w).length ≤ s.claims.xmss.length := direct_length_le _ _
  have hX : s.claims.xmss.length ≤ rX s w := Nat.le_add_right _ _
  have h := rawX_completeAtB fs cert hc (rawXD fs fp hn (hRawX s w)[0]) (by omega) (by omega) hT 0 hpos
  rw [pow_zero] at h
  exact h

/-- **`__loop3` on an honest run.** -/
theorem mainGoalL4B (hn : NodeRel bytecode seed s w) (hl : Limits s w)
    (hc : Sig.verify_sig_lean_sphincs_complete_loads_Spec) {SK : String → ℕ}
    (hT : TotalLeOn coreProgram fs "__loop3" LoopPre (fun a => logG (a.getD 1 0) * SK "__loop3")) :
    MainGoalL4B fs cert fp seed s w SK := by
  intro h0
  have hpos : 0 < (hRawS s w).length := Nat.pos_of_ne_zero h0
  have hb := regions_lt hl
  have hnl : (hRawS s w).length ≤ s.claims.sphincs.length := direct_length_le _ _
  have hY : s.claims.sphincs.length ≤ rY s w := Nat.le_add_right _ _
  have h := rawS_completeAtB fs cert hc (rawSD fs fp hn (hRawS s w)[0]) (by omega) (by omega) hT 0 hpos
  rw [pow_zero] at h
  exact h

end
end LeanVM.Guest.B1.Main
