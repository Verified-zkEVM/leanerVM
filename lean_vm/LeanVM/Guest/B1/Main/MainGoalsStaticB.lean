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

`MainGoalL0B` … `MainGoalStB`: `MainGoalL0` … `MainGoalSt` with `CompleteAtDTB` within the static
bounds (`SB`, `SK`, the loops' counts) or, for `cover_da_root`, its frame.
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

def MainGoalL0B : Prop :=
  (hm fs fp seed s w).nda + (hm fs fp seed s w).ndd ≠ 0 →
    CompleteAtDTB fs cert 16 "__loop0" (hLmain fs fp seed s w)
      [1, gen ^ ((hm fs fp seed s w).nda + (hm fs fp seed s w).ndd), (hm fs fp seed s w).a69] (Returns []) (fun _ => True)
      (((hm fs fp seed s w).nda + (hm fs fp seed s w).ndd) * SK "__loop0")

def MainGoalL1B : Prop :=
  (hm fs fp seed s w).nxd ≠ 0 →
    CompleteAtDTB fs cert 16 "__loop1" (hLmain fs fp seed s w)
      [1, gen ^ (hm fs fp seed s w).nxd, (hm fs fp seed s w).a77, gen ^ (hm fs fp seed s w).nlx] (Returns []) (fun _ => True) ((hm fs fp seed s w).nxd * SK "__loop1")

def MainGoalL2B : Prop :=
  (hm fs fp seed s w).nsd ≠ 0 →
    CompleteAtDTB fs cert 16 "__loop2" (hLmain fs fp seed s w)
      [1, gen ^ (hm fs fp seed s w).nsd, (hm fs fp seed s w).a80, gen ^ (hm fs fp seed s w).nls] (Returns []) (fun _ => True) ((hm fs fp seed s w).nsd * SK "__loop2")

def MainGoalDlB : Prop :=
  CompleteAtDTB fs cert 16 "da_list_digest" (hLmain fs fp seed s w)
    [(hm fs fp seed s w).a69, gen ^ (hm fs fp seed s w).nda] (Returns (B1.Digest.digestCells (hm fs fp seed s w).dad)) (fun _ => True)
    (SB "da_list_digest")

def MainGoalL3B : Prop :=
  (hm fs fp seed s w).nrx ≠ 0 →
    CompleteAtDTB fs cert 16 "__loop3" (hLmain fs fp seed s w)
      [1, gen ^ (hm fs fp seed s w).nrx, gen ^ ((hm fs fp seed s w).nlx + (hm fs fp seed s w).nxd), (hm fs fp seed s w).a117, (hm fs fp seed s w).a77] (Returns []) (fun _ => True)
      ((hm fs fp seed s w).nrx * SK "__loop3")

def MainGoalL4B : Prop :=
  (hm fs fp seed s w).nrs ≠ 0 →
    CompleteAtDTB fs cert 16 "__loop4" (hLmain fs fp seed s w)
      [1, gen ^ (hm fs fp seed s w).nrs, gen ^ ((hm fs fp seed s w).nls + (hm fs fp seed s w).nsd), (hm fs fp seed s w).a117, gen ^ ((hm fs fp seed s w).nlx + (hm fs fp seed s w).nxd),
        gen ^ (hm fs fp seed s w).nrx, (hm fs fp seed s w).a80, (hm fs fp seed s w).a119] (Returns []) (fun _ => True) ((hm fs fp seed s w).nrs * SK "__loop4")

def MainGoalCvB : Prop :=
  (hm fs fp seed s w).nd = 1 →
    CompleteAtDTB fs cert 16 "cover_da_root" (hLmain fs fp seed s w)
      [(hm fs fp seed s w).a69, (hm fs fp seed s w).a117 * gen ^ ((hm fs fp seed s w).nlx + (hm fs fp seed s w).nxd + ((hm fs fp seed s w).nls + (hm fs fp seed s w).nsd)),
        gen ^ ((hm fs fp seed s w).nda + (hm fs fp seed s w).ndd), gen ^ ((hm fs fp seed s w).nrx + (hm fs fp seed s w).nrs)] (Returns (hm fs fp seed s w).daR) (fun _ => True)
      (fs "cover_da_root")

def MainGoalStB : Prop :=
  CompleteAtDTB fs cert 16 "statement_digest" (hLmain fs fp seed s w)
    [(digestScalars (hm fs fp seed s w).seed).1, (digestScalars (hm fs fp seed s w).seed).2, (hm fs fp seed s w).a116, (digestScalars (hm fs fp seed s w).dad).1,
      (digestScalars (hm fs fp seed s w).dad).2, (hm fs fp seed s w).a417] (Returns (B1.Digest.digestCells (hm fs fp seed s w).sdg)) (fun _ => True)
    (SB "statement_digest")

variable {fs cert fp seed s w SB SK} {bytecode : List K}

/-- **`__loop0`…`__loop2` within their static bounds.** -/
theorem mainGoalL0B (hT : TotalLeOn coreProgram fs "__loop0" LoopPre (fun a => logG (a.getD 1 0) * SK "__loop0"))
    (hl : (hm fs fp seed s w).nda + (hm fs fp seed s w).ndd < 2 ^ 64 - 1) : MainGoalL0B fs cert fp seed s w SK := fun hne =>
  (completeAt_of_rel_pureBat mfLoop_pure (by simp [mfLoopSet]) (fun rd _ => mfL0_rel rd _ hne) 16
    fun rd t hn hv hb => by
      have := hT rd t _ _ hn (loopPre_gen (Nat.pos_of_ne_zero hne) hl _) hv hb
      simpa [logG_gen hl] using this).toDTB

theorem mainGoalL1B (hT : TotalLeOn coreProgram fs "__loop1" LoopPre (fun a => logG (a.getD 1 0) * SK "__loop1"))
    (hl : (hm fs fp seed s w).nxd < 2 ^ 64 - 1) : MainGoalL1B fs cert fp seed s w SK := fun hne =>
  (completeAt_of_rel_pureBat mfLoop_pure (by simp [mfLoopSet]) (fun rd _ => mfL1_rel rd _ _ hne) 16
    fun rd t hn hv hb => by
      have := hT rd t _ _ hn (loopPre_gen (Nat.pos_of_ne_zero hne) hl _) hv hb
      simpa [logG_gen hl] using this).toDTB

theorem mainGoalL2B (hT : TotalLeOn coreProgram fs "__loop2" LoopPre (fun a => logG (a.getD 1 0) * SK "__loop2"))
    (hl : (hm fs fp seed s w).nsd < 2 ^ 64 - 1) : MainGoalL2B fs cert fp seed s w SK := fun hne =>
  (completeAt_of_rel_pureBat mfLoop_pure (by simp [mfLoopSet]) (fun rd _ => mfL2_rel rd _ _ hne) 16
    fun rd t hn hv hb => by
      have := hT rd t _ _ hn (loopPre_gen (Nat.pos_of_ne_zero hne) hl _) hv hb
      simpa [logG_gen hl] using this).toDTB

/-- **`da_list_digest` on the DA table's declared claims.** -/
theorem mainGoalDlB {bytecode : List K} (hL : Limits bytecode s w) {SB : String → ℕ}
    (hT : TotalLe coreProgram fs "da_list_digest" (fun _ => SB "da_list_digest")) :
    MainGoalDlB fs cert fp seed s w SB := by
  refine daList_completeAtB fs cert hT fun rd h => ?_
  have h0 := mf_reads fs fp seed s w h (i := 0) (by omega)
  rw [show (hOwn seed s w).getD 0 [] = s.claims.da.flatMap daCells ++ (dPlan s w).dups.flatMap daCells
    by rw [← List.flatMap_append]; rfl] at h0
  refine ⟨s.claims.da.length, hL.daRoots.1, rfl, s.claims.da.flatMap daCells,
    mf_length_flatMap _ mf_daCells_length _, (readsAt_append'.mp h0).1,
    mf_canon_flatMap _ mf_daCells_canon _, ?_⟩
  exact congrArg digestCells (mf_da_digest s.claims.da)

/-- **`statement_digest` on the signer set's cells and the deferred claim**, a bytecode of `2^23`
words making the deferred claim `24` cells. -/
theorem mainGoalStB {bytecode : List K} (hR : NodeRel bytecode seed s w)
    (hbl : bytecode.length = 2 ^ bytecodeVars) {SB : String → ℕ}
    (hT : TotalLe coreProgram fs "statement_digest" (fun _ => SB "statement_digest")) :
    MainGoalStB fs cert fp seed s w SB := by
  have hlen : s.defer.cells.length = 24 := by
    have h1 : s.defer.bytecodePoint.length = Nat.log2 bytecode.length := hR.1
    rw [hbl, Nat.log2_two_pow] at h1
    simp [DeferredClaim.cells, h1, bytecodeVars]
  refine statement_completeAtB fs cert hT fun rd h => ?_
  have h3 := mf_reads fs fp seed s w h (i := 3) (by omega)
  have h10 := mf_reads fs fp seed s w h (i := 10) (by omega)
  refine ⟨(digestScalars (signersDigest s.claims.xmss s.claims.sphincs)).1,
    (digestScalars (signersDigest s.claims.xmss s.claims.sphincs)).2, s.defer.cells,
    h3 0 (by simp [hOwn, digestCells]), h3 1 (by simp [hOwn, digestCells]), hlen, h10, ?_, ?_⟩
  · intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact (digestScalars_canonical _).1 | exact (digestScalars_canonical _).2
  · exact congrArg digestCells (statementDigest_parts (digestBytes_eq_cells _)
      (digestBytes_eq_cells _) (digestBytes_eq_cells _) rfl hlen)

/-- **`__loop3` on an honest run.** -/
theorem mainGoalL3B (hn : NodeRel bytecode seed s w) (hl : Limits bytecode s w)
    (hc : Sig.verify_lean_xmss_complete_Spec) {SK : String → ℕ}
    (hT : TotalLeOn coreProgram fs "__loop3" LoopPre (fun a => logG (a.getD 1 0) * SK "__loop3")) :
    MainGoalL3B fs cert fp seed s w SK := by
  intro h0
  have hpos : 0 < (hRawX s w).length := Nat.pos_of_ne_zero h0
  have hb := regions_lt hl
  have hnl : (hRawX s w).length ≤ s.claims.xmss.length := direct_length_le _ _
  have hX : s.claims.xmss.length ≤ rX s w := Nat.le_add_right _ _
  have h := rawX_completeAtB fs cert hc (rawXD fs fp hn (hRawX s w)[0]) (by omega) (by omega) hT 0 hpos
  rw [pow_zero] at h
  exact h

/-- **`__loop4` on an honest run.** -/
theorem mainGoalL4B (hn : NodeRel bytecode seed s w) (hl : Limits bytecode s w)
    (hc : Sig.verify_sig_lean_sphincs_complete_loads_Spec) {SK : String → ℕ}
    (hT : TotalLeOn coreProgram fs "__loop4" LoopPre (fun a => logG (a.getD 1 0) * SK "__loop4")) :
    MainGoalL4B fs cert fp seed s w SK := by
  intro h0
  have hpos : 0 < (hRawS s w).length := Nat.pos_of_ne_zero h0
  have hb := regions_lt hl
  have hnl : (hRawS s w).length ≤ s.claims.sphincs.length := direct_length_le _ _
  have hY : s.claims.sphincs.length ≤ rY s w := Nat.le_add_right _ _
  have h := rawS_completeAtB fs cert hc (rawSD fs fp hn (hRawS s w)[0]) (by omega) (by omega) hT 0 hpos
  rw [pow_zero] at h
  exact h

/-- **`cover_da_root` on an honest run.** -/
theorem mainGoalCvB (hl : Limits bytecode s w) : MainGoalCvB fs cert fp seed s w := by
  intro h1
  obtain ⟨p, hp, hR⟩ := direct_da fs fp h1
  rw [hR]
  have h0 : 0 < (hRawD s w).length := by rw [hp]; simp
  obtain ⟨hk, hc⟩ := dslot h0
  have hp0 : (hRawD s w)[0] = p := by simp only [hp, List.getElem_cons_zero]
  rw [hp0] at hc
  have hb := regions_lt hl
  have hilt := slotD_lt s w hk
  have h := cover_completeAtB fs cert (R := hPos seed s w fs fp 0)
    (C := hPos seed s w fs fp 4 + (rX s w + rY s w)) (n := rS s w) (i := (slotsOf (dPlan s w))[0])
    (mark := gen ^ ((hRawX s w).length + (hRawS s w).length)) (r := daCells p.1) (by omega) hilt
    (daCells_length _) (Lin := hLmain fs fp seed s w) (fun rd hM => ⟨?_, tableD_reads hM hc⟩)
    (by rw [Nat.add_assoc]; exact cover_region (by omega)) (fun c hc4 => tableD_region hilt hc4)
  · have key : CompleteAtDTB fs cert 16 "cover_da_root" (hLmain fs fp seed s w)
        [gen ^ hPos seed s w fs fp 0, gen ^ hPos seed s w fs fp 4 * gen ^ (rX s w + rY s w),
          gen ^ rS s w, gen ^ ((hRawX s w).length + (hRawS s w).length)] (Returns (daCells p.1))
        (fun _ => True) (fs "cover_da_root") := by
      rw [← pow_add]; exact h
    exact key
  · have := coverD_load hM hk
    rw [hMarkD_raw s w h0, Nat.add_zero] at this
    rw [pow_add, loadHolds_mul_gen_pow]
    exact this

end
end LeanVM.Guest.B1.Main
