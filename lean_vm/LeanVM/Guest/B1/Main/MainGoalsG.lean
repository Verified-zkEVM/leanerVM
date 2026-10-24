/-
  LeanVM.Guest.B1.Main.MainGoalsG

  `main`'s raw-signature loops and its direct DA check on an honest run: `MainGoalL3`,
  `MainGoalL4`, `MainGoalDv`, `MainGoalCv`.

  The DA witness and `Da.Witness.Opens` are Benedikt Wagner's LeanDA formalization, as ported here.
-/

module

public import LeanVM.Guest.B1.Main.MainCoverLemmas
public import LeanVM.Guest.B1.Main.RawAt
public import LeanVM.Guest.B1.Main.KidCoverAt
public import LeanVM.Guest.B1.Da.WitnessAt

/-!
# `main`'s raw signatures and direct DA claim, honestly

For a statement `s` held by `w` (`NodeRel`) within the deployed limits (`Limits`), on `main`'s
honest words `hLmain`:

* `rawXD`, `rawSD`: the raw signatures' data (`RawXData`, `RawSData`): raw signature `i` takes
  slot `(slotsOf p)[i]` of its region (`plan_raw`), whose coverage word is `g` to its mark
  (`hMarkX_raw`, `hMarkS_raw`) and whose table entry is its claim;
* `mainGoalL3`, `mainGoalL4`: `__loop3`, `__loop4` from the counter `1 = g^0` (`rawX_completeAt`,
  `rawS_completeAt`), the regions below `2^16` by `Limits.coverage`;
* `mainGoalDv`: `da_verify` on the direct DA claim's witness (`da_verify_completeAt_runs`), its
  squares table `exponent_tables`' second (`wLog_lt`: the padded count's log is below `34`);
* `mainGoalCv`: `cover_da_root` at the direct DA claim's slot, marked `g^(nrx + nrs)`
  (`cover_completeAt`).
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest.Hints (direct plan)
open LeanVM.Guest.B1 (CompleteAtD Returns)
open LeanVM.Guest.B1.Da (reads_of_memL exists_of_length_succ wLog)

@[expose] public section

variable {bytecode : List K} {seed : Digest} {s : NodeStatement} {w : NodeWitness}

/-! ## Bounds -/

/-- The coverage table is below `2^16`. -/
theorem regions_lt (hl : Limits bytecode s w) : rX s w + rY s w + rS s w < 2 ^ 16 := by
  have := hl.coverage
  rw [coverage_eq] at this
  simp only [List.length_append] at this
  simp only [rX, rY, rS]
  omega

/-- The padded count's log is below `34`: at most `1024` rows. -/
theorem wLog_lt {x : LeanVM.Da.Witness} {r v : Digest} (hw : x.Opens r v) : wLog x < 34 := by
  obtain ⟨h1, h2, -⟩ := hw
  have hb := (Da.nPad_bounds h1).2
  unfold LeanDa.maxRows at h2
  by_contra hc
  have : 2 ^ 34 ≤ LeanDa.nPad x.rows.length := by
    unfold LeanDa.nPad
    exact Nat.pow_le_pow_right (by norm_num) (by unfold wLog at hc; omega)
  omega

/-! ## The raw claims' slots -/

theorem xslot {i : ℕ} (hi : i < (hRawX s w).length) :
    ∃ hk : i < (slotsOf (xPlan s w)).length,
      (s.claims.xmss ++ (xPlan s w).dups)[(slotsOf (xPlan s w))[i]]? = some ((hRawX s w)[i]).1 := by
  obtain ⟨hk', hs, e, hc⟩ := plan_raw s.claims.xmss ((hRawX s w).map (·.1))
    (w.children.map (·.statement.claims.xmss)) (k := i) (by simpa using hi)
  rw [← e, List.getElem_map] at hc
  exact ⟨hs, hc⟩

theorem sslot {i : ℕ} (hi : i < (hRawS s w).length) :
    ∃ hk : i < (slotsOf (sPlan s w)).length,
      (s.claims.sphincs ++ (sPlan s w).dups)[(slotsOf (sPlan s w))[i]]? = some ((hRawS s w)[i]).1 := by
  obtain ⟨hk', hs, e, hc⟩ := plan_raw s.claims.sphincs ((hRawS s w).map (·.1))
    (w.children.map (·.statement.claims.sphincs)) (k := i) (by simpa using hi)
  rw [← e, List.getElem_map] at hc
  exact ⟨hs, hc⟩

theorem dslot {i : ℕ} (hi : i < (hRawD s w).length) :
    ∃ hk : i < (slotsOf (dPlan s w)).length,
      (s.claims.da ++ (dPlan s w).dups)[(slotsOf (dPlan s w))[i]]? = some ((hRawD s w)[i]).1 := by
  obtain ⟨hk', hs, e, hc⟩ := plan_raw s.claims.da ((hRawD s w).map (·.1))
    (w.children.map (·.statement.claims.da)) (k := i) (by simpa using hi)
  rw [← e, List.getElem_map] at hc
  exact ⟨hs, hc⟩

/-! ## The raw leanXMSS signatures -/

variable (fs : String → ℕ) (cert : String → V → ℕ) (fp : ℕ)

section
variable {fs fp}

theorem xs_lt {i : ℕ} (hi : i < (hRawX s w).length) : (slotsOf (xPlan s w)).getD i 0 < rX s w := by
  obtain ⟨hk, -⟩ := xslot hi
  rw [List.getD_eq_getElem _ _ hk]
  exact slotX_lt s w hk

theorem xs_verify (hn : NodeRel bytecode seed s w) (d0 : XmssClaim × LeanXmss.Signature) {i : ℕ}
    (hi : i < (hRawX s w).length) :
    xmssVerify ((hRawX s w).getD i d0).1.1 ((hRawX s w).getD i d0).1.2 ((hRawX s w).getD i d0).2 =
      true := by
  rw [List.getD_eq_getElem _ _ hi]
  exact direct_held (H := XmssHeld w.children) (P := fun c σ => xmssVerify c.1 c.2 σ = true)
    (fun _ _ h => h) hn.2.2.1 _ (List.getElem_mem hi)

theorem xs_cover {rd : Reader} (hL : MemL rd (hLmain fs fp seed s w)) {i : ℕ}
    (hi : i < (hRawX s w).length) :
    LoadHolds rd (gen ^ hPos seed s w fs fp 4) ((slotsOf (xPlan s w)).getD i 0) (gen ^ i) := by
  obtain ⟨hk, -⟩ := xslot hi
  have := coverX_load hL hk
  rw [hMarkX_raw s w hi] at this
  rw [List.getD_eq_getElem _ _ hk]
  exact this

theorem xs_claim {rd : Reader} (hL : MemL rd (hLmain fs fp seed s w))
    (d0 : XmssClaim × LeanXmss.Signature) {i : ℕ} (hi : i < (hRawX s w).length) :
    Sig.ClaimAt rd (gen ^ (hPos seed s w fs fp 1 + 4 * (slotsOf (xPlan s w)).getD i 0))
      (Sig.cellOf128 ((hRawX s w).getD i d0).1.1.root)
      (Sig.cellOf128 ((hRawX s w).getD i d0).1.1.parameter)
      (Sig.cellOf128 (((hRawX s w).getD i d0).1.2.extractLsb' 0 128))
      (Sig.cellOf128 (((hRawX s w).getD i d0).1.2.extractLsb' 128 128)) := by
  obtain ⟨hk, hc⟩ := xslot hi
  rw [List.getD_eq_getElem _ _ hk, List.getD_eq_getElem _ _ hi]
  exact tableX_claim hL hc

theorem xs_regCover {i : ℕ} (hi : i < (hRawX s w).length) :
    RegionL (hLmain fs fp seed s w) (hPos seed s w fs fp 4 + (slotsOf (xPlan s w)).getD i 0) :=
  cover_region (by have := xs_lt hi; omega)

theorem xs_regClaim {i : ℕ} (hi : i < (hRawX s w).length) {k : ℕ} (hk : k < 4) :
    RegionL (hLmain fs fp seed s w) (hPos seed s w fs fp 1 + 4 * (slotsOf (xPlan s w)).getD i 0 + k) :=
  tableX_region (xs_lt hi) hk

end

/-- **The raw leanXMSS signatures' honest data.** -/
def rawXD (hn : NodeRel bytecode seed s w) (d0 : XmssClaim × LeanXmss.Signature) :
    RawXData (hRawX s w).length (rX s w) (hPos seed s w fs fp 4) (hPos seed s w fs fp 1)
      (hLmain fs fp seed s w) where
  slot i := (slotsOf (xPlan s w)).getD i 0
  pk i := ((hRawX s w).getD i d0).1.1
  msg i := ((hRawX s w).getD i d0).1.2
  sig i := ((hRawX s w).getD i d0).2
  slot_lt _ hi := xs_lt hi
  verify _ hi := xs_verify hn d0 hi
  cover _ _ hL _ hi := xs_cover hL hi
  claim _ _ hL _ hi := xs_claim hL d0 hi
  regCover _ hi := xs_regCover hi
  regClaim _ hi _ hk := xs_regClaim hi hk

/-- **`__loop3` on an honest run.** -/
theorem mainGoalL3 (hn : NodeRel bytecode seed s w) (hl : Limits bytecode s w)
    (hc : Sig.verify_lean_xmss_complete_Spec) : MainGoalL3 fs cert fp seed s w := by
  intro h0
  have hpos : 0 < (hRawX s w).length := Nat.pos_of_ne_zero h0
  have hb := regions_lt hl
  have hnl : (hRawX s w).length ≤ s.claims.xmss.length := direct_length_le _ _
  have hX : s.claims.xmss.length ≤ rX s w := Nat.le_add_right _ _
  have h := rawX_completeAt fs cert hc (rawXD fs fp hn (hRawX s w)[0]) (by omega) (by omega) 0 hpos
  rw [pow_zero] at h
  exact h

/-! ## The raw leanSPHINCS signatures -/

section
variable {fs fp}

theorem ss_lt {j : ℕ} (hj : j < (hRawS s w).length) : (slotsOf (sPlan s w)).getD j 0 < rY s w := by
  obtain ⟨hk, -⟩ := sslot hj
  rw [List.getD_eq_getElem _ _ hk]
  exact slotS_lt s w hk

theorem ss_verify (hn : NodeRel bytecode seed s w) (d0 : SphincsClaim × Sphincs.Signature) {j : ℕ}
    (hj : j < (hRawS s w).length) :
    sphincsVerify ((hRawS s w).getD j d0).1.1 ((hRawS s w).getD j d0).1.2 ((hRawS s w).getD j d0).2 =
      true := by
  rw [List.getD_eq_getElem _ _ hj]
  exact direct_held (H := SphincsHeld w.children) (P := fun c σ => sphincsVerify c.1 c.2 σ = true)
    (fun _ _ h => h) hn.2.2.2.1 _ (List.getElem_mem hj)

theorem ss_cover {rd : Reader} (hL : MemL rd (hLmain fs fp seed s w)) {j : ℕ}
    (hj : j < (hRawS s w).length) :
    LoadHolds rd (gen ^ hPos seed s w fs fp 4) (rX s w + (slotsOf (sPlan s w)).getD j 0)
      (gen ^ ((hRawX s w).length + j)) := by
  obtain ⟨hk, -⟩ := sslot hj
  have := coverS_load hL hk
  rw [hMarkS_raw s w hj] at this
  rw [List.getD_eq_getElem _ _ hk]
  exact this

theorem ss_claim {rd : Reader} (hL : MemL rd (hLmain fs fp seed s w))
    (d0 : SphincsClaim × Sphincs.Signature) {j : ℕ} (hj : j < (hRawS s w).length) :
    Sig.ClaimAt rd (gen ^ (hPos seed s w fs fp 2 + 4 * (slotsOf (sPlan s w)).getD j 0))
      (Sig.cellOf128 ((hRawS s w).getD j d0).1.1.root)
      (Sig.cellOf128 ((hRawS s w).getD j d0).1.1.parameter)
      (Sig.cellOf128 (((hRawS s w).getD j d0).1.2.extractLsb' 0 128))
      (Sig.cellOf128 (((hRawS s w).getD j d0).1.2.extractLsb' 128 128)) := by
  obtain ⟨hk, hc⟩ := sslot hj
  rw [List.getD_eq_getElem _ _ hk, List.getD_eq_getElem _ _ hj]
  exact tableS_claim hL hc

theorem ss_regCover {j : ℕ} (hj : j < (hRawS s w).length) :
    RegionL (hLmain fs fp seed s w)
      (hPos seed s w fs fp 4 + (rX s w + (slotsOf (sPlan s w)).getD j 0)) :=
  cover_region (by have := ss_lt hj; omega)

theorem ss_regClaim {j : ℕ} (hj : j < (hRawS s w).length) {k : ℕ} (hk : k < 4) :
    RegionL (hLmain fs fp seed s w) (hPos seed s w fs fp 2 + 4 * (slotsOf (sPlan s w)).getD j 0 + k) :=
  tableS_region (ss_lt hj) hk

end

/-- **The raw leanSPHINCS signatures' honest data.** -/
def rawSD (hn : NodeRel bytecode seed s w) (d0 : SphincsClaim × Sphincs.Signature) :
    RawSData (hRawS s w).length (rY s w) (rX s w) (hRawX s w).length (hPos seed s w fs fp 4)
      (hPos seed s w fs fp 2) (hPos seed s w fs fp 5) (hLmain fs fp seed s w) where
  slot j := (slotsOf (sPlan s w)).getD j 0
  pk j := ((hRawS s w).getD j d0).1.1
  msg j := ((hRawS s w).getD j d0).1.2
  sig j := ((hRawS s w).getD j d0).2
  slot_lt _ hj := ss_lt hj
  verify _ hj := ss_verify hn d0 hj
  cover _ _ hL _ hj := ss_cover hL hj
  claim _ _ hL _ hj := ss_claim hL d0 hj
  bytes _ _ hL := bytes_hold hL
  regCover _ hj := ss_regCover hj
  regClaim _ hj _ hk := ss_regClaim hj hk
  regBytes _ hv := bytes_region hv

/-- **`__loop4` on an honest run.** -/
theorem mainGoalL4 (hn : NodeRel bytecode seed s w) (hl : Limits bytecode s w)
    (hc : Sig.verify_sig_lean_sphincs_complete_loads_Spec) : MainGoalL4 fs cert fp seed s w := by
  intro h0
  have hpos : 0 < (hRawS s w).length := Nat.pos_of_ne_zero h0
  have hb := regions_lt hl
  have hnl : (hRawS s w).length ≤ s.claims.sphincs.length := direct_length_le _ _
  have hY : s.claims.sphincs.length ≤ rY s w := Nat.le_add_right _ _
  have h := rawS_completeAt fs cert hc (rawSD fs fp hn (hRawS s w)[0]) (by omega) (by omega) 0 hpos
  rw [pow_zero] at h
  exact h

/-! ## The direct DA claim -/

/-- The direct DA claim, when there is one. -/
theorem direct_da (h1 : (hRawD s w).length = 1) :
    ∃ p, hRawD s w = [p] ∧ (hm fs fp seed s w).daR = daCells p.1 := by
  obtain ⟨p, t, hp, ht⟩ := exists_of_length_succ (show (hRawD s w).length = 0 + 1 from h1)
  rw [List.length_eq_zero_iff] at ht
  subst ht
  refine ⟨p, hp, ?_⟩
  show ((hRawD s w).map fun p => daCells p.1).headD [0, 0, 0, 0] = _
  rw [hp]
  rfl

/-- **`da_verify` on an honest run.** -/
theorem mainGoalDv (hn : NodeRel bytecode seed s w) (hrf : Lift.RunsFit fs cert) :
    MainGoalDv fs cert fp seed s w := by
  intro h1
  obtain ⟨p, hp, hR⟩ := direct_da fs fp h1
  rw [hR]
  have hw : p.2.Opens p.1.1 p.1.2 :=
    direct_held (H := DaHeld w.children) (P := fun c x => x.Opens c.1 c.2) (fun _ _ h => h)
      hn.2.2.2.2.1 p (show p ∈ hRawD s w by rw [hp]; exact List.mem_singleton_self p)
  have hL := wLog_lt hw
  have h := Da.da_verify_completeAt_runs fs cert hrf hw (etB fs (mK0 (hData seed s w) fs fp) + 34)
  have hq : (etB fs (mK0 (hData seed s w) fs fp) + 34, etTabs.getD 1 []) ∈ hLmain fs fp seed s w :=
    List.mem_append_right _ (by simp [etL])
  have hlen : (etTabs.getD 1 []).length = 34 := by simp [etTabs]
  refine completeAtD_lin_mono (fun rd hM => ?_) (fun i hi => ?_) h
  · have hr := reads_of_memL hM hq (wLog p.2) (by omega)
    have hv : (etTabs.getD 1 [])[wLog p.2]'(by omega) = gen ^ 2 ^ wLog p.2 := by simp [etTabs]
    rw [hv] at hr
    intro q hq'
    rw [List.mem_singleton] at hq'
    subst hq'
    intro k hk
    simp only [List.length_singleton, Nat.lt_one_iff] at hk
    subst hk
    rw [← gen_pow_eq_ofK, pow_add, loadHolds_mul_gen_pow, Nat.add_zero]
    exact hr
  · obtain ⟨q, hq', h1, h2⟩ := hi
    rw [List.mem_singleton] at hq'
    subst hq'
    simp only [List.length_singleton] at h1 h2
    exact ⟨_, hq, show etB fs (mK0 (hData seed s w) fs fp) + 34 ≤ i by omega,
      show i < etB fs (mK0 (hData seed s w) fs fp) + 34 + (etTabs.getD 1 []).length by omega⟩

/-- **`cover_da_root` on an honest run.** -/
theorem mainGoalCv (hl : Limits bytecode s w) : MainGoalCv fs cert fp seed s w := by
  intro h1
  obtain ⟨p, hp, hR⟩ := direct_da fs fp h1
  rw [hR]
  have h0 : 0 < (hRawD s w).length := by rw [hp]; simp
  obtain ⟨hk, hc⟩ := dslot h0
  have hp0 : (hRawD s w)[0] = p := by simp only [hp, List.getElem_cons_zero]
  rw [hp0] at hc
  have hb := regions_lt hl
  have hilt := slotD_lt s w hk
  have h := cover_completeAt fs cert (R := hPos seed s w fs fp 0)
    (C := hPos seed s w fs fp 4 + (rX s w + rY s w)) (n := rS s w) (i := (slotsOf (dPlan s w))[0])
    (mark := gen ^ ((hRawX s w).length + (hRawS s w).length)) (r := daCells p.1) (by omega) hilt
    (daCells_length _) (Lin := hLmain fs fp seed s w) (fun rd hM => ⟨?_, tableD_reads hM hc⟩)
    (by rw [Nat.add_assoc]; exact cover_region (by omega)) (fun c hc4 => tableD_region hilt hc4)
  · have key : CompleteAtD fs cert 16 "cover_da_root" (hLmain fs fp seed s w)
        [gen ^ hPos seed s w fs fp 0, gen ^ hPos seed s w fs fp 4 * gen ^ (rX s w + rY s w),
          gen ^ rS s w, gen ^ ((hRawX s w).length + (hRawS s w).length)] (Returns (daCells p.1)) := by
      rw [← pow_add]; exact h
    exact key
  · have := coverD_load hM hk
    rw [hMarkD_raw s w h0, Nat.add_zero] at this
    rw [pow_add, loadHolds_mul_gen_pow]
    exact this

end
end LeanVM.Guest.B1.Main
