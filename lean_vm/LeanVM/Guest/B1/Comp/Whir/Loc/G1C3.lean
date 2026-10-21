/-
  LeanVM.Guest.B1.Comp.Whir.Loc.G1C3

  `opening_ood_point`, placed, over a completeness model.
-/

module

public import LeanVM.Guest.B1.Comp.Whir.Loc.G1C2
public import LeanVM.Guest.B1.Comp.OpeningOod
public import LeanVM.Guest.B1.OodPlaced

/-!
# `opening_ood_point`, placed, over a completeness model

`ood_holdsC`: `ood_holds` over a model, its loop's relation under `CM.sem`; `oodStatesC`: the
states' run of the answered squeezes (`sqAt`); `opening_ood_point_completeRelBC`:
`opening_ood_point_completeRelB` on `OodPointPreC CM`, the loop `__loop9` by its iterations over the
model (`loop9_step_bwdC`, `loop9_bodies_bwdC`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Main (MemL RegionL)
open LeanVM.E2E.Complete

@[expose] public section

theorem ood_holdsC {CM : CompModel} (rd : Reader) (fs0 fs1 point ng p r0 r1 : E) (m : ℕ) (hN : ng = gen ^ m)
    (l0 : LoadHolds rd p 0 fs0) (l1 : LoadHolds rd p 1 fs1) (l13 : LoadHolds rd p (2 * m) r0)
    (l14 : LoadHolds rd p (2 * m + 1) r1) (hK : IsInK (1 + ng))
    (hcall : 1 + ng ≠ 0 → coreProgram.RelB CM.sem rd "__loop9" [1, ng, p, point] []) :
    (Fn.params Data.core9).map (oodVal fs0 fs1 point ng p r0 r1) = [fs0, fs1, point, ng] ∧
      Stmt.HoldsListB CM.sem (coreProgram.RelB CM.sem rd) rd (oodVal fs0 fs1 point ng p r0 r1) (Fn.body Data.core9)
        False (fun rs => rs = [r0, r1]) := by
  rw [show Fn.params Data.core9 = [.n 0, .n 1, .n 2, .n 3] from rfl,
    show Fn.body Data.core9 = Data.core9.body from rfl, Data.core9.body]
  unfold oodVal
  simp only [Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, List.map_cons, List.map_nil, word_one,
    word_gen, true_and]
  have hx : ∀ k w, LoadHolds rd (p * ng * ng) k w ↔ LoadHolds rd p (2 * m + k) w := by
    intro k w
    rw [hN, mul_assoc, ← pow_add, loadHolds_mul_gen_pow, ← two_mul]
  refine ⟨?_, ?_⟩
  · b1_look
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals (try b1_look)
    · exact l0
    · exact l1
    · exact hK
    · exact hcall
    · exact (hx 0 _).mpr l13
    · exact (hx 1 _).mpr l14

/-- The states' run over a model: the state after each of the `m` answered squeezes from `cv`. -/
def oodStatesC (M : HashModel) (cv : Digest) (m : ℕ) : List E :=
  (List.range (m + 1)).flatMap fun j => [(digestScalars (sqAt M cv j)).1, (digestScalars (sqAt M cv j)).2]

theorem length_oodStatesC (M : HashModel) (cv : Digest) (m : ℕ) : (oodStatesC M cv m).length = 2 * m + 2 :=
  (ood_pairs_facts _ _ (m + 1)).1

theorem oodStatesC_getD (M : HashModel) (cv : Digest) (m : ℕ) {j : ℕ} (hj : j ≤ m) :
    (oodStatesC M cv m).getD (2 * j) 0 = (digestScalars (sqAt M cv j)).1 ∧
      (oodStatesC M cv m).getD (2 * j + 1) 0 = (digestScalars (sqAt M cv j)).2 :=
  (ood_pairs_facts _ _ (m + 1)).2 j (by omega)

theorem opening_ood_point_completeRelBC {CM : CompModel} (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ)
    (B9 : E → ℕ) (h9 : TotalLeOnB CM.sem coreProgram fs "__loop9" LoopPre fun a => B9 (a.getD 1 0)) :
    ∀ (args rets : List E) (Lin : Main.Layout), (∀ rd, LowDef k rd → MemL rd Lin → OodPointPreC CM rd args rets) →
      CompleteAtBS CM.sem fs cert k "opening_ood_point" Lin args (Returns rets)
        (fs "opening_ood_point" + (2 * logG (args.getD 3 0) + 2) + max (B9 (args.getD 3 0)) (fs "__loop9")) := by
  intro args rets Lin hpre fp
  classical
  by_cases hex : ∃ rd1, LowDef k rd1 ∧ MemL rd1 Lin
  swap
  · exact ⟨0, [], rets, [], ⟨rfl, rfl⟩, by simp [Within], disj_nil, Nat.zero_le _, fun rd hl hL =>
      absurd ⟨rd, hl, by simpa using hL⟩ hex⟩
  obtain ⟨rd1, hl1, hL1⟩ := hex
  obtain ⟨fs0, fs1, point, ng, rfl⟩ : ∃ fs0 fs1 point ng, args = [fs0, fs1, point, ng] := by
    match args, hpre rd1 hl1 hL1 with
    | [a, b, c, d], _ => exact ⟨a, b, c, d, rfl⟩
  obtain ⟨m, hm, hm2, hN, hcase⟩ := hpre rd1 hl1 hL1
  set b0 := fp + fs "opening_ood_point" with hb0
  set p : E := ofK (Parameters.gpow b0) with hpdef
  obtain ⟨st, r0, r1, hst, hrets, s0, s1, sr0, sr1, hloop⟩ : ∃ (st : List E) (r0 r1 : E),
      st.length = 2 * m + 2 ∧ rets = [r0, r1] ∧ st.getD 0 0 = fs0 ∧ st.getD 1 0 = fs1 ∧
      st.getD (2 * m) 0 = r0 ∧ st.getD (2 * m + 1) 0 = r1 ∧
      (0 < m → ∀ rd, MemL rd ([(b0, st)] ++ Lin) → coreProgram.RelB CM.sem rd "__loop9" [1, ng, p, point] []) := by
    rcases hcase with ⟨rfl, rfl⟩ | ⟨h0, cv, rs, cv', hcv, hrun, -, rfl⟩
    · exact ⟨[fs0, fs1], fs0, fs1, rfl, rfl, rfl, rfl, rfl, rfl, fun h => absurd h (Nat.lt_irrefl 0)⟩
    · obtain ⟨-, hsq⟩ := hrun.sampleN_sqAll
      have hpt : ∀ rd, LowDef k rd → MemL rd Lin → ReadsAt rd point rs := by
        intro rd hl hL
        obtain ⟨m', hm', -, hN', hc'⟩ := hpre rd hl hL
        have hmm : m' = m := gen_pow_inj hm' hm (hN'.symm.trans hN)
        subst hmm
        rcases hc' with ⟨h0', -⟩ | ⟨-, cv2, rs2, cv2', hcv2, hrun2, hpt2, -⟩
        · omega
        · obtain rfl : cv2 = cv := digestScalars_injective (hcv2.symm.trans hcv)
          obtain ⟨-, hsq2⟩ := hrun2.sampleN_sqAll
          rw [hsq] at hsq2
          obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hsq2)
          exact hpt2
      have hpt' := (readsAt_lift hl1 hL1 hpt).2
      obtain ⟨-, -, hc'⟩ := sqAllM_sqAt hsq
      obtain ⟨g0, g1⟩ := oodStatesC_getD CM.hm cv m (Nat.zero_le m)
      obtain ⟨gm0, gm1⟩ := oodStatesC_getD CM.hm cv m le_rfl
      rw [← hc'] at gm0 gm1
      refine ⟨oodStatesC CM.hm cv m, _, _, length_oodStatesC CM.hm cv m, rfl, ?_, ?_, gm0, gm1, fun _ rd hM => ?_⟩
      · rw [g0]; exact (congrArg Prod.fst hcv).symm
      · rw [g1]; exact (congrArg Prod.snd hcv).symm
      · obtain ⟨hS, hL⟩ := Main.memL_append.mp hM
        have hsc : OodScratchC CM.hm rd p cv m := fun j hj => by
          obtain ⟨a0, a1⟩ := oodStatesC_getD CM.hm cv m hj
          rw [← a0, ← a1]
          exact ⟨g1_loadHolds_of_memL hS (by rw [length_oodStatesC]; omega),
            g1_loadHolds_of_memL hS (by rw [length_oodStatesC]; omega)⟩
        exact (Digest.guarded_loopB_bwd (B := Loop9BodyC CM.hm rd p point)
          (fun x hB hK hc => loop9_step_bwdC rd ng p point x hB hK hc) hN
          (loop9_bodies_bwdC rd p point hsq hsc (hpt' rd hL))).2
          (by rw [hN]; exact ood_one_add_ne hm h0)
  have hLoopC : 0 < m → CompleteAtBS CM.sem fs cert k "__loop9" ([(b0, st)] ++ Lin) [1, ng, p, point] (Returns []) (B9 ng) :=
    fun h0 => completeAtS_of_rel_pureBat find_loop9_pure (by simp) (hloop h0) k fun rd t hn hv hb =>
      h9 rd t _ [] hn (by rw [hN]; exact loopPre_gen h0 hm _) hv hb
  set b := b0 + (2 * m + 2) with hbdef
  obtain ⟨nl, Ll, hWl, hDl, hnb, hRl, hnl⟩ : ∃ (nl : ℕ) (Ll : Main.Layout), Within Ll b nl ∧ DisjL Ll ∧
      nl ≤ max (B9 ng) (fs "__loop9") ∧ (0 < m → ∀ rd,
      LowDef k rd → MemL rd ([] ++ Ll ++ ([(b0, st)] ++ Lin)) →
        RelAtInB CM.sem coreProgram fs cert rd (RegionL ([(b0, st)] ++ Lin)) (RegionL []) b nl "__loop9"
          [1, ng, p, point] []) ∧ (m = 0 → nl = fs "__loop9") := by
    by_cases h0 : 0 < m
    · obtain ⟨n', Lo, rets', Lout', ⟨rfl, rfl⟩, hw, hd, hnb, hr⟩ := hLoopC h0 b
      exact ⟨n', Lo, by simpa using hw, by simpa using hd, le_trans hnb (le_max_left _ _), fun _ => hr, fun h => absurd h (by omega)⟩
    · exact ⟨fs "__loop9", [], by simp [Within], disj_nil, le_max_right _ _, fun h => absurd h h0, fun _ => rfl⟩
  refine ⟨fs "opening_ood_point" + (2 * m + 2) + nl, [(b0, st)] ++ Ll, [r0, r1], [], ⟨hrets.symm, rfl⟩,
    ?_, ?_, ?_, fun rd hl hM => ?_⟩
  · rw [List.nil_append, within_append]
    refine ⟨fun q hq => ?_, hWl.mono (by omega) (by omega)⟩
    rw [List.mem_singleton] at hq
    subst hq
    simp only [hst]
    omega
  · rw [List.nil_append]
    refine disj_append (by simp [DisjL]) hDl (fun q hq => ?_) hWl le_rfl
    rw [List.mem_singleton] at hq
    subst hq
    simp only [hst]
    omega
  · have hlg : logG ng = m := by rw [hN, gen_pow_eq_ofK]; exact logG_spec hm
    change fs "opening_ood_point" + (2 * m + 2) + nl ≤
      fs "opening_ood_point" + (2 * logG ng + 2) + max (B9 ng) (fs "__loop9")
    rw [hlg]
    omega
  rw [List.nil_append] at hM
  obtain ⟨hM1, hLin⟩ := Main.memL_append.mp hM
  obtain ⟨hS, hLl⟩ := Main.memL_append.mp hM1
  have l0 : LoadHolds rd p 0 fs0 := s0 ▸ g1_loadHolds_of_memL hS (by omega)
  have l1 : LoadHolds rd p 1 fs1 := s1 ▸ g1_loadHolds_of_memL hS (by omega)
  have l13 : LoadHolds rd p (2 * m) r0 := sr0 ▸ g1_loadHolds_of_memL hS (by omega)
  have l14 : LoadHolds rd p (2 * m + 1) r1 := sr1 ▸ g1_loadHolds_of_memL hS (by omega)
  have hK : IsInK (1 + ng) := by
    rw [hN]; exact isInK_add (by rw [← pow_zero gen]; exact gen_pow_isInK 0) (gen_pow_isInK m)
  have hcall : 1 + ng ≠ 0 → coreProgram.RelB CM.sem rd "__loop9" [1, ng, p, point] [] := fun hne =>
    hloop (by
      rcases Nat.eq_zero_or_pos m with h | h
      · exact absurd (by rw [hN, h, pow_zero]; exact e_add_self 1) hne
      · exact h) rd (Main.memL_append.mpr ⟨hS, hLin⟩)
  obtain ⟨hpar, hh⟩ := ood_holdsC (CM := CM) rd fs0 fs1 point ng p r0 r1 m hN l0 l1 l13 l14 hK hcall
  set τ := oodVal fs0 fs1 point ng p r0 r1 with hτ
  have t7 : τ (.n 7) = p := by simp only [hτ, oodVal]; b1_look
  have t9 : τ (.n 9) = 1 + ng := by simp only [hτ, oodVal]; b1_look
  have t10 : τ (.n 10) = 1 := by simp only [hτ, oodVal]; b1_look
  have t3 : τ (.n 3) = ng := by simp only [hτ, oodVal]; b1_look
  have t2 : τ (.n 2) = point := by simp only [hτ, oodVal]; b1_look
  have t6 : τ (.n 6) = ng * gen * (ng * gen) := by simp only [hτ, oodVal]; b1_look
  have t12 : τ (.n 12) = p * ng * ng := by simp only [hτ, oodVal]; b1_look
  have t13 : τ (.n 13) = r0 := by simp only [hτ, oodVal]; b1_look
  have t14 : τ (.n 14) = r1 := by simp only [hτ, oodVal]; b1_look
  have hwf : Stmt.wfList coreProgram (Fn.body Data.core9) = true :=
    coreProgram_wf Data.core9 (List.mem_of_find?_eq_some find_opening_ood_point)
  rw [core9_body_eq] at hwf hh
  obtain ⟨hstr, hal, had, hca, hlo⟩ := oodPre_shape
  have hw := Main.walk_straight τ [.n 13, .n 14] oodPre hstr
  have hs := walkB_sat _ hwf hh
  rw [hw] at hs
  obtain ⟨e1, e2, e3, e4⟩ := Main.straight_parts τ oodPre hstr
  rw [hal] at e1 e2
  rw [had] at e3
  rw [hca] at e4
  have h6 : logG (τ (.n 6)) = 2 * m + 2 := by
    rw [t6, hN, show gen ^ m * gen * (gen ^ m * gen) = gen ^ (2 * m + 2) by ring, gen_pow_eq_ofK]
    exact logG_spec hm2
  simp only [List.map_cons, List.map_nil, Sum.elim_inr, h6] at e1 e2
  have hp12 : τ (.n 12) = gen ^ (b0 + 2 * m) := by
    rw [t12, hpdef, hN, ← gen_pow_eq_ofK]; ring
  have hbuf : ∀ i, b0 ≤ i → i < b0 + (2 * m + 2) → ownData cert fp (fp + fs "opening_ood_point")
      "opening_ood_point" [2 * m + 2] (oodPre.flatMap (Main.slEvs τ)) i := fun i h1 h2 =>
    Or.inl ⟨(2 * m + 2, b0), by simp [bases, hb0], h1, by omega⟩
  have h := relAtInB_of_walk (P := coreProgram) (fs := fs) (cert := cert) (σ := τ) (R := RegionL Lin)
    (D := RegionL []) (Dk := fun _ => False) (fp := fp) (N := nl) (args := [fs0, fs1, point, ng])
    (rets := [r0, r1]) coreProgram_wf find_opening_ood_point (Or.inl not_loop_ood) hpar
    (by rw [core9_body_eq]; exact hw) (by simp [t13, t14]) (fun e he => (hs.1 e he).1)
    (by rw [e1, e2]; simp [bases, t7, hpdef, hb0])
    (fun q hq => by rw [e3] at hq; exact absurd hq List.not_mem_nil)
    (by
      rw [show calls (oodPre.flatMap (Main.slEvs τ)) =
        [⟨"__loop9", [.n 10, .n 3, .n 7, .n 2], [], decide (τ (.n 9) ≠ 0)⟩] from e4.trans rfl, e2]
      simp only [List.sum_cons, List.sum_nil, Nat.add_zero]
      refine ⟨nl, 0, RegionL ([(b0, st)] ++ Lin), RegionL [], (Nat.add_zero nl).symm, fun i hi => ?_, ?_,
        rfl, fun _ h => h.elim⟩
      · obtain ⟨q, hq, h1, h2⟩ := hi
        rcases List.mem_append.mp hq with hq | hq
        · rw [List.mem_singleton] at hq
          subst hq
          exact Or.inl (Or.inr (hbuf i h1 (by rw [hst] at h2; exact h2)))
        · exact Or.inl (Or.inl ⟨q, hq, h1, h2⟩)
      · by_cases h0 : 0 < m
        · have hne : τ (.n 9) ≠ 0 := by rw [t9, hN]; exact ood_one_add_ne hm h0
          simp only [hne, ne_eq, not_false_eq_true, decide_true, ↓reduceIte, List.map_cons,
            List.map_nil, t10, t3, t7, t2]
          exact hRl h0 rd hl (by rw [List.nil_append]; exact Main.memL_append.mpr ⟨hLl, Main.memL_append.mpr ⟨hS, hLin⟩⟩)
        · have hz : τ (.n 9) = 0 := by
            rw [t9, hN, show m = 0 by omega, pow_zero]; exact e_add_self 1
          simp only [hz, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
          exact hnl (by omega))
    (fun A hA => by
      rw [e2]
      rw [loadAddrs_straight τ oodPre hstr, hlo] at hA
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hA
      rcases hA with rfl | rfl | rfl | rfl
      · exact ⟨b0 + 0, by rw [t7, hpdef, Main.addr_ofK], Or.inl (hbuf _ (by omega) (by omega))⟩
      · exact ⟨b0 + 1, by rw [t7, hpdef, Main.addr_ofK], Or.inl (hbuf _ (by omega) (by omega))⟩
      · exact ⟨b0 + 2 * m + 0, by rw [hp12, Digest.limb0_gen_pow, Digest.gpow_add'],
          Or.inl (hbuf _ (by omega) (by omega))⟩
      · exact ⟨b0 + 2 * m + 1, by rw [hp12, Digest.limb0_gen_pow, Digest.gpow_add'],
          Or.inl (hbuf _ (by omega) (by omega))⟩)
    (fun i hi => by obtain ⟨q, hq, _⟩ := hi; simp at hq)
  rwa [e2, List.sum_cons, List.sum_nil, Nat.add_zero] at h

end
end LeanVM.Guest.B1
