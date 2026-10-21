/-
  LeanVM.Guest.B1.Main.MainAtCT

  `main` placed under a semantics `S` over an answered hash, its tree satisfying a predicate
  (`MainAtC.lean` with `Comp/TreeRoot.lean`'s tree predicates).
-/

module

public import LeanVM.Guest.B1.Main.MainAtC
public import LeanVM.Guest.B1.Main.ChildrenAtCT

/-!
# `main` placed, its tree kept

* `mainS_relAtIn_coreWT`: `mainS_relAtIn_coreW` with its callees `KidsWST`, `main`'s node satisfying
  any predicate its valuation `mainVal rd (mainRunAt fs fp W)` and its callees' trees give it.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest.B1 (DisjL disj_nil disj_append bufL_disj Within LowDef CompleteAtB CompleteRelB Returns Kid
  CallsMatch OutsOk OutsIn RegionsOk outRegion kidsFromIn_of_kidsB kidsBound regionsOk_of memL_lins relAtIn_dmono
  within_append bufL bufL_region bufL_within RelAtInWST CompleteAtWST KidsFromInWST KidsWST KidsSat
  kidsFromInWST_of_kidsW)

@[expose] public section

variable {S : BlakeSem}

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- A placed relation within weights by a tree satisfying `True`. -/
theorem RelAtInWS.toWST {Θ : Type} {w : Θ → String → ℕ} {rd : Reader} {R D : ℕ → Prop} {fp n : ℕ}
    {f : String} {args rets : List E} {Bw : Θ → ℕ}
    (h : RelAtInWS S fs cert w rd R D fp n f args rets Bw) :
    RelAtInWST S fs cert w rd R D fp n f args rets Bw fun _ => True :=
  let ⟨t, hn, hv, hb, hp, ht, hl, hd, hw⟩ := h
  ⟨t, trivial, hn, hv, hb, hp, ht, hl, hd, hw⟩

variable {Ha : List UInt8 → Option Digest} {κ : ℕ} {VsGood : VerifySub.VsData → VerifySub.VsRunC → Prop}
  {Bd : CalleeBounds} {fp : ℕ} {W : MainWords}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- **`main` at `fp`, from its callees**: the callees after `exponent_tables` as `Kid`s reading
`mainIn`, within bounds `bs` (`KidsBS`), matching `main`'s frames under its valuation. -/
theorem mainS_relAtIn_coreWT {Θ : Type} {w : Θ → String → ℕ} (Wt : ∀ θ, MainWeightHypsS S fs (w θ))
    (hκ : 16 ≤ κ) (hW : MainWordsOkC S fs Ha κ VsGood fp W) (ks : List Kid)
    (bs : List ℕ) (bws : List (Θ → ℕ)) (Qs : List (ℕ → Reader → Memory.Tree → Prop))
    (hks : KidsWST S fs cert w κ ks bs bws Qs)
    (hsub : ∀ k ∈ ks, SubL k.Lin (mainIn fs fp W))
    (hcm : ∀ rd, ∀ outs, OutsOk ks outs → CallsMatch (mainVal rd (mainRunAt fs fp W))
      ((mainFronts (decide (W.rd = 1)) (decide (W.nc = 0))).map
        (mkCall (mainVal rd (mainRunAt fs fp W)))) ks outs)
    (Q : Reader → Memory.Tree → Prop)
    (hQ : ∀ rd (ks' : List Memory.Tree), Tree.KidsValidB S coreProgram rd (mainVal rd (mainRunAt fs fp W))
      (⟨"exponent_tables", [], [.n 65, .n 66], true⟩ :: (mainFronts (decide (W.rd = 1))
        (decide (W.nc = 0))).map (mkCall (mainVal rd (mainRunAt fs fp W)))) ks' →
      KidsSat (⟨"exponent_tables", [], [.n 65, .n 66], true⟩ :: (mainFronts (decide (W.rd = 1))
        (decide (W.nc = 0))).map (mkCall (mainVal rd (mainRunAt fs fp W))))
        ((fun _ _ => True) :: Qs.map fun Q b t => Q b rd t)
        (bases (fp + fs "main" + W.sizes.sum) (ks'.map (Tree.total fs))) ks' →
      Q rd (Memory.Tree.node "main" (mainVal rd (mainRunAt fs fp W)) W.sizes ks')) :
    ∃ (m : ℕ) (L : Layout), Within (mainIn fs fp W ++ L) (fp + fs "main") m ∧
      DisjL (mainIn fs fp W ++ L) ∧ m ≤ W.sizes.sum + (fs "exponent_tables" + 68 + bs.sum) ∧
      ∀ rd, LowDef κ rd → MemL rd (mainIn fs fp W ++ L) →
        rd 1 = some (digestScalars W.stDig).1 → rd g = some (digestScalars W.stDig).2 →
        RelAtInWST S fs cert w rd (fun i => i < 2) (fun _ => False) fp (fs "main" + m)
          "main" [] [] (fun θ => w θ "main" + ((Wt θ).Bexp + (bws.map (· θ)).sum)) (Q rd) := by
  set b0 := fp + fs "main" with hb0
  set bK := b0 + W.sizes.sum with hbK
  set n0 := fs "exponent_tables" + [34, 34].sum + 0 with hn0
  obtain ⟨N, Lk, outs, ho, hWk, hDk, hNb, -, hK⟩ := kidsFromInWST_of_kidsW (fs := fs) (cert := cert) (w := w) κ
    ks bs bws Qs hks (bK + n0)
  have hf := forall₂_of_map_length _ _ hW.lens
  have hWx : Within (mainLexp fs fp W) bK n0 := by
    intro q hq
    simp only [mainLexp, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> simp only [mainExpBase, expTbl1, expTbl2, List.length_map,
      List.length_range, hn0, List.sum_cons, List.sum_nil] <;> omega
  have hWin : Within (mainIn fs fp W) b0 (W.sizes.sum + n0) := by
    rw [mainIn, within_append]
    exact ⟨(bufL_within _ _ _ hf).mono le_rfl (by omega), hWx.mono (by omega) (by omega)⟩
  have hDx : DisjL (mainLexp fs fp W) := by
    simp only [mainLexp, DisjL, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq, List.Pairwise.nil, and_true, IsEmpty.forall_iff, implies_true]
    left; simp [expTbl1]
  have hDin : DisjL (mainIn fs fp W) :=
    disj_append (bufL_disj _ _ _ hf) hDx (bufL_within _ _ _ hf) hWx (by omega)
  refine ⟨W.sizes.sum + (n0 + N), Lk, ?_, disj_append hDin hDk hWin hWk (by omega), ?_,
    fun rd hl hL hp0 hp1 => ?_⟩
  · rw [within_append]
    exact ⟨hWin.mono le_rfl (by omega), hWk.mono (by omega) (by omega)⟩
  · simp only [hn0, List.sum_cons, List.sum_nil]
    omega
  obtain ⟨hLin, hLk⟩ := memL_append.mp hL
  set R := mainRunAt fs fp W with hR
  set σ := mainVal rd R with hσ
  have hok := mainOkS_of_words hκ hW hl hLin hp0 hp1
  have hH := mainS_body_holds hok
  have hwf : Stmt.wfList coreProgram mainBody = true := by
    have := coreProgram_wf Data.core0 (List.mem_of_find?_eq_some find_main)
    rwa [core0_body] at this
  have hw := walk_mainBody σ
  have hsat := walkB_sat mainBody hwf hH
  rw [hw] at hsat
  have hb1 : decide (σ (.n 112) = 0) = decide (W.rd = 1) := branch1 hW.rd1
  have hb2 : decide (σ (.n 155) = 0) = decide (W.nc = 0) := branch2 hW.nc
  obtain ⟨q1, q2, q3, q4⟩ := mainLin_parts (decide (W.rd = 1)) (decide (W.nc = 0))
  obtain ⟨e1, e2, e3, e4⟩ := straight_parts σ _ (mainLin_straight (decide (W.rd = 1)) (decide (W.nc = 0)))
  rw [q1] at e1 e2
  rw [q2] at e3
  rw [q3] at e4
  have hal : allocs σ (mainEvs σ) = W.sizes := by
    rw [allocs_mainEvs, hb1, hb2, e2]; exact mainS_allocs hW
  have hdst : (allocDsts (mainEvs σ)).map σ =
      (bases b0 (allocs σ (mainEvs σ))).map fun b => ofK (gpow b) := by
    rw [allocDsts_mainEvs, hb1, hb2, e1, hal]
    simp only [mainAllocs, List.map_cons, List.map_nil, hσ, mainVal, hR, mainRunAt]
    b1_look
    rfl
  have hcalls : calls (mainEvs σ) =
      ⟨"exponent_tables", [], [.n 65, .n 66], true⟩ :: (mainFronts (decide (W.rd = 1))
        (decide (W.nc = 0))).map (mkCall σ) := by
    rw [calls_mainEvs, hb1, hb2, e4]; rfl
  have hexp : MemL rd (mainLexp fs fp W) := (memL_append.mp hLin).2
  have hown : ∀ i, RegionL (mainLb fs fp W) i →
      ownData cert fp b0 "main" W.sizes (mainEvs σ) i := fun i hi =>
    Or.inl (bufL_region _ _ _ (forall₂_of_map_length _ _ hW.lens) i hi)
  have hexpRel := exponentS_tables_relAtIn (S := S) (fs := fs) (cert := cert) bK rd hexp
  have hk : KidsFromInWST S fs cert w rd σ
      (fun i => i < 2 ∨ ownData cert fp b0 "main" (allocs σ (mainEvs σ)) (mainEvs σ) i)
      (fun _ => False) (calls (mainEvs σ)) ((fun θ => (Wt θ).Bexp) :: bws)
      ((fun _ _ => True) :: Qs.map fun Q b t => Q b rd t)
      (b0 + (allocs σ (mainEvs σ)).sum) (n0 + N)
      (fun i => (False ∨ (true = true ∧ RegionL (mainLexp fs fp W) i)) ∨ outRegion ks outs i) := by
    rw [hcalls, hal]
    refine ⟨n0, N, RegionL [], RegionL (mainLexp fs fp W), rfl,
      fun i hi => by obtain ⟨q, hq, _⟩ := hi; simp at hq, ?_, ?_⟩
    · simp only [↓reduceIte, List.map_nil, List.map_cons]
      have e65 : σ (.n 65) = ofK (gpow (bK + fs "exponent_tables")) := by
        simp only [hσ, mainVal, hR, mainRunAt]; b1_look; rfl
      have e66 : σ (.n 66) = ofK (gpow (bK + fs "exponent_tables" + 34)) := by
        simp only [hσ, mainVal, hR, mainRunAt]; b1_look; rfl
      rw [e65, e66]
      exact RelAtInWS.toWST (relAtInWS_of_weightLe (Bf := fun θ _ => (Wt θ).Bexp) hexpRel
        fun θ => (Wt θ).exp)
    · refine hK rd σ _ _ _ (hcm rd outs ho) hl hLk
        (memL_lins fun k hk' => (hsub k hk').1 rd hLin) (regionsOk_of fun k hk' _ i hi => ?_)
      rcases regionL_append_or ((hsub k hk').2 i hi) with h | h
      · exact Or.inl (Or.inr (hown i h))
      · exact Or.inr (Or.inr ⟨rfl, h⟩)
  have := LeanVM.Guest.B1.relAtInWST_of_walk (fs := fs) (cert := cert) (w := w) (R := fun i => i < 2)
    (D := fun _ => False) (fp := fp) (σ := σ) (rd := rd) (args := []) (rets := []) (Q := Q rd)
    find_main (Or.inl main_not_loop) rfl (by rw [core0_body]; exact hw) rfl
    (fun e he => (hsat.1 e he).1) hdst (by rw [addrs_mainEvs, hb1, hb2, e3]; simp) hk ?_
    (fun i hi => hi.elim) ?_
  · rw [hal, Nat.add_assoc] at this
    exact RelAtInWST.wmono this fun θ => by simp only [List.map_cons, List.sum_cons]; omega
  · have hreg : ∀ j < 10, ∀ k < W.sizes.getD j 0,
        ownData cert fp b0 "main" (allocs σ (mainEvs σ)) (mainEvs σ) (mainBase fs fp W j + k) := by
      intro j hj k hk
      rw [hal]
      refine hown _ (regionL_of_mem (mainLb_mem j hj) ?_)
      rw [getD_map_length, hW.lens]
      exact hk
    have hbuf : ∀ j < 10, ∀ k < W.sizes.getD j 0, ∃ i,
        (mainPtr fs fp W j).limb 0 * Parameters.gpow k = Parameters.gpow i ∧
        (ownData cert fp b0 "main" (allocs σ (mainEvs σ)) (mainEvs σ) i ∨ i < 2 ∨
          ((False ∨ (true = true ∧ RegionL (mainLexp fs fp W) i)) ∨ outRegion ks outs i)) :=
      fun j hj k hk => ⟨mainBase fs fp W j + k, addr_ofK _ _, Or.inl (hreg j hj k hk)⟩
    intro A hA
    rw [loadAddrs_mainEvs, hb1, hb2, LeanVM.Guest.B1.loadAddrs_straight σ _ (mainLin_straight _ _), q4,
      List.mem_map] at hA
    obtain ⟨q, hq, rfl⟩ := hA
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hq
    have p3 : σ (.n 102) = mainPtr fs fp W 3 := by simp only [hσ, mainVal, hR, mainRunAt]; b1_look
    have p8 : σ (.n 145) = mainPtr fs fp W 8 := by simp only [hσ, mainVal, hR, mainRunAt]; b1_look
    have p9 : σ (.n 153) = mainPtr fs fp W 9 := by simp only [hσ, mainVal, hR, mainRunAt]; b1_look
    have p151 : σ (.n 151) = mainPtr fs fp W 8 * gen ^ W.nc := by
      simp only [hσ, mainVal, hR, mainRunAt]; b1_look
    have p211 : σ (.n 211) = 1 := by simp only [hσ, mainVal]; b1_look
    have p215 : σ (.n 215) = 1 * gen := by simp only [hσ, mainVal]; b1_look
    have s3 : W.sizes.getD 3 0 = 2 := rfl
    have s8 : W.sizes.getD 8 0 = W.nc + 1 := rfl
    have s9 : W.sizes.getD 9 0 = 53 := rfl
    rcases hq with (((rfl | rfl | rfl | rfl) | hq) | rfl | rfl)
    · rw [p3]; exact hbuf 3 (by omega) 0 (by rw [s3]; omega)
    · rw [p3]; exact hbuf 3 (by omega) 1 (by rw [s3]; omega)
    · rw [p8]; exact hbuf 8 (by omega) 0 (by rw [s8]; omega)
    · rw [p151]
      refine ⟨mainBase fs fp W 8 + W.nc, ?_, Or.inl (hreg 8 (by omega) W.nc (by rw [s8]; omega))⟩
      rw [mainPtr, ofK_gpow_mul_gen, addr_ofK, Nat.add_zero]
    · cases hb : decide (W.nc = 0) <;> simp only [hb, Bool.false_eq_true, ↓reduceIte,
        List.not_mem_nil] at hq
      simp only [leafLoads, List.mem_append, List.mem_map, List.mem_range, List.mem_cons,
        List.not_mem_nil, or_false] at hq
      rcases hq with ((⟨k, hk, rfl⟩ | rfl) | ⟨k, hk, rfl⟩) | rfl | rfl <;> rw [p9]
      · exact hbuf 9 (by omega) k (by rw [s9]; omega)
      · exact hbuf 9 (by omega) 22 (by rw [s9]; omega)
      · exact hbuf 9 (by omega) (23 + k) (by rw [s9]; omega)
      · exact hbuf 9 (by omega) 51 (by rw [s9]; omega)
      · exact hbuf 9 (by omega) 52 (by rw [s9]; omega)
    · rw [p211]
      exact ⟨0, by rw [← ofK_one, limb_ofK]; simp [Parameters.gpow], Or.inr (Or.inl (by omega))⟩
    · rw [p215]
      exact ⟨1, by rw [one_mul, gen_eq_ofK, limb_ofK]; simp [Parameters.gpow], Or.inr (Or.inl (by omega))⟩
  · intro ks' hkv' hks'
    rw [hcalls] at hkv' hks'
    rw [hal] at hks' ⊢
    exact hQ rd ks' hkv' hks'


/-! ## Callees with predicates -/

/-- Callees without predicates, with `True` ones. -/
theorem KidsWS.toWST {Θ : Type} {w : Θ → String → ℕ} {κ : ℕ} :
    ∀ {ks : List Kid} {bs : List ℕ} {bws : List (Θ → ℕ)}, KidsWS S fs cert w κ ks bs bws →
      KidsWST S fs cert w κ ks bs bws (ks.map fun _ _ _ _ => True)
  | [], [], [], _ => trivial
  | _ :: _, _ :: _, _ :: _, ⟨h1, h2, h⟩ =>
      ⟨fun ht => LeanVM.Guest.B1.CompleteAtWS.toWST (h1 ht), h2, KidsWS.toWST h⟩
  | [], _ :: _, _, h => h.elim
  | [], [], _ :: _, h => h.elim
  | _ :: _, [], _, h => h.elim
  | _ :: _, _ :: _, [], h => h.elim

/-- `KidsWS.append` with predicates. -/
theorem KidsWST.append {Θ : Type} {w : Θ → String → ℕ} {κ : ℕ} :
    ∀ {ks ks' : List Kid} {bs bs' : List ℕ} {bws bws' : List (Θ → ℕ)}
      {Qs Qs' : List (ℕ → Reader → Memory.Tree → Prop)},
    KidsWST S fs cert w κ ks bs bws Qs → KidsWST S fs cert w κ ks' bs' bws' Qs' →
      KidsWST S fs cert w κ (ks ++ ks') (bs ++ bs') (bws ++ bws') (Qs ++ Qs')
  | [], _, [], _, [], _, [], _, _, h' => h'
  | _ :: _, _, _ :: _, _, _ :: _, _, _ :: _, _, ⟨h1, h2, h⟩, h' => ⟨h1, h2, KidsWST.append h h'⟩
  | [], _, _ :: _, _, _, _, _, _, h, _ => h.elim
  | [], _, [], _, _ :: _, _, _, _, h, _ => h.elim
  | [], _, [], _, [], _, _ :: _, _, h, _ => h.elim
  | _ :: _, _, [], _, _, _, _, _, h, _ => h.elim
  | _ :: _, _, _ :: _, _, [], _, _, _, h, _ => h.elim
  | _ :: _, _, _ :: _, _, _ :: _, _, [], _, h, _ => h.elim

/-! ## `main`'s tree -/

/-- **`main`'s tree**: the node of `main` at the valuation `σ`, and, with children, one callee's
tree satisfying `Loop5Q` from iteration `0` where it is placed. -/
def MainQ (VsQ : VerifySub.VsData → VerifySub.VsRunC → ℕ → Reader → Memory.Tree → Prop)
    (vr : ℕ → VerifySub.VsData × VerifySub.VsRunC) (fs : String → ℕ) (nc fp : ℕ) (σ : Val)
    (rd : Reader) (t : Memory.Tree) : Prop :=
  ∃ (bufs : List ℕ) (ks : List Memory.Tree), t = Memory.Tree.node "main" σ bufs ks ∧
    (nc ≠ 0 → ∃ (i : ℕ) (k : Memory.Tree) (b : ℕ), ks[i]? = some k ∧
      (bases (fp + fs "main" + bufs.sum) (ks.map (Memory.Tree.total fs)))[i]? = some b ∧
      Loop5Q VsQ vr fs nc 0 b rd k)

set_option maxRecDepth 100000 in
/-- `main`'s node gives `MainQ` from its callees' predicates, the loop's `Loop5Q`. -/
theorem mainQ_of_sat {VsQ : VerifySub.VsData → VerifySub.VsRunC → ℕ → Reader → Memory.Tree → Prop}
    {vr : ℕ → VerifySub.VsData × VerifySub.VsRunC}
    (hnc16 : W.nc ≤ 16) (hnc : W.nc ≠ 0) (Qrest Qrest' : List (ℕ → Reader → Memory.Tree → Prop))
    (hQr : Qrest.length + Qrest'.length = 2)
    (rd : Reader) (ks' : List Memory.Tree)
    (hkv : Tree.KidsValidB S coreProgram rd (mainVal rd (mainRunAt fs fp W))
      (⟨"exponent_tables", [], [.n 65, .n 66], true⟩ :: (mainFronts (decide (W.rd = 1))
        (decide (W.nc = 0))).map (mkCall (mainVal rd (mainRunAt fs fp W)))) ks')
    (hks : KidsSat (⟨"exponent_tables", [], [.n 65, .n 66], true⟩ :: (mainFronts (decide (W.rd = 1))
        (decide (W.nc = 0))).map (mkCall (mainVal rd (mainRunAt fs fp W))))
      ((fun _ _ => True) :: (((mainKids8 fs fp W ++ (if W.rd = 1 then mainKidsDa fs fp W else [])).map
        (fun _ _ _ _ => True) ++ [fun b rd t => Loop5Q VsQ vr fs W.nc 0 b rd t]) ++
          Qrest ++ Qrest').map fun (Q : ℕ → Reader → Memory.Tree → Prop) b t => Q b rd t)
      (bases (fp + fs "main" + W.sizes.sum) (ks'.map (Tree.total fs))) ks') :
    MainQ VsQ vr fs W.nc fp (mainVal rd (mainRunAt fs fp W)) rd
      (Memory.Tree.node "main" (mainVal rd (mainRunAt fs fp W)) W.sizes ks') := by
  set σ := mainVal rd (mainRunAt fs fp W) with hσ
  have e : (⟨"exponent_tables", [], [.n 65, .n 66], true⟩ :: (mainFronts (decide (W.rd = 1))
      (decide (W.nc = 0))).map (mkCall σ) : List Call) =
      (⟨"exponent_tables", [], [.n 65, .n 66], true⟩ :: (mainFronts8 ++
        (if decide (W.rd = 1) then mainFrontsDa else [])).map (mkCall σ)) ++
      mkCall σ mainFront5 :: ((if decide (W.nc = 0) then [] else [mainFrontAgg]) ++
        [mainFrontSd]).map (mkCall σ) := by
    simp [mainFronts]
  have eq : ((fun _ _ => True) :: (((mainKids8 fs fp W ++ (if W.rd = 1 then mainKidsDa fs fp W else [])).map
        (fun _ _ _ _ => True) ++ [fun b rd t => Loop5Q VsQ vr fs W.nc 0 b rd t]) ++
          Qrest ++ Qrest').map fun (Q : ℕ → Reader → Memory.Tree → Prop) b t => Q b rd t :
            List (ℕ → Memory.Tree → Prop)) =
      ((fun _ _ => True) :: ((mainKids8 fs fp W ++ (if W.rd = 1 then mainKidsDa fs fp W else [])).map
        (fun (_ : Kid) (_ : ℕ) (_ : Reader) (_ : Memory.Tree) => True)).map
          fun (Q : ℕ → Reader → Memory.Tree → Prop) b t => Q b rd t) ++
        (fun b t => Loop5Q VsQ vr fs W.nc 0 b rd t) ::
          (Qrest ++ Qrest').map fun (Q : ℕ → Reader → Memory.Tree → Prop) b t => Q b rd t := by
    simp
  rw [e] at hkv hks
  rw [eq] at hks
  have hlen : ((fun _ _ => True) :: ((mainKids8 fs fp W ++ (if W.rd = 1 then mainKidsDa fs fp W else [])).map
        (fun (_ : Kid) (_ : ℕ) (_ : Reader) (_ : Memory.Tree) => True)).map
          fun (Q : ℕ → Reader → Memory.Tree → Prop) b t => Q b rd t : List (ℕ → Memory.Tree → Prop)).length =
      (⟨"exponent_tables", [], [.n 65, .n 66], true⟩ :: (mainFronts8 ++
        (if decide (W.rd = 1) then mainFrontsDa else [])).map (mkCall σ) : List Call).length := by
    by_cases h : W.rd = 1 <;> simp [h, mainKids8, mainKidsDa, mainFronts8, mainFrontsDa]
  have ht : (mkCall σ mainFront5).taken = true := by
    simp only [mainFront5, mkCall, hσ, mainVal, mainRunAt]
    b1_look
    rw [one_add_gen_pow_dec (by omega)]
    simpa using hnc
  have hql : (((fun _ _ => True) :: ((mainKids8 fs fp W ++ (if W.rd = 1 then mainKidsDa fs fp W else [])).map
        (fun (_ : Kid) (_ : ℕ) (_ : Reader) (_ : Memory.Tree) => True)).map
          fun (Q : ℕ → Reader → Memory.Tree → Prop) b t => Q b rd t : List (ℕ → Memory.Tree → Prop)) ++
        (fun b t => Loop5Q VsQ vr fs W.nc 0 b rd t) ::
          (Qrest ++ Qrest').map fun (Q : ℕ → Reader → Memory.Tree → Prop) b t => Q b rd t).length =
      ((⟨"exponent_tables", [], [.n 65, .n 66], true⟩ :: (mainFronts8 ++
        (if decide (W.rd = 1) then mainFrontsDa else [])).map (mkCall σ) : List Call) ++
      mkCall σ mainFront5 :: ((if decide (W.nc = 0) then [] else [mainFrontAgg]) ++
        [mainFrontSd]).map (mkCall σ)).length := by
    by_cases h : W.rd = 1 <;> simp [h, hnc, mainKids8, mainKidsDa, mainFronts8, mainFrontsDa] <;> omega
  obtain ⟨k, b, q, hk, hb, hq, hqk⟩ := kidsSat_get hkv hql (by rw [length_bases, List.length_map]) hks
    (⟨"exponent_tables", [], [.n 65, .n 66], true⟩ :: (mainFronts8 ++
        (if decide (W.rd = 1) then mainFrontsDa else [])).map (mkCall σ) : List Call).length
    (by simp) (by simp [ht])
  rw [← hlen] at hq
  simp only [List.getElem?_append_right (le_refl _), Nat.sub_self, List.getElem?_cons_zero,
    Option.some.injEq] at hq
  subst hq
  exact ⟨W.sizes, ks', rfl, fun _ => ⟨_, k, b, hk, hb, hqk⟩⟩

set_option maxHeartbeats 1000000 in
/-- **`main`, placed** (G:3119-3316; TRIAGE #76): at `fp`, for `main`'s words within what its
callees need, one size, within its buffers, the exponent tables and `mainKidsBound`, and one
layout serve every memory holding `main`'s words, the callees' and the public input at words `0`,
`1`: `main` holds by a tree placed at `fp`, loading from its own data or its header, within
`mainWeightS` at every `w θ`. -/
theorem mainS_relAtInWT {Θ : Type} {w : Θ → String → ℕ} (Wt : ∀ θ, MainWeightHypsS S fs (w θ))
    (H : CalleesAtC Ha S fs cert κ VsGood Bd) (hF : FsRowsC S Ha) (hBs : BsRowsC S Ha) (hκ : 16 ≤ κ)
    (hW : MainWordsOkC S fs Ha κ VsGood fp W)
    (VsQ : VerifySub.VsData → VerifySub.VsRunC → ℕ → Reader → Memory.Tree → Prop)
    (HV : ∀ D R, VsGood D R → ∀ lpA sqA outA : ℕ, ∀ (c : Θ → VerifySub.VsStat),
      (∀ θ, VerifySub.VsStatOkS S (w θ) (c θ)) →
      CompleteAtWST S fs cert w κ "verify_sub" (vsExtLR lpA sqA outA D R)
        [(digestScalars D.pi).1, (digestScalars D.pi).2, (digestScalars D.seed).1,
          (digestScalars D.seed).2, ofK (gpow lpA), ofK (gpow sqA), ofK (gpow outA)] (Returns []) Bd.vs
        (fun θ => Bd.vsW (w θ) (c θ)) (VsQ D R))
    (vr : ℕ → VerifySub.VsData × VerifySub.VsRunC)
    (hvr : ∀ c < W.nc, ∃ lpA sqA outA : ℕ, VsGood (vr c).1 (vr c).2 ∧ (vr c).1.pi = (W.child c).pd ∧
      (vr c).1.seed = W.seed ∧ ofK (gpow (mainExpBase fs fp W)) = ofK (gpow lpA) ∧
      ofK (gpow (mainExpBase fs fp W + 34)) = ofK (gpow sqA) ∧
      mainPtr fs fp W 6 * gen ^ (106 * c) = ofK (gpow outA) ∧
      SubL (vsExtLR lpA sqA outA (vr c).1 (vr c).2) (mainIn fs fp W)) :
    ∃ (m : ℕ) (L : Layout), Within (mainIn fs fp W ++ L) (fp + fs "main") m ∧
      DisjL (mainIn fs fp W ++ L) ∧
      m ≤ W.sizes.sum + (fs "exponent_tables" + 68 + mainKidsBound fs Bd W) ∧
      ∀ rd, LowDef κ rd → MemL rd (mainIn fs fp W ++ L) →
        rd 1 = some (digestScalars W.stDig).1 → rd g = some (digestScalars W.stDig).2 →
        RelAtInWST S fs cert w rd (fun i => i < 2) (fun _ => False) fp (fs "main" + m)
          "main" [] [] (fun θ => mainWeightS S (w θ) Bd (Wt θ) W)
          (MainQ VsQ vr fs W.nc fp (mainVal rd (mainRunAt fs fp W)) rd) := by
  set bsDa : List ℕ := if W.rd = 1 then [Bd.daVerify W.drows, Bd.cover] else [] with hbsDa
  set bwsDa : List (Θ → ℕ) := if W.rd = 1 then [fun θ => Bd.daVerifyW (w θ) W.drows,
    fun θ => (Wt θ).Bcov] else [] with hbwsDa
  set b5 := loopSum (fs "__loop5") (fun c => childBd fs Bd (W.child c)) 0 W.nc with hb5
  set bw5 : Θ → ℕ := fun θ => loopSum (w θ "__loop5") (fun c => childWS S (w θ) Bd (Wt θ) (W.child c)) 0 W.nc
    with hbw5
  have hDa : KidsWS S fs cert w κ (if W.rd = 1 then mainKidsDa fs fp W else []) bsDa bwsDa := by
    by_cases hr : W.rd = 1
    · simp only [hbsDa, hbwsDa, hr, ↓reduceIte]
      refine ⟨fun _ => ?_, fun h => by simp at h, fun _ => ?_,
        fun h => by simp at h, trivial⟩
      · obtain ⟨wt, root, vd, ho, hrows, h⟩ := hW.daVerify hr
        rw [← hrows]
        exact (H.da_verify wt root vd ho _ _ _ h).reindex w
      · obtain ⟨i, h⟩ := hW.daCover hr
        exact CompleteAtB.toWS_weightLe (Bf := fun θ _ => (Wt θ).Bcov) (H.cover_da_root i _ _ _ h)
          fun θ => (Wt θ).cov
    · simp only [hbsDa, hbwsDa, hr, ↓reduceIte]; trivial
  have h5 : KidsWST S fs cert w κ [mainKid5 fs fp W] [b5] [bw5]
      [fun b rd t => Loop5Q VsQ vr fs W.nc 0 b rd t] := by
    refine ⟨fun htk => ?_, fun htk => ?_, trivial⟩
    · simp only [mainKid5, decide_eq_true_eq] at htk
      exact loop5C_completeAtWT H Wt hκ hW.nc (by omega) (mainIn fs fp W) W.child hW.children VsQ
        (fun D R hD lpA sqA outA c hc => HV D R hD lpA sqA outA c hc) vr hvr
    · simp only [mainKid5, decide_eq_false_iff_not, not_not] at htk
      simp only [mainKid5, hb5, htk, loopSum, le_refl]
  have hpre : KidsWST S fs cert w κ (mainKids8 fs fp W ++ (if W.rd = 1 then mainKidsDa fs fp W else []) ++
      [mainKid5 fs fp W]) (mainBs8 fs Bd W ++ bsDa ++ [b5]) (mainBws8S S Bd Wt W ++ bwsDa ++ [bw5])
      (((mainKids8 fs fp W ++ (if W.rd = 1 then mainKidsDa fs fp W else [])).map
        fun _ _ _ _ => True) ++ [fun b rd t => Loop5Q VsQ vr fs W.nc 0 b rd t]) := by
    rw [List.map_append]
    exact KidsWST.append (KidsWST.append (KidsWS.toWST (mainS_kw8 Wt H hκ hW)) (KidsWS.toWST hDa)) h5
  have hsd' : KidsWS S fs cert w κ [mainKidSd fs fp W] [Bd.sd] [fun θ => (Wt θ).Bsd] := by
    refine ⟨fun _ => ?_, fun h => by simp [mainKidSd] at h, trivial⟩
    obtain ⟨sig, cells, h⟩ := hW.stmt
    exact CompleteAtB.toWS_weightLe (Bf := fun θ _ => (Wt θ).Bsd) (H.statement_digest sig cells _ _ _ h)
      fun θ => (Wt θ).sd
  have hsd := KidsWS.toWST hsd'
  have hsum : (mainBs8 fs Bd W ++ bsDa ++ [b5]).sum + Bd.sd + (if W.nc = 0 then 0 else aggBound fs W.nc) =
      mainKidsBound fs Bd W := by
    simp only [mainKidsBound, List.sum_append, List.sum_cons, List.sum_nil, hbsDa, sum_ite_pair, hb5]
    omega
  have hwsum : ∀ θ, ((mainBws8S S Bd Wt W ++ bwsDa ++ [bw5]).map (· θ)).sum + (Wt θ).Bsd +
      (if W.nc = 0 then 0 else (Wt θ).cAgg + (Wt θ).dAgg * W.nc) + (Wt θ).Bexp + w θ "main" =
      mainWeightS S (w θ) Bd (Wt θ) W := by
    intro θ
    by_cases hr : W.rd = 1 <;>
      simp only [mainWeightS, mainBws8S, hbwsDa, hbw5, hr, ↓reduceIte, List.map_append, List.map_cons,
        List.map_nil, List.sum_append, List.sum_cons, List.sum_nil] <;> omega
  have hsubPre : ∀ k ∈ mainKids8 fs fp W ++ (if W.rd = 1 then mainKidsDa fs fp W else []) ++
      [mainKid5 fs fp W], SubL k.Lin (mainIn fs fp W) := by
    intro k hk
    refine SubL.of_mem fun q hq => ?_
    simp only [List.mem_append, List.mem_singleton] at hk
    rcases hk with (hk | hk) | rfl
    · simp only [mainKids8, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact hq
    · by_cases hr : W.rd = 1
      · simp only [hr, ↓reduceIte, mainKidsDa, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl <;> exact hq
      · simp [hr] at hk
    · exact hq
  by_cases hnc : W.nc = 0
  · refine (fun hc => ?_) (mainS_relAtIn_coreWT (cert := cert) Wt hκ hW _ _ _ _ (KidsWST.append (KidsWST.append hpre
      (show KidsWST S fs cert w κ [] [] [] [] from trivial)) hsd) (fun k hk => ?_)
      (mainS_hcm hW [] fun rd o ho => by simp only [hnc, decide_true, ↓reduceIte]; exact callsMatch_nil o ho)
      (fun rd t => MainQ VsQ vr fs W.nc fp (mainVal rd (mainRunAt fs fp W)) rd t)
      (fun rd ks' _ _ => ⟨W.sizes, ks', rfl, fun h => absurd hnc h⟩))
    · obtain ⟨m, L, h1, h2, h3, h4⟩ := hc
      refine ⟨m, L, h1, h2, ?_, fun rd hl hL hp0 hp1 => RelAtInWST.wmono (h4 rd hl hL hp0 hp1) fun θ => ?_⟩
      · rw [← hsum]
        simp only [List.sum_append, List.sum_cons, List.sum_nil, hnc, ↓reduceIte] at h3 ⊢
        omega
      · have := hwsum θ
        simp only [List.append_nil, List.map_append, List.map_cons, List.map_nil, List.sum_append,
          List.sum_cons, List.sum_nil, hnc, ↓reduceIte] at this ⊢
        omega
    · simp only [List.append_nil, List.mem_append, List.mem_singleton] at hk
      rcases hk with hk | rfl
      · exact hsubPre k (by simp only [List.mem_append, List.mem_singleton]; exact hk)
      · exact SubL.of_mem fun q hq => hq
  · obtain ⟨cs, h, d, hlen, hb, hbr, hmr, hsh, hcpi, hfr, hcar, hdT⟩ := hW.agg hnc
    have hagg' : KidsWS S fs cert w κ [mainKidAgg fs fp W cs d] [aggBound fs W.nc]
        [fun θ => (Wt θ).cAgg + (Wt θ).dAgg * W.nc] := by
      refine ⟨fun _ => ?_, fun h => by simp [mainKidAgg] at h, trivial⟩
      have := aggregateC_claims_completeAt (fs := fs) (cert := cert) hF hBs κ
        (by intro h0; rw [h0] at hlen; exact hnc hlen.symm) (by rw [hlen]; exact hW.nc) hb hbr hmr hsh
        (mainBase fs fp W 5) (mainBase fs fp W 6) (mainBase fs fp W 7) (mainBase fs fp W 9)
      rw [hlen] at this
      exact CompleteAtB.toWS this fun θ rd t rets hn hv hbo => (Wt θ).agg rd t _ rets W.nc hn hv hbo
        (by simp [mainKidAgg, gen_pow_eq_ofK]) (by omega) (by have := hW.nc; omega)
    have hagg := KidsWS.toWST hagg'
    refine (fun hc => ?_) (mainS_relAtIn_coreWT (cert := cert) Wt hκ hW _ _ _ _
      (KidsWST.append (KidsWST.append hpre hagg) hsd)
      (fun k hk => ?_)
      (mainS_hcm hW [mainKidAgg fs fp W cs d] fun rd o ho => by
        simp only [hnc, decide_false, Bool.false_eq_true, ↓reduceIte]; exact main_cmAgg rd cs d o ho)
      (fun rd t => MainQ VsQ vr fs W.nc fp (mainVal rd (mainRunAt fs fp W)) rd t)
      (fun rd ks' hkv hks => mainQ_of_sat (VsQ := VsQ) (vr := vr) hW.nc hnc _ _ rfl rd ks' hkv hks))
    · obtain ⟨m, L, h1, h2, h3, h4⟩ := hc
      refine ⟨m, L, h1, h2, ?_, fun rd hl hL hp0 hp1 => RelAtInWST.wmono (h4 rd hl hL hp0 hp1) fun θ => ?_⟩
      · rw [← hsum]
        simp only [List.sum_append, List.sum_cons, List.sum_nil, hnc, ↓reduceIte] at h3 ⊢
        omega
      · have := hwsum θ
        simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append,
          List.sum_cons, List.sum_nil, hnc, ↓reduceIte] at this ⊢
        omega
    · simp only [List.mem_append, List.mem_singleton] at hk
      rcases hk with (hk | rfl) | rfl
      · exact hsubPre k (by simp only [List.mem_append, List.mem_singleton]; exact hk)
      · refine SubL.of_mem fun q hq => ?_
        simp only [mainKidAgg, aggExtL, List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl
        · rw [← hcpi]; exact mainIn_mem 5 (by omega)
        · rw [← hfr]; exact mainIn_mem 6 (by omega)
        · rw [← hcar]; exact mainIn_mem 7 (by omega)
        · rw [← hdT]; exact mainIn_mem 9 (by omega)
      · exact SubL.of_mem fun q hq => hq

end
end LeanVM.Guest.B1.Main
