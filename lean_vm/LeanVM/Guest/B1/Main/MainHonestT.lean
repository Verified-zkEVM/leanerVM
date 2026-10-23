/-
  LeanVM.Guest.B1.Main.MainHonestT

  `main` placed on a node's honest run, its children's loop by a tree satisfying a predicate
  `T5`: `main`'s node then has a `__loop5` child satisfying `T5`.
-/

module

public import LeanVM.Guest.B1.Main.MainHonestEnd

/-!
# `main` on an honest run, the children's loop's tree exposed

`mTs m T5`: the predicates on `main`'s callees' trees, `T5` on `__loop5`'s, none on the others'.
`mainKidsDT`: `MainGoals` and the children's loop complete by trees satisfying `T5` give
`KidsDT`. `main_honest_relAtInT`: `main_honest_end` with `main`'s node's children satisfying
`KidsT (mCalls σ m) (_ :: mTs m T5)`.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest.B1 (LowDef DisjL Within Kid CompleteAtD CompleteAtDT KidsDT Returns)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ}

theorem kidsDT_append {κ : ℕ} {ks2 : List Kid} {Ts2 : List (Tree → Prop)} :
    ∀ (ks1 : List Kid) (Ts1 : List (Tree → Prop)), ks1.length = Ts1.length →
      KidsDT fs cert κ ks1 Ts1 → KidsDT fs cert κ ks2 Ts2 → KidsDT fs cert κ (ks1 ++ ks2) (Ts1 ++ Ts2)
  | [], [], _, _, h2 => h2
  | k :: ks1, T :: Ts1, hl, h1, h2 =>
    ⟨h1.1, kidsDT_append ks1 Ts1 (by simpa using hl) h1.2 h2⟩
  | [], _ :: _, hl, _, _ => by simp at hl
  | _ :: _, [], hl, _, _ => by simp at hl

theorem kidsDT_rep {κ : ℕ} : ∀ (ks : List Kid),
    (∀ k ∈ ks, k.taken = true → CompleteAtD fs cert κ k.f k.Lin k.args k.Out) →
      KidsDT fs cert κ ks (List.replicate ks.length fun _ => True)
  | [], _ => trivial
  | k :: ks, h => ⟨fun ht => (h k (by simp) ht).toT, kidsDT_rep ks fun k' hk' => h k' (by simp [hk'])⟩

/-- **The predicates on `main`'s callees' trees**: `T5` on the children's loop's. -/
def mTs (m : MainIn) (T5 : Tree → Prop) : List (Tree → Prop) :=
  List.replicate 8 (fun _ => True) ++ List.replicate (if m.nd = 1 then 2 else 0) (fun _ => True) ++
    [T5] ++ List.replicate (if m.nc = 0 then 0 else 1) (fun _ => True) ++ [fun _ => True]

variable {fp : ℕ} {seed : Digest} {s : NodeStatement} {w : NodeWitness} {bytecode : List K}

/-- The children's loop complete by trees satisfying `T5`. -/
def MainGoalL5T (fs : String → ℕ) (cert : String → V → ℕ) (fp : ℕ) (seed : Digest)
    (s : NodeStatement) (w : NodeWitness) (T5 : Tree → Prop) : Prop :=
  (hm fs fp seed s w).nc ≠ 0 →
    CompleteAtDT fs cert 16 "__loop5" (hLmain fs fp seed s w)
      [1, gen ^ (hm fs fp seed s w).nc, (hm fs fp seed s w).a409, (hm fs fp seed s w).a77,
        (hm fs fp seed s w).a117, gen ^ ((hm fs fp seed s w).nlx + (hm fs fp seed s w).nxd),
        (hm fs fp seed s w).a80, gen ^ ((hm fs fp seed s w).nls + (hm fs fp seed s w).nsd),
        (hm fs fp seed s w).a406, (hm fs fp seed s w).a69,
        (hm fs fp seed s w).a117 * gen ^ ((hm fs fp seed s w).nlx + (hm fs fp seed s w).nxd +
          ((hm fs fp seed s w).nls + (hm fs fp seed s w).nsd)),
        gen ^ ((hm fs fp seed s w).nda + (hm fs fp seed s w).ndd),
        (digestScalars (hm fs fp seed s w).seed).1, (digestScalars (hm fs fp seed s w).seed).2,
        (hm fs fp seed s w).a394, (hm fs fp seed s w).et1, (hm fs fp seed s w).et2,
        (hm fs fp seed s w).a400] (Returns []) T5

theorem MainGoalL5T.goal {T5 : Tree → Prop} (h : MainGoalL5T fs cert fp seed s w T5) :
    MainGoalL5 fs cert fp seed s w := fun hn => (h hn).toD

/-- **`main`'s callees, the children's loop by trees satisfying `T5`.** -/
theorem mainKidsDT {T5 : Tree → Prop} (hg : MainGoals fs cert fp seed s w)
    (h5 : MainGoalL5T fs cert fp seed s w T5) :
    KidsDT fs cert 16 (mKids (hm fs fp seed s w) (hLmain fs fp seed s w))
      (mTs (hm fs fp seed s w) T5) := by
  have hall := mainKids_ok hg
  unfold mTs
  dsimp only [mKids]
  refine kidsDT_append _ _ ?_ (kidsDT_append _ _ ?_ (kidsDT_append _ _ ?_
    (kidsDT_append _ _ ?_ ?_ ?_) ?_) ?_) ?_
  · split_ifs <;> simp
  · split_ifs <;> simp
  · split_ifs <;> simp
  · rfl
  · exact kidsDT_rep _ fun k hk => hall k (by
      dsimp only [mKids]
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_left _ hk))))
  · split
    · next h =>
      exact kidsDT_rep _ fun k hk => hall k (by
        dsimp only [mKids]
        simp only [h, ↓reduceIte]
        exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
          (List.mem_append_right _ hk))))
    · trivial
  · exact ⟨fun ht => h5 (of_decide_eq_true ht), trivial⟩
  · split
    · trivial
    · next h =>
      exact kidsDT_rep _ fun k hk => hall k (by
        dsimp only [mKids]
        simp only [h, ↓reduceIte]
        exact List.mem_append_left _ (List.mem_append_right _ hk))
  · exact kidsDT_rep _ fun k hk => hall k (by
      dsimp only [mKids]
      exact List.mem_append_right _ hk)

/-- **`main` at `fp` on the honest run, its children's loop's tree satisfying `T5`.** -/
theorem main_honest_relAtInT {T5 : Tree → Prop} (hbl : bytecode.length = 2 ^ 23)
    (hr : NodeRel bytecode seed s w) (hl : Limits bytecode s w)
    (hxc : Sig.verify_lean_xmss_complete_Spec)
    (hsc : Sig.verify_sig_lean_sphincs_complete_loads_Spec) (hrf : Lift.RunsFit fs cert)
    (hl5 : MainGoalL5T fs cert fp seed s w T5) (hag : MainGoalAg fs cert fp seed s w) :
    ∃ (n : ℕ) (L : B1.Main.Layout), Within L fp n ∧ (∀ q ∈ L, fp + fs "main" ≤ q.1) ∧ DisjL L ∧
      (∀ q ∈ hLmain fs fp seed s w, q ∈ L) ∧
      ∀ rd, LowDef 16 rd → B1.Main.MemL rd L →
        LoadHolds rd 1 0 (digestScalars (statementDigest seed s)).1 →
        LoadHolds rd gen 0 (digestScalars (statementDigest seed s)).2 →
        RelAtInT coreProgram fs cert rd (fun i => i < 2) (fun _ => False) fp n "main" [] []
          (fun t => ∃ σ bufs ks, t = .node "main" σ bufs ks ∧ MVals rd σ (hm fs fp seed s w) ∧
            KidsT (mCalls σ (hm fs fp seed s w)) ((fun _ => True) :: mTs (hm fs fp seed s w) T5) ks ∧
            calls (mEvs σ) = mCalls σ (hm fs fp seed s w) ∧ bufs = mSizes (hData seed s w)) :=
  main_relAtInT fs cert fp (hData seed s w) (hOwn seed s w) (hOwn_fit (log2_of_length hbl) hr (freshShaped_of hbl hr))
    (hData_bounds hl fs fp) hData_daR _
    (mainKidsDT (mainGoals_of hbl hr hl hxc hsc hrf hl5.goal hag) hl5)
    (fun rd hM h0 h1 => hMainMem (log2_of_length hbl) hr (freshShaped_of hbl hr) hl fs fp rd hM h0 h1)

end
end LeanVM.Guest.B1.Main
