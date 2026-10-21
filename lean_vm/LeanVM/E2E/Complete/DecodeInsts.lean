/-
  LeanVM.E2E.Complete.DecodeInsts

  The children's `__loop5` iterations and `verify_sub` calls as instances of the honest memory,
  from `main`'s tree form.
-/

module

public import LeanVM.Guest.EndCompleteCT
public import LeanVM.Guest.B1.Main.MainAt

/-!
# The children's instances

The honest memory is laid out from the re-chosen tree `T0.retemp coreProgram fs ν 0` of a tree
`T0` satisfying `main`'s tree form (`MainQ`, `honest_of_mainCT`). Its instances
(`Memory.Tree.insts`, `honestInsts`) are the re-chosen subtrees at their callee frames:

* `retemp_kid_inst`: the `i`-th callee `k` of an instance that is a re-chosen node, at the `i`-th
  callee frame `p` (`kidPos`), is an instance: `k.retemp … p` at `p`;
* `kidPos_loop_append`, `kidPos_plain`: the callee frames of a loop helper (its tail call last, at
  `fp + fs f`) and of a plain function;
* `loop5Q_insts`: along `Loop5Q`, each iteration `c` is an instance, the re-chosen node at the
  frame the tree form names, with `Loop5H` (the iteration's facts but its tail) at child `j + c`,
  an invariant `Inv` carried from each iteration to the next;
* `loop5H_vs_inst`: the iteration's `verify_sub` callee, placed where `Loop5H` says, is an
  instance, the `5`-th callee of the iteration's;
* `mainQ_loop5_inst`: `main`'s first `__loop5` iteration is an instance, a callee of the root.
-/

namespace LeanVM.E2E.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Loop5Q MainQ)

@[expose] public section

variable {fs : String → ℕ} {ν : ℕ → String → Val → V → E} {H : Inst → ℕ → E × E}

/-! ## Callees of re-chosen nodes -/

theorem getElem?_retempKids {P : Core.Program} :
    ∀ (ks : List Memory.Tree) (ps : List ℕ) {i : ℕ} {k : Memory.Tree} {p : ℕ}, ks[i]? = some k → ps[i]? = some p →
      (Memory.Tree.retempKids P fs ν ps ks)[i]? = some (k.retemp P fs ν p)
  | [], _, _, _, _, hk, _ => by simp at hk
  | _ :: _, [], _, _, _, _, hp => by simp at hp
  | k' :: ks, p' :: ps, 0, k, p, hk, hp => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hk hp
      subst hk hp
      rw [retempKids_cons]; rfl
  | k' :: ks, p' :: ps, i + 1, k, p, hk, hp => by
      simp only [List.getElem?_cons_succ] at hk hp
      rw [retempKids_cons, List.getElem?_cons_succ]
      exact getElem?_retempKids ks ps hk hp

/-- **The callee of a re-chosen node instance is an instance**: the re-chosen callee at its
callee frame. -/
theorem retemp_kid_inst {P : Core.Program} {T : Memory.Tree} {fp0 : ℕ} {hdr : E × E} {I : Inst}
    (hI : I ∈ T.insts fs P.loop H fp0 hdr) {f : String} {σ : Val} {bufs : List ℕ}
    {ks : List Memory.Tree} (hIt : I.t = (Memory.Tree.node f σ bufs ks).retemp P fs ν I.fp) {i : ℕ} {k : Memory.Tree}
    (hk : ks[i]? = some k) {p : ℕ}
    (hp : (kidPos fs P.loop I.fp f bufs (ks.map (Memory.Tree.total fs)))[i]? = some p) :
    ∃ J ∈ T.insts fs P.loop H fp0 hdr, J.t = k.retemp P fs ν p ∧ J.fp = p ∧
      I.t.kids[i]? = some J.t ∧ I.kidFps[i]? = some J.fp := by
  have hkids : I.t.kids[i]? = some (k.retemp P fs ν p) := by
    rw [hIt, retemp_node]
    exact getElem?_retempKids ks _ hk hp
  obtain ⟨J, hJ, hJt, hJfp, -⟩ := insts_kid T fp0 hdr I hI i _ hkids
  have hpl := (insts_placed T fp0 hdr I hI).1
  have hfps : I.kidFps = kidPos fs P.loop I.fp f bufs (ks.map (Memory.Tree.total fs)) := by
    rw [hpl, hIt, retemp_node]
    simp only [Memory.Tree.name, Memory.Tree.bufs, Memory.Tree.kids]
    rw [map_total_retempKids_kidPos]
  have hJp : J.fp = p := by
    rw [hfps, hp] at hJfp
    exact (Option.some.inj hJfp).symm
  exact ⟨J, hJ, hJt, hJp, by rw [hJt]; exact hkids, by rw [hJfp, hJp]⟩

/-- The callee frames of a loop helper whose tail call is last. -/
theorem kidPos_loop_append {lp : String → Bool} {fp : ℕ} {f : String} (hl : lp f = true)
    (bufs : List ℕ) (ns : List ℕ) (m : ℕ) :
    kidPos fs lp fp f bufs (ns ++ [m]) = bases (fp + fs f + m + bufs.sum) ns ++ [fp + fs f] := by
  simp [kidPos, bufBase, hl]

/-- The callee frames of a plain function. -/
theorem kidPos_plain {lp : String → Bool} {fp : ℕ} {f : String} (hl : lp f = false)
    (bufs : List ℕ) (ns : List ℕ) :
    kidPos fs lp fp f bufs ns = bases (fp + fs f + bufs.sum) ns := by
  simp [kidPos, bufBase, hl]

/-! ## `main`'s iterations -/

variable {VsQ : B1.VerifySub.VsData → B1.VerifySub.VsRunC → ℕ → Reader → Memory.Tree → Prop}
  {vr : ℕ → B1.VerifySub.VsData × B1.VerifySub.VsRunC}
  {CQ : List E → List E → ℕ → Reader → Memory.Tree → Prop}
  {SQ : List E → List E → ℕ → Reader → Memory.Tree → Prop}
  {LQ : List E → ℕ → Reader → Memory.Tree → Prop} {IQ : ℕ → Reader → Val → Prop}

/-- **An iteration's facts but its tail** (`Loop5Q` at `n + 1`): the iteration's valuation at
child `j`, its child-claim digests' trees, its `verify_sub` callee's tree. -/
def Loop5H (VsQ : B1.VerifySub.VsData → B1.VerifySub.VsRunC → ℕ → Reader → Memory.Tree → Prop)
    (vr : ℕ → B1.VerifySub.VsData × B1.VerifySub.VsRunC)
    (CQ : List E → List E → ℕ → Reader → Memory.Tree → Prop)
    (SQ : List E → List E → ℕ → Reader → Memory.Tree → Prop)
    (LQ : List E → ℕ → Reader → Memory.Tree → Prop) (IQ : ℕ → Reader → Val → Prop)
    (fs : String → ℕ) (j fp : ℕ) (rd : Reader) (σ : Val) (bufs : List ℕ) (ks : List Memory.Tree)
    (k : Memory.Tree) : Prop :=
  IQ j rd σ ∧
    (∃ (kc : Memory.Tree) (b : ℕ), ks[0]? = some kc ∧
      (bases (fp + fs "__loop5" + k.total fs + bufs.sum) (ks.map (Memory.Tree.total fs)))[0]? = some b ∧
      CQ ([.n 3, .n 4, .n 19, .n 31, .n 5, .n 20, .n 6].map σ) ([.n 32, .n 33].map σ) b rd kc) ∧
    (∃ (kc : Memory.Tree) (b : ℕ), ks[1]? = some kc ∧
      (bases (fp + fs "__loop5" + k.total fs + bufs.sum) (ks.map (Memory.Tree.total fs)))[1]? = some b ∧
      CQ ([.n 7, .n 4, .n 34, .n 5, .n 8, .n 21, .n 6].map σ) ([.n 35, .n 36].map σ) b rd kc) ∧
    (σ (.n 61) ≠ 0 → ∃ (kl : Memory.Tree) (b : ℕ), ks[2]? = some kl ∧
      (bases (fp + fs "__loop5" + k.total fs + bufs.sum) (ks.map (Memory.Tree.total fs)))[2]? = some b ∧
      LQ ([.n 62, .n 52, .n 59, .n 10, .n 11, .n 12, .n 19, .n 30].map σ) b rd kl) ∧
    (∃ (kd : Memory.Tree) (b : ℕ), ks[4]? = some kd ∧
      (bases (fp + fs "__loop5" + k.total fs + bufs.sum) (ks.map (Memory.Tree.total fs)))[4]? = some b ∧
      SQ ([.n 13, .n 14, .n 42, .n 63, .n 64, .n 51].map σ) ([.n 65, .n 66].map σ) b rd kd) ∧
    (∃ (kv : Memory.Tree) (b : ℕ), ks[5]? = some kv ∧
      (bases (fp + fs "__loop5" + k.total fs + bufs.sum) (ks.map (Memory.Tree.total fs)))[5]? = some b ∧
      VsQ (vr j).1 (vr j).2 b rd kv)

/-- **`Loop5Q`'s iterations are instances**: along `Loop5Q` from an instance of the re-chosen
iteration tree, iteration `c` is an instance of the re-chosen node, with `Loop5H` at child
`j + c`, and every invariant carried from an iteration to its tail call holds there. -/
theorem loop5Q_insts {T : Memory.Tree} {fp0 : ℕ} {hdr : E × E} {rd : Reader} (Inv : Inst → Prop)
    (hInv : ∀ I ∈ T.insts fs coreProgram.loop H fp0 hdr, ∀ J ∈ T.insts fs coreProgram.loop H fp0 hdr,
      Inv I → ∀ (σ : Val) (bufs : List ℕ) (ks : List Memory.Tree) (k : Memory.Tree),
      I.t = (Memory.Tree.node "__loop5" σ bufs (ks ++ [k])).retemp coreProgram fs ν I.fp →
      J.t = k.retemp coreProgram fs ν (I.fp + fs "__loop5") → J.fp = I.fp + fs "__loop5" →
      I.t.kids[ks.length]? = some J.t → I.kidFps[ks.length]? = some J.fp → Inv J) :
    ∀ (n j fp : ℕ) (t : Memory.Tree), Loop5Q VsQ vr CQ SQ LQ IQ fs n j fp rd t →
      ∀ I ∈ T.insts fs coreProgram.loop H fp0 hdr, I.t = t.retemp coreProgram fs ν fp → I.fp = fp →
      Inv I → ∀ c < n, ∃ I' ∈ T.insts fs coreProgram.loop H fp0 hdr, Inv I' ∧
        ∃ (σ : Val) (bufs : List ℕ) (ks : List Memory.Tree) (k : Memory.Tree),
          I'.t = (Memory.Tree.node "__loop5" σ bufs (ks ++ [k])).retemp coreProgram fs ν I'.fp ∧
          Loop5H VsQ vr CQ SQ LQ IQ fs (j + c) I'.fp rd σ bufs ks k
  | 0, _, _, _, _, _, _, _, _, _, c, hc => absurd hc (Nat.not_lt_zero c)
  | n + 1, j, fp, t, hQ, I, hI, hIt, hIfp, hInvI, c, hc => by
      obtain ⟨σ, bufs, ks, k, rfl, hIQ, h0, h1, h2, h4, hv, hrest⟩ := hQ
      have hIt' : I.t = (Memory.Tree.node "__loop5" σ bufs (ks ++ [k])).retemp coreProgram fs ν I.fp := by
        rw [hIt, hIfp]
      rcases c with _ | c
      · refine ⟨I, hI, hInvI, σ, bufs, ks, k, hIt', ?_⟩
        rw [hIfp]
        exact ⟨hIQ, h0, h1, h2, h4, hv⟩
      · -- the tail call
        have hpos : (kidPos fs coreProgram.loop I.fp "__loop5" bufs
            ((ks ++ [k]).map (Memory.Tree.total fs)))[ks.length]? = some (fp + fs "__loop5") := by
          rw [List.map_append, List.map_singleton,
            kidPos_loop_append B1.Main.loop5_isLoop, hIfp]
          simp [length_bases]
        obtain ⟨J, hJ, hJt, hJfp, hJk, hJf⟩ := retemp_kid_inst hI hIt'
          (by simp : (ks ++ [k])[ks.length]? = some k) hpos
        have hInvJ := hInv I hI J hJ hInvI σ bufs ks k hIt' (by rw [hJt, hIfp])
          (by rw [hJfp, hIfp]) hJk hJf
        obtain ⟨I', hI', hInv', rest⟩ := loop5Q_insts Inv hInv n (j + 1) (fp + fs "__loop5") k hrest J hJ
          hJt hJfp hInvJ c (by omega)
        refine ⟨I', hI', hInv', ?_⟩
        rw [show j + (c + 1) = j + 1 + c by omega]
        exact rest

/-- **The iteration's `verify_sub` callee is an instance**, its `5`-th callee, at the frame
`Loop5H` names, satisfying `VsQ` at child `j`'s run. -/
theorem loop5H_vs_inst {T : Memory.Tree} {fp0 : ℕ} {hdr : E × E} {rd : Reader} {I : Inst}
    (hI : I ∈ T.insts fs coreProgram.loop H fp0 hdr) {σ : Val} {bufs : List ℕ} {ks : List Memory.Tree}
    {k : Memory.Tree} (hIt : I.t = (Memory.Tree.node "__loop5" σ bufs (ks ++ [k])).retemp coreProgram fs ν I.fp)
    {j : ℕ} (hH : Loop5H VsQ vr CQ SQ LQ IQ fs j I.fp rd σ bufs ks k) :
    ∃ (kv : Memory.Tree) (W : Inst), W ∈ T.insts fs coreProgram.loop H fp0 hdr ∧
      W.t = kv.retemp coreProgram fs ν W.fp ∧ I.t.kids[5]? = some W.t ∧ I.kidFps[5]? = some W.fp ∧
      VsQ (vr j).1 (vr j).2 W.fp rd kv := by
  obtain ⟨-, -, -, -, -, kv, b, hkv, hb, hq⟩ := hH
  have h5 : 5 < ks.length := (List.getElem?_eq_some_iff.mp hkv).1
  have hpos : (kidPos fs coreProgram.loop I.fp "__loop5" bufs
      ((ks ++ [k]).map (Memory.Tree.total fs)))[5]? = some b := by
    rw [List.map_append, List.map_singleton, kidPos_loop_append B1.Main.loop5_isLoop,
      List.getElem?_append_left (by rw [length_bases, List.length_map]; exact h5)]
    exact hb
  obtain ⟨W, hW, hWt, hWfp, hWk, hWf⟩ := retemp_kid_inst hI hIt
    (by rw [List.getElem?_append_left h5]; exact hkv) hpos
  exact ⟨kv, W, hW, by rw [hWt, hWfp], hWk, hWf, by rw [hWfp]; exact hq⟩

/-- **`main`'s first iteration is an instance**, a callee of the root instance, where `MainQ`
places it. -/
theorem mainQ_loop5_inst {T : Memory.Tree} {hdr : E × E} {rd : Reader} {nc : ℕ} {σ : Val} {R : Inst}
    (hR : R ∈ T.insts fs coreProgram.loop H 0 hdr) {T0 : Memory.Tree}
    (hRt : R.t = T0.retemp coreProgram fs ν 0) (hRfp : R.fp = 0)
    (hQ : MainQ VsQ vr CQ SQ LQ IQ fs nc 0 σ rd T0) (hnc : nc ≠ 0) :
    ∃ (b : ℕ) (k : Memory.Tree) (J : Inst) (i : ℕ), J ∈ T.insts fs coreProgram.loop H 0 hdr ∧
      J.t = k.retemp coreProgram fs ν b ∧ J.fp = b ∧ R.t.kids[i]? = some J.t ∧
      R.kidFps[i]? = some J.fp ∧ Loop5Q VsQ vr CQ SQ LQ IQ fs nc 0 b rd k := by
  obtain ⟨bufs, ks, rfl, hk⟩ := hQ
  obtain ⟨i, k, b, hki, hb, hL⟩ := hk hnc
  have hpos : (kidPos fs coreProgram.loop R.fp "main" bufs (ks.map (Memory.Tree.total fs)))[i]? = some b := by
    rw [kidPos_plain B1.Main.main_not_loop, hRfp]
    exact hb
  obtain ⟨J, hJ, hJt, hJfp, hJk, hJf⟩ := retemp_kid_inst hR (by rw [hRt, hRfp]) hki hpos
  exact ⟨b, k, J, i, hJ, hJt, hJfp, hJk, hJf, hL⟩

end
end LeanVM.E2E.Complete
