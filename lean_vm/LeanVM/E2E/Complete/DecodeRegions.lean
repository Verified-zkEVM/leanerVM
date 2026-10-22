/-
  LeanVM.E2E.Complete.DecodeRegions

  The children's `verify_sub` trees occupy disjoint regions of the honest memory.
-/

module

public import LeanVM.E2E.Complete.DecodeStmtTree

/-!
# The children's regions

`__loop5`'s iteration `c` is the `c`-th tail of its tree (`tailN`), at `fp + c·f5`; its
`verify_sub` callee lies after its tail's region (`loop5H_vs_region`), and each tail's region
lies within the iteration's (`tailN_total`). Hence the children's `verify_sub` callees occupy
disjoint regions (`loop5Q_vs_disjoint`).
-/

namespace LeanVM.E2E.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Loop5Q)

@[expose] public section

/-- The `c`-th tail of a loop's tree: its last callee, `c` times. -/
def tailN (c : ℕ) (t : Memory.Tree) : Memory.Tree := (fun u => u.kids.getLastD u)^[c] t

theorem tailN_succ (c : ℕ) (t : Memory.Tree) :
    tailN (c + 1) t = (tailN c t).kids.getLastD (tailN c t) :=
  Function.iterate_succ_apply' _ c t

theorem tailN_succ' (c : ℕ) (t : Memory.Tree) : tailN (c + 1) t = tailN c (t.kids.getLastD t) :=
  Function.iterate_succ_apply _ c t

variable {VsQ : B1.VerifySub.VsData → B1.VerifySub.VsRunC → ℕ → Reader → Memory.Tree → Prop}
  {vr : ℕ → B1.VerifySub.VsData × B1.VerifySub.VsRunC}
  {CQ SQ : List E → List E → ℕ → Reader → Memory.Tree → Prop}
  {LQ : List E → ℕ → Reader → Memory.Tree → Prop} {IQ : ℕ → Reader → Val → Prop}
  {fs : String → ℕ} {rd : Reader}

/-- **`Loop5Q`'s iteration `c` is its tree's `c`-th tail**, at `fp + c·f5`. -/
theorem loop5Q_iter : ∀ (n j fp : ℕ) (t : Memory.Tree), Loop5Q VsQ vr CQ SQ LQ IQ fs n j fp rd t →
    ∀ c < n, ∃ (σ : Val) (bufs : List ℕ) (ks : List Memory.Tree) (k : Memory.Tree),
      tailN c t = .node "__loop5" σ bufs (ks ++ [k]) ∧ tailN (c + 1) t = k ∧
      Loop5H VsQ vr CQ SQ LQ IQ fs (j + c) (fp + c * fs "__loop5") rd σ bufs ks k
  | 0, _, _, _, _, c, hc => absurd hc (Nat.not_lt_zero c)
  | n + 1, j, fp, t, hQ, c, hc => by
      obtain ⟨σ, bufs, ks, k, rfl, hIQ, h0, h1, h2, h4, hv, hrest⟩ := hQ
      have hk : (Memory.Tree.node "__loop5" σ bufs (ks ++ [k])).kids.getLastD
          (Memory.Tree.node "__loop5" σ bufs (ks ++ [k])) = k := by
        simp [Memory.Tree.kids]
      rcases c with _ | c
      · refine ⟨σ, bufs, ks, k, rfl, by rw [tailN_succ']; rw [hk]; rfl, ?_⟩
        rw [Nat.add_zero, Nat.zero_mul, Nat.add_zero]
        exact ⟨hIQ, h0, h1, h2, h4, hv⟩
      · obtain ⟨σ', bufs', ks', k', h1', h2', h3'⟩ :=
          loop5Q_iter n (j + 1) (fp + fs "__loop5") k hrest c (by omega)
        refine ⟨σ', bufs', ks', k', ?_, ?_, ?_⟩
        · rw [tailN_succ', hk]; exact h1'
        · rw [tailN_succ', hk]; exact h2'
        · rw [show j + (c + 1) = j + 1 + c by omega,
            show fp + (c + 1) * fs "__loop5" = fp + fs "__loop5" + c * fs "__loop5" by ring]
          exact h3'

/-- A loop iteration's tail lies within it, after its frame. -/
theorem total_tail {σ : Val} {bufs : List ℕ} {ks : List Memory.Tree} {k : Memory.Tree} :
    k.total fs + fs "__loop5" ≤ (Memory.Tree.node "__loop5" σ bufs (ks ++ [k])).total fs := by
  rw [total_node, totalKids_eq_sum]
  simp
  omega

/-- **An iteration's `verify_sub` callee lies after its tail's region**, within the iteration's. -/
theorem loop5H_vs_region {j fp : ℕ} {σ : Val} {bufs : List ℕ} {ks : List Memory.Tree}
    {k : Memory.Tree} (hH : Loop5H VsQ vr CQ SQ LQ IQ fs j fp rd σ bufs ks k) :
    ∃ (kv : Memory.Tree) (b : ℕ), ks[5]? = some kv ∧
      (bases (fp + fs "__loop5" + k.total fs + bufs.sum) (ks.map (Memory.Tree.total fs)))[5]? = some b ∧
      VsQ (vr j).1 (vr j).2 b rd kv ∧ fp + fs "__loop5" + k.total fs ≤ b ∧
      b + kv.total fs ≤ fp + (Memory.Tree.node "__loop5" σ bufs (ks ++ [k])).total fs := by
  obtain ⟨-, -, -, -, -, kv, b, hkv, hb, hq⟩ := hH
  have h5 : 5 < ks.length := (List.getElem?_eq_some_iff.mp hkv).1
  refine ⟨kv, b, hkv, hb, hq, ?_, ?_⟩
  · rw [getElem?_bases (by simpa using h5), Option.some.injEq] at hb
    omega
  · rw [getElem?_bases (by simpa using h5), Option.some.injEq] at hb
    rw [total_node, totalKids_eq_sum]
    have hs : ((ks.map (Memory.Tree.total fs)).take 5).sum + kv.total fs ≤
        (ks.map (Memory.Tree.total fs)).sum := by
      have e := List.sum_take_add_sum_drop (ks.map (Memory.Tree.total fs)) 5
      have hd : kv.total fs ≤ ((ks.map (Memory.Tree.total fs)).drop 5).sum := by
        have : ((ks.map (Memory.Tree.total fs)).drop 5)[0]? = some (kv.total fs) := by
          simp [List.getElem?_drop, hkv]
        obtain ⟨l, hl⟩ : ∃ l, (ks.map (Memory.Tree.total fs)).drop 5 = kv.total fs :: l := by
          rcases h : (ks.map (Memory.Tree.total fs)).drop 5 with _ | ⟨x, l⟩
          · rw [h] at this; simp at this
          · rw [h] at this; simp at this; exact ⟨l, by rw [this]⟩
        rw [hl]; simp
      omega
    simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
      List.sum_nil] at *
    omega

/-- The bounds of a `verify_sub` callee's region in an iteration from `p = fp + f5`. -/
theorem vs_bounds {p : ℕ} {bufs : List ℕ} {ks : List Memory.Tree} {k kv : Memory.Tree} {b : ℕ}
    (hkv : ks[5]? = some kv)
    (hb : (bases (p + k.total fs + bufs.sum) (ks.map (Memory.Tree.total fs)))[5]? = some b) :
    p + k.total fs ≤ b ∧ b + kv.total fs ≤ p + k.total fs + bufs.sum + (ks.map (Memory.Tree.total fs)).sum := by
  have h5 : 5 < ks.length := (List.getElem?_eq_some_iff.mp hkv).1
  rw [getElem?_bases (by simpa using h5), Option.some.injEq] at hb
  refine ⟨by omega, ?_⟩
  have e := List.sum_take_add_sum_drop (ks.map (Memory.Tree.total fs)) 5
  obtain ⟨l, hl⟩ : ∃ l, (ks.map (Memory.Tree.total fs)).drop 5 = kv.total fs :: l := by
    have : ((ks.map (Memory.Tree.total fs)).drop 5)[0]? = some (kv.total fs) := by
      simp [List.getElem?_drop, hkv]
    rcases h : (ks.map (Memory.Tree.total fs)).drop 5 with _ | ⟨x, l⟩
    · rw [h] at this; simp at this
    · rw [h] at this; simp at this; exact ⟨l, by rw [this]⟩
  rw [hl, List.sum_cons] at e
  omega

/-- **The children's `verify_sub` callees occupy disjoint regions**: iteration `c`'s and
iteration `c'`'s, `c < c'`, the later one before the earlier. -/
theorem loop5Q_vs_disjoint {n j fp : ℕ} {t : Memory.Tree}
    (hQ : Loop5Q VsQ vr CQ SQ LQ IQ fs n j fp rd t) {c c' : ℕ} (hcc : c < c') (hc' : c' < n)
    {σ : Val} {bufs : List ℕ} {ks : List Memory.Tree} {k : Memory.Tree}
    (ht : tailN c t = .node "__loop5" σ bufs (ks ++ [k]))
    {σ' : Val} {bufs' : List ℕ} {ks' : List Memory.Tree} {k' : Memory.Tree}
    (ht' : tailN c' t = .node "__loop5" σ' bufs' (ks' ++ [k']))
    {kv kv' : Memory.Tree} {b b' : ℕ} (hkv : ks[5]? = some kv)
    (hb : (bases (fp + c * fs "__loop5" + fs "__loop5" + k.total fs + bufs.sum)
      (ks.map (Memory.Tree.total fs)))[5]? = some b)
    (hkv' : ks'[5]? = some kv')
    (hb' : (bases (fp + c' * fs "__loop5" + fs "__loop5" + k'.total fs + bufs'.sum)
      (ks'.map (Memory.Tree.total fs)))[5]? = some b') :
    b' + kv'.total fs ≤ b := by
  -- the iterations' regions shrink
  have hmono : ∀ d, c + 1 + d ≤ c' → fp + (c + 1 + d) * fs "__loop5" + (tailN (c + 1 + d) t).total fs ≤
      fp + (c + 1) * fs "__loop5" + (tailN (c + 1) t).total fs := by
    intro d
    induction d with
    | zero => intro _; simp
    | succ d ih =>
      intro hd
      have := ih (by omega)
      obtain ⟨σm, bufsm, ksm, km, hm1, hm2, -⟩ := loop5Q_iter n j fp t hQ (c + 1 + d) (by omega)
      have ht2 := total_tail (fs := fs) (σ := σm) (bufs := bufsm) (ks := ksm) (k := km)
      rw [← hm1, ← hm2] at ht2
      rw [show c + 1 + (d + 1) = c + 1 + d + 1 by omega]
      have : (c + 1 + d + 1) * fs "__loop5" = (c + 1 + d) * fs "__loop5" + fs "__loop5" := by ring
      omega
  have hm := hmono (c' - (c + 1)) (by omega)
  rw [show c + 1 + (c' - (c + 1)) = c' by omega] at hm
  have hk : tailN (c + 1) t = k := by rw [tailN_succ, ht]; simp [Memory.Tree.kids]
  rw [hk] at hm
  obtain ⟨hb1, -⟩ := vs_bounds hkv hb
  obtain ⟨-, hb2⟩ := vs_bounds hkv' hb'
  have htot : (tailN c' t).total fs = fs "__loop5" + (ks'.map (Memory.Tree.total fs)).sum + k'.total fs +
      bufs'.sum := by
    rw [ht', total_node, totalKids_eq_sum]; simp; omega
  have : (c + 1) * fs "__loop5" = c * fs "__loop5" + fs "__loop5" := by ring
  omega


/-- **`Loop5Q`'s iterations are instances at their positions** (`loop5Q_insts`): iteration `c` is
the re-chosen `c`-th tail, at `fp + c·f5`. -/
theorem loop5Q_insts_pos {ν : ℕ → String → Val → V → E} {H : Inst → ℕ → E × E} {T : Memory.Tree}
    {fp0 : ℕ} {hdr : E × E} (Inv : Inst → Prop)
    (hInv : ∀ I ∈ T.insts fs coreProgram.loop H fp0 hdr, ∀ J ∈ T.insts fs coreProgram.loop H fp0 hdr,
      Inv I → ∀ (σ : Val) (bufs : List ℕ) (ks : List Memory.Tree) (k : Memory.Tree),
      I.t = (Memory.Tree.node "__loop5" σ bufs (ks ++ [k])).retemp coreProgram fs ν I.fp →
      J.t = k.retemp coreProgram fs ν (I.fp + fs "__loop5") → J.fp = I.fp + fs "__loop5" →
      I.t.kids[ks.length]? = some J.t → I.kidFps[ks.length]? = some J.fp → Inv J) :
    ∀ (n j fp : ℕ) (t : Memory.Tree), Loop5Q VsQ vr CQ SQ LQ IQ fs n j fp rd t →
      ∀ I ∈ T.insts fs coreProgram.loop H fp0 hdr, I.t = t.retemp coreProgram fs ν fp → I.fp = fp →
      Inv I → ∀ c < n, ∃ I' ∈ T.insts fs coreProgram.loop H fp0 hdr, Inv I' ∧ I'.fp = fp + c * fs "__loop5" ∧
        ∃ (σ : Val) (bufs : List ℕ) (ks : List Memory.Tree) (k : Memory.Tree),
          tailN c t = .node "__loop5" σ bufs (ks ++ [k]) ∧
          I'.t = (Memory.Tree.node "__loop5" σ bufs (ks ++ [k])).retemp coreProgram fs ν I'.fp ∧
          Loop5H VsQ vr CQ SQ LQ IQ fs (j + c) I'.fp rd σ bufs ks k
  | 0, _, _, _, _, _, _, _, _, _, c, hc => absurd hc (Nat.not_lt_zero c)
  | n + 1, j, fp, t, hQ, I, hI, hIt, hIfp, hInvI, c, hc => by
      obtain ⟨σ, bufs, ks, k, rfl, hIQ, h0, h1, h2, h4, hv, hrest⟩ := hQ
      have hIt' : I.t = (Memory.Tree.node "__loop5" σ bufs (ks ++ [k])).retemp coreProgram fs ν I.fp := by
        rw [hIt, hIfp]
      have hk : (Memory.Tree.node "__loop5" σ bufs (ks ++ [k])).kids.getLastD
          (Memory.Tree.node "__loop5" σ bufs (ks ++ [k])) = k := by
        simp [Memory.Tree.kids]
      rcases c with _ | c
      · refine ⟨I, hI, hInvI, by rw [hIfp]; ring, σ, bufs, ks, k, rfl, hIt', ?_⟩
        rw [hIfp, Nat.add_zero]
        exact ⟨hIQ, h0, h1, h2, h4, hv⟩
      · have hpos : (kidPos fs coreProgram.loop I.fp "__loop5" bufs
            ((ks ++ [k]).map (Memory.Tree.total fs)))[ks.length]? = some (fp + fs "__loop5") := by
          rw [List.map_append, List.map_singleton,
            kidPos_loop_append B1.Main.loop5_isLoop, hIfp]
          simp [length_bases]
        obtain ⟨J, hJ, hJt, hJfp, hJk, hJf⟩ := retemp_kid_inst hI hIt'
          (by simp : (ks ++ [k])[ks.length]? = some k) hpos
        have hInvJ := hInv I hI J hJ hInvI σ bufs ks k hIt' (by rw [hJt, hIfp])
          (by rw [hJfp, hIfp]) hJk hJf
        obtain ⟨I', hI', hInv', hpos', rest⟩ := loop5Q_insts_pos Inv hInv n (j + 1) (fp + fs "__loop5") k
          hrest J hJ hJt hJfp hInvJ c (by omega)
        refine ⟨I', hI', hInv', by rw [hpos']; ring, ?_⟩
        rw [show j + (c + 1) = j + 1 + c by omega, tailN_succ', hk]
        exact rest


/-- `loop5H_vs_inst` with the callee's position. -/
theorem loop5H_vs_inst_pos {ν : ℕ → String → Val → V → E} {H : Inst → ℕ → E × E} {T : Memory.Tree}
    {fp0 : ℕ} {hdr : E × E} {I : Inst}
    (hI : I ∈ T.insts fs coreProgram.loop H fp0 hdr) {σ : Val} {bufs : List ℕ} {ks : List Memory.Tree}
    {k : Memory.Tree} (hIt : I.t = (Memory.Tree.node "__loop5" σ bufs (ks ++ [k])).retemp coreProgram fs ν I.fp)
    {j : ℕ} (hH : Loop5H VsQ vr CQ SQ LQ IQ fs j I.fp rd σ bufs ks k) :
    ∃ (kv : Memory.Tree) (W : Inst), W ∈ T.insts fs coreProgram.loop H fp0 hdr ∧
      W.t = kv.retemp coreProgram fs ν W.fp ∧ I.t.kids[5]? = some W.t ∧ I.kidFps[5]? = some W.fp ∧
      VsQ (vr j).1 (vr j).2 W.fp rd kv ∧ ks[5]? = some kv ∧
      (bases (I.fp + fs "__loop5" + k.total fs + bufs.sum) (ks.map (Memory.Tree.total fs)))[5]? = some W.fp := by
  obtain ⟨-, -, -, -, -, kv, b, hkv, hb, hq⟩ := hH
  have h5 : 5 < ks.length := (List.getElem?_eq_some_iff.mp hkv).1
  have hpos : (kidPos fs coreProgram.loop I.fp "__loop5" bufs
      ((ks ++ [k]).map (Memory.Tree.total fs)))[5]? = some b := by
    rw [List.map_append, List.map_singleton, kidPos_loop_append B1.Main.loop5_isLoop,
      List.getElem?_append_left (by rw [length_bases, List.length_map]; exact h5)]
    exact hb
  obtain ⟨W, hW, hWt, hWfp, hWk, hWf⟩ := retemp_kid_inst hI hIt
    (by rw [List.getElem?_append_left h5]; exact hkv) hpos
  exact ⟨kv, W, hW, by rw [hWt, hWfp], hWk, hWf, by rw [hWfp]; exact hq, hkv, by rw [hWfp]; exact hb⟩


section Sub

variable {lp : String → Bool} {H : Inst → ℕ → E × E}

mutual
/-- **An instance's subtree's instances are the tree's.** -/
theorem insts_sub : ∀ (t : Memory.Tree) (fp : ℕ) (hdr : E × E), ∀ J ∈ t.insts fs lp H fp hdr,
    ∀ K ∈ J.t.insts fs lp H J.fp J.hdr, K ∈ t.insts fs lp H fp hdr
  | .node f σ bufs kids, fp, hdr, J, hJ, K, hK => by
      rw [insts_node, List.mem_cons] at hJ
      rcases hJ with rfl | hJ
      · simpa [insts_node] using hK
      · rw [insts_node]
        exact List.mem_cons_of_mem _ (instsKids_sub kids _ _ 0 J hJ K hK)
  | .phantom f σ, fp, hdr, J, hJ, K, hK => by
      rw [insts_phantom, List.mem_singleton] at hJ
      subst hJ
      simpa [insts_phantom] using hK

/-- `insts_sub` for the callees. -/
theorem instsKids_sub : ∀ (ks : List Memory.Tree) (ps : List ℕ) (I : Inst) (j : ℕ),
    ∀ J ∈ Memory.Tree.instsKids fs lp H I j ps ks, ∀ K ∈ J.t.insts fs lp H J.fp J.hdr,
      K ∈ Memory.Tree.instsKids fs lp H I j ps ks
  | [], _, _, _, J, hJ, _, _ => by rw [instsKids_nil] at hJ; exact (List.not_mem_nil hJ).elim
  | _ :: _, [], _, _, J, hJ, _, _ => by rw [instsKids_nil_left] at hJ; exact (List.not_mem_nil hJ).elim
  | k :: ks, p :: ps, I, j, J, hJ, K, hK => by
      rw [instsKids_cons, List.mem_append] at hJ ⊢
      rcases hJ with hJ | hJ
      · exact Or.inl (insts_sub k _ _ J hJ K hK)
      · exact Or.inr (instsKids_sub ks ps I (j + 1) J hJ K hK)
end

end Sub

end
end LeanVM.E2E.Complete
