/-
  LeanVM.Guest.B1.Sig.SphincsForsComplete

  The FORS block of `verify_sig_lean_sphincs` (`sp_fors_tree`, `lean_ethereum.py:3866-3885`, and
  `T_k`, `lean_ethereum.py:4053-4058`, at leanVM 834e6614) is complete: each tree's secret and the
  ordered children of its levels hinted, the FORS key is `T_k` of the roots.
-/

module

public import LeanVM.Guest.B1.Sig.SphincsPathComplete
public import LeanVM.Guest.B1.Sig.SphincsSoundFors

/-!
# FORS, complete

* `sForsAt_seq`: `sp_fors_at` is a sequential block;
* `sForsLevels_complete`: a tree's levels, the siblings read back (`sForsSib`);
* `sForsTree_complete`: a tree, its secret and siblings read back, its root `fRootE`;
* `sForsTrees_complete`, `sForsBlock_complete`: the 24 trees, and the FORS key.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier (eOfNat)

@[expose] public section

variable {C : CallRel} {rd : Reader}

theorem pFold_congr {node node' : Nat → E → E} : ∀ (m : Nat) (v : E),
    (∀ j < m, node j = node' j) → pFold node m v = pFold node' m v
  | 0, _, _ => rfl
  | m + 1, v, h => by
      rw [pFold, pFold, pFold_congr m v fun j hj => h j (by omega), h m (by omega)]

theorem fRootE_congr {pp a0 A1 : E} {c s : Nat} {secret : E} {sib sib' : Nat → E}
    (h : ∀ j < 10, sib j = sib' j) : fRootE pp a0 A1 c s secret sib = fRootE pp a0 A1 c s secret sib' := by
  unfold fRootE
  refine pFold_congr 10 _ fun j hj => ?_
  funext v
  unfold fNodeE
  rw [h j hj]

theorem canon_fAdrE {A1 : E} (h : IsCanonical128 A1) (c z s : Nat) : IsCanonical128 (fAdrE A1 c z s) :=
  canon_add h (canon_word _ _)

/-! ## Shapes -/

theorem sForsAt_seq {a1 : V} {val : Nat → V} {c z x : Nat} (ha : NBv x a1)
    (h0 : z ≠ 10 → NBv x (val (10 * c + z))) (h8 : z ≤ 1 → NBv x (val (10 * c + z + 8))) :
    SeqOK x (sForsAt a1 val c z x).1 (sForsAt a1 val c z x).2.1 ∧
      NBv (sForsAt a1 val c z x).2.1 (sForsAt a1 val c z x).2.2 := by
  have hK : SeqOK x (sForsAtK a1 c z x).1 (sForsAtK a1 c z x).2.1 ∧
      NBv (sForsAtK a1 c z x).2.1 (sForsAtK a1 c z x).2.2 ∧ x ≤ (sForsAtK a1 c z x).2.1 := by
    unfold sForsAtK
    split
    · exact ⟨rfl, ha, le_rfl⟩
    · exact ⟨⟨rfl, ⟨rfl, ha.mono' (by omega), ⟨x, by omega, rfl⟩⟩, rfl⟩,
        ⟨x + 1, show x + 1 < x + 2 by omega, rfl⟩, show x ≤ x + 2 by omega⟩
  obtain ⟨k1, k2, k3⟩ := hK
  by_cases hz : z = 10
  · subst hz
    simp only [sForsAt, ↓reduceIte]
    exact ⟨k1, k2⟩
  · simp only [sForsAt, hz, ↓reduceIte]
    have hs := sBe16_seq (val := val) (pos := 10 * c + z) (n := 10 - z)
      (x := (sForsAtK a1 c z x).2.1) ((h0 hz).mono' k3) (fun h2 => (h8 (by omega)).mono' k3)
    have hle := hs.le
    have ho := sBe16_out val (10 * c + z) (10 - z) (sForsAtK a1 c z x).2.1
    have hx : (sForsAtK a1 c z x).2.1 < (sBe16 val (10 * c + z) (10 - z) (sForsAtK a1 c z x).2.1).2.1 := by
      rw [sBe16_next]; split <;> omega
    refine ⟨SeqOK.append (SeqOK.append k1 hs) ⟨⟨rfl, k2.mono' (by omega), ?_⟩, rfl⟩,
      ⟨_, by omega, rfl⟩⟩
    rw [ho]; exact ⟨_, by omega, rfl⟩

theorem sForsAt_atoms (a1 : V) (val : Nat → V) (c z x : Nat) :
    atomsOnly (sForsAt a1 val c z x).1 = true := by
  unfold sForsAt sForsAtK
  split_ifs <;> simp [atomsOnly, atomsOnly_append, sBe16_atoms, cst, addS]

theorem sForsLevels_atoms (pad : Nat) (pp a0 a1 : V) (bit val : Nat → V) (c : Nat) :
    ∀ (m z : Nat) (cur : V) (x : Nat), atomsOnly (sForsLevels pad pp a0 a1 bit val c m z cur x).1 = true
  | 0, _, _, _ => rfl
  | m + 1, z, cur, x => by
      rw [sForsLevels_succ, sForsLevel_eq]
      simp only [atomsOnly_append, sForsAt_atoms, kNode, kMsg_atoms,
        sForsLevels_atoms pad pp a0 a1 bit val c m (z + 1)]
      rfl

theorem sForsLevels_le (pad : Nat) (pp a0 a1 : V) (bit val : Nat → V) (c : Nat) :
    ∀ (m z : Nat) (cur : V) (x : Nat), z + m ≤ 10 →
      x ≤ (sForsLevels pad pp a0 a1 bit val c m z cur x).2.1 := by
  intro m z cur x h
  rw [forsLevels_shape pad pp a0 a1 bit val c m z cur x h]
  omega

/-! ## The levels -/

/-- **A FORS tree's levels complete** from level `z` (base `x`), `m` levels up to `10`: each level's
children hinted in the order of the leaf `s`'s bit, the siblings `sib` read back, the node reached
canonical. -/
theorem sForsLevels_complete {pad : Nat} {pp a0 a1 : V} {bit val : Nat → V} {c s : Nat}
    (hc : c < 24) (hs : s < 2 ^ 10) {sib : Nat → E} (hsib : ∀ j, IsCanonical128 (sib j)) :
    ∀ (m z : Nat) (cur : V) (x : Nat) (σ : Val), z + m ≤ 10 → pad + 5 ≤ x → NBv x pp →
      NBv x a0 → NBv x a1 → (∀ j < 10, NBv x (bit (10 * c + j))) →
      (∀ j < 10, NBv x (val (10 * c + j))) → NBv x cur → PadOK σ pad →
      IsCanonical128 (σ pp) → IsCanonical128 (σ a0) → IsCanonical128 (σ a1) →
      IsCanonical128 (σ cur) →
      (∀ j < 10, σ (bit (10 * c + j)) = if s.testBit j then 1 else 0) →
      (∀ j < 10, σ (val (10 * c + j)) = eOfNat (s >>> j)) →
      Completes C rd x (sForsLevels pad pp a0 a1 bit val c m z cur x).2.1
        (sForsLevels pad pp a0 a1 bit val c m z cur x).1 σ
        (fun σ' => AgreeBelow x σ σ' ∧
          IsCanonical128 (σ' (sForsLevels pad pp a0 a1 bit val c m z cur x).2.2) ∧
          ∀ j, z ≤ j → j < z + m → sForsSib σ' bit c m z x j = sib j)
  | 0, z, cur, x, σ, _, _, _, _, _, _, _, hcur, _, _, _, _, hcc, _, _ =>
      ⟨σ, Ext.refl _ _ _, ⟨fun _ _ => rfl, hcc, fun j h1 h2 => by omega⟩, fun _ _ hn => hn⟩
  | m + 1, z, cur, x, σ, hm, hpx, hpp, ha0, ha1, hbn, hvn, hcur, hp, hppc, ha0c, ha1c, hcc, hbit,
      hval => by
      rw [sForsLevels_succ, sForsLevel_eq]
      set A := sForsAt a1 val c (z + 1) (x + 4) with hA
      obtain ⟨hseqA, hadrA⟩ := sForsAt_seq (a1 := a1) (val := val) (c := c) (z := z + 1) (x := x + 4)
        (ha1.mono' (by omega)) (fun _ => (hvn (z + 1) (by omega)).mono' (by omega))
        (fun h1 => (hvn (z + 1 + 8) (by omega)).mono' (by omega))
      have hnext := sForsAt_next a1 val c z x (by omega)
      rw [← hA] at hseqA hadrA hnext
      have hlev := pairNode_complete (C := C) (rd := rd) "sp_fors_nodes" σ hp hpx hpp ha0
        (hbn z (by omega)) hcur hseqA hadrA (bt := s.testBit z) (hbit z (by omega)) (hsib z) hcc
        hppc ha0c (fun σ' hag hAt => by
          rw [hA, sForsAt_sound hc (by omega) hs
            (fun j hj => by rw [hag.apply (hvn j hj)]; exact hval j hj) hAt, hag.apply ha1]
          exact canon_fAdrE ha1c _ _ _)
      have hle := hseqA.le
      have hx18 : x + forsLevelWidth z = A.2.1 + 18 := by
        rw [hnext]; unfold forsLevelWidth; split_ifs <;> omega
      have hnb : NumBelow (A.2.1 + 18) (Stmt.valsList ([hintW "sp_fors_nodes" [.n x, .n (x + 1)]] ++
          isChildS cur (.n x) (.n (x + 1)) (bit (10 * c + z)) (x + 2) ++ A.1 ++
          (kNode pad pp a0 A.2.2 (.n x) (.n (x + 1)) A.2.1).1)) := by
        simp only [valsList_append]
        refine NumBelow.append (NumBelow.append (NumBelow.append ?_ ?_) ?_) ?_
        · rw [valsList_hint]
          exact .cons ⟨x, by omega, rfl⟩ (.cons ⟨x + 1, by omega, rfl⟩ (.nil _))
        · intro v hv
          simp only [isChildS, addS, mulS, valsList_cons, valsList_nil, Stmt.vals, Atom.vals,
            List.append_nil, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
            or_false] at hv
          rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          all_goals first | exact ⟨_, by omega, rfl⟩ | exact hcur.mono' (by omega) |
            exact (hbn z (by omega)).mono' (by omega)
        · exact hseqA.numBelow.mono (by omega)
        · refine kNode_numBelow (by omega) ?_
          simp only [List.mem_cons, List.not_mem_nil, or_false]
          rintro v (rfl | rfl | rfl | rfl | rfl)
          · exact hpp.mono' (by omega)
          · exact ha0.mono' (by omega)
          · exact hadrA
          · exact ⟨x, by omega, rfl⟩
          · exact ⟨x + 1, by omega, rfl⟩
      refine Completes.append (m := A.2.1 + 18) (by omega)
        (sForsLevels_le pad pp a0 a1 bit val c m (z + 1) _ _ (by omega)) hnb
        (hlev.withAtoms (by simp only [atomsOnly_append, hseqA.atoms, kNode, kMsg_atoms]; rfl))
        (fun σ1 he1 h1 => ?_)
      obtain ⟨⟨hag1, hk0, hk1⟩, hA1⟩ := h1
      have t1 : ∀ v, NBv x v → σ1 v = σ v := fun v hv => hag1.apply hv
      obtain ⟨hib, hd⟩ := bit_facts (hbit z (by omega))
      have hib1 : IsBit (σ1 (bit (10 * c + z))) := by rw [t1 _ (hbn z (by omega))]; exact hib
      have hp1 : PadOK σ1 pad := hp.congr hpx hag1
      have hlv := level_sound hp1 hib1
        (hA1.left.left.sub fun t ht => List.mem_append_right _ ht) hA1.right
      have hcan1 : IsCanonical128 (σ1 (.n (A.2.1 + 5))) := by rw [hlv]; exact canon_hcellFst _
      have ih := sForsLevels_complete hc hs hsib m (z + 1) (.n (A.2.1 + 5)) (A.2.1 + 18) σ1
        (by omega) (by omega) (hpp.mono' (by omega)) (ha0.mono' (by omega)) (ha1.mono' (by omega))
        (fun j hj => (hbn j hj).mono' (by omega)) (fun j hj => (hvn j hj).mono' (by omega))
        ⟨A.2.1 + 5, by omega, rfl⟩ hp1 (by rw [t1 _ hpp]; exact hppc) (by rw [t1 _ ha0]; exact ha0c)
        (by rw [t1 _ ha1]; exact ha1c) hcan1 (fun j hj => by rw [t1 _ (hbn j hj)]; exact hbit j hj)
        (fun j hj => by rw [t1 _ (hvn j hj)]; exact hval j hj)
      refine ih.mono le_rfl le_rfl (fun σ' ⟨hag', hc', hs'⟩ => ⟨?_, hc', ?_⟩)
      · exact fun j hj => (hag1 j hj).trans (hag' j (by omega))
      · intro j hj1 hj2
        by_cases hjz : j = z
        · subst hjz
          simp only [sForsSib, ite_true]
          have hb' : σ' (bit (10 * c + j)) = if s.testBit j then 1 else 0 := by
            rw [(hag'.apply ((hbn j (by omega)).mono' (by omega))), t1 _ (hbn j (by omega))]
            exact hbit j (by omega)
          exact siblingOf_mPair (node := σ cur) hb' (by rw [← hag' x (by omega), hk0])
            (by rw [← hag' (x + 1) (by omega), hk1])
        · simp only [sForsSib, hjz, ite_false, hx18]
          exact hs' j (by omega) (by omega)

/-! ## A tree -/

theorem k64_numBelow {pad : Nat} {m0 m1 m2 m3 : V} {c : Nat} (hpc : pad + 5 ≤ c)
    (hm : ∀ v ∈ [m0, m1, m2, m3], NBv c v) :
    NumBelow (c + 14) (Stmt.valsList (k64 pad m0 m1 m2 m3 c (c + 1))) := by
  rw [k64_vals_eq]
  intro v hv
  simp only [cst, kecS, valsList_cons, valsList_nil, Stmt.vals, Atom.vals,
    List.append_nil, List.cons_append, List.nil_append, List.mem_cons] at hv
  have hr : ∀ w ∈ runV (c + 1) 13, NBv (c + 14) w := runV_nb (by omega)
  have h0 := hm m0 (by simp)
  have h1 := hm m1 (by simp)
  have h2 := hm m2 (by simp)
  have h3 := hm m3 (by simp)
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    hv
  all_goals first
    | exact ⟨_, by omega, rfl⟩
    | exact h0.mono' (by omega)
    | exact h1.mono' (by omega)
    | exact h2.mono' (by omega)
    | exact h3.mono' (by omega)
    | exact hr _ hv

theorem sForsTree_atoms (pad : Nat) (pp a0 a1 : V) (bit val : Nat → V) (c b : Nat) :
    atomsOnly (sForsTree pad pp a0 a1 bit val c b).1 = true := by
  simp only [sForsTree, atomsOnly_append, sForsAt_atoms, sForsLevels_atoms, k64]
  rfl

/-- **FORS tree `c` completes** from base `b`: its secret hinted at `b`, its levels' children in the
order of the leaf `s`'s bits; the secret and the siblings `sib` read back. -/
theorem sForsTree_complete {pad : Nat} {pp a0 a1 : V} {bit val : Nat → V} {c s b : Nat}
    (hc : c < 24) (hs : s < 2 ^ 10) {secret : E} (hsec : IsCanonical128 secret) {sib : Nat → E}
    (hsib : ∀ j, IsCanonical128 (sib j)) (σ : Val) (hpb : pad + 5 ≤ b) (hpp : NBv b pp)
    (ha0 : NBv b a0) (ha1 : NBv b a1) (hbn : ∀ j < 10, NBv b (bit (10 * c + j)))
    (hvn : ∀ j < 10, NBv b (val (10 * c + j))) (hp : PadOK σ pad) (hppc : IsCanonical128 (σ pp))
    (ha0c : IsCanonical128 (σ a0)) (ha1c : IsCanonical128 (σ a1))
    (hbit : ∀ j < 10, σ (bit (10 * c + j)) = if s.testBit j then 1 else 0)
    (hval : ∀ j < 10, σ (val (10 * c + j)) = eOfNat (s >>> j)) :
    Completes C rd b (sForsTree pad pp a0 a1 bit val c b).2.1 (sForsTree pad pp a0 a1 bit val c b).1 σ
      (fun σ' => AgreeBelow b σ σ' ∧ σ' (.n b) = secret ∧
        ∀ j < 10, sForsSib σ' bit c 10 0 (b + forsLeafWidth c) j = sib j) := by
  set σr := updRun σ b 1 (fun _ => secret) with hσr
  have tk : ∀ v, NBv b v → σr v = σ v := fun v hv => updRun_below σ b 1 (fun _ => secret) hv
  have hsr : σr (.n b) = secret := by
    have := updRun_at σ b 1 (fun _ => secret) (j := 0) (by norm_num); rwa [Nat.add_zero] at this
  refine Completes.reload ((updRun_ext σ b 1 (fun _ => secret)).mono le_rfl
    (by rw [(sForsTree_shape pad pp a0 a1 bit val c b).1]; omega)) ?_
  have hy := sForsAt_leaf_next a1 val c b
  have hlw : 24 ≤ forsLeafWidth c := by unfold forsLeafWidth; split <;> omega
  simp only [sForsTree, List.append_assoc]
  set A := sForsAt a1 val c 0 (b + 1) with hA
  obtain ⟨hseqA, hadrA⟩ := sForsAt_seq (a1 := a1) (val := val) (c := c) (z := 0) (x := b + 1)
    (ha1.mono' (by omega)) (fun _ => (hvn 0 (by omega)).mono' (by omega))
    (fun _ => (hvn 8 (by omega)).mono' (by omega))
  rw [← hA] at hseqA hadrA
  have hle := hseqA.le
  have hw : A.2.1 + 14 = b + forsLeafWidth c := by omega
  have hlv_le := sForsLevels_le pad pp a0 a1 bit val c 10 0 (.n (A.2.1 + 1)) (A.2.1 + 14) (by norm_num)
  refine Completes.append (m := b + 1) (by omega) (by omega)
    (by rw [valsList_hint]; exact .cons ⟨b, by omega, rfl⟩ (.nil _))
    (hintKeep_complete σr _ _ _ _) (fun σ1 he1 hp1 => ?_)
  subst hp1
  refine Completes.seqThen hseqA (by omega) (fun σ2 he2 hA2 => ?_)
  have hag2 : AgreeBelow (b + 1) σr σ2 := he2.agree
  have t2 : ∀ v, NBv b v → σ2 v = σ v := fun v hv =>
    (hag2.apply (hv.mono' (by omega))).trans (tk v hv)
  have hs2 : σ2 (.n b) = secret := (hag2.apply ⟨b, by omega, rfl⟩).trans hsr
  have hadrv : σ2 A.2.2 = fAdrE (σ a1) c 0 s := by
    rw [hA, sForsAt_sound hc (by norm_num) hs
      (fun j hj => by rw [t2 _ (hvn j hj)]; exact hval j hj) hA2, t2 _ ha1]
  have hk := k64_complete (C := C) (rd := rd) (pad := pad) (m0 := pp) (m1 := a0) (m2 := A.2.2)
    (m3 := .n b) (c := A.2.1) σ2 (hp.congr hpb fun j hj => (t2 (.n j) ⟨j, hj, rfl⟩).symm)
    (by omega) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro v (rfl | rfl | rfl | rfl)
      · exact ⟨hpp.mono' (by omega), by rw [t2 _ hpp]; exact hppc⟩
      · exact ⟨ha0.mono' (by omega), by rw [t2 _ ha0]; exact ha0c⟩
      · exact ⟨hadrA, by rw [hadrv]; exact canon_fAdrE ha1c _ _ _⟩
      · exact ⟨⟨b, by omega, rfl⟩, by rw [hs2]; exact hsec⟩)
  have hnbk := k64_numBelow (pad := pad) (m0 := pp) (m1 := a0) (m2 := A.2.2) (m3 := .n b)
    (c := A.2.1) (by omega) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro v (rfl | rfl | rfl | rfl)
      · exact hpp.mono' (by omega)
      · exact ha0.mono' (by omega)
      · exact hadrA
      · exact ⟨b, by omega, rfl⟩)
  refine Completes.append (m := A.2.1 + 14) (by omega) hlv_le hnbk hk.withExt
    (fun σ3 he3 h3 => ?_)
  obtain ⟨⟨-, hc3⟩, he3'⟩ := h3
  have hag3 : AgreeBelow A.2.1 σ2 σ3 := he3'.agree
  have t3 : ∀ v, NBv b v → σ3 v = σ v := fun v hv =>
    (hag3.apply (hv.mono' (by omega))).trans (t2 v hv)
  have hlvc := sForsLevels_complete (C := C) (rd := rd) (pad := pad) (pp := pp) (a0 := a0) (a1 := a1)
    (bit := bit) (val := val) hc hs hsib 10 0 (.n (A.2.1 + 1)) (A.2.1 + 14) σ3 (by norm_num)
    (by omega) (hpp.mono' (by omega)) (ha0.mono' (by omega)) (ha1.mono' (by omega))
    (fun j hj => (hbn j hj).mono' (by omega)) (fun j hj => (hvn j hj).mono' (by omega))
    ⟨A.2.1 + 1, by omega, rfl⟩ (hp.congr hpb fun j hj => (t3 (.n j) ⟨j, hj, rfl⟩).symm)
    (by rw [t3 _ hpp]; exact hppc) (by rw [t3 _ ha0]; exact ha0c) (by rw [t3 _ ha1]; exact ha1c)
    hc3 (fun j hj => by rw [t3 _ (hbn j hj)]; exact hbit j hj)
    (fun j hj => by rw [t3 _ (hvn j hj)]; exact hval j hj)
  refine hlvc.mono le_rfl le_rfl (fun σ' ⟨hag', _, hs'⟩ => ⟨?_, ?_, ?_⟩)
  · intro j hj
    rw [← t3 (.n j) ⟨j, hj, rfl⟩]
    exact hag' j (by omega)
  · rw [← hag' b (by omega), ← hag3 b (by omega), hs2]
  · intro j hj
    rw [← hw]
    exact hs' j (by omega) (by omega)

/-- **FORS tree `c`'s root**, completed: `fRootE` of the secret and siblings. -/
theorem sForsTree_complete_val {pad : Nat} {pp a0 a1 : V} {bit val : Nat → V} {c s b : Nat}
    (hc : c < 24) (hs : s < 2 ^ 10) {secret : E} (hsec : IsCanonical128 secret) {sib : Nat → E}
    (hsib : ∀ j, IsCanonical128 (sib j)) (σ : Val) (hpb : pad + 5 ≤ b) (hpp : NBv b pp)
    (ha0 : NBv b a0) (ha1 : NBv b a1) (hbn : ∀ j < 10, NBv b (bit (10 * c + j)))
    (hvn : ∀ j < 10, NBv b (val (10 * c + j))) (hp : PadOK σ pad) (hppc : IsCanonical128 (σ pp))
    (ha0c : IsCanonical128 (σ a0)) (ha1c : IsCanonical128 (σ a1))
    (hbit : ∀ j < 10, σ (bit (10 * c + j)) = if s.testBit j then 1 else 0)
    (hval : ∀ j < 10, σ (val (10 * c + j)) = eOfNat (s >>> j)) :
    Completes C rd b (sForsTree pad pp a0 a1 bit val c b).2.1 (sForsTree pad pp a0 a1 bit val c b).1 σ
      (fun σ' => AgreeBelow b σ σ' ∧
        σ' (sForsTree pad pp a0 a1 bit val c b).2.2 = fRootE (σ pp) (σ a0) (σ a1) c s secret sib) := by
  refine ((sForsTree_complete hc hs hsec hsib σ hpb hpp ha0 ha1 hbn hvn hp hppc ha0c ha1c hbit
    hval).withAtoms (sForsTree_atoms ..)).mono le_rfl le_rfl
    (fun σ' ⟨⟨hag, hsec', hsib'⟩, hA⟩ => ⟨hag, ?_⟩)
  have t : ∀ v, NBv b v → σ' v = σ v := fun v hv => hag.apply hv
  rw [sForsTree_sound (hp.congr hpb hag) hc hs
    (fun j hj => by rw [t _ (hbn j hj)]; exact hbit j hj)
    (fun j hj => by rw [t _ (hvn j hj)]; exact hval j hj) hA, t _ hpp, t _ ha0, t _ ha1, hsec']
  exact fRootE_congr hsib'

end
end LeanVM.Guest.B1.Sig
