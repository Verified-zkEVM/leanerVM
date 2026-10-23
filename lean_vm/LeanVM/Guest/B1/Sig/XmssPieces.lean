/-
  LeanVM.Guest.B1.Sig.XmssPieces

  The prologue and the message digests of `verify_lean_xmss` complete.
-/

module

public import LeanVM.Guest.B1.Sig.XmssCore

/-!
# The prologue and the digests, complete

* `xPrologue_complete`: the prologue completes from a valuation holding `P` at its argument's
  offset `1` and Boolean bits;
* `xDigest0_complete`: the bottom layer's digest, its randomizer `rho` loaded, from the message's
  cells at the argument's offsets `2` and `3`;
* `xDigest1_complete`: the top layer's index and digest over the bottom root.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

variable {C : CallRel} {rd : Reader}

theorem AtomsHold.frame {σ σ' : Val} {ss : List Stmt} {b : Nat} (h : AtomsHold rd σ ss)
    (hn : NumBelow b (Stmt.valsList ss)) (hag : AgreeBelow b σ σ') : AtomsHold rd σ' ss := fun a ha =>
  (atom_congr a fun v hv => by
    obtain ⟨k, hk, rfl⟩ := hn v (mem_valsList_of_mem ha hv)
    exact hag k hk).mp (h a ha)

/-! ## The prologue -/

/-- The prologue's checks and its sequential block. -/
def xPreChecks : List Stmt :=
  [loadS (.n 1) (.n 0) 1, hintW "leaf_index_bits" (runV 2 32)] ++ booleans 2 32

def xPreSeq : List Stmt :=
  shifts 2 32 34 ++ (List.range 10).map (fun s => cst (128 + s) (word (2 ^ s) 0 0)) ++
    (List.range 58).map (fun i => cst (138 + i) (word i 0 0))

theorem xPrologue_split : xPrologue = xPreChecks ++ xPreSeq := by
  simp [xPrologue, xPreChecks, xPreSeq, List.append_assoc]

theorem xPreSeq_ok : SeqOK 34 xPreSeq 196 := seqB_ok (by decide +kernel)

theorem xPreChecks_nb : NumBelow 34 (Stmt.valsList xPreChecks) := numBelow_of_all (by decide +kernel)

theorem xPreChecks_atoms : atomsOnly xPreChecks = true := by decide +kernel

/-- **The prologue completes** from a valuation holding `P` at its argument's offset `1` and
Boolean bits. -/
theorem xPrologue_complete (σ : Val) (hld : LoadHolds rd (σ (.n 0)) 1 (σ (.n 1)))
    (hb : ∀ j < 32, IsBit (σ (.n (2 + j)))) :
    Completes C rd 34 196 xPrologue σ (fun σ' => AtomsHold rd σ' xPrologue) := by
  rw [xPrologue_split]
  have hchk : AtomsHold rd σ xPreChecks := by
    intro a ha
    simp only [xPreChecks, List.mem_append, List.mem_cons, booleans, List.mem_map, List.mem_range,
      loadS, hintW, Stmt.atom.injEq, List.not_mem_nil, or_false] at ha
    rcases ha with (rfl | rfl) | ⟨j, hj, e⟩
    · exact hld
    · trivial
    · simp only [mulS, Stmt.atom.injEq] at e
      subst e
      exact (hb j hj).symm
  refine Completes.checks xPreChecks_atoms hchk xPreChecks_nb (by norm_num)
    (((seq_completes xPreSeq_ok σ).keep (Q := fun σ' => AtomsHold rd σ' xPreChecks) hchk
      (fun σ' he h => h.frame xPreChecks_nb he.agree)).mono le_rfl le_rfl (fun σ' ⟨h1, h2⟩ => ?_))
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · exact h2 a ha
  · exact h1 a ha

/-! ## The bottom layer's digest -/

theorem xDigest0_split : xDigest0 196 = [hintW "randomizer" [.n 196]] ++
    ([cst 197 (word (tw 12) 0 0), addS (.n 198) (xNode 0) (.n 197)] ++
      (loadS (.n 199) (.n 0) 2 :: loadS (.n 200) (.n 0) 3 ::
        ((copyS (.n 201) (.n 196) :: cst 202 (word 1 0 0) :: cst 203 (word 0 0 0) :: cst 204 (word 0 0 0) ::
          cst 205 (word (2 ^ 63) 0 0) ::
          (List.range 5).map (fun k => cst (206 + k) (word (if k = 0 then 1 else 0) 0 0))) ++
        [kecS [.n 1, .n 198, .n 199, .n 200, .n 201, .n 202, .n 203, .n 204, .n 205, .n 207, .n 208,
          .n 209, .n 210] (runV 211 13) false false]))) := rfl

/-- **The bottom layer's digest completes**, its randomizer `rho` loaded. -/
theorem xDigest0_complete (σ : Val) {rho c d : E} (hrho : IsCanonical128 rho) (hc : IsCanonical128 c)
    (hd : IsCanonical128 d) (hld2 : LoadHolds rd (σ (.n 0)) 2 c) (hld3 : LoadHolds rd (σ (.n 0)) 3 d)
    (hP : IsCanonical128 (σ (.n 1))) (hn0 : IsCanonical128 (σ (xNode 0))) :
    Completes C rd 196 224 (xDigest0 196) σ (fun σ' => σ' (.n 196) = rho) := by
  have hext : Ext 196 197 σ (Function.update σ (.n 196) rho) := fun v hv =>
    Function.update_of_ne (hv 196 le_rfl (by norm_num)) _ _
  refine Completes.reload (hext.mono le_rfl (by norm_num)) ?_
  rw [xDigest0_split]
  refine Completes.append (m := 197) (by norm_num) (by norm_num)
    (by rw [valsList_hint]; exact .cons ⟨196, by norm_num, rfl⟩ (.nil _)) (hintKeep_complete _ _ _ _ _)
    (fun σ1 _ e1 => ?_)
  subst e1
  have h196 : Function.update σ (.n 196) rho (.n 196) = rho := Function.update_self ..
  have hlow : ∀ k < 196, Function.update σ (.n 196) rho (.n k) = σ (.n k) := fun k hk =>
    Function.update_of_ne (by simp; omega) _ _
  refine Completes.seq (m := 199) (seqB_ok (by decide +kernel)) (by norm_num) (fun σ2 he2 hh2 => ?_)
  have hag2 := he2.agree
  have e197 : σ2 (.n 197) = word (tw 12) 0 0 := hh2.atom (a := .const (.n 197) _) (by simp [cst])
  have e198 : σ2 (.n 198) = σ2 (xNode 0) + σ2 (.n 197) :=
    hh2.atom (a := .add (.n 198) (xNode 0) (.n 197)) (by simp [addS])
  have hn02 : σ2 (xNode 0) = σ (xNode 0) := by
    rw [show xNode 0 = V.n 127 from rfl, hag2.apply ⟨127, by norm_num, rfl⟩]; exact hlow 127 (by norm_num)
  refine Completes.load ⟨0, by norm_num, rfl⟩ (w := c)
    (by rw [hag2.apply ⟨0, by norm_num, rfl⟩, hlow 0 (by norm_num)]; exact hld2) (by norm_num)
    (fun σ3 he3 e3 => ?_)
  have hag3 := he3.agree
  refine Completes.load ⟨0, by norm_num, rfl⟩ (w := d)
    (by rw [hag3.apply ⟨0, by norm_num, rfl⟩, hag2.apply ⟨0, by norm_num, rfl⟩, hlow 0 (by norm_num)]
        exact hld3) (by norm_num) (fun σ4 he4 e4 => ?_)
  have hag4 := he4.agree
  refine Completes.seq (m := 211) (seqB_ok (by decide +kernel)) (by norm_num) (fun σ5 he5 hh5 => ?_)
  have hag5 := he5.agree
  -- the values the hash reads
  have v1 : σ5 (.n 1) = σ (.n 1) := by
    rw [hag5.apply ⟨1, by norm_num, rfl⟩, hag4.apply ⟨1, by norm_num, rfl⟩, hag3.apply ⟨1, by norm_num, rfl⟩,
      hag2.apply ⟨1, by norm_num, rfl⟩, hlow 1 (by norm_num)]
  have v198 : σ5 (.n 198) = σ (xNode 0) + word (tw 12) 0 0 := by
    rw [hag5.apply ⟨198, by norm_num, rfl⟩, hag4.apply ⟨198, by norm_num, rfl⟩,
      hag3.apply ⟨198, by norm_num, rfl⟩, e198, e197, hn02]
  have v199 : σ5 (.n 199) = c := by
    rw [hag5.apply ⟨199, by norm_num, rfl⟩, hag4.apply ⟨199, by norm_num, rfl⟩, e3]
  have v200 : σ5 (.n 200) = d := by rw [hag5.apply ⟨200, by norm_num, rfl⟩, e4]
  have v196 : σ5 (.n 196) = rho := by
    rw [hag5.apply ⟨196, by norm_num, rfl⟩, hag4.apply ⟨196, by norm_num, rfl⟩,
      hag3.apply ⟨196, by norm_num, rfl⟩, hag2.apply ⟨196, by norm_num, rfl⟩, h196]
  have v201 : σ5 (.n 201) = rho := by
    rw [← v196]; exact hh5.atom (a := .copy (.n 201) (.n 196)) (by simp [copyS])
  have vc : ∀ k w, Stmt.atom (.const (.n k) (word w 0 0)) ∈ (copyS (.n 201) (.n 196) :: cst 202 (word 1 0 0) ::
      cst 203 (word 0 0 0) :: cst 204 (word 0 0 0) :: cst 205 (word (2 ^ 63) 0 0) ::
      (List.range 5).map (fun k => cst (206 + k) (word (if k = 0 then 1 else 0) 0 0))) →
      IsCanonical128 (σ5 (.n k)) := fun k w h => by
    rw [show σ5 (.n k) = word w 0 0 from hh5.atom h]; exact canon_word _ _
  have vm : ∀ k, 0 < k → k < 5 → IsCanonical128 (σ5 (.n (206 + k))) := fun k h0 h5 =>
    vc (206 + k) 0 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨k, List.mem_range.mpr h5,
        by simp [cst, show k ≠ 0 by omega]⟩))))))
  have hcan : ∀ cc : Fin 13, IsCanonical128 (cells13 ([.n 1, .n 198, .n 199, .n 200, .n 201, .n 202, .n 203,
      .n 204, .n 205, .n 207, .n 208, .n 209, .n 210].map σ5) cc) := by
    intro cc
    fin_cases cc <;> simp only [cells13, List.map_cons, List.map_nil, List.getD_cons_zero,
      List.getD_cons_succ]
    · rw [v1]; exact hP
    · rw [v198]; exact canon_add hn0 (canon_word _ _)
    · rw [v199]; exact hc
    · rw [v200]; exact hd
    · rw [v201]; exact hrho
    · exact vc 202 1 (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    · exact vc 203 0 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    · exact vc 204 0 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_self ..))))
    · exact vc 205 (2 ^ 63) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))
    · exact vm 1 (by norm_num) (by norm_num)
    · exact vm 2 (by norm_num) (by norm_num)
    · exact vm 3 (by norm_num) (by norm_num)
    · exact vm 4 (by norm_num) (by norm_num)
  refine ((kecS_complete (C := C) (rd := rd) σ5 211 rfl (fun v hv => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact ⟨_, by norm_num, rfl⟩) hcan false false).keep (Q := fun σ' => σ' (.n 196) = rho) v196
    (fun σ' he h => by rw [he.apply (Or.inl (by norm_num))]; exact h)).mono le_rfl le_rfl
    (fun σ' h => h.2)

/-! ## The top layer's digest -/

theorem xDigest1_split (b : Nat) (root : V) : xDigest1 b root =
    [cst b (word lxTop 0 0), addS (.n (b + 1)) (xNode 16) (.n b)] ++ (hintW "randomizer" [.n (b + 2)] ::
      ([cst (b + 3) (word (tw 12) 0 0), addS (.n (b + 4)) (.n (b + 1)) (.n (b + 3))] ++
        k64 xPad (.n 1) (.n (b + 4)) root (.n (b + 2)) (b + 5) (b + 5 + 1))) := rfl

/-- **The top layer's index and digest complete**, its randomizer `rho` loaded. -/
theorem xDigest1_complete {b : Nat} {root : V} (σ : Val) {rho : E} (hb : 211 ≤ b) (hroot : NBv b root)
    (hrc : IsCanonical128 (σ root)) (hrho : IsCanonical128 rho) (hP : IsCanonical128 (σ (.n 1)))
    (hn16 : IsCanonical128 (σ (xNode 16))) (hpad : PadOK σ xPad) :
    Completes C rd b (b + 5 + 14) (xDigest1 b root) σ (fun σ' => σ' (.n (b + 2)) = rho) := by
  rw [xDigest1_split]
  refine Completes.seq (m := b + 2)
    ⟨rfl, ⟨rfl, ⟨34 + 3 * (31 - 16), by omega, rfl⟩, ⟨b, by omega, rfl⟩⟩, rfl⟩ (by omega)
    (fun σ1 he1 hh1 => ?_)
  have hag1 := he1.agree
  have e0 : σ1 (.n b) = word lxTop 0 0 := hh1.atom (List.mem_cons_self ..)
  have e1 : σ1 (.n (b + 1)) = σ1 (xNode 16) + σ1 (.n b) :=
    hh1.atom (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  have hext : Ext (b + 2) (b + 3) σ1 (Function.update σ1 (.n (b + 2)) rho) := fun v hv =>
    Function.update_of_ne (hv (b + 2) le_rfl (by omega)) _ _
  refine Completes.reload (hext.mono le_rfl (by omega)) ?_
  refine Completes.append (xs := [hintW "randomizer" [.n (b + 2)]]) (m := b + 3) (by omega) (by omega)
    (by rw [valsList_hint]; exact .cons ⟨b + 2, by omega, rfl⟩ (.nil _)) (hintKeep_complete _ _ _ _ _)
    (fun σ2 _ e2 => ?_)
  subst e2
  have hr2 : Function.update σ1 (.n (b + 2)) rho (.n (b + 2)) = rho := Function.update_self ..
  have hlow : ∀ k < b + 2, Function.update σ1 (.n (b + 2)) rho (.n k) = σ1 (.n k) := fun k hk =>
    Function.update_of_ne (by simp; omega) _ _
  have hs3 : SeqOK (b + 3) [cst (b + 3) (word (tw 12) 0 0), addS (.n (b + 4)) (.n (b + 1)) (.n (b + 3))]
      (b + 5) := ⟨rfl, ⟨rfl, ⟨b + 1, by omega, rfl⟩, ⟨b + 3, by omega, rfl⟩⟩, rfl⟩
  refine Completes.seq (m := b + 5) hs3 (by omega) (fun σ3 he3 hh3 => ?_)
  have hag3 := he3.agree
  have e3 : σ3 (.n (b + 3)) = word (tw 12) 0 0 := hh3.atom (List.mem_cons_self ..)
  have e4 : σ3 (.n (b + 4)) = σ3 (.n (b + 1)) + σ3 (.n (b + 3)) :=
    hh3.atom (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  have tr : ∀ k < b, σ3 (.n k) = σ (.n k) := fun k hk => by
    rw [hag3.apply ⟨k, by omega, rfl⟩, hlow k (by omega), hag1.apply ⟨k, hk, rfl⟩]
  have v1 : σ3 (.n (b + 1)) = σ (xNode 16) + word lxTop 0 0 := by
    rw [hag3.apply ⟨b + 1, by omega, rfl⟩, hlow (b + 1) (by omega), e1, e0,
      show xNode 16 = V.n (34 + 3 * (31 - 16)) from rfl, hag1.apply ⟨_, by omega, rfl⟩]
  have v2 : σ3 (.n (b + 2)) = rho := by rw [hag3.apply ⟨b + 2, by omega, rfl⟩, hr2]
  have hpad3 : PadOK σ3 xPad := by
    obtain ⟨q0, q1, q2, q3, q4⟩ := hpad
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rw [tr _ (by simp [xPad]; omega)]
    exacts [q0, q1, q2, q3, q4]
  have hroot3 : σ3 root = σ root := by
    obtain ⟨k, hk, rfl⟩ := hroot; exact tr k hk
  refine ((k64_complete (C := C) (rd := rd) σ3 hpad3 (by simp [xPad]; omega) (fun v hv => ?_)).keep
    (Q := fun σ' => σ' (.n (b + 2)) = rho) v2
    (fun σ' he h => by rw [he.apply (Or.inl (by omega))]; exact h)).mono le_rfl le_rfl (fun σ' h => h.2)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl
  · exact ⟨⟨1, by omega, rfl⟩, by rw [tr 1 (by omega)]; exact hP⟩
  · have hc4 : IsCanonical128 (σ3 (.n (b + 4))) := by
      rw [e4, e3, v1]
      exact canon_add (canon_add hn16 (canon_word _ _)) (canon_word _ _)
    exact ⟨⟨b + 4, by omega, rfl⟩, hc4⟩
  · exact ⟨hroot.mono' (by omega), by rw [hroot3]; exact hrc⟩
  · exact ⟨⟨b + 2, by omega, rfl⟩, by rw [v2]; exact hrho⟩

/-! ## The layers' values -/

theorem xDigest0_nb : NumBelow 224 (Stmt.valsList (xDigest0 196)) := numBelow_of_all (by decide +kernel)

theorem xDigest1_nb {b : Nat} {root : V} (hb : 211 ≤ b) (hroot : NBv b root) :
    NumBelow (b + 19) (Stmt.valsList (xDigest1 b root)) := by
  intro x hx
  rw [xDigest1_split, valsList_append, valsList_cons (hintW "randomizer" [.n (b + 2)]), valsList_append] at hx
  rcases List.mem_append.mp hx with hx | hx
  · simp [cst, addS, Stmt.vals, Atom.vals] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    all_goals exact ⟨_, by omega, rfl⟩
  rcases List.mem_append.mp hx with hx | hx
  · simp [hintW, Stmt.vals, Atom.vals, Hint.vals, Dest.vals] at hx
    subst hx
    exact ⟨b + 2, by omega, rfl⟩
  rcases List.mem_append.mp hx with hx | hx
  · simp [cst, addS, Stmt.vals, Atom.vals] at hx
    rcases hx with rfl | rfl | rfl | rfl
    all_goals exact ⟨_, by omega, rfl⟩
  rcases k64_vals _ _ _ _ _ _ _ hx with hx | rfl | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact ⟨1, by omega, rfl⟩
    · exact ⟨b + 4, by omega, rfl⟩
    · exact NBv.mono' hroot (show b ≤ b + 19 by omega)
    · exact ⟨b + 2, by omega, rfl⟩
  · exact ⟨b + 5, by omega, rfl⟩
  · exact ⟨xPad + k, by simp only [xPad]; omega, rfl⟩
  · exact ⟨b + 5 + 1 + k, by omega, rfl⟩

/-- **A layer's core's values lie below its end.** -/
theorem xCore_nb {layer b : Nat} (hA : 211 ≤ xA layer b) (hidx : NBv (xA layer b) (xIdx layer b))
    (hd0 : NBv (xA layer b) (xD0 layer b)) (hbits : ∀ l < 16, NBv (xA layer b) (xBitOf layer l))
    (hnodes : ∀ l nd, xNodeOf layer l = some nd → NBv (xA layer b) nd) :
    NumBelow (xMk layer b).2.1 (Stmt.valsList (xStepAddrs (xIdx layer b) (xA layer b) ++ ((xCw layer b).1 ++
      ([cst (xCw layer b).2.1 (word (tw 2) 0 0), addS (.n ((xCw layer b).2.1 + 1)) (xIdx layer b)
        (.n (xCw layer b).2.1)] ++ ((xLeafK layer b).1 ++ (xMk layer b).1))))) := by
  have b1 : xA layer b + 6 < (xCw layer b).2.1 := by
    rw [xCw_eq]
    exact cwBase_lt (xWc layer b) (q := 0) (G := 19) _ _ _ (by norm_num)
  have htips : (xCw layer b).2.2 = (List.range 58).map (cwTip (xW layer b) (xA layer b + 6)) :=
    codewordT_tips (xW layer b) (G := 19) (by norm_num) _ _ _
  have hcellNB : ∀ c ∈ (xLeafCells layer b).map KC.cell, KCb ((xCw layer b).2.1 + 2) c := by
    intro c hc
    simp only [xLeafCells, List.map_cons, List.mem_cons, htips, List.map_map, List.mem_map,
      List.mem_range, Function.comp_apply] at hc
    rcases hc with rfl | rfl | ⟨i, hi, rfl⟩
    · exact ⟨1, by omega, rfl⟩
    · exact ⟨_, by omega, rfl⟩
    · obtain ⟨j, ej, hj⟩ := cwTip_lt (xW layer b) (G := 19) xTarget (xD0 layer b) (xA layer b + 6)
        (by norm_num) (show i < 3 * 19 + 1 by omega)
      have hj' : j < (xCw layer b).2.1 := hj
      exact ⟨j, by omega, ej⟩
  have b2 : (xCw layer b).2.1 + 2 ≤ (xLeafK layer b).2.1 :=
    kMsg_le (show xPad + 5 ≤ (xCw layer b).2.1 + 2 by simp [xPad]; omega) hcellNB
  have b3 : (xLeafK layer b).2.1 ≤ (xMk layer b).2.1 := merkleT_snd_ge ..
  have hout : (xLeafK layer b).2.2 + 13 ≤ (xLeafK layer b).2.1 :=
    kMsg_out xPad ((xLeafCells layer b).map KC.cell) 960 false ((xCw layer b).2.1 + 2)
  have n1 := (xStepAddrs_seq hidx).numBelow
  have n2 : NumBelow (xCw layer b).2.1 (Stmt.valsList (xCw layer b).1) := by
    rw [xCw_eq]
    exact codewordT_numBelow (xWc_shape hA) (by omega) le_rfl (xWc_pw layer b hA) (hd0.mono' (by omega))
  have n3 := (show SeqOK (xCw layer b).2.1 [cst (xCw layer b).2.1 (word (tw 2) 0 0),
      addS (.n ((xCw layer b).2.1 + 1)) (xIdx layer b) (.n (xCw layer b).2.1)] ((xCw layer b).2.1 + 2) from
    ⟨rfl, ⟨rfl, hidx.mono' (by omega), ⟨_, by omega, rfl⟩⟩, rfl⟩).numBelow
  have n4 : NumBelow (xLeafK layer b).2.1 (Stmt.valsList (xLeafK layer b).1) :=
    kMsg_numBelow (show xPad + 5 ≤ (xCw layer b).2.1 + 2 by simp [xPad]; omega) hcellNB
  have n5 : NumBelow (xMk layer b).2.1 (Stmt.valsList (xMk layer b).1) :=
    merkleT_numBelow 16 0 _ _ (by simp [xPad]; omega) ⟨1, by omega, rfl⟩ ⟨_, by omega, rfl⟩
      (fun j hj => by rw [Nat.zero_add]; exact (hbits j hj).mono' (by omega))
      (fun l nd h => (hnodes l nd h).mono' (by omega))
  simp only [valsList_append]
  exact (n1.mono (by omega)).append ((n2.mono (by omega)).append ((n3.mono (by omega)).append
    ((n4.mono b3).append n5)))

/-! ## The prologue's facts, kept -/

theorem XPre.congr {σ σ' : Val} (h : XPre σ) (hag : AgreeBelow 196 σ σ') : XPre σ' := by
  have hl : xLeaf σ' = xLeaf σ := by
    unfold xLeaf bitsOf
    exact bitsVal_congr fun i hi => by rw [hag.apply ⟨2 + i, by omega, rfl⟩]
  refine ⟨fun j hj => ?_, fun l hl' => ?_, fun s hs => ?_, fun i hi => ?_⟩
  · rw [show xBit j = V.n (2 + j) from rfl, hag.apply ⟨2 + j, by omega, rfl⟩]; exact h.bits j hj
  · rw [show xNode l = V.n (34 + 3 * (31 - l)) from rfl, hag.apply ⟨_, by omega, rfl⟩, hl]
    exact h.nodes l hl'
  · rw [show xPower s = V.n (128 + s) from rfl, hag.apply ⟨_, by omega, rfl⟩]; exact h.powers s hs
  · rw [show xTag i = V.n (138 + i) from rfl, hag.apply ⟨_, by omega, rfl⟩]; exact h.tags i hi

theorem xLeaf_eq {σ : Val} {L : Nat} (hL : L < 2 ^ 32)
    (h : ∀ j < 32, σ (.n (2 + j)) = if L.testBit j then 1 else 0) : xLeaf σ = L := by
  unfold xLeaf bitsOf
  rw [← bitsVal_testBit hL]
  refine bitsVal_congr fun i hi => ?_
  rw [h i hi]
  cases L.testBit i <;> simp

end
end LeanVM.Guest.B1.Sig
