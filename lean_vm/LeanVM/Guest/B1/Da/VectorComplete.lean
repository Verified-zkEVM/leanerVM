/-
  LeanVM.Guest.B1.Da.VectorComplete

  `da_vector_cell`, completely: `256` weights (the hint) in a frame run at `p`, their digest's
  cells in memory at its argument, give its core IR relation returning `p` (TRIAGE G #93).
-/

module

public import LeanVM.Guest.B1.Da.VectorSound
public import LeanVM.Guest.B1.Da.VectorCChk
public import LeanVM.Guest.B1.Digest.PairComplete
public import LeanVM.Guest.B1.Digest.ChainFilter

/-!
# `da_vector_cell`, completely

The honest valuation is the body evaluated on the digest's pointer (`Fwd.ev`), the hinted weights
the honest ones and the frame address `p`. The template's packs hold (`vpair_holds`) and pack the
weights into canonical cells; the chain's inputs are canonical, so every atom but the two stores
holds, and the chain's digest (`chain_final` on the block without its stores, `check_filter`) is
the digest the memory holds at the argument, so the stores hold too.
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Main LeanVM.Guest.B1.Fwd

@[expose] public section

variable {rd : Reader}

/-- `da_vector_cell`'s meaning, for given weights in a frame run at `p` and their digest at its
argument, gives its core IR. -/
def da_vector_cell_complete_Spec : Prop :=
  ∀ (rd : Reader) (dg p : E) (ws : List E), ws.length = LeanDa.cellSymbols → IsInK p →
    (∀ k < LeanDa.cellSymbols, ∀ w, rd (p.limb 0 * Parameters.gpow k) = some w → w = ws.getD k 0) →
    ReadsAt rd dg (digestCells (keccak256 (ws.flatMap Node.extensionElementBytes))) →
    coreProgram.Rel rd "da_vector_cell" [dg] [p]

/-- **A pack of two stack words holds** on an evaluated valuation. -/
theorem vpair_holds {S : List Atom} {w : ℕ → E} {σ : Val} {s t : V} {b : ℕ}
    (hg : ∀ a ∈ vpairA s t b, Good rd S w σ a) : ∀ a ∈ vpairA s t b, a.Holds rd σ := by
  have g := hg
  simp only [vpairA, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true, and_true] at g
  obtain ⟨h2, h3, -, c6, m7, a8, a9, c10, m11, a12, c13, m14, -, c15, m16, a17, a18, c19,
    m20, a21, c22, m23, -, c24, m25, a26⟩ := g
  simp only [Good] at c6 a8 a9 c10 a12 c13 c15 a17 a18 c19 a21 c22 c24 a26
  have mul_eq : ∀ {d x y : ℕ}, x < d → y < d → Good rd S w σ (.mul (.n d) (.n x) (.n y)) →
      σ (.n d) = σ (.n x) * σ (.n y) := by
    intro d x y hx hy h
    simp only [Good] at h
    rwa [ite_pos' ⟨hx, hy⟩] at h
  have e7 := mul_eq (by omega) (by omega) m7
  have e11 := mul_eq (by omega) (by omega) m11
  have e14 := mul_eq (by omega) (by omega) m14
  have e16 := mul_eq (by omega) (by omega) m16
  have e20 := mul_eq (by omega) (by omega) m20
  have e23 := mul_eq (by omega) (by omega) m23
  have e25 := mul_eq (by omega) (by omega) m25
  simp only [Good] at h2 h3
  have v2 : σ (.n (b + 2)) = ofK ((σ s).limb 0) := by
    have := h2 0 (by simp); simpa [limbAt_zero] using this
  have v3 : σ (.n (b + 3)) = ofK ((σ s).limb 1) := by
    have := h2 1 (by simp); simpa [limbAt_one] using this
  have v4 : σ (.n (b + 4)) = ofK ((σ t).limb 0) := by
    have := h3 0 (by simp); simpa [limbAt_zero] using this
  have v5 : σ (.n (b + 5)) = ofK ((σ t).limb 1) := by
    have := h3 1 (by simp); simpa [limbAt_one] using this
  have v14 : σ (.n (b + 14)) = ofK ((σ s).limb 2) := by
    rw [e14, a12, e11, a9, c10, c13, v2, v3, top_eq]
  have v23 : σ (.n (b + 23)) = ofK ((σ t).limb 2) := by
    rw [e23, a21, e20, a18, c19, c22, v4, v5, top_eq]
  simp only [vpairA, List.forall_mem_cons, Atom.Holds, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true, and_true]
  exact ⟨trivial, trivial, ⟨by rw [v2]; exact ofK_isInK _, by rw [v3]; exact ofK_isInK _⟩,
    c6, e7, a8, a9, c10, e11, a12, c13, e14, ⟨by rw [v14]; exact ofK_isInK _,
    by rw [v4]; exact ofK_isInK _⟩, c15, e16, a17, a18, c19, e20, a21, c22, e23,
    ⟨by rw [v5]; exact ofK_isInK _, by rw [v23]; exact ofK_isInK _⟩, c24, e25, a26⟩

/-- The oracle of the weights' hint and the frame address. -/
def vecOrc (p : E) (ws : List E) (j : ℕ) : E := if j = 4461 then p else ws.getD (j - 1) 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
/-- **`da_vector_cell` is complete.** -/
theorem da_vector_cell_complete : da_vector_cell_complete_Spec := by
  intro rd dg p ws hwl hp hfr hdig
  simp only [LeanDa.cellSymbols] at hwl hfr
  have hok := vec_tmpl_ok
  have hch := vec_tail_ok
  have hcok := vecc_ok
  unfold vecTmplOk at hok
  unfold vecTailOk at hch
  unfold vecCOk at hcok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok hch
  simp only [Bool.and_eq_true, Option.isSome_iff_exists, decide_eq_true_eq, List.all_eq_true,
    Bool.or_eq_true, Bool.not_eq_true'] at hcok
  obtain ⟨⟨⟨⟨⟨hshape, hnb⟩, -⟩, -⟩, hfrA⟩, hcp⟩ := hch
  obtain ⟨⟨⟨⟨⟨c', hchk⟩, hst⟩, hcanT⟩, hneedsT⟩, hcok⟩ := hcok
  have hchkT : (vecSpec vecTail).check vecTail = true :=
    ChainSpec.check_of_parts hshape fun k hk => by
      rcases Nat.lt_or_ge k 10 with h1 | h1
      · exact ChainSpec.partOk_sound vec_chain0_ok k (by omega) h1
      rcases Nat.lt_or_ge k 20 with h2 | h2
      · exact ChainSpec.partOk_sound vec_chain1_ok k h1 h2
      rcases Nat.lt_or_ge k 30 with h3 | h3
      · exact ChainSpec.partOk_sound vec_chain2_ok k h2 h3
      rcases Nat.lt_or_ge k 38 with h4 | h4
      · exact ChainSpec.partOk_sound vec_chain3_ok k h3 h4
      · exact ChainSpec.partOk_sound vec_chain4_ok k h4 (by omega)
  obtain ⟨hparams, hok⟩ := hok
  split at hok
  · rename_i A vs hsp
    rw [hsp] at hcok
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true,
      Bool.not_eq_true'] at hcok
    obtain ⟨⟨hcanC, hneedsC⟩, hhint⟩ := hcok
    have hT : vecTail = A.drop 3329 := by rw [vecTail, hsp]; rfl
    rw [hT] at hchkT hcp hfrA
    have hvo := vec_out
    rw [hT] at hvo
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨rfl, hA3329⟩, htm⟩ := hok
    have hbody := splitBody_eq hsp
    set S := storesOf 1 (Fn.body Data.core28) with hSdef
    let w : ℕ → E := vecOrc p ws
    obtain ⟨σ, hσ⟩ : ∃ σ : Val, σ = B1.Val.ofArgs (ev rd w [dg] (Fn.body Data.core28)) := ⟨_, rfl⟩
    have hidx : ∀ v, σ v = σ (.n v.idx) := fun v => by rw [hσ]; rfl
    obtain ⟨-, -, hgs⟩ := ev_spec rd w (Fn.body Data.core28) [dg] hchk
    rw [show [dg].length = 1 from rfl, ← hσ] at hgs
    have hg : ∀ a ∈ A, Good rd S w σ a := fun a ha =>
      hgs (.atom a) (by rw [hbody]; exact List.mem_append_left _ (List.mem_map_of_mem ha))
    have e0 : σ (.n 0) = dg := by rw [hσ]; exact ev_params rd _ (l := [dg]) hchk (by simp)
    -- the split of the atoms
    have hA : A = A.take 1 ++ (A.drop 1).take 3328 ++ A.drop 3329 := by
      have h1 : (A.drop 1).drop 3328 = A.drop 3329 := by simp
      rw [List.append_assoc, ← h1, List.take_append_drop, List.take_append_drop]
    rw [atomsEqb_sound htm, hhint] at hA
    have hmT : ∀ a ∈ tmplV, a ∈ A := fun a ha => by rw [hA]; simp [ha]
    have hmC : ∀ a ∈ A.drop 3329, a ∈ A := fun a ha => List.mem_of_mem_drop ha
    -- the weights
    have hw : ∀ k < 256, σ (.n (k + 1)) = ws.getD k 0 := by
      intro k hk
      have h := hg wHint (by
        rw [hA]; exact List.mem_append_left _ (List.mem_append_left _ (List.mem_singleton_self _)))
      have := h (.n (k + 1)) (by simp [wRun]; omega)
      rw [this]
      simp only [w, vecOrc]
      rw [ite_neg' (by simp; omega)]
      rfl
    -- the template
    have htmpl : ∀ a ∈ tmplV, a.Holds rd σ := by
      intro a ha
      obtain ⟨q, hq, ha'⟩ := List.mem_flatMap.mp ha
      exact vpair_holds (fun b hb => hg b (hmT b (List.mem_flatMap.mpr ⟨q, hq, hb⟩))) a ha'
    have hcells : ∀ q < 128, [σ (.n (255 + 25 * q + 8)), σ (.n (255 + 25 * q + 17)),
        σ (.n (255 + 25 * q + 26))] = Digest.pairCells (σ (.n (2 * q + 1))) (σ (.n (2 * q + 2))) :=
      fun q hq => vpair_fwd fun a ha =>
        htmpl a (List.mem_flatMap.mpr ⟨q, List.mem_range.mpr hq, ha⟩)
    have hcanA : ∀ i ∈ vecA, IsCanonical128 (σ (.n i)) := by
      intro i hi
      obtain ⟨q, hq, hi⟩ := List.mem_flatMap.mp hi
      have hm : σ (.n i) ∈ [σ (.n (255 + 25 * q + 8)), σ (.n (255 + 25 * q + 17)),
          σ (.n (255 + 25 * q + 26))] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
        rcases hi with rfl | rfl | rfl <;> simp
      rw [hcells q (List.mem_range.mp hq)] at hm
      exact pairCells_canonical _ _ _ hm
    -- the frame address
    obtain ⟨fa, hfa, hfp⟩ := List.any_eq_true.mp hfrA
    have hfa' : fa = .frameAddr (.n 4461) wRun := by
      cases fa <;> simp only [isFrameAt, Bool.false_eq_true, Bool.and_eq_true,
        decide_eq_true_eq] at hfp
      rw [hfp.1, hfp.2]
    subst hfa'
    have h4461 : σ (.n 4461) = p := by
      have h : Good rd S w σ (.frameAddr (.n 4461) wRun) := hg _ (hmC _ hfa)
      simp only [Good] at h
      rw [h]
      simp [w, vecOrc]
    -- the stores
    have hq : ∀ a, isLoadB a = false → decide (a ∉ S) = true := by
      intro a ha
      simp only [decide_eq_true_eq]
      intro hm
      rw [hst] at hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl <;> simp [isLoadB] at ha
    -- the tail
    have hC : ∀ a ∈ A.drop 3329, a.Holds rd σ := by
      refine atoms_holds_stores (S := S) (w := w) hidx hcanC (fun a ha => hg a (hmC a ha)) hcanA
        (fun a ha hnS hns => Or.inl ?_) (fun h1 a ha haS => ?_)
      · rcases hneedsC a ha with (h | h) | h
        · rw [hns] at h; exact absurd h (by simp)
        · exact absurd h hnS
        · subst h
          refine ⟨by rw [h4461]; exact hp, fun k hk v hv => ?_⟩
          rw [h4461] at hv
          have hk' : k < 256 := by simpa [wRun] using hk
          rw [hfr k hk' v hv]
          simp only [wRun, List.getElem_map, List.getElem_range]
          exact (hw k hk').symm
      · have hA' : ∀ b ∈ (A.drop 3329).filter (fun a => decide (a ∉ S)), b.Holds rd σ :=
          fun b hb => h1 b (List.mem_filter.mp hb).1 (by simpa using (List.mem_filter.mp hb).2)
        have hchk' : (vecSpec (A.drop 3329)).check ((A.drop 3329).filter
            (fun a => decide (a ∉ S))) = true := by rw [check_filter hq]; exact hchkT
        obtain ⟨hd, -⟩ := chain_final hchk' rfl hA' (pre := []) (n := 0) rfl
          (fun c => (cellsOfState_zero false c).symm)
        have hv : ((vecSpec (A.drop 3329)).vals σ).take ((vecSpec (A.drop 3329)).len / 16) =
            (List.range 128).flatMap fun q =>
              Digest.pairCells (σ (.n (2 * q + 1))) (σ (.n (2 * q + 2))) := by
          rw [show (vecSpec (A.drop 3329)).len / 16 = 384 by simp [vecSpec], List.take_of_length_le
            (by simp [vecSpec, ChainSpec.vals, vcells])]
          simp only [vecSpec, ChainSpec.vals, List.map_flatMap]
          refine List.flatMap_congr fun q hq => ?_
          rw [← hcells q (List.mem_range.mp hq)]
          rfl
        have hws : vecWsOf σ = ws := by
          refine List.ext_getElem (by simp [vecWsOf, hwl]) fun k h1 h2 => ?_
          simp only [vecWsOf, List.getElem_map, List.getElem_range]
          rw [hw k (by simpa [vecWsOf] using h1), List.getD_eq_getElem _ _ h2]
        have hbytes : cellsBytes ((List.range 128).flatMap fun q =>
            Digest.pairCells (σ (.n (2 * q + 1))) (σ (.n (2 * q + 2)))) =
            ws.flatMap Node.extensionElementBytes := by
          rw [← hws, vecWsOf, show (256 : ℕ) = 2 * 128 from rfl, flatMap_pairs, cellsBytes,
            List.flatMap_assoc]
          refine List.flatMap_congr fun q _ => ?_
          rw [← cellsBytes, pair_bytes]
        rw [hv, List.nil_append, hbytes, hvo.1, hvo.2] at hd
        simp only [Prod.ext_iff] at hd
        rw [hst] at haS
        simp only [List.mem_cons, List.not_mem_nil, or_false] at haS
        rcases haS with rfl | rfl
        · show LoadHolds rd (σ (.n 0)) 0 (σ (.n 4448))
          rw [e0, hd.1]
          exact hdig 0 (by simp [digestCells])
        · show LoadHolds rd (σ (.n 0)) 1 (σ (.n 4449))
          rw [e0, hd.2]
          exact hdig 1 (by simp [digestCells])
    have hat : ∀ a ∈ A, a.Holds rd σ := by
      intro a ha
      rw [hA] at ha
      simp only [List.mem_append, List.mem_singleton] at ha
      rcases ha with (rfl | ha) | ha
      · trivial
      · exact htmpl a ha
      · exact hC a ha
    refine (rel_iff_sem find_da_vector_cell _ _).mpr ⟨σ, by rw [hparams]; simp [e0], ?_⟩
    rw [hbody, holdsList_atoms_ret]
    refine ⟨hat, ?_⟩
    show [σ (.n 4462)] = [p]
    rw [copy_sound hcp hC, h4461]
  · exact absurd hok (by simp)

end
end LeanVM.Guest.B1.Da
