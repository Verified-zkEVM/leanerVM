/-
  LeanVM.Guest.B1.Da.VectorSound

  `da_vector_cell`'s core IR gives its meaning (TRIAGE G #93).
-/

module

public import LeanVM.Guest.B1.Da.VectorChk
public import LeanVM.Guest.B1.Da.VectorChain
public import LeanVM.Guest.B1.Da.VectorChain0
public import LeanVM.Guest.B1.Da.VectorChain1
public import LeanVM.Guest.B1.Da.VectorChain2
public import LeanVM.Guest.B1.Da.VectorChain3
public import LeanVM.Guest.B1.Da.VectorChain4

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Main

@[expose] public section

/-- The weights `da_vector_cell` hints, read off its valuation. -/
def vecWsOf (σ : Val) : List E := (List.range 256).map fun k => σ (.n (k + 1))

/-- **`da_vector_cell`'s body, at a valuation**: under any call relation (it calls nothing), it
returns its frame run's pointer, and the meaning holds with the weights `vecWsOf σ`. -/
theorem da_vector_cell_val {C : CallRel} {rd : Reader} {σ : Val} {args rets : List E}
    (hpar : Data.core28.params.map σ = args)
    (hb : Stmt.HoldsList C rd σ (Fn.body Data.core28) False (fun rs => rs = rets)) :
    ∃ dg, args = [dg] ∧ rets = [σ (.n 4462)] ∧ (vecWsOf σ).length = LeanDa.cellSymbols ∧
      IsInK (σ (.n 4462)) ∧
      (∀ k < LeanDa.cellSymbols, ∀ w, rd ((σ (.n 4462)).limb 0 * Parameters.gpow k) = some w →
        w = (vecWsOf σ).getD k 0) ∧
      ReadsAt rd dg (digestCells (keccak256 ((vecWsOf σ).flatMap Node.extensionElementBytes))) := by
  have hok := vec_tmpl_ok
  have hch := vec_tail_ok
  unfold vecTmplOk at hok
  unfold vecTailOk at hch
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok hch
  obtain ⟨⟨⟨⟨⟨hshape, hnb⟩, hd0⟩, hd1⟩, hfr⟩, hcp⟩ := hch
  have hchk : (vecSpec vecTail).check vecTail = true :=
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
    have hT : vecTail = A.drop 3329 := by rw [vecTail, hsp]; rfl
    rw [hT] at hchk hd0 hd1 hfr hcp
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨rfl, -⟩, htm⟩ := hok
    rw [splitBody_eq hsp, holdsList_atoms_ret] at hb
    obtain ⟨hat, hrets⟩ := hb
    rw [hparams] at hpar
    subst hpar
    have hr : [σ (.n 4462)] = rets := hrets
    subst hr
    refine ⟨σ (.n 0), rfl, rfl, ?_⟩
    have htmpl : ∀ a ∈ tmplV, a.Holds rd σ := fun a ha => by
      rw [← atomsEqb_sound htm] at ha
      exact hat a (List.mem_of_mem_drop (List.mem_of_mem_take ha))
    have hC : ∀ a ∈ A.drop 3329, a.Holds rd σ := fun a ha => hat a (List.mem_of_mem_drop ha)
    have hcells : ∀ p < 128, [σ (.n (255 + 25 * p + 8)), σ (.n (255 + 25 * p + 17)),
        σ (.n (255 + 25 * p + 26))] = Digest.pairCells (σ (.n (2 * p + 1)))
          (σ (.n (2 * p + 2))) :=
      fun p hp => vpair_fwd fun a ha => htmpl a (List.mem_flatMap.mpr ⟨p, List.mem_range.mpr hp, ha⟩)
    obtain ⟨hd, -⟩ := chain_final hchk rfl hC (pre := []) (n := 0) rfl
      (fun c => (cellsOfState_zero false c).symm)
    have hv : ((vecSpec (A.drop 3329)).vals σ).take ((vecSpec (A.drop 3329)).len / 16) =
        (List.range 128).flatMap fun p => Digest.pairCells (σ (.n (2 * p + 1))) (σ (.n (2 * p + 2))) := by
      rw [show (vecSpec (A.drop 3329)).len / 16 = 384 by simp [vecSpec], List.take_of_length_le
        (by simp [vecSpec, ChainSpec.vals, vcells])]
      simp only [vecSpec, ChainSpec.vals, List.map_flatMap]
      refine List.flatMap_congr fun p hp => ?_
      rw [← hcells p (List.mem_range.mp hp)]
      rfl
    have hbytes : cellsBytes ((List.range 128).flatMap fun p =>
        Digest.pairCells (σ (.n (2 * p + 1))) (σ (.n (2 * p + 2)))) =
        (vecWsOf σ).flatMap Node.extensionElementBytes := by
      rw [vecWsOf, show (256 : ℕ) = 2 * 128 from rfl, flatMap_pairs, cellsBytes, List.flatMap_assoc]
      refine List.flatMap_congr fun p _ => ?_
      rw [← cellsBytes, pair_bytes]
    rw [hv, List.nil_append, hbytes] at hd
    obtain ⟨hp, hframe⟩ := frame_sound hfr hC
    refine ⟨by simp [vecWsOf, LeanDa.cellSymbols], ?_, ?_, ?_⟩
    · rw [copy_sound hcp hC]; exact hp
    · intro k hk w hw
      rw [copy_sound hcp hC] at hw
      rw [hframe k (by simpa [wRun, LeanDa.cellSymbols] using hk) w hw]
      simp [wRun, vecWsOf, List.getD_eq_getElem?_getD,
        show k < 256 by simpa [LeanDa.cellSymbols] using hk]
    · intro k hk
      simp only [digestCells, List.length_cons, List.length_nil] at hk
      rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
      · have := load_sound hd0 hC
        rw [show ((vecSpec (A.drop 3329)).outV ((vecSpec (A.drop 3329)).nb - 1) 0) =
          ((vecSpec (A.drop 3329)).outV ((vecSpec (A.drop 3329)).nb - 1) ((0 : Fin 13) : ℕ))
          from rfl] at this
        simp only [digestCells, List.getElem_cons_zero]
        rw [← hd]; exact this
      · have := load_sound hd1 hC
        rw [show ((vecSpec (A.drop 3329)).outV ((vecSpec (A.drop 3329)).nb - 1) 1) =
          ((vecSpec (A.drop 3329)).outV ((vecSpec (A.drop 3329)).nb - 1) ((1 : Fin 13) : ℕ))
          from rfl] at this
        simp only [digestCells, List.getElem_cons_succ, List.getElem_cons_zero]
        rw [← hd]; exact this
  · exact absurd hok (by simp)

/-- **`da_vector_cell`'s core IR gives its meaning.** -/
theorem da_vector_cell_holds : da_vector_cell_sound_Spec := by
  intro rd args rets hrel
  obtain ⟨σ, hpar, hb⟩ := (rel_iff_sem find_da_vector_cell _ _).mp hrel
  obtain ⟨dg, rfl, rfl, hl, hp, hfr, hrd⟩ := da_vector_cell_val hpar hb
  exact ⟨vecWsOf σ, hl, hp, hfr, hrd⟩

end
end LeanVM.Guest.B1.Da
